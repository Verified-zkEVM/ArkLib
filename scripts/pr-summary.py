import os
import re
import sys
from datetime import datetime
import google.generativeai as genai
from github import Github, Auth

# --- Constants ---
MAX_DIFF_TOKENS = 1_500_000
COMMENT_IDENTIFIER = "<!-- gemini-pr-summary -->"
SORRY_KEYWORDS = ["theorem", "def", "lemma", "instance", "example", "corollary", "proposition"]

# --- AI Summary Generation ---
def generate_ai_summary(diff):
    """Generates a concise, high-level summary of a git diff using the Gemini API."""
    if len(diff) > MAX_DIFF_TOKENS:
        diff = diff[:MAX_DIFF_TOKENS]
        truncated = True
    else:
        truncated = False

    model = genai.GenerativeModel('gemini-1.5-pro-latest')
    prompt = f"""
    Please provide a concise, high-level summary of the following git diff.
    Focus on the key changes and their purpose. Do not describe the changes line-by-line.
    Use bullet points for clarity if needed.

    Diff:
    {diff}
    """
    try:
        response = model.generate_content(prompt)
        return response.text, truncated
    except Exception as e:
        return f"Error generating summary: {e}", False

# --- Diff Analysis ---
def analyze_diff(diff):
    """Parses a git diff to extract statistics and track 'sorry's."""
    files_changed = set()
    lines_added = 0
    lines_removed = 0
    added_sorries = []
    removed_sorries = []
    
    current_file = ""
    context_line = ""

    for line in diff.splitlines():
        if line.startswith("diff --git"):
            current_file = line.split(" b/")[-1]
            files_changed.add(current_file)
            context_line = "" # Reset context for new file
        
        elif line.startswith("+++"):
            continue
        elif line.startswith("---"):
            continue

        elif line.startswith('+'):
            lines_added += 1
            if 'sorry' in line:
                added_sorries.append(f'`{context_line.strip()}`' if context_line else f'in `{current_file}`')
        elif line.startswith('-'):
            lines_removed += 1
            if 'sorry' in line:
                removed_sorries.append(f'`{context_line.strip()}`' if context_line else f'in `{current_file}`')
        
        # Track the last relevant definition line as context for sorries
        if any(keyword in line for keyword in SORRY_KEYWORDS):
            # Strip leading +/- and whitespace
            context_line = re.sub(r"^[+-]\s*", "", line)


    stats = {
        "files_changed": len(files_changed),
        "lines_added": lines_added,
        "lines_removed": lines_removed,
    }
    return stats, added_sorries, removed_sorries

# --- Comment Formatting ---
def format_summary(ai_summary, stats, added_sorries, removed_sorries, truncated):
    """Formats the final summary comment in Markdown."""
    
    summary = f"### 🤖 Gemini PR Summary\n\n{COMMENT_IDENTIFIER}\n\n"
    summary += f"{ai_summary}\n"
    if truncated:
        summary += "> *Note: The diff was too large to be fully analyzed and was truncated.*\n"
    
    summary += "\n---\n\n"
    summary += "**Analysis of Changes**\n\n"
    summary += "| Metric | Count |\n| --- | --- |\n"
    summary += f"| 📝 **Files Changed** | {stats['files_changed']} |\n"
    summary += f"| ✅ **Lines Added** | {stats['lines_added']} |\n"
    summary += f"| ❌ **Lines Removed** | {stats['lines_removed']} |\n"

    summary += "\n---\n\n"
    summary += "**`sorry` Tracking**\n\n"
    
    if removed_sorries:
        summary += f"*   ✅ **Removed:** {len(removed_sorries)} `sorry`s\n"
        for sorry in removed_sorries:
            summary += f"    *   in {sorry}\n"
    
    if added_sorries:
        summary += f"*   ❌ **Added:** {len(added_sorries)} `sorry`s\n"
        for sorry in added_sorries:
            summary += f"    *   in {sorry}\n"

    if not added_sorries and not removed_sorries:
        summary += "*   No `sorry`s were added or removed.\n"

    timestamp = datetime.utcnow().strftime("%Y-%m-%d %H:%M UTC")
    summary += f"\n---\n\n*Last updated: {timestamp}. See the [main CI run](https://github.com/{os.environ['GITHUB_REPOSITORY']}/actions) for build status.*"
    
    return summary

# --- GitHub Interaction ---
def post_github_comment(summary):
    """Finds and updates an existing comment or creates a new one."""
    token = os.environ["GITHUB_TOKEN"]
    repo_name = os.environ["GITHUB_REPOSITORY"]
    pr_number = int(os.environ["PR_NUMBER"])

    auth = Auth.Token(token)
    g = Github(auth=auth)
    repo = g.get_repo(repo_name)
    pr = repo.get_pull(pr_number)

    existing_comment = None
    for comment in pr.get_issue_comments():
        if COMMENT_IDENTIFIER in comment.body:
            existing_comment = comment
            break
    
    if existing_comment:
        existing_comment.edit(summary)
        print("Updated existing comment.")
    else:
        pr.create_issue_comment(summary)
        print("Created a new comment.")

# --- Main Execution ---
if __name__ == "__main__":
    if "GEMINI_API_KEY" not in os.environ:
        print("Error: GEMINI_API_KEY environment variable not set.")
        sys.exit(1)
    genai.configure(api_key=os.environ["GEMINI_API_KEY"])

    try:
        with open("pr.diff", "r") as f:
            diff = f.read()
    except FileNotFoundError:
        print("Error: pr.diff not found.")
        sys.exit(1)

    stats, added_sorries, removed_sorries = analyze_diff(diff)
    ai_summary, truncated = generate_ai_summary(diff)
    
    final_summary = format_summary(ai_summary, stats, added_sorries, removed_sorries, truncated)
    
    if "GITHUB_TOKEN" not in os.environ:
        print("Not in GitHub Actions context. Printing summary instead of posting:")
        print(final_summary)
    else:
        post_github_comment(final_summary)