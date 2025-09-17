import os
import sys
import google.generativeai as genai
from github import Github

def generate_ai_summary(diff):
    """
    Generate a concise summary of the changes from a diff using an AI model.
    """
    model = genai.GenerativeModel('gemini-2.5-pro')
    prompt = f"""
    Please provide a concise, high-level summary of the following git diff.
    Focus on the key changes and their purpose. Do not describe the changes line-by-line.
    Use bullet points for clarity.

    Diff:
    {diff}
    """
    try:
        response = model.generate_content(prompt)
        return response.text
    except Exception as e:
        return f"Error generating summary: {e}"

def generate_summary(diff):
    """
    Generate a summary of the changes from a diff.
    """
    summary = "### 🤖 AI-Generated PR Summary\n\n"
    summary += "**Files Changed:**\n"
    files = set()
    # A simple parser for changed files from the diff
    for line in diff.splitlines():
        if line.startswith("diff --git"):
            # Extracts file path like 'b/ArkLib/Data/Hash/Poseidon2.lean' -> 'ArkLib/Data/Hash/Poseidon2.lean'
            try:
                file_path = line.split(" ")[-1][2:]
                files.add(file_path)
            except IndexError:
                continue # Ignore malformed diff lines

    for file in sorted(list(files)):
        summary += f"- `{file}`\n"

    summary += "\n**Overview of Changes:**\n"
    summary += generate_ai_summary(diff)

    return summary

def count_sorries(diff):
    """
    Count the number of new "sorry"s in a diff.
    """
    # We only want to count additions
    new_sorries = 0
    for line in diff.splitlines():
        if line.startswith('+') and 'sorry' in line:
            # Exclude lines that are not code changes, like '+++ b/file.lean'
            if not line.startswith('+++'):
                new_sorries += 1
    return new_sorries

if __name__ == "__main__":
    # Ensure Gemini API key is available
    if "GEMINI_API_KEY" not in os.environ:
        print("Error: GEMINI_API_KEY environment variable not set.")
        sys.exit(1)

    genai.configure(api_key=os.environ["GEMINI_API_KEY"])

    diff = os.environ["PR_DIFF"]
    summary = generate_summary(diff)
    sorries = count_sorries(diff)

    summary += f"\n\n**New 'sorry's:** {sorries}\n"

    # Ensure GitHub token and other variables are available for posting the comment
    if "GITHUB_TOKEN" not in os.environ or "GITHUB_REPOSITORY" not in os.environ or "PR_NUMBER" not in os.environ:
        # If we're not in the GitHub Actions context, just print the summary
        print(summary)
    else:
        g = Github(os.environ["GITHUB_TOKEN"])
        repo = g.get_repo(os.environ["GITHUB_REPOSITORY"])
        pr = repo.get_pull(int(os.environ["PR_NUMBER"]))
        pr.create_issue_comment(summary)
