import os
import sys
import subprocess
import re
import argparse
import concurrent.futures
import google.generativeai as genai
import urllib.error
import urllib.request

import shutil

# --- ⚙️ Configuration ---
ISSUE_LABEL = 'proof wanted'
MAX_IMPORT_FILE_SIZE = 25000  # Max size in bytes for an imported file to be included in the context.
FETCH_TIMEOUT_SEC = 30
USER_AGENT = "ArkLib-sorry-tracker/1.0"


# --- Helper Functions ---

def check_dependencies():
    """Checks if required command-line tools are installed."""
    if not shutil.which("gh"):
        print("❌ Error: The GitHub CLI ('gh') is not installed or not in your PATH.", file=sys.stderr)
        print("   Please install it from https://cli.github.com/", file=sys.stderr)
        sys.exit(1)
    if not shutil.which("gcloud"):
        print("⚠️  Warning: The Google Cloud SDK ('gcloud') is not found in your PATH.", file=sys.stderr)
        print("   If you experience authentication issues, installing it may help:", file=sys.stderr)
        print("   https://cloud.google.com/sdk/docs/install", file=sys.stderr)

def fetch_urls_content(urls: list[str]) -> str:
    """Fetches content from a list of URLs and returns the combined text."""
    if not urls:
        return ""

    print(f"📚 Fetching content from {len(urls)} reference URL(s)...")

    chunks: list[str] = []
    failures: list[str] = []
    for url in urls:
        try:
            req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
            with urllib.request.urlopen(req, timeout=FETCH_TIMEOUT_SEC) as resp:
                raw = resp.read()
            text = raw.decode("utf-8", errors="replace")
            chunks.append(f"--- Content from {url} ---\n{text}")
        except (urllib.error.URLError, TimeoutError, ValueError) as e:
            failures.append(f"{url}: {e}")

    if failures:
        print("❌ Failed to fetch one or more reference URLs:", file=sys.stderr)
        for msg in failures:
            print(f"   {msg}", file=sys.stderr)
        sys.exit(1)

    return "\n\n".join(chunks)



def find_and_read_imports(file_content: str, repo_root: str, web_search: bool) -> str:
    """Finds all Lean imports, resolves them to files, and returns their concatenated content."""
    import_regex = re.compile(r"^import\s+([^\s]+)")
    imported_content = []
    
    # A pre-computed map of the first part of an import to its package directory.
    package_map = {}
    lake_packages_path = os.path.join(repo_root, '.lake', 'packages')
    if os.path.isdir(lake_packages_path):
        for package_name in os.listdir(lake_packages_path):
            capitalized_name = package_name.capitalize()
            package_map[capitalized_name] = os.path.join(lake_packages_path, package_name)

    for line in file_content.splitlines():
        match = import_regex.match(line)
        if not match:
            continue
            
        import_path_str = match.group(1)
        import_parts = import_path_str.split('.')
        
        relative_path = os.path.join(*import_parts) + '.lean'
        
        full_path = None
        
        # 1. Check dependencies
        if import_parts and import_parts[0] in package_map:
            package_root = package_map[import_parts[0]]
            potential_path = os.path.join(package_root, relative_path)
            if os.path.exists(potential_path):
                full_path = potential_path

        # 2. Check project root and src/
        if not full_path:
            # Check from project root
            potential_path_root = os.path.join(repo_root, relative_path)
            if os.path.exists(potential_path_root):
                full_path = potential_path_root
            else:
                # Check from a 'src' directory if it exists
                potential_path_src = os.path.join(repo_root, 'src', relative_path)
                if os.path.exists(potential_path_src):
                    full_path = potential_path_src

        if full_path:
            try:
                with open(full_path, 'r', encoding='utf-8') as f:
                    content = f.read()
                    if len(content) < MAX_IMPORT_FILE_SIZE:
                        imported_content.append(f"\n---\n-- Content from: {import_path_str}\n---\n{content}")
                    else:
                        print(f"⚠️  Skipping large import: {import_path_str}")
            except OSError as e:
                print(f"⚠️  Could not read import file {full_path}: {e}", file=sys.stderr)
        elif web_search:
            print(
                f"⚠️  Could not resolve import '{import_path_str}'; "
                "web-search fallback is not implemented.",
                file=sys.stderr,
            )
        else:
            print(f"⚠️  Could not find imported file for: {import_path_str}")

    return "".join(imported_content)


def run_command(command):

    """Runs a command and returns its stdout, exiting on failure."""
    try:
        result = subprocess.run(
            command, check=True, capture_output=True, text=True, encoding='utf-8'
        )
        return result.stdout.strip()
    except subprocess.CalledProcessError as e:
        print(f"❌ Error running command: {' '.join(command)}\n{e.stderr}", file=sys.stderr)
        sys.exit(1)

def generate_ai_analysis(code_snippet: str, full_file_content: str, model_name: str, imports_context: str, reference_context: str) -> str:
    """Calls the Gemini API to generate a detailed analysis of a proof obligation."""
    print(f"🤖 Calling Gemini API ({model_name}) for detailed analysis...")
    try:
        model = genai.GenerativeModel(model_name)
        
        # Conditionally add the reference context to the prompt
        reference_section = ""
        if reference_context:
            reference_section = f"**External Reference Content:**\n```\n{reference_context}\n```\n\n"

        prompt = (
            "You are an expert in Lean 4 and formal mathematics. Your task is to help a user by providing a detailed "
            "comment for a proof obligation marked with `sorry`.\n\n"
            "Your response must be a markdown-formatted comment with exactly three sections. "
            "**Do not write the full proof.** Your goal is to guide the user.\n\n"
            "1.  `### Statement Explanation`: Explain what the theorem/definition states in clear, simple terms. Describe the goal and the hypotheses.\n"
            "2.  `### Context`: Explain how this statement relates to other definitions or theorems in the file, imported files, or any provided external references. For example, mention if it's a key lemma for a larger proof, if it generalizes another concept, or if it connects two different ideas.\n"
            "3.  `### Proof Suggestion`: Provide a high-level, step-by-step suggestion for how to approach the proof. Mention relevant tactics (like `simp`, `rw`, `cases`, `induction`) and specific lemmas from the provided file content that might be useful. Do not write the full proof code.\n\n"
            "---\n\n"
            "### Example\n\n"
            "**Full File Content:**\n"
            "```lean\n"
            "import Mathlib.Data.Nat.Prime\n\n"
            "def is_even (n : ℕ) : Prop :=\n"
            "  ∃ k, n = 2 * k\n\n"
            "theorem even_plus_even (a b : ℕ) (ha : is_even a) (hb : is_even b) : is_even (a + b) := by\n"
            "  sorry\n"
            "```\n\n"
            "**Declaration with `sorry`:**\n"
            "```lean\n"
            "theorem even_plus_even (a b : ℕ) (ha : is_even a) (hb : is_even b) : is_even (a + b) := by\n"
            "  sorry\n"
            "```\n\n"
            "**Your Ideal Response:**\n"
            "```markdown\n"
            "### Statement Explanation\n"
            "This theorem states that for any two natural numbers `a` and `b`, if both `a` and `b` are even, then their sum `a + b` is also even.\n\n"
            "### Context\n"
            "This is a fundamental property of even numbers and relies on the definition `is_even` provided in the same file. It's a basic building block for number theory proofs.\n\n"
            "### Proof Suggestion\n"
            "1.  Start by using the `unfold is_even` tactic to expand the definition of `is_even` in the hypotheses `ha` and `hb` and the goal.\n"
            "2.  This will give you two witnesses, let's say `k_a` and `k_b`, such that `a = 2 * k_a` and `b = 2 * k_b`.\n"
            "3.  Substitute these equations into the goal `is_even (a + b)`.\n"
            "4.  The goal will become `∃ k, 2 * k_a + 2 * k_b = 2 * k`.\n"
            "5.  Use the `ring` tactic or factor out the 2 to show that you can provide `k_a + k_b` as the witness for the existential quantifier.\n"
            "```\n\n"
            "---\n\n"
            "### User Request\n\n"
            f"**Full File Content:**\n```lean\n{full_file_content}\n```\n\n"
            f"**Imported Files Content:**\n```lean\n{imports_context}\n```\n\n"
            f"{reference_section}"
            f"**Declaration with `sorry`:**\n```lean\n{code_snippet}\n```"
        )
        
        response = model.generate_content(prompt)
        return response.text.strip()
    except Exception as e:
        print(
            f"⚠️ Warning: Gemini API call failed. Have you run 'gcloud auth application-default login'?",
            f"\n   Error: {e}",
            file=sys.stderr
        )
        return ""


def create_github_issue(title: str, body: str, repo_name: str, label: str, stable_id: str):
    """
    Uses the GitHub CLI to create an issue, checking for duplicates using a targeted search for a stable ID.
    """
    # 1. Check if an issue with our stable ID already exists.
    id_comment = f"<!-- sorry-tracker-id: {stable_id} -->"
    search_query = f'"{id_comment}" in:body repo:{repo_name} is:open'
    
    try:
        # We run the command and check its output. If it finds an issue, it will return text.
        # If it finds no issues, it will return an empty string and a non-zero exit code.
        existing_issues = run_command([
            "gh", "issue", "list",
            "--search", search_query,
            "--json", "number" # We only need to know if it exists, so we fetch a minimal field.
        ])
        
        # If the command returned anything, it means an issue was found.
        if existing_issues and existing_issues.strip() != "[]":
            # We can even parse the JSON to get the issue number for a more informative message.
            import json
            issue_number = json.loads(existing_issues)[0]['number']
            print(f"⚠️  Issue #{issue_number} already exists for '{stable_id}'. Skipping.")
            return
            
    except subprocess.CalledProcessError as e:
        # This is the expected case for "no duplicates found". 
        # `gh` exits with 1 if the search query returns no results.
        if "no issues found" in e.stderr.lower():
            pass # This is fine, it means we can proceed to create the issue.
        else:
            # For any other error, we should report it.
            print(f"❌ Error checking for existing issues: {e.stderr}", file=sys.stderr)
            return # Do not proceed if the check failed.

    # 2. If no duplicates were found, create the new issue.
    full_body = f"{body}\n\n{id_comment}"
    command = [
        "gh", "issue", "create",
        "--title", title,
        "--body", full_body,
        "--label", label
    ]
    try:
        subprocess.run(command, check=True, capture_output=True, text=True, encoding='utf-8')
        print(f"✅ Successfully created issue: '{title}'")
    except subprocess.CalledProcessError as e:
        print(f"❌ Failed to create GitHub issue.\nTitle: {title}\nError: {e.stderr}", file=sys.stderr)




def find_sorries_in_diff(diff_file_path: str, repo_root: str, web_search: bool) -> list[dict]:
    """Parses a git diff, finds newly added 'sorry's, and extracts their context."""
    sorries_to_process = []
    
    decl_regex = re.compile(
        r"^(private|protected)?\s*(noncomputable)?\s*"
        r"(theorem|lemma|def|instance|example|opaque|abbrev|inductive|structure)\s+"
    )
    name_extract_regex = re.compile(
        r".*?(?:theorem|lemma|def|instance|example|opaque|abbrev|inductive|structure)\s+"
        r"([^\s\(\{:]+)"
    )

    current_file = ""
    with open(diff_file_path, 'r', encoding='utf-8') as f:
        lines = f.readlines()

    for i, line in enumerate(lines):
        if line.startswith("diff --git"):
            # a/path/to/file.lean b/path/to/file.lean
            current_file = line.split(" b/")[-1].strip()
            continue

        if not current_file.endswith(".lean"):
            continue

        if line.startswith('+') and re.search(r'\bsorry\b', line):
            # Ignore if it's in a comment
            comment_pos = line.find("--")
            sorry_pos = line.find("sorry")
            if comment_pos != -1 and sorry_pos > comment_pos:
                continue

            # We found a new sorry. Now we need its context from the full file.
            added_line_content = line[1:].strip() # Get content of the added line, removing '+'

            full_file_path = os.path.join(repo_root, current_file)
            if not os.path.exists(full_file_path):
                print(f"⚠️ Could not find file from diff: {full_file_path}", file=sys.stderr)
                continue

            with open(full_file_path, 'r', encoding='utf-8') as f_full:
                full_file_lines = f_full.readlines()

            # Find the line number of our added 'sorry' in the full file
            sorry_line_num = -1
            # Use a different variable for the inner loop to avoid shadowing
            for line_index, file_line in enumerate(full_file_lines):
                if added_line_content == file_line.strip():
                    sorry_line_num = line_index + 1
                    break
            
            if sorry_line_num == -1:
                print(f"⚠️ Could not find the added sorry line in the full file: {current_file}", file=sys.stderr)
                continue

            # Now find the declaration header for this sorry in the full file
            current_decl_header = ""
            current_decl_linenum = 0
            # Search backwards from the line *before* the sorry
            for k in range(sorry_line_num - 2, -1, -1):
                if decl_regex.search(full_file_lines[k]):
                    current_decl_header = full_file_lines[k].strip()
                    current_decl_linenum = k + 1
                    break
            
            decl_name_match = name_extract_regex.match(current_decl_header)
            decl_name_only = decl_name_match.group(1) if decl_name_match else ""

            start_line = current_decl_linenum if current_decl_linenum > 0 else sorry_line_num
            # Ensure snippet end is not out of bounds
            end_line_num = min(sorry_line_num, len(full_file_lines))
            full_snippet = "".join(full_file_lines[start_line - 1 : end_line_num])
            full_file_content = "".join(full_file_lines)

            imports_context = find_and_read_imports(full_file_content, repo_root, web_search)
            sorries_to_process.append({
                "file_path": current_file,
                "line_num": sorry_line_num,
                "decl_name": decl_name_only,
                "snippet": full_snippet,
                "full_content": full_file_content,
                "imports_context": imports_context
            })

    return sorries_to_process

def process_sorries(sorries: list[dict], repo_name: str, reference_context: str, args):
    """Processes a list of sorries, generating AI analysis and creating GitHub issues."""
    with concurrent.futures.ThreadPoolExecutor() as executor:
        future_to_sorry = {
            executor.submit(generate_ai_analysis, s['snippet'], s['full_content'], args.model, s['imports_context'], reference_context): s 
            for s in sorries
        }
        for future in concurrent.futures.as_completed(future_to_sorry):
            sorry_info = future_to_sorry[future]
            try:
                ai_analysis = future.result()
                
                title = f"Proof obligation for `{sorry_info['decl_name']}` in `{sorry_info['file_path']}`"
                if not sorry_info['decl_name']:
                    title = f"Proof obligation in `{sorry_info['file_path']}` near line {sorry_info['line_num']}"

                analysis_section = ""
                if ai_analysis:
                    analysis_section = f"\n\n**🤖 AI Analysis:**\n{ai_analysis}"

                body = (
                    f"A proof in `{sorry_info['file_path']}` contains a `sorry`.{analysis_section}\n\n"
                    f"**Goal:** Replace the `sorry` with a complete proof.\n\n"
                    f"[Link to the sorry on GitHub](https://github.com/{repo_name}/blob/master/{sorry_info['file_path']}#L{sorry_info['line_num']})\n\n"
                    f"**Code Snippet:**\n```lean\n{sorry_info['snippet']}\n```"
                )
                
                # Generate the stable ID
                stable_id = f"{sorry_info['decl_name']}@{sorry_info['file_path']}"
                
                create_github_issue(title, body, repo_name, args.label, stable_id)
            except Exception as exc:
                print(f"❌ Error processing {sorry_info['file_path']}: {exc}", file=sys.stderr)

# --- Main Logic ---

def main():
    check_dependencies()
    parser = argparse.ArgumentParser(
        description="Find new 'sorry' statements in a git diff and create GitHub issues."
    )
    parser.add_argument(
        "--diff-file",
        required=True,
        help="The path to the diff file containing the changes to analyze."
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Simulate the script's execution without calling APIs or creating issues."
    )
    parser.add_argument(
        "--label",
        default=ISSUE_LABEL,
        help=f"The GitHub issue label to use (default: '{ISSUE_LABEL}')."
    )
    parser.add_argument(
        "--model",
        default='gemini-2.5-pro',
        help="The Gemini model to use for analysis (default: 'gemini-2.5-pro')."
    )
    parser.add_argument(
        '--reference-url',
        action='append',
        metavar='URL',
        help='A URL to a PDF or webpage to be used as context. Can be specified multiple times.'
    )
    parser.add_argument(
        '--web-search',
        action='store_true',
        help='Enable web search as a fallback for finding definitions.'
    )
    args = parser.parse_args()

    repo_root = os.getcwd()
    
    repo_name = run_command(["gh", "repo", "view", "--json", "nameWithOwner", "--jq", ".nameWithOwner"])
    
    print(f"✅ Detected repository: {repo_name}")
    
    reference_context = fetch_urls_content(args.reference_url if args.reference_url else [])
    
    print(f"🔎 Scanning for new 'sorry' statements in '{args.diff_file}'...")
    print("----------------------------------------------------")

    sorries_to_process = find_sorries_in_diff(args.diff_file, repo_root, args.web_search)

    if not sorries_to_process:
        print("✅ No new 'sorry' statements found in the diff.")
        return

    if args.dry_run:
        print("DRY RUN: Would process the following new sorries:")
        for sorry in sorries_to_process:
            print(f"  - {sorry['file_path']}:{sorry['line_num']} ({sorry['decl_name'] or 'task'})")
        return
    
    process_sorries(sorries_to_process, repo_name, reference_context, args)

    print("----------------------------------------------------")
    print("🎉 All done! Named issues have been created.")

if __name__ == "__main__":
    main()
