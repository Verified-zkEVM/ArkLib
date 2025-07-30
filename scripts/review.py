import os
import argparse
import subprocess
import requests
from bs4 import BeautifulSoup
import google.generativeai as genai
import fitz
import io

# --- Helper Functions ---
# --- PR diff ---
def get_pr_diff(pr_number: str) -> str:
    """Fetches the diff of the specified pull request."""
    try:
        diff = subprocess.check_output(["gh", "pr", "diff", pr_number], text=True).strip()
        if not diff: return "Could not retrieve PR diff."
        return diff
    except subprocess.CalledProcessError as e: return f"Error fetching PR diff: {e}"

# --- Reference document ---
def get_document_content(url: str) -> str:
    """Fetches and extracts text content from a URL (supports HTML and PDF)."""
    try:
        headers = {'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64)'}
        response = requests.get(url, timeout=30, headers=headers)
        response.raise_for_status()
        content_type = response.headers.get("Content-Type", "")
        if "application/pdf" in content_type or url.lower().endswith('.pdf'):
            with fitz.open(stream=io.BytesIO(response.content), filetype="pdf") as doc:
                return "".join(page.get_text() for page in doc)
        else:
            soup = BeautifulSoup(response.content, "html.parser")
            for element in soup(["script", "style", "nav", "footer", "header"]): element.decompose()
            text = soup.get_text()
            lines = (line.strip() for line in text.splitlines())
            return "\n".join(chunk for line in lines for chunk in line.split("  ") if chunk)
    except Exception as e: return f"Error processing document '{url}': {e}"

# --- Relevant files from the repository ---
def get_repo_files_content(file_paths_str: str) -> str:
    """Reads content from a comma-separated string of file paths."""
    if not file_paths_str:
        return "No context files were provided."

    all_files_content = ""
    file_paths = [path.strip() for path in file_paths_str.split(',')]

    for file_path in file_paths:
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
                all_files_content += f"--- Start of content from {file_path} ---\n{content}\n--- End of content from {file_path} ---\n\n"
        except FileNotFoundError:
            all_files_content += f"--- Error: Could not find file {file_path} ---\n\n"
        except Exception as e:
            all_files_content += f"--- Error reading file {file_path}: {e} ---\n\n"

    return all_files_content

def analyze_code_with_context(diff: str, external_context: str, repo_context: str) -> str:
    """Generates a code review using the Gemini 2.5 Pro."""
    api_key = os.getenv("GEMINI_API_KEY")
    if not api_key: return "Error: GEMINI_API_KEY environment variable not set."

    genai.configure(api_key=api_key)
    model = genai.GenerativeModel('gemini-2.5-pro')

    prompt = f"""
    You are an expert code reviewer. Your task is to review a pull request. To do this, you have been given three pieces of information:
    1.  The code changes ("diff") from the pull request.
    2.  The content of an external reference document.
    3.  The full content of other relevant files from the repository, to be used as additional context.

    **1. External Reference Document:**
    ---
    {external_context}
    ---

    **2. Additional Repository Context Files:**
    ---
    {repo_context}
    ---

    **3. Pull Request Diff:**
    ---
    {diff}
    ---

    **Your Instructions:**
    1.  Carefully analyze the "Pull Request Diff" paying attention to the logic, correctness, and style of the changes.
    2.  Take into account the additional context provide by other files in the repository.
    3.  Compare the formalization against the information and specifications described in the "Reference Document Content".
    4.  Provide a concise, high-level summary of the changes.
    5.  Check that the code correctly formalizes the relevant material from the reference document.
    6.  Provide specific, actionable feedback. If you find issues, suggest what changes are required, explaining why, and illustrate this with code.
    7.  Structure your review clearly. Use markdown for formatting.
    """
    try:
        response = model.generate_content(prompt)
        return response.text
    except Exception as e: return f"An error occurred while calling the Gemini API: {e}"

def main():
    parser = argparse.ArgumentParser(description="AI Code Reviewer")
    parser.add_argument("--pr-number", required=True)
    parser.add_argument("--context-url", required=True)
    parser.add_argument("--context-files", required=False, default="")
    args = parser.parse_args()

    diff = get_pr_diff(args.pr_number)
    external_context = get_document_content(args.context_url)
    repo_context = get_repo_files_content(args.context_files)

    # Basic checks for errors
    if "Error" in diff[:60] or "Error" in external_context[:60]:
        print(f"Aborting due to error fetching context:\nDiff: {diff}\nExternal Doc: {external_context}")
        return

    print("Generating AI review...")
    review = analyze_code_with_context(diff, external_context, repo_context)
    print(review)

if __name__ == "__main__":
    main()
