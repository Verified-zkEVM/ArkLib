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
def get_document_content(urls_str: str) -> str:
    """Fetches and extracts text content from a comma-separated string of URLs."""
    if not urls_str:
        return "No external references were provided."

    all_docs_content = ""
    urls = [url.strip() for url in urls_str.split(',')]

    for url in urls:
        if not url: continue
        try:
            headers = {'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64)'}
            response = requests.get(url, timeout=30, headers=headers)
            response.raise_for_status()
            content_type = response.headers.get("Content-Type", "")
            content = ""
            if "application/pdf" in content_type or url.lower().endswith('.pdf'):
                with fitz.open(stream=io.BytesIO(response.content), filetype="pdf") as doc:
                    content = "".join(page.get_text() for page in doc)
            else:
                soup = BeautifulSoup(response.content, "html.parser")
                for element in soup(["script", "style", "nav", "footer", "header"]): element.decompose()
                text = soup.get_text()
                lines = (line.strip() for line in text.splitlines())
                content = "\n".join(chunk for line in lines for chunk in line.split("  ") if chunk)
            all_docs_content += f"--- Start of content from {url} ---\n{content}\n--- End of content from {url} ---\n\n"
        except Exception as e:
            all_docs_content += f"--- Error processing document '{url}': {e} ---\n\n"
    return all_docs_content

# --- Relevant files from the repository ---
def get_repo_files_content(paths_str: str) -> str:
    """Reads content from a comma-separated string of file and directory paths."""
    if not paths_str:
        return "No ArkLib references were provided."

    all_files_content = ""
    paths = [path.strip() for path in paths_str.split(',')]

    expanded_files = []
    for path in paths:
        if not path: continue
        if os.path.isdir(path):
            for root, _, files in os.walk(path):
                for name in files:
                    expanded_files.append(os.path.join(root, name))
        elif os.path.isfile(path):
            expanded_files.append(path)
        else:
            all_files_content += f"--- Error: Could not find file or directory {path} ---\n\n"

    unique_files = sorted(list(set(expanded_files)))

    for file_path in unique_files:
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
                all_files_content += f"--- Start of content from {file_path} ---\n{content}\n--- End of content from {file_path} ---\n\n"
        except Exception as e:
            all_files_content += f"--- Error reading file {file_path}: {e} ---\n\n"

    return all_files_content

def analyze_code_with_context(diff: str, external_context: str, repo_context: str, additional_comments: str) -> str:
    """Generates a code review using the Gemini 2.5 Pro."""
    api_key = os.getenv("GEMINI_API_KEY")
    if not api_key: return "Error: GEMINI_API_KEY environment variable not set."

    genai.configure(api_key=api_key)
    model = genai.GenerativeModel('gemini-2.5-pro')

    additional_comments_section = ""
    if additional_comments and additional_comments.strip():
        additional_comments_section = f"""
    **4. Additional Reviewer Comments:**
    ---
    {additional_comments}
    ---
    """

    prompt = f"""
    You are an expert code reviewer. Your task is to review a pull request. You have been given the following information:
    1.  The content of external reference documents.
    2.  The full content of other relevant files from the repository.
    3.  The code changes ("diff") from the pull request.
    {additional_comments_section}
    **1. External Reference Documents:**
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
    2.  Take into account the additional context provided by other files in the repository.
    3.  Compare the formalization against the information and specifications described in the "Reference Document Content".
    4.  If "Additional Reviewer Comments" are provided, pay close attention to them as they give specific instructions or focus areas for your review.
    5.  Provide a concise, high-level summary of the changes.
    6.  Check that the code correctly formalizes the relevant material from the reference document.
    7.  Provide specific, actionable feedback. If you find issues, suggest what changes are required, explaining why, and illustrate this with code.
    8.  Structure your review clearly. Use markdown for formatting.
    """
    try:
        response = model.generate_content(prompt)
        return response.text
    except Exception as e: return f"An error occurred while calling the Gemini API: {e}"

def main():
    parser = argparse.ArgumentParser(description="AI Code Reviewer")
    parser.add_argument("--pr-number", required=True)
    parser.add_argument("--external-refs", required=False, default="")
    parser.add_argument("--arklib-refs", required=False, default="")
    parser.add_argument("--additional-comments", required=False, default="")
    args = parser.parse_args()

    diff = get_pr_diff(args.pr_number)
    external_context = get_document_content(args.external_refs)
    repo_context = get_repo_files_content(args.arklib_refs)

    # Basic checks for errors
    if "Error" in diff[:60] or "Error" in external_context[:60]:
        print(f"Aborting due to error fetching context:\nDiff: {diff}\nExternal Doc: {external_context}")
        return

    print("Generating AI review...")
    review = analyze_code_with_context(diff, external_context, repo_context, args.additional_comments)
    print(review)

if __name__ == "__main__":
    main()
