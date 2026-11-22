import os
import sys
import re

def revert_nav(directory):
    print(f"Reverting nav in {directory}...")
    
    # Regex to capture the injected div (approximate, should match what inject_nav.py did)
    # It starts with <div id="arklib-global-nav"> and ends with </div> but has nested divs.
    # Since we know the exact structure we injected, we can look for the specific block.
    # However, simple string replacement of the specific block is safer?
    # Or just Regex with dotall?
    
    # The block structure from inject_nav.py:
    # <div id="arklib-global-nav"> ... </div>
    # It accounts for about 12 lines.
    
    # Let's use a robust strategy:
    # Find <div id="arklib-global-nav"> and find the matching closing </div> (it's the first one that closes the outer div).
    # Actually, simpler: we know we injected it immediately after <body>.
    # So we can look for <body><div id="arklib-global-nav">...</div>
    
    # Or even simpler: Use the same HTML string template but with regex for the relative paths.
    
    link_regex = re.compile(r'<link rel="stylesheet" href="[^"]*global_nav.css">')
    
    # This regex attempts to match the div block. 
    # Non-greedy match until the closing </div> of the outer div is risky if nested divs are present.
    # But our injected HTML has nested divs. 
    # The structure is: <div id="arklib-global-nav">...<div class="container">...</div>...</div>
    # So there are 2 closing divs.
    
    # Let's just read the file lines and filter out the range.
    
    for root, dirs, files in os.walk(directory):
        for file in files:
            if file.endswith(".html"):
                file_path = os.path.join(root, file)
                try:
                    with open(file_path, "r", encoding="utf-8") as f:
                        content = f.read()

                    # Remove CSS link
                    content = link_regex.sub('', content)
                    
                    # Remove Nav Div
                    # We look for the start marker
                    start_marker = '<div id="arklib-global-nav">'
                    if start_marker in content:
                        start_idx = content.find(start_marker)
                        # We need to find the end. 
                        # Since we know the structure, let's just cheat and look for the specific closing context or just count braces if we were parsing.
                        # But since we generated it, we know it ends with:
                        # </div>\n    </div>\n</div> (formatting might vary)
                        # Actually inject_nav.py creates a multi-line string.
                        
                        # Alternative: Just remove everything between start_marker and the known end of our block?
                        # Or better: Assume the block is well defined.
                        
                        # Let's try to match the exact string known from inject_nav.py if possible, but relative paths vary.
                        
                        # Helper: find </div> matching the start.
                        # Basic counter approach.
                        end_idx = start_idx + len(start_marker)
                        open_divs = 1
                        while open_divs > 0 and end_idx < len(content):
                            if content[end_idx:].startswith('<div'):
                                open_divs += 1
                                end_idx += 4
                            elif content[end_idx:].startswith('</div>'):
                                open_divs -= 1
                                end_idx += 6
                            else:
                                end_idx += 1
                        
                        if open_divs == 0:
                            # Found the end
                            content = content[:start_idx] + content[end_idx:]

                    with open(file_path, "w", encoding="utf-8") as f:
                        f.write(content)
                        
                except Exception as e:
                    print(f"Error processing {file_path}: {e}")

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: uv run --no-project --python 3.12 python revert_nav.py <target_directory>")
        sys.exit(1)
        
    target_dir = sys.argv[1]
    if os.path.exists(target_dir):
        revert_nav(target_dir)
