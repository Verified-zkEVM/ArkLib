import os
import sys

def get_relative_path(current_file, target_path):
    return os.path.relpath(target_path, os.path.dirname(current_file))

GLOBAL_NAV_HTML = """
<div id="arklib-global-nav">
    <div class="container">
        <a href="{root}index.html" class="logo">ArkLib</a>
        <div class="nav-links">
            <a href="{root}docs/">Documentation</a>
            <a href="{root}blueprint/">Blueprint (Web)</a>
            <a href="{root}blueprint.pdf">Blueprint (PDF)</a>
            <a href="https://github.com/Verified-zkEVM/ArkLib" target="_blank">GitHub</a>
        </div>
    </div>
</div>
"""

def inject_nav(directory, root_dir):
    print(f"Injecting nav in {directory}...")
    css_path = os.path.join(root_dir, "global_nav.css")
    
    for root, dirs, files in os.walk(directory):
        for file in files:
            if file.endswith(".html"):
                if file == "navbar.html":
                    continue
                file_path = os.path.join(root, file)
                
                # Calculate relative paths
                rel_css = get_relative_path(file_path, css_path)
                rel_root = get_relative_path(file_path, root_dir)
                if not rel_root.endswith('/'):
                    rel_root += '/'
                if rel_root == './':
                    rel_root = ''

                try:
                    with open(file_path, "r", encoding="utf-8") as f:
                        content = f.read()

                    if "id=\"arklib-global-nav\"" in content:
                        continue # Already injected

                    # Inject CSS link before </head>
                    css_link = f'<link rel="stylesheet" href="{rel_css}">'
                    if "</head>" in content:
                        content = content.replace("</head>", f'{css_link}</head>')
                    
                    # Inject Nav HTML after <body>
                    nav_html = GLOBAL_NAV_HTML.format(root=rel_root)
                    if "<body>" in content:
                        content = content.replace("<body>", f"<body>{nav_html}")
                    
                    with open(file_path, "w", encoding="utf-8") as f:
                        f.write(content)
                        
                except Exception as e:
                    print(f"Error processing {file_path}: {e}")

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: uv run --no-project --python 3.12 python inject_nav.py <target_directory_base>")
        sys.exit(1)
        
    base_dir = sys.argv[1] # e.g., home_page
    
    # Inject in docs
    docs_dir = os.path.join(base_dir, "docs")
    if os.path.exists(docs_dir):
        inject_nav(docs_dir, base_dir)
        
    # Inject in blueprint
    blueprint_dir = os.path.join(base_dir, "blueprint")
    if os.path.exists(blueprint_dir):
        inject_nav(blueprint_dir, base_dir)
