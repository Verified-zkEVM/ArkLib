#!/usr/bin/env bash
set -e

# Build the Lean Project Documentation
echo "Fetching Cache..."
lake exe cache get

echo "Building Blueprint Declaration Environment..."
lake build ArkLibBlueprint

echo "Building Project Documentation..."
lake build ArkLib:docs
lake build ArkLibBlueprint:docs

# Build the Blueprint
if [ -d "blueprint" ]; then
    echo "Building Blueprint..."
    cd blueprint
    if command -v leanblueprint &> /dev/null; then
        leanblueprint pdf
        leanblueprint web
    else
        echo "Warning: 'leanblueprint' command not found. Skipping blueprint generation."
        echo "To install: pip install leanblueprint"
    fi
    cd ..
    lake exe checkdecls blueprint/lean_decls
fi

# Prepare the Website Directory
echo "Assembling Website..."
DEST="home_page"

# Ensure destination directories exist
mkdir -p "$DEST/docs"
mkdir -p "$DEST/blueprint"

# Copy Documentation
if [ -d ".lake/build/doc" ]; then
    echo "Copying docs..."
    cp -r .lake/build/doc/* "$DEST/docs/"
else
    echo "Warning: Docs build directory not found."
fi

# Copy Blueprint
if [ -d "blueprint/web" ]; then
    echo "Copying blueprint (HTML)..."
    cp -r blueprint/web/* "$DEST/blueprint/"
fi

if [ -f "blueprint/print/print.pdf" ]; then
    echo "Copying blueprint (PDF)..."
    cp "blueprint/print/print.pdf" "$DEST/blueprint.pdf"
fi

echo "Website build complete in $DEST/"

# Inject Global Navigation
echo "Injecting Global Navigation..."
if [ -f "scripts/inject_nav.py" ]; then
    python3 scripts/inject_nav.py "$DEST"
fi

echo "Open $DEST/index.html to view."
