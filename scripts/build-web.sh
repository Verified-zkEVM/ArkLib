#!/usr/bin/env bash
set -e

# Build the Lean Project Documentation
echo "Fetching Cache..."
lake exe cache get

echo "Building Blueprint Declaration Environment..."
lake build ArkLibBlueprint

# doc-gen4 and checkdecls are required by the separate docbuild package, which requires ArkLib
# by path and shares its packages and build; see docbuild/lakefile.toml.
echo "Resolving Documentation Package..."
(cd docbuild && MATHLIB_NO_CACHE_ON_UPDATE=1 lake update Arklib)

echo "Building Project Documentation..."
(cd docbuild && lake build ArkLib:docs && lake build ArkLibBlueprint:docs)

# Build the Blueprint
if [ -d "blueprint" ]; then
    echo "Building Blueprint..."
    cd blueprint
    if command -v leanblueprint &> /dev/null; then
        leanblueprint pdf
        leanblueprint web
    else
        echo "Warning: 'leanblueprint' command not found. Skipping blueprint generation."
        echo "To install: uv tool install --python 3.12 leanblueprint"
    fi
    cd ..
    (cd docbuild && lake build BlueprintDecls && lake exe checkdecls ../blueprint/lean_decls)
fi

# Prepare the Website Directory
echo "Assembling Website..."
DEST="home_page"

# Ensure destination directories exist
mkdir -p "$DEST/docs"
mkdir -p "$DEST/blueprint"

# Copy Documentation
if [ -d "docbuild/.lake/build/doc" ]; then
    echo "Copying docs..."
    cp -r docbuild/.lake/build/doc/* "$DEST/docs/"
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
    uv run --no-project --python 3.12 python scripts/inject_nav.py "$DEST"
fi

echo "Open $DEST/index.html to view."
