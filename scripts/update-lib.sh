#!/bin/bash

# Update ArkLib.lean with all imports
# This script generates the main library file by scanning all .lean files

set -e  # Exit on any error

echo "Updating ArkLib.lean with all imports..."

# Generate imports for ArkLib
git ls-files 'ArkLib/*.lean' | LC_ALL=C sort | sed 's/\.lean//;s,/,.,g;s/^/import /' > ArkLib.lean

echo "✓ ArkLib.lean updated with $(wc -l < ArkLib.lean) imports"

# Uncomment if you have Examples
# git ls-files 'Examples/*.lean' | LC_ALL=C sort | sed 's/\.lean//;s,/,.,g;s/^/import /' > Examples.lean
