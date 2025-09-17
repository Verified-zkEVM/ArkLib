#!/bin/bash

# Check if all imports are up to date
# This script updates ArkLib.lean and checks if there are any differences

set -e  # Exit on any error

echo "Checking if all imports are up to date..."

# Save current ArkLib.lean
cp ArkLib.lean ArkLib.lean.backup

# Update imports
./scripts/update-lib.sh

# Check for differences
if git diff --exit-code ArkLib.lean > /dev/null; then
    echo "✓ All imports are up to date!"
    rm ArkLib.lean.backup
    exit 0
else
    echo "❌ Import file is out of date!"
    echo "Differences found:"
    git diff ArkLib.lean
    echo ""
    echo "To fix this, run: ./scripts/update-lib.sh"

    # Restore original file
    mv ArkLib.lean.backup ArkLib.lean
    exit 1
fi
