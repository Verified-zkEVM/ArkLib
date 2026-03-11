# ArkLib Scripts 

This directory contains various utility scripts for the ArkLib project.

## Available Scripts

### Build and Validation
- **`validate.sh`** - Recommended convenience wrapper for routine local validation
- **`build-project.sh`** - Compile-only helper (`lake build`)
- **`update-lib.sh`** - Update ArkLib.lean with all imports from source files
- **`check-imports.sh`** - Check if ArkLib.lean is up to date with all imports
- **`check-docs-integrity.py`** - Check docs links and the `CLAUDE.md` symlink
- **`lint-style.py`** - Python-based style linting
- **`lint-style.lean`** - Lean-based style linting

### Dependency Analysis
- **`dependency_analysis/`** - Complete dependency analysis toolkit
  - Generate dependency graphs for all ArkLib modules
  - Interactive exploration of dependencies
  - Visual representations (PNG, SVG)
  - See `dependency_analysis/README.md` for detailed usage

## Quick Start

### Recommended Routine Validation
```bash
./scripts/validate.sh
```

### Validation With Optional Checks
```bash
# Add Lean style linting
./scripts/validate.sh --lint

# Build API docs too
./scripts/validate.sh --docs

# Build site / blueprint output too
./scripts/validate.sh --site
```

### Generate Dependency Graphs
```bash
cd scripts/dependency_analysis
python generate_dependency_graph.py --root ../../ --output-dir ../../dependency_graphs
```

### Compile Only
```bash
./scripts/build-project.sh
```

### Update Library Imports
```bash
# Update ArkLib.lean with all imports
./scripts/update-lib.sh

# Check if imports are up to date
./scripts/check-imports.sh
```

### Check Docs Integrity
```bash
python3 ./scripts/check-docs-integrity.py
```

## Requirements

- Python 3.6+ (for Python scripts)
- Lean 4 (for Lean scripts)
- Graphviz (for dependency visualization)
- Virtual environment (`.venv`) for Python dependencies

## Notes

- Most scripts should be run from the ArkLib root directory
- Python scripts require the virtual environment to be activated
- Some scripts may require specific Lean toolchain versions
- `validate.sh` is the recommended local wrapper; use the lower-level scripts directly when you
  want to run or debug one piece in isolation
- New `ArkLib/**/*.lean` files must be staged before `update-lib.sh` or `check-imports.sh`
