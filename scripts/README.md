# ArkLib Scripts

This directory contains various utility scripts for the ArkLib project.

## Available Scripts

### Build and Development
- **`build-project.sh`** - Build the ArkLib project
- **`update-lib.sh`** - Update library dependencies
- **`lint-style.py`** - Python-based style linting
- **`lint-style.lean`** - Lean-based style linting

### Code Review
- **`review.py`** - Code review automation tool

### Dependency Analysis
- **`dependency_analysis/`** - Complete dependency analysis toolkit
  - Generate dependency graphs for all ArkLib modules
  - Interactive exploration of dependencies
  - Visual representations (PNG, SVG)
  - See `dependency_analysis/README.md` for detailed usage

### Benchmarking
- **`bench/`** - Benchmarking tools and scripts

## Quick Start

### Generate Dependency Graphs
```bash
cd scripts/dependency_analysis
python generate_dependency_graph.py --root ../../ --output-dir ../../dependency_graphs
```

### Build Project
```bash
./scripts/build-project.sh
```

### Update Dependencies
```bash
./scripts/update-lib.sh
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
- The dependency analysis tools have been tested and verified to work correctly
