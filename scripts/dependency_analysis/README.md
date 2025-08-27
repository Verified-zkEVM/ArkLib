# ArkLib Dependency Analysis

This directory contains tools and visualizations for analyzing the dependency structure of the ArkLib project.

## Folder Structure

```
scripts/dependency_analysis/
├── README.md                           # This file
├── generate_dependency_graph.py        # Main dependency graph generator
├── generate_top_level_graph.py         # Simplified category-level graph generator
├── explore_dependencies.py             # Interactive dependency explorer
└── dependency_graphs/                  # Generated output files (created when running scripts)
    ├── arklib_dependencies.dot        # Full dependency graph in DOT format
    ├── arklib_dependencies.png        # Full dependency graph visualization
    ├── arklib_dependencies.json       # Machine-readable dependency data
    ├── arklib_dependencies.txt        # Human-readable summary
    ├── arklib_top_level.dot           # Simplified top-level graph in DOT format
    └── arklib_top_level.png           # Simplified top-level graph visualization
```

## Generated Files

### 1. `arklib_dependencies.dot` / `arklib_dependencies.png`
- **Full dependency graph** showing all modules and their import relationships
- Contains 176 nodes and 422 edges
- Shows both internal ArkLib dependencies and external dependencies (Mathlib, etc.)
- **Warning**: This graph is very large and may be hard to read due to the number of connections

### 2. `arklib_top_level.dot` / `arklib_top_level.png`
- **Simplified top-level graph** showing only the main categories
- Much more readable overview of the project structure
- Shows 7 main categories and their inter-dependencies
- Recommended for understanding the high-level architecture

### 3. `arklib_dependencies.json`
- **Machine-readable dependency data** in JSON format
- Can be used for custom analysis or integration with other tools
- Contains detailed information about each module and dependency relationship

### 4. `arklib_dependencies.txt`
- **Human-readable summary** of dependencies
- Organized by category with dependency counts
- Lists modules with the most dependencies

## Main Categories

The ArkLib project is organized into these main categories:

1. **AGM** - Algebraic Geometry and Mathematics
2. **CommitmentScheme** - Cryptographic commitment schemes
3. **Data** - Core data structures and algorithms
4. **OracleReduction** - Oracle reduction protocols
5. **ProofSystem** - Zero-knowledge proof systems
6. **ToMathlib** - Extensions and utilities for mathlib
7. **ToVCVio** - Integration with VCV-io

## Key Insights

### Most Dependent Modules
- `ArkLib.Data.CodingTheory.Basic` (16 dependencies)
- `ArkLib.Data.CodingTheory.ReedSolomon` (15 dependencies)
- `ArkLib.OracleReduction.Security.RoundByRound` (12 dependencies)

### Architecture Patterns
- **Data** category is the largest and most foundational
- **ProofSystem** modules build on **Data** and **CommitmentScheme**
- **OracleReduction** provides protocol abstractions used throughout
- **ToMathlib** and **ToVCVio** are integration layers

## Usage

### Generate New Graphs
```bash
# From the ArkLib root directory
cd scripts/dependency_analysis

# Generate all dependency graphs
python generate_dependency_graph.py --root ../../ --output-dir ../../dependency_graphs

# Generate only top-level graph
python generate_top_level_graph.py ../../dependency_graphs/arklib_dependencies.json ../../dependency_graphs/arklib_top_level.dot
```

### Explore Dependencies Interactively
```bash
# Interactive mode
python explore_dependencies.py ../../dependency_graphs/arklib_dependencies.json --interactive

# Quick queries
python explore_dependencies.py ../../dependency_graphs/arklib_dependencies.json --info "Data.CodingTheory.Basic"
python explore_dependencies.py ../../dependency_graphs/arklib_dependencies.json --category "Data"
python explore_dependencies.py ../../dependency_graphs/arklib_dependencies.json --top 10
```

### Visualize Graphs
```bash
# Generate PNG images
dot -Tpng arklib_dependencies.dot -o arklib_dependencies.png
dot -Tpng arklib_top_level.dot -o arklib_top_level.png

# Generate SVG (scalable)
dot -Tsvg arklib_dependencies.dot -o arklib_dependencies.svg
dot -Tsvg arklib_top_level.dot -o arklib_top_level.svg
```

## Dependencies Required

- **Python 3.6+** with standard library
- **Graphviz** for visualization (`brew install graphviz` on macOS)
- **Virtual environment** (`.venv`) for Python dependencies

## Notes

- The dependency analysis is based on parsing `import` statements in `.lean` files
- External dependencies (Mathlib, etc.) are tracked but not included in internal graphs
- No dependency cycles were detected, indicating good architectural design
- The analysis excludes build artifacts and temporary files

## Customization

You can modify the scripts to:
- Filter specific types of dependencies
- Generate different graph layouts
- Export to other formats (CSV, GEXF, etc.)
- Focus on specific subcategories
- Analyze dependency metrics (depth, breadth, etc.)

## Quick Start

1. **Generate graphs**: `python generate_dependency_graph.py --root ../../ --output-dir ../../dependency_graphs`
2. **View top-level**: Open `../../dependency_graphs/arklib_top_level.png`
3. **Explore interactively**: `python explore_dependencies.py ../../dependency_graphs/arklib_dependencies.json --interactive`
4. **Custom analysis**: Use the JSON output for your own tools
