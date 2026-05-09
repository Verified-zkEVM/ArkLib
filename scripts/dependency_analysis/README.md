# ArkLib Dependency Analysis

This directory contains tools and visualizations for analyzing the dependency structure of the ArkLib project.

## Folder Structure

```
<repo root>/
├── scripts/dependency_analysis/
│   ├── README.md                       # This file
│   ├── generate_dependency_graph.py    # Main dependency graph generator
│   ├── generate_top_level_graph.py     # Simplified category-level graph generator
│   └── explore_dependencies.py         # Interactive dependency explorer
└── dependency_graphs/                  # Generated output files when using the examples below
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
- Size depends on the current checkout; the generator prints Lean file and module counts, and the
  explorer reports node and edge counts when it loads the JSON
- Includes internal `ArkLib.*` import edges; external imports such as Mathlib are parsed but not
  emitted in the graph
- **Warning**: This graph is very large and may be hard to read due to the number of connections

### 2. `arklib_top_level.dot` / `arklib_top_level.png`
- **Simplified top-level graph** showing only the main categories
- Much more readable overview of the project structure
- Shows the current top-level categories and their inter-dependencies
- Recommended for understanding the high-level architecture

### 3. `arklib_dependencies.json`
- **Machine-readable dependency data** in JSON format
- Can be used for custom analysis or integration with other tools
- Contains each emitted module node and internal import edge

### 4. `arklib_dependencies.txt`
- **Human-readable summary** of dependencies
- Organized by category with dependency counts
- Lists modules with the most dependencies

## Main Categories

The dependency graph groups modules by the first component after `ArkLib.`. Current categories
include:

1. **AGM** - Algebraic Group Model
2. **CommitmentScheme** - Cryptographic commitment schemes
3. **Data** - Core data structures and algorithms
4. **OracleReduction** - Oracle reduction protocols
5. **ProofSystem** - Zero-knowledge proof systems
6. **ToMathlib** - Extensions and utilities for mathlib

## Key Insights

### Most Dependent Modules
- Run `python3 scripts/dependency_analysis/explore_dependencies.py
  dependency_graphs/arklib_dependencies.json --top 10` after regenerating the graph to see the
  current ranking.

### Architecture Patterns
- **Data** category is the largest and most foundational
- **ProofSystem** modules build on **Data** and **CommitmentScheme**
- **OracleReduction** provides protocol abstractions used throughout
- **ToMathlib** provides the main upstream-facing extension layer

## Usage

### Generate New Graphs
```bash
# From the ArkLib root directory
# Generate all dependency graphs
python3 scripts/dependency_analysis/generate_dependency_graph.py --root . --output-dir dependency_graphs

# Generate only top-level graph
python3 scripts/dependency_analysis/generate_top_level_graph.py dependency_graphs/arklib_dependencies.json dependency_graphs/arklib_top_level.dot
```

### Explore Dependencies Interactively
```bash
# Interactive mode
python3 scripts/dependency_analysis/explore_dependencies.py dependency_graphs/arklib_dependencies.json --interactive

# Quick queries
python3 scripts/dependency_analysis/explore_dependencies.py dependency_graphs/arklib_dependencies.json --info "Data.CodingTheory.Basic"
python3 scripts/dependency_analysis/explore_dependencies.py dependency_graphs/arklib_dependencies.json --category "Data"
python3 scripts/dependency_analysis/explore_dependencies.py dependency_graphs/arklib_dependencies.json --top 10
```

### Visualize Graphs
```bash
# Generate PNG images
dot -Tpng dependency_graphs/arklib_dependencies.dot -o dependency_graphs/arklib_dependencies.png
dot -Tpng dependency_graphs/arklib_top_level.dot -o dependency_graphs/arklib_top_level.png

# Generate SVG (scalable)
dot -Tsvg dependency_graphs/arklib_dependencies.dot -o dependency_graphs/arklib_dependencies.svg
dot -Tsvg dependency_graphs/arklib_top_level.dot -o dependency_graphs/arklib_top_level.svg
```

## Dependencies Required

- **Python 3.6+** with standard library
- **Graphviz** for optional visualization (`brew install graphviz` on macOS)

## Notes

- The dependency analysis is based on parsing `import` statements in `.lean` files
- External dependencies (Mathlib, etc.) are ignored by the emitted internal graph
- The generator reports dependency cycles when it detects any
- The analysis skips `.lake`, `.git`, `.cursor`, `.claude`, and `.vscode` directories

## Customization

You can modify the scripts to:
- Filter specific types of dependencies
- Generate different graph layouts
- Export to other formats (CSV, GEXF, etc.)
- Focus on specific subcategories
- Analyze dependency metrics (depth, breadth, etc.)

## Quick Start

1. **Generate graphs**: `python3 scripts/dependency_analysis/generate_dependency_graph.py --root . --output-dir dependency_graphs`
2. **View top-level**: Open `dependency_graphs/arklib_top_level.png`
3. **Explore interactively**: `python3 scripts/dependency_analysis/explore_dependencies.py dependency_graphs/arklib_dependencies.json --interactive`
4. **Custom analysis**: Use the JSON output for your own tools
