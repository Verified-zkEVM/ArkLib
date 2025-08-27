#!/usr/bin/env python3
"""
Generate dependency graph for ArkLib Lean files.
This script parses import statements and creates a visual representation
of the dependency relationships between modules.
"""

import os
import re
import json
from pathlib import Path
from collections import defaultdict, deque
from typing import Dict, List, Set, Tuple
import argparse

def find_lean_files(root_dir: str) -> List[str]:
    """Find all .lean files in the given directory."""
    lean_files = []
    for root, dirs, files in os.walk(root_dir):
        # Skip .lake and other build directories
        if any(skip in root for skip in ['.lake', '.git', '.cursor', '.claude', '.vscode']):
            continue
        for file in files:
            if file.endswith('.lean'):
                lean_files.append(os.path.join(root, file))
    return sorted(lean_files)

def parse_imports(file_path: str) -> List[str]:
    """Parse import statements from a Lean file."""
    imports = []
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()

        # Find import statements
        import_pattern = r'^import\s+([^\s]+)'
        for line in content.split('\n'):
            line = line.strip()
            if line.startswith('import'):
                match = re.match(import_pattern, line)
                if match:
                    imports.append(match.group(1))
    except Exception as e:
        print(f"Warning: Could not read {file_path}: {e}")

    return imports

def normalize_module_name(file_path: str, root_dir: str) -> str:
    """Convert file path to normalized module name."""
    # Remove root directory and .lean extension
    rel_path = os.path.relpath(file_path, root_dir)
    module_name = rel_path.replace('.lean', '').replace('/', '.')
    return module_name

def build_dependency_graph(lean_files: List[str], root_dir: str) -> Dict[str, List[str]]:
    """Build dependency graph from Lean files."""
    graph = defaultdict(list)
    file_to_module = {}

    # First pass: create mapping from file to module name
    for file_path in lean_files:
        module_name = normalize_module_name(file_path, root_dir)
        file_to_module[file_path] = module_name

    # Second pass: parse imports and build graph
    for file_path in lean_files:
        module_name = file_to_module[file_path]
        imports = parse_imports(file_path)

        for imp in imports:
            # Handle both external (Mathlib) and internal (ArkLib) imports
            if imp.startswith('ArkLib.'):
                # Internal import - add to graph
                graph[imp].append(module_name)
            # Note: External imports like Mathlib are not added to internal graph

    return dict(graph)

def find_cycles(graph: Dict[str, List[str]]) -> List[List[str]]:
    """Find cycles in the dependency graph using DFS."""
    visited = set()
    rec_stack = set()
    cycles = []

    def dfs(node: str, path: List[str]):
        if node in rec_stack:
            # Found a cycle
            cycle_start = path.index(node)
            cycles.append(path[cycle_start:] + [node])
            return

        if node in visited:
            return

        visited.add(node)
        rec_stack.add(node)
        path.append(node)

        for neighbor in graph.get(node, []):
            dfs(neighbor, path.copy())

        rec_stack.remove(node)

    for node in graph:
        if node not in visited:
            dfs(node, [])

    return cycles

def generate_dot_graph(graph: Dict[str, List[str]], output_file: str):
    """Generate DOT format graph for Graphviz."""
    with open(output_file, 'w') as f:
        f.write("digraph ArkLibDependencies {\n")
        f.write("  rankdir=TB;\n")
        f.write("  node [shape=box, style=filled, fillcolor=lightblue];\n")
        f.write("  edge [color=gray];\n\n")

        # Add nodes
        all_nodes = set()
        for module, deps in graph.items():
            all_nodes.add(module)
            all_nodes.update(deps)

        for node in sorted(all_nodes):
            if node.startswith('ArkLib.'):
                f.write(f'  "{node}" [fillcolor=lightgreen];\n')
            else:
                f.write(f'  "{node}";\n')

        f.write("\n")

        # Add edges
        for module, deps in graph.items():
            for dep in deps:
                f.write(f'  "{module}" -> "{dep}";\n')

        f.write("}\n")

def generate_json_graph(graph: Dict[str, List[str]], output_file: str):
    """Generate JSON format dependency graph."""
    graph_data = {
        "nodes": [],
        "edges": []
    }

    all_nodes = set()
    for module, deps in graph.items():
        all_nodes.add(module)
        all_nodes.update(deps)

    for node in sorted(all_nodes):
        node_data = {
            "id": node,
            "type": "internal" if node.startswith('ArkLib.') else "external"
        }
        graph_data["nodes"].append(node_data)

    for module, deps in graph.items():
        for dep in deps:
            edge_data = {
                "source": module,
                "target": dep
            }
            graph_data["edges"].append(edge_data)

    with open(output_file, 'w') as f:
        json.dump(graph_data, f, indent=2)

def generate_text_summary(graph: Dict[str, List[str]], output_file: str):
    """Generate human-readable text summary of dependencies."""
    with open(output_file, 'w') as f:
        f.write("ArkLib Dependency Summary\n")
        f.write("=" * 50 + "\n\n")

        # Group by top-level modules
        top_level = defaultdict(list)
        for module in graph:
            if module.startswith('ArkLib.'):
                parts = module.split('.')
                if len(parts) >= 3:
                    top_level[parts[1]].append(module)

        for category, modules in sorted(top_level.items()):
            f.write(f"{category.upper()} MODULES:\n")
            f.write("-" * 30 + "\n")
            for module in sorted(modules):
                deps = graph.get(module, [])
                f.write(f"{module} ({len(deps)} dependencies)\n")
                for dep in sorted(deps):
                    f.write(f"  -> {dep}\n")
                f.write("\n")

        # Find modules with most dependencies
        f.write("MODULES WITH MOST DEPENDENCIES:\n")
        f.write("-" * 40 + "\n")
        sorted_modules = sorted(graph.items(), key=lambda x: len(x[1]), reverse=True)
        for module, deps in sorted_modules[:20]:
            if module.startswith('ArkLib.'):
                f.write(f"{module}: {len(deps)} dependencies\n")

def main():
    parser = argparse.ArgumentParser(description='Generate dependency graph for ArkLib')
    parser.add_argument('--root', default='.', help='Root directory (default: current)')
    parser.add_argument('--output-dir', default='dependency_graphs', help='Output directory for graphs')
    parser.add_argument('--format', choices=['dot', 'json', 'text', 'all'], default='all',
                       help='Output format (default: all)')

    args = parser.parse_args()

    root_dir = os.path.abspath(args.root)
    output_dir = args.output_dir

    # Create output directory
    os.makedirs(output_dir, exist_ok=True)

    print(f"Scanning for Lean files in {root_dir}...")
    lean_files = find_lean_files(root_dir)
    print(f"Found {len(lean_files)} Lean files")

    print("Building dependency graph...")
    graph = build_dependency_graph(lean_files, root_dir)

    print(f"Graph has {len(graph)} modules with dependencies")

    # Check for cycles
    cycles = find_cycles(graph)
    if cycles:
        print(f"Warning: Found {len(cycles)} dependency cycles:")
        for cycle in cycles[:5]:  # Show first 5 cycles
            print(f"  {' -> '.join(cycle)}")
        if len(cycles) > 5:
            print(f"  ... and {len(cycles) - 5} more")
    else:
        print("No dependency cycles found")

    # Generate outputs
    if args.format in ['dot', 'all']:
        dot_file = os.path.join(output_dir, 'arklib_dependencies.dot')
        generate_dot_graph(graph, dot_file)
        print(f"Generated DOT graph: {dot_file}")

    if args.format in ['json', 'all']:
        json_file = os.path.join(output_dir, 'arklib_dependencies.json')
        generate_json_graph(graph, json_file)
        print(f"Generated JSON graph: {json_file}")

    if args.format in ['text', 'all']:
        text_file = os.path.join(output_dir, 'arklib_dependencies.txt')
        generate_text_summary(graph, text_file)
        print(f"Generated text summary: {text_file}")

    print(f"\nAll outputs saved to: {output_dir}")
    print("\nTo visualize the DOT file:")
    print("  dot -Tpng arklib_dependencies.dot -o arklib_dependencies.png")
    print("  dot -Tsvg arklib_dependencies.dot -o arklib_dependencies.svg")

if __name__ == "__main__":
    main()
