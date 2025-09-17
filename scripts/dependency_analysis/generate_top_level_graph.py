#!/usr/bin/env python3
"""
Generate a simplified top-level dependency graph for ArkLib.
This shows only the main categories and their relationships.
"""

import os
import json
import argparse
from collections import defaultdict

def generate_top_level_graph(json_file: str, output_file: str):
    """Generate a simplified top-level dependency graph."""
    with open(json_file, 'r') as f:
        data = json.load(f)

    # Group modules by top-level category
    categories = defaultdict(set)
    for node in data['nodes']:
        if node['id'].startswith('ArkLib.'):
            parts = node['id'].split('.')
            if len(parts) >= 2:
                category = parts[1]
                categories[category].add(node['id'])

    # Create simplified graph
    top_level_graph = defaultdict(set)

    for edge in data['edges']:
        source = edge['source']
        target = edge['target']

        if source.startswith('ArkLib.') and target.startswith('ArkLib.'):
            source_cat = source.split('.')[1]
            target_cat = target.split('.')[1]

            if source_cat != target_cat:
                top_level_graph[source_cat].add(target_cat)

    # Generate DOT file
    with open(output_file, 'w') as f:
        f.write("digraph ArkLibTopLevel {\n")
        f.write("  rankdir=TB;\n")
        f.write("  node [shape=box, style=filled, fillcolor=lightblue, fontsize=12];\n")
        f.write("  edge [color=gray, penwidth=2];\n\n")

        # Add category nodes
        for category in sorted(categories.keys()):
            count = len(categories[category])
            f.write(f'  "{category}" [label="{category}\\n({count} modules)", fillcolor=lightgreen];\n')

        f.write("\n")

        # Add edges between categories
        for source_cat, target_cats in top_level_graph.items():
            for target_cat in sorted(target_cats):
                f.write(f'  "{source_cat}" -> "{target_cat}";\n')

        f.write("}\n")

    print(f"Generated top-level graph: {output_file}")
    print(f"Categories: {len(categories)}")
    print(f"Inter-category dependencies: {sum(len(deps) for deps in top_level_graph.values())}")

def main():
    parser = argparse.ArgumentParser(description='Generate top-level dependency graph for ArkLib')
    parser.add_argument('input_json', help='Input JSON dependency file')
    parser.add_argument('output_dot', help='Output DOT file')

    args = parser.parse_args()

    generate_top_level_graph(args.input_json, args.output_dot)

if __name__ == "__main__":
    main()
