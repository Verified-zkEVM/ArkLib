#!/usr/bin/env python3
"""
Interactive script to explore ArkLib dependencies.
"""

import json
import argparse
from collections import defaultdict

def load_dependencies(json_file: str):
    """Load dependency data from JSON file."""
    with open(json_file, 'r') as f:
        return json.load(f)

def show_module_info(data, module_name: str):
    """Show detailed information about a specific module."""
    if not module_name.startswith('ArkLib.'):
        module_name = f"ArkLib.{module_name}"

    # Find the module
    module_node = None
    for node in data['nodes']:
        if node['id'] == module_name:
            module_node = node
            break

    if not module_node:
        print(f"Module '{module_name}' not found.")
        return

    # Find dependencies (what this module imports)
    dependencies = []
    for edge in data['edges']:
        if edge['source'] == module_name:
            dependencies.append(edge['target'])

    # Find dependents (what imports this module)
    dependents = []
    for edge in data['edges']:
        if edge['target'] == module_name:
            dependents.append(edge['source'])

    print(f"\nModule: {module_name}")
    print(f"Type: {module_node['type']}")
    print(f"Dependencies ({len(dependencies)}):")
    for dep in sorted(dependencies):
        print(f"  -> {dep}")

    print(f"\nDependents ({len(dependents)}):")
    for dep in sorted(dependents):
        print(f"  -> {dep}")

def show_category_summary(data, category: str):
    """Show summary for a specific category."""
    if not category.startswith('ArkLib.'):
        category = f"ArkLib.{category}"

    modules = []
    for node in data['nodes']:
        if node['id'].startswith(category):
            modules.append(node['id'])

    if not modules:
        print(f"Category '{category}' not found.")
        return

    print(f"\nCategory: {category}")
    print(f"Modules ({len(modules)}):")
    for module in sorted(modules):
        # Count dependencies
        deps = sum(1 for edge in data['edges'] if edge['source'] == module)
        print(f"  {module} ({deps} dependencies)")

def show_top_dependencies(data, limit: int = 10):
    """Show modules with most dependencies."""
    dep_counts = defaultdict(int)
    for edge in data['edges']:
        if edge['source'].startswith('ArkLib.'):
            dep_counts[edge['source']] += 1

    sorted_modules = sorted(dep_counts.items(), key=lambda x: x[1], reverse=True)

    print(f"\nTop {limit} modules by dependency count:")
    print("-" * 50)
    for module, count in sorted_modules[:limit]:
        print(f"{module}: {count} dependencies")

def show_dependency_path(data, source: str, target: str):
    """Show dependency path between two modules."""
    if not source.startswith('ArkLib.'):
        source = f"ArkLib.{source}"
    if not target.startswith('ArkLib.'):
        target = f"ArkLib.{target}"

    # Simple BFS to find path
    visited = set()
    queue = [(source, [source])]

    while queue:
        current, path = queue.pop(0)
        if current == target:
            print(f"\nDependency path from {source} to {target}:")
            print(" -> ".join(path))
            return

        if current in visited:
            continue

        visited.add(current)

        for edge in data['edges']:
            if edge['source'] == current:
                next_module = edge['target']
                if next_module not in visited:
                    queue.append((next_module, path + [next_module]))

    print(f"No dependency path found from {source} to {target}")

def interactive_mode(data):
    """Run interactive mode."""
    print("ArkLib Dependency Explorer")
    print("=" * 30)
    print("Commands:")
    print("  info <module>     - Show module information")
    print("  category <cat>    - Show category summary")
    print("  top [N]           - Show top N modules by dependencies")
    print("  path <from> <to>  - Show dependency path")
    print("  quit              - Exit")
    print()

    while True:
        try:
            cmd = input("> ").strip().split()
            if not cmd:
                continue

            if cmd[0] == 'quit':
                break
            elif cmd[0] == 'info' and len(cmd) > 1:
                show_module_info(data, cmd[1])
            elif cmd[0] == 'category' and len(cmd) > 1:
                show_category_summary(data, cmd[1])
            elif cmd[0] == 'top':
                limit = int(cmd[1]) if len(cmd) > 1 else 10
                show_top_dependencies(data, limit)
            elif cmd[0] == 'path' and len(cmd) > 2:
                show_dependency_path(data, cmd[1], cmd[2])
            else:
                print("Invalid command. Type 'quit' to exit.")
        except KeyboardInterrupt:
            break
        except Exception as e:
            print(f"Error: {e}")

def main():
    parser = argparse.ArgumentParser(description='Explore ArkLib dependencies')
    parser.add_argument('json_file', help='JSON dependency file')
    parser.add_argument('--info', help='Show info for specific module')
    parser.add_argument('--category', help='Show summary for specific category')
    parser.add_argument('--top', type=int, help='Show top N modules by dependencies')
    parser.add_argument('--path', nargs=2, help='Show dependency path between two modules')
    parser.add_argument('--interactive', '-i', action='store_true', help='Run interactive mode')

    args = parser.parse_args()

    try:
        data = load_dependencies(args.json_file)
        print(f"Loaded {len(data['nodes'])} nodes and {len(data['edges'])} edges")

        if args.info:
            show_module_info(data, args.info)
        elif args.category:
            show_category_summary(data, args.category)
        elif args.top:
            show_top_dependencies(data, args.top)
        elif args.path:
            show_dependency_path(data, args.path[0], args.path[1])
        elif args.interactive:
            interactive_mode(data)
        else:
            print("Use --help for usage information or --interactive for interactive mode")

    except FileNotFoundError:
        print(f"Error: File '{args.json_file}' not found.")
    except json.JSONDecodeError:
        print(f"Error: Invalid JSON file '{args.json_file}'.")

if __name__ == "__main__":
    main()
