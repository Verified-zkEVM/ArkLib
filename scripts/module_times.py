#!/usr/bin/env python3
"""Per-module compile times that travel with the cached ArkLib build.

CI restores `.lake/build` from the latest `main` build and rebuilds only the modules whose inputs
changed. Lake prints a `Built <module> (<time>)` line exactly for those modules, so a build log is
a timing sample of the changed cone. `update` overlays such samples onto the table stored at
`.lake/build/arklib-module-times.json` and drops modules whose source file is gone.

Because Lake rebuilds a module whenever its source or any import changes, every entry was measured
against the inputs the module still has. The table is therefore a per-module profile of the whole
library at the cached commit, assembled from the runs that last rebuilt each module; its sum
estimates the compile time of a clean build without running one.
"""

from __future__ import annotations

import argparse
import json
import pathlib
import re
from typing import Any

SCHEMA_VERSION = 1
MODULE_PREFIXES = ("ArkLib", "ArkLibTest")

# Lake's own formatter (`Lake/Build/Run.lean`) prints `NNNms` below 1s, one decimal between 1s
# and 10s, and whole seconds above 10s. Keep the precision Lake reported.
TARGET_PATTERN = re.compile(r"Built\s+(.+?)\s+\((\d+(?:\.\d+)?)(ms|s)\)")


def parse_duration(value: str, unit: str) -> tuple[float, int]:
    """Return the duration in seconds together with the decimal places Lake actually reported."""
    if unit == "ms":
        return float(value) / 1000.0, 3
    return float(value), len(value.partition(".")[2])


def is_module(target: str) -> bool:
    # Facet-qualified captions (`Mod:c.o`, `Mod:dynlib`) are native work, not elaboration.
    if ":" in target:
        return False
    return any(target == prefix or target.startswith(prefix + ".") for prefix in MODULE_PREFIXES)


def source_path(module: str) -> str:
    return module.replace(".", "/") + ".lean"


def parse_logs(paths: list[pathlib.Path]) -> dict[str, dict[str, Any]]:
    """Return `{module: {"seconds", "decimals"}}` for every module built in the given logs."""
    built: dict[str, dict[str, Any]] = {}
    for path in paths:
        if not path.exists():
            continue
        for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
            match = TARGET_PATTERN.search(line)
            if not match:
                continue
            target = match.group(1).strip()
            if not is_module(target) or target in built:
                continue
            seconds, decimals = parse_duration(match.group(2), match.group(3))
            built[target] = {"seconds": seconds, "decimals": decimals}
    return built


def empty_table() -> dict[str, Any]:
    return {"schema_version": SCHEMA_VERSION, "commit": None, "modules": {}}


def load_table(path: pathlib.Path) -> dict[str, Any] | None:
    """Load a table, or return None when it is absent or unreadable (treated as no baseline)."""
    try:
        table = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None
    if not isinstance(table, dict) or table.get("schema_version") != SCHEMA_VERSION:
        return None
    if not isinstance(table.get("modules"), dict):
        return None
    return table


def total_seconds(table: dict[str, Any]) -> float:
    return sum(entry["seconds"] for entry in table["modules"].values())


def update_table(
    table: dict[str, Any], built: dict[str, dict[str, Any]], commit: str | None, root: pathlib.Path
) -> dict[str, Any]:
    modules = dict(table["modules"])
    modules.update(built)
    modules = {
        module: entry
        for module, entry in sorted(modules.items())
        if (root / source_path(module)).is_file()
    }
    return {"schema_version": SCHEMA_VERSION, "commit": commit, "modules": modules}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    subparsers = parser.add_subparsers(dest="command", required=True)
    update = subparsers.add_parser("update", help="overlay build-log samples onto a table")
    update.add_argument("table", type=pathlib.Path)
    update.add_argument("logs", type=pathlib.Path, nargs="+")
    update.add_argument("--commit", help="commit whose build the updated table describes")
    update.add_argument("--root", type=pathlib.Path, default=pathlib.Path("."))
    args = parser.parse_args()

    table = load_table(args.table) or empty_table()
    built = parse_logs(args.logs)
    updated = update_table(table, built, args.commit, args.root)
    args.table.parent.mkdir(parents=True, exist_ok=True)
    args.table.write_text(json.dumps(updated, indent=1, sort_keys=True) + "\n", encoding="utf-8")
    print(
        f"Recorded {len(built)} rebuilt modules; table covers {len(updated['modules'])} modules, "
        f"{total_seconds(updated):.0f}s of compile time."
    )


if __name__ == "__main__":
    main()
