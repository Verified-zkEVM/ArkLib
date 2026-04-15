#!/usr/bin/env python3
"""Fail when a build log contains warnings that match a scoped warning budget."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Check a build log for warnings under selected path prefixes."
    )
    parser.add_argument("log_file", help="Path to the captured build log.")
    parser.add_argument(
        "--path-prefix",
        action="append",
        default=[],
        help="Only match warnings whose path starts with this prefix. Repeatable.",
    )
    parser.add_argument(
        "--exclude-substring",
        action="append",
        default=[],
        help="Ignore matching warnings that contain this substring. Repeatable.",
    )
    parser.add_argument(
        "--label",
        default="matching warnings",
        help="Human-readable name for the warning class being checked.",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    log_path = Path(args.log_file)
    lines = log_path.read_text(encoding="utf-8").splitlines()

    prefixes = tuple(f"warning: {prefix}" for prefix in args.path_prefix)
    offenders: list[str] = []

    for line in lines:
        if not line.startswith("warning: "):
            continue
        if prefixes and not line.startswith(prefixes):
            continue
        if any(substr in line for substr in args.exclude_substring):
            continue
        offenders.append(line)

    if not offenders:
        print(f"No {args.label} found.")
        return 0

    print(f"ERROR: Found {len(offenders)} {args.label}:", file=sys.stderr)
    for line in offenders:
        print(line, file=sys.stderr)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
