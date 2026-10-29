#!/usr/bin/env python3
"""Generate the normalized bibliography export for the ArkLib knowledge base."""

from __future__ import annotations

import argparse
from pathlib import Path

from common import DEFAULT_BIB_PATH, DEFAULT_REFERENCES_JSON, REPO_ROOT, load_bib_entries, write_json


def build_payload(bib_path: Path) -> dict[str, object]:
    """Build the JSON payload written to ``references.json``."""

    entries = sorted(load_bib_entries(bib_path), key=lambda entry: entry.key)
    entries_json = {entry.key: entry.to_json() for entry in entries}
    return {
        "count": len(entries),
        "entries": entries_json,
        "source_bib": str(bib_path.relative_to(REPO_ROOT)),
    }


def parse_args() -> argparse.Namespace:
    """Parse CLI arguments."""

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--bib",
        type=Path,
        default=DEFAULT_BIB_PATH,
        help="Path to references.bib",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=DEFAULT_REFERENCES_JSON,
        help="Output path for the generated references.json",
    )
    return parser.parse_args()


def main() -> int:
    """Entry point."""

    args = parse_args()
    payload = build_payload(args.bib.resolve())
    write_json(args.output.resolve(), payload)
    print(f"Wrote {payload['count']} bibliography entries to {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
