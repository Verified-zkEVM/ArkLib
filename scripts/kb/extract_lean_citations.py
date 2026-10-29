#!/usr/bin/env python3
"""Generate a map from ArkLib Lean files to cited BibTeX keys."""

from __future__ import annotations

import argparse
from pathlib import Path
import json
import re

from common import (
    DEFAULT_BIB_PATH,
    DEFAULT_CITATIONS_JSON,
    DEFAULT_LEAN_ROOT,
    DEFAULT_REFERENCES_JSON,
    REPO_ROOT,
    load_bib_entries,
    write_json,
)


def load_reference_keys(references_json: Path, bib_path: Path) -> list[str]:
    """Load known BibTeX keys from references.json, falling back to references.bib."""

    if references_json.exists():
        payload = json.loads(references_json.read_text(encoding="utf-8"))
        entries = payload.get("entries", {})
        return sorted(entries)
    return sorted(entry.key for entry in load_bib_entries(bib_path))


def build_pattern(keys: list[str]) -> re.Pattern[str]:
    """Build the citation-matching regex for the known key set."""

    escaped_keys = sorted((re.escape(key) for key in keys), key=len, reverse=True)
    return re.compile(r"\[(" + "|".join(escaped_keys) + r")\]")


def extract_citations(lean_root: Path, keys: list[str]) -> dict[str, object]:
    """Scan Lean files and build file-to-key and key-to-file maps."""

    pattern = build_pattern(keys)
    file_map: dict[str, list[str]] = {}
    key_map: dict[str, list[str]] = {key: [] for key in keys}

    for lean_file in sorted(lean_root.rglob("*.lean")):
        text = lean_file.read_text(encoding="utf-8")
        citations = sorted(set(match.group(1) for match in pattern.finditer(text)))
        if not citations:
            continue
        rel_path = str(lean_file.relative_to(lean_root.parents[0]))
        file_map[rel_path] = citations
        for key in citations:
            key_map[key].append(rel_path)

    used_key_map = {key: paths for key, paths in key_map.items() if paths}
    counts = {
        "files_with_citations": len(file_map),
        "keys_cited": len(used_key_map),
        "total_citation_edges": sum(len(paths) for paths in used_key_map.values()),
    }
    return {
        "counts": counts,
        "files": file_map,
        "keys": used_key_map,
        "lean_root": str(lean_root.relative_to(lean_root.parents[0])),
    }


def parse_args() -> argparse.Namespace:
    """Parse CLI arguments."""

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--lean-root",
        type=Path,
        default=DEFAULT_LEAN_ROOT,
        help="Root directory to scan for .lean files",
    )
    parser.add_argument(
        "--references-json",
        type=Path,
        default=DEFAULT_REFERENCES_JSON,
        help="Path to the generated references.json file",
    )
    parser.add_argument(
        "--bib",
        type=Path,
        default=DEFAULT_BIB_PATH,
        help="Fallback path to references.bib if references.json does not exist",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=DEFAULT_CITATIONS_JSON,
        help="Output path for the generated lean-citations.json",
    )
    return parser.parse_args()


def main() -> int:
    """Entry point."""

    args = parse_args()
    lean_root = args.lean_root.resolve()
    references_json = args.references_json.resolve()
    bib_path = args.bib.resolve()
    keys = load_reference_keys(references_json, bib_path)
    payload = extract_citations(lean_root, keys)
    payload["reference_source"] = (
        str(references_json.relative_to(REPO_ROOT))
        if references_json.exists()
        else str(bib_path.relative_to(REPO_ROOT))
    )
    write_json(args.output.resolve(), payload)
    print(
        "Wrote citation map with "
        f"{payload['counts']['files_with_citations']} files and "
        f"{payload['counts']['keys_cited']} cited keys to {args.output}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
