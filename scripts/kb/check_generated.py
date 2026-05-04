#!/usr/bin/env python3
"""Check that committed knowledge-base generated files are fresh."""

from __future__ import annotations

import json
from pathlib import Path

from common import (
    DEFAULT_BIB_PATH,
    DEFAULT_CITATIONS_JSON,
    DEFAULT_LEAN_ROOT,
    DEFAULT_REFERENCES_JSON,
    REPO_ROOT,
)
from extract_lean_citations import extract_citations
from sync_from_bib import build_payload


def load_json(path: Path) -> dict[str, object]:
    """Load a committed generated JSON file."""

    return json.loads(path.read_text(encoding="utf-8"))


def expected_citations(keys: list[str]) -> dict[str, object]:
    """Build the expected Lean citation payload."""

    payload = extract_citations(DEFAULT_LEAN_ROOT, keys)
    payload["reference_source"] = str(DEFAULT_REFERENCES_JSON.relative_to(REPO_ROOT))
    return payload


def compare_payload(name: str, expected: dict[str, object], actual_path: Path) -> list[str]:
    """Return a human-readable error if a generated file is stale."""

    actual = load_json(actual_path)
    if actual == expected:
        return []
    return [
        f"{actual_path.relative_to(REPO_ROOT)} is out of date; regenerate it with "
        f"`python3 ./scripts/kb/{name}`."
    ]


def main() -> int:
    """Entry point."""

    expected_references = build_payload(DEFAULT_BIB_PATH)
    keys = sorted(expected_references["entries"])
    errors: list[str] = []
    errors.extend(compare_payload("sync_from_bib.py", expected_references, DEFAULT_REFERENCES_JSON))
    errors.extend(
        compare_payload(
            "extract_lean_citations.py",
            expected_citations(keys),
            DEFAULT_CITATIONS_JSON,
        )
    )

    if errors:
        print("Knowledge base generated files are stale:")
        for error in errors:
            print(f"  - {error}")
        return 1

    print("Knowledge base generated files are up to date.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
