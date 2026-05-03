#!/usr/bin/env python3
"""Resolve ArkLib paper-review context from citation keys or Lean files."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from common import DEFAULT_CITATIONS_JSON, DEFAULT_REFERENCES_JSON, REPO_ROOT


def load_json(path: Path) -> dict[str, object]:
    """Load a JSON file."""

    return json.loads(path.read_text(encoding="utf-8"))


def parse_csv_items(raw_items: list[str]) -> list[str]:
    """Split comma-separated CLI items into a flat list."""

    items: list[str] = []
    for raw in raw_items:
        items.extend(part.strip() for part in raw.split(",") if part.strip())
    return items


def normalize_repo_path(raw_path: str) -> str:
    """Normalize a repository-relative path string."""

    path = Path(raw_path)
    if path.is_absolute():
        return str(path.resolve().relative_to(REPO_ROOT))
    return str(path)


def infer_keys_from_files(file_paths: list[str], citations_payload: dict[str, object]) -> set[str]:
    """Infer citation keys from known Lean files."""

    file_map = citations_payload.get("files", {})
    if not isinstance(file_map, dict):
        return set()
    keys: set[str] = set()
    for raw_path in file_paths:
        normalized = normalize_repo_path(raw_path)
        cited = file_map.get(normalized, [])
        if isinstance(cited, list):
            keys.update(str(item) for item in cited)
    return keys


def build_repo_refs(keys: list[str]) -> list[str]:
    """Build the repository-local context paths for the given citation keys."""

    refs: list[str] = []
    for key in keys:
        paper_page = Path("docs/kb/papers") / f"{key}.md"
        if (REPO_ROOT / paper_page).exists():
            refs.append(str(paper_page))
        metadata = Path("docs/kb/sources") / key / "metadata.yml"
        if (REPO_ROOT / metadata).exists():
            refs.append(str(metadata))
    return refs


def build_external_refs(keys: list[str], references_payload: dict[str, object]) -> list[str]:
    """Build external URLs for the given citation keys when known."""

    entries = references_payload.get("entries", {})
    if not isinstance(entries, dict):
        return []
    refs: list[str] = []
    for key in keys:
        entry = entries.get(key, {})
        if not isinstance(entry, dict):
            continue
        url = str(entry.get("url", "")).strip()
        if url:
            refs.append(url)
    return refs


def unique_in_order(items: list[str]) -> list[str]:
    """Deduplicate while preserving order."""

    seen: set[str] = set()
    result: list[str] = []
    for item in items:
        if item in seen:
            continue
        seen.add(item)
        result.append(item)
    return result


def validate_explicit_keys(keys: list[str], references_payload: dict[str, object]) -> None:
    """Reject explicit keys that are not present in the bibliography export."""

    entries = references_payload.get("entries", {})
    if not isinstance(entries, dict):
        raise SystemExit("references.json is missing an `entries` object")
    unknown = sorted(key for key in keys if key not in entries)
    if unknown:
        raise SystemExit(f"Unknown BibTeX key(s): {', '.join(unknown)}")


def parse_args() -> argparse.Namespace:
    """Parse CLI arguments."""

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--keys",
        action="append",
        default=[],
        help="Comma-separated BibTeX keys to resolve",
    )
    parser.add_argument(
        "--files",
        action="append",
        default=[],
        help="Comma-separated repository paths to changed Lean files",
    )
    parser.add_argument(
        "--citations-json",
        type=Path,
        default=DEFAULT_CITATIONS_JSON,
        help="Path to the generated lean-citations.json file",
    )
    parser.add_argument(
        "--references-json",
        type=Path,
        default=DEFAULT_REFERENCES_JSON,
        help="Path to the generated references.json file",
    )
    parser.add_argument(
        "--format",
        choices=["shell", "review"],
        default="shell",
        help="Output either shell-friendly lines or a review-comment block",
    )
    return parser.parse_args()


def emit_shell(keys: list[str], repo_refs: list[str], external_refs: list[str]) -> None:
    """Emit shell-friendly output."""

    print(f"keys={','.join(keys)}")
    print(f"repo_context_refs={','.join(repo_refs)}")
    print(f"external_refs={','.join(external_refs)}")


def emit_review(keys: list[str], repo_refs: list[str], external_refs: list[str]) -> None:
    """Emit a block suitable for a `/review` comment body."""

    print("/review")
    if external_refs:
        print("External:")
        for ref in external_refs:
            print(f"- {ref}")
    if repo_refs:
        print("Internal:")
        for ref in repo_refs:
            print(f"- {ref}")
    print("Comments:")
    if keys:
        print(f"Focus on citation-backed review context for: {', '.join(keys)}")
    else:
        print("Focus on citation-backed review context inferred from the supplied files.")


def main() -> int:
    """Entry point."""

    args = parse_args()
    citations_payload = load_json(args.citations_json.resolve())
    references_payload = load_json(args.references_json.resolve())

    explicit_keys = parse_csv_items(args.keys)
    validate_explicit_keys(explicit_keys, references_payload)
    file_paths = parse_csv_items(args.files)
    inferred_keys = infer_keys_from_files(file_paths, citations_payload)
    keys = unique_in_order(explicit_keys + sorted(inferred_keys))

    repo_refs = unique_in_order(build_repo_refs(keys))
    external_refs = unique_in_order(build_external_refs(keys, references_payload))

    if args.format == "shell":
        emit_shell(keys, repo_refs, external_refs)
    else:
        emit_review(keys, repo_refs, external_refs)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
