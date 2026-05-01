#!/usr/bin/env python3
"""Lint the ArkLib knowledge base for basic structural consistency."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from common import DEFAULT_BIB_PATH, DEFAULT_REFERENCES_JSON, DEFAULT_CITATIONS_JSON, REPO_ROOT, load_bib_entries


PAPERS_DIR = REPO_ROOT / "docs" / "kb" / "papers"
SOURCES_DIR = REPO_ROOT / "docs" / "kb" / "sources"

REQUIRED_PAPER_HEADINGS = [
    "## At A Glance",
    "## What ArkLib Uses From This Paper",
    "## Main ArkLib Touchpoints",
    "## Source Access",
]


def load_reference_keys(references_json: Path, bib_path: Path) -> set[str]:
    """Load the known bibliography keys."""

    if references_json.exists():
        payload = json.loads(references_json.read_text(encoding="utf-8"))
        return set(payload.get("entries", {}))
    return {entry.key for entry in load_bib_entries(bib_path)}


def load_cited_keys(citations_json: Path) -> set[str]:
    """Load the cited keys from the generated citation map if present."""

    if not citations_json.exists():
        return set()
    payload = json.loads(citations_json.read_text(encoding="utf-8"))
    return set(payload.get("keys", {}))


def parse_frontmatter(text: str) -> dict[str, str]:
    """Parse the top-level YAML frontmatter block with a minimal line-based parser."""

    if not text.startswith("---\n"):
        return {}
    end = text.find("\n---\n", 4)
    if end == -1:
        return {}
    block = text[4:end]
    fields: dict[str, str] = {}
    for line in block.splitlines():
        if not line or line.startswith(" ") or ":" not in line:
            continue
        key, value = line.split(":", 1)
        fields[key.strip()] = value.strip()
    return fields


def is_quoted_yaml_scalar(value: str) -> bool:
    """Return true if ``value`` is explicitly quoted as a YAML string."""

    return len(value) >= 2 and (
        (value.startswith('"') and value.endswith('"')) or (value.startswith("'") and value.endswith("'"))
    )


def lint_plain_yaml_scalars(path: Path, lines: list[str]) -> list[str]:
    """Catch plain scalar values that are likely invalid YAML."""

    errors: list[str] = []
    for line_number, line in enumerate(lines, 1):
        stripped = line.strip()
        if not stripped or stripped == "---" or line.startswith(" ") or line.startswith("-"):
            continue
        if ":" not in line:
            continue
        key, value = line.split(":", 1)
        value = value.strip()
        if not key.strip() or not value or is_quoted_yaml_scalar(value):
            continue
        if ": " in value:
            rel_path = path.relative_to(REPO_ROOT)
            errors.append(f"Unquoted YAML scalar with ': ' in {rel_path}:{line_number}")
    return errors


def lint_source_metadata() -> list[str]:
    """Lint source metadata YAML files for basic scalar safety."""

    errors: list[str] = []
    for metadata_path in sorted(SOURCES_DIR.glob("*/metadata.yml")):
        lines = metadata_path.read_text(encoding="utf-8").splitlines()
        errors.extend(lint_plain_yaml_scalars(metadata_path, lines))
    return errors


def lint_paper_pages(reference_keys: set[str]) -> tuple[list[str], list[str], set[str]]:
    """Lint paper pages and collect structural errors and warnings."""

    errors: list[str] = []
    warnings: list[str] = []
    page_keys: set[str] = set()

    for paper_path in sorted(PAPERS_DIR.glob("*.md")):
        if paper_path.name == "README.md":
            continue
        key = paper_path.stem
        page_keys.add(key)
        if key not in reference_keys:
            errors.append(f"Paper page without matching BibTeX key: {paper_path.relative_to(REPO_ROOT)}")

        text = paper_path.read_text(encoding="utf-8")
        if text.startswith("---\n"):
            frontmatter_end = text.find("\n---\n", 4)
            if frontmatter_end == -1:
                errors.append(f"Paper page has unterminated frontmatter: {paper_path.relative_to(REPO_ROOT)}")
            else:
                frontmatter_lines = text[:frontmatter_end].splitlines()
                errors.extend(lint_plain_yaml_scalars(paper_path, frontmatter_lines))
        frontmatter = parse_frontmatter(text)
        bibkey = frontmatter.get("bibkey")
        if bibkey != key:
            errors.append(
                f"Paper page bibkey mismatch in {paper_path.relative_to(REPO_ROOT)}: "
                f"expected {key}, found {bibkey or '<missing>'}"
            )

        source_metadata = frontmatter.get("source_metadata")
        if source_metadata:
            resolved = (paper_path.parent / source_metadata).resolve()
            if not resolved.exists():
                errors.append(
                    f"Missing source_metadata target in {paper_path.relative_to(REPO_ROOT)}: {source_metadata}"
                )
        else:
            warnings.append(f"Paper page missing source_metadata: {paper_path.relative_to(REPO_ROOT)}")

        for heading in REQUIRED_PAPER_HEADINGS:
            if heading not in text:
                errors.append(
                    f"Paper page missing required heading in {paper_path.relative_to(REPO_ROOT)}: {heading}"
                )

    return errors, warnings, page_keys


def lint_duplicate_canonical_urls() -> list[str]:
    """Detect duplicate canonical_url values across paper pages."""

    seen: dict[str, Path] = {}
    errors: list[str] = []
    for paper_path in sorted(PAPERS_DIR.glob("*.md")):
        if paper_path.name == "README.md":
            continue
        frontmatter = parse_frontmatter(paper_path.read_text(encoding="utf-8"))
        url = frontmatter.get("canonical_url")
        if not url:
            continue
        if url in seen:
            errors.append(
                "Duplicate canonical_url across "
                f"{seen[url].relative_to(REPO_ROOT)} and {paper_path.relative_to(REPO_ROOT)}: {url}"
            )
        else:
            seen[url] = paper_path
    return errors


def parse_args() -> argparse.Namespace:
    """Parse CLI arguments."""

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--references-json",
        type=Path,
        default=DEFAULT_REFERENCES_JSON,
        help="Path to the generated references.json file",
    )
    parser.add_argument(
        "--citations-json",
        type=Path,
        default=DEFAULT_CITATIONS_JSON,
        help="Path to the generated lean-citations.json file",
    )
    parser.add_argument(
        "--bib",
        type=Path,
        default=DEFAULT_BIB_PATH,
        help="Fallback path to references.bib if references.json does not exist",
    )
    parser.add_argument(
        "--strict-cited-pages",
        action="store_true",
        help="Fail if any cited BibTeX key lacks a paper page",
    )
    return parser.parse_args()


def main() -> int:
    """Entry point."""

    args = parse_args()
    reference_keys = load_reference_keys(args.references_json.resolve(), args.bib.resolve())
    cited_keys = load_cited_keys(args.citations_json.resolve())

    errors, warnings, page_keys = lint_paper_pages(reference_keys)
    errors.extend(lint_duplicate_canonical_urls())
    errors.extend(lint_source_metadata())

    missing_cited_pages = sorted(cited_keys - page_keys)
    if args.strict_cited_pages and missing_cited_pages:
        errors.extend(f"Missing paper page for cited key: {key}" for key in missing_cited_pages)
    else:
        warnings.extend(f"Missing paper page for cited key: {key}" for key in missing_cited_pages)

    if warnings:
        print("Warnings:")
        for warning in warnings:
            print(f"  - {warning}")

    if errors:
        print("\nErrors:")
        for error in errors:
            print(f"  - {error}")
        return 1

    print("Knowledge base lint passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
