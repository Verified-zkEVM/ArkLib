#!/usr/bin/env python3
"""Scaffold a paper page and source metadata file from a BibTeX key."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from common import DEFAULT_BIB_PATH, DEFAULT_REFERENCES_JSON, REPO_ROOT, load_bib_entries


PAPERS_DIR = REPO_ROOT / "docs" / "kb" / "papers"
SOURCES_DIR = REPO_ROOT / "docs" / "kb" / "sources"


def yaml_quote(value: str) -> str:
    """Quote a string for the simple YAML metadata files used by the KB."""

    return json.dumps(value)


def load_entries(references_json: Path, bib_path: Path) -> dict[str, dict[str, object]]:
    """Load bibliography entries keyed by BibTeX key."""

    if references_json.exists():
        payload = json.loads(references_json.read_text(encoding="utf-8"))
        entries = payload.get("entries", {})
        return {str(key): value for key, value in entries.items()}
    return {entry.key: entry.to_json() for entry in load_bib_entries(bib_path)}


def build_paper_template(key: str, entry: dict[str, object]) -> str:
    """Build the initial paper page template."""

    title = str(entry.get("title", ""))
    year = str(entry.get("year", ""))
    url = str(entry.get("url", ""))
    canonical_url_line = f"canonical_url: {url}\n" if url else ""
    return (
        "---\n"
        "kind: paper\n"
        f"bibkey: {key}\n"
        f"title: {yaml_quote(title)}\n"
        f"year: {yaml_quote(year)}\n"
        "bib_source: blueprint/src/references.bib\n"
        f"{canonical_url_line}"
        f"source_metadata: ../sources/{key}/metadata.yml\n"
        "status: stub\n"
        "---\n\n"
        f"# {key}\n\n"
        "## At A Glance\n\n"
        "TODO: summarize the paper in ArkLib terms.\n\n"
        "## What ArkLib Uses From This Paper\n\n"
        "TODO: list the main definitions, theorems, or protocol ideas ArkLib relies on.\n\n"
        "## Main ArkLib Touchpoints\n\n"
        "TODO: add the relevant Lean modules or doc pages.\n\n"
        "## Version Notes\n\n"
        "TODO: record version lineage, duplicate keys, or publication-status issues if relevant.\n\n"
        "## Known Divergences From ArkLib\n\n"
        "TODO: record material interface or statement-shape differences.\n\n"
        "## Open Formalization Gaps\n\n"
        "TODO: record important missing theorems, abstractions, or proof gaps.\n\n"
        "## Source Access\n\n"
        f"- Source metadata: [`../sources/{key}/metadata.yml`](../sources/{key}/metadata.yml)\n"
        "- Public reference: "
        "[`blueprint/src/references.bib`](../../../blueprint/src/references.bib)\n"
    )


def build_metadata_template(key: str, entry: dict[str, object]) -> str:
    """Build the initial source metadata template."""

    url = str(entry.get("url", ""))
    title = str(entry.get("title", ""))
    lines = [
        f"bibkey: {key}",
        "source_kind: bibliography-only",
    ]
    if url:
        lines.append(f"canonical_url: {url}")
    lines.extend(
        [
            "committed_artifacts: []",
            f"notes: {yaml_quote(f'Scaffolded from references.bib for {title}.')}",
        ]
    )
    return "\n".join(lines) + "\n"


def parse_args() -> argparse.Namespace:
    """Parse CLI arguments."""

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("key", help="BibTeX key to scaffold")
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
        "--force",
        action="store_true",
        help="Overwrite existing files instead of refusing to modify them",
    )
    return parser.parse_args()


def write_if_allowed(path: Path, content: str, force: bool) -> None:
    """Write ``content`` to ``path`` unless the file exists and ``force`` is false."""

    if path.exists() and not force:
        raise FileExistsError(f"Refusing to overwrite existing file: {path}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def main() -> int:
    """Entry point."""

    args = parse_args()
    key = args.key.strip()
    entries = load_entries(args.references_json.resolve(), args.bib.resolve())
    if key not in entries:
        available = ", ".join(sorted(entries)[:10])
        raise SystemExit(f"Unknown BibTeX key {key!r}. Example known keys: {available}")

    paper_path = PAPERS_DIR / f"{key}.md"
    metadata_path = SOURCES_DIR / key / "metadata.yml"
    entry = entries[key]

    write_if_allowed(paper_path, build_paper_template(key, entry), args.force)
    write_if_allowed(metadata_path, build_metadata_template(key, entry), args.force)

    rel_paper = paper_path.relative_to(REPO_ROOT)
    rel_metadata = metadata_path.relative_to(REPO_ROOT)
    print(f"Scaffolded {rel_paper}")
    print(f"Scaffolded {rel_metadata}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
