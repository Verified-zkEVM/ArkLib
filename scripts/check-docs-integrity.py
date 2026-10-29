#!/usr/bin/env python3
"""Check ArkLib documentation integrity.

Checks:
1. The canonical `AGENTS.md` guide and documentation entry points exist
2. Local markdown links in tracked `.md` files resolve

Exit code 0 if all checks pass, 1 otherwise.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
AGENTS_PATH = REPO_ROOT / "AGENTS.md"

MARKDOWN_LINK_RE = re.compile(r"(?<!!)\[[^\]]+\]\(([^)]+)\)")


def tracked_markdown_files() -> list[Path]:
    # `docs/kb/_generated/` is machine-generated and refreshed on `main` by the KB
    # generated-files workflow (and is off-limits to feature PRs per the CI guard).
    # Its line-anchored source links are inherently fragile and not hand-maintained,
    # so they are excluded from the link-integrity check.
    docs_md = sorted(
        p for p in (REPO_ROOT / "docs").rglob("*.md") if "_generated" not in p.parts
    )
    return [
        AGENTS_PATH,
        REPO_ROOT / "scripts" / "README.md",
        *docs_md,
    ]


def resolve_link(source_file: Path, raw_target: str) -> Path | None:
    target = raw_target.strip().strip("`")
    if not target or "://" in target or target.startswith("mailto:"):
        return None

    path_part = target.split("#", 1)[0].strip()
    if not path_part:
        return None

    if path_part.startswith("/"):
        return (REPO_ROOT / path_part.lstrip("/")).resolve()
    return (source_file.parent / path_part).resolve()


def check_markdown_links() -> list[str]:
    errors: list[str] = []
    for doc_file in tracked_markdown_files():
        if not doc_file.is_file():
            errors.append(f"Missing documentation file: {doc_file.relative_to(REPO_ROOT)}")
            continue
        text = doc_file.read_text()
        for raw_target in MARKDOWN_LINK_RE.findall(text):
            resolved = resolve_link(doc_file, raw_target)
            if resolved is None:
                continue
            if not resolved.exists():
                rel_doc = doc_file.relative_to(REPO_ROOT)
                errors.append(f"Broken link in {rel_doc}: {raw_target}")
    return errors


def main() -> int:
    print("Checking canonical agent guide and documentation links...")
    all_errors = check_markdown_links()

    if all_errors:
        print(f"\n{len(all_errors)} issue(s) found:\n")
        for err in all_errors:
            print(f"  - {err}")
        return 1

    print("\nAll documentation integrity checks passed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
