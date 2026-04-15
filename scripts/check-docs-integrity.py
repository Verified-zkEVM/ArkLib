#!/usr/bin/env python3
"""Check ArkLib documentation integrity.

Checks:
1. `CLAUDE.md` exists and is a symlink to `AGENTS.md`
2. Local markdown links in tracked `.md` files resolve

Exit code 0 if all checks pass, 1 otherwise.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
CLAUDE_PATH = REPO_ROOT / "CLAUDE.md"
AGENTS_PATH = REPO_ROOT / "AGENTS.md"

MARKDOWN_LINK_RE = re.compile(r"(?<!!)\[[^\]]+\]\(([^)]+)\)")


def tracked_markdown_files() -> list[Path]:
    return [
        AGENTS_PATH,
        REPO_ROOT / "scripts" / "README.md",
        *sorted((REPO_ROOT / "docs").rglob("*.md")),
    ]


def check_claude_symlink() -> list[str]:
    errors: list[str] = []
    if not AGENTS_PATH.exists():
        errors.append("Missing AGENTS.md")
        return errors
    if not CLAUDE_PATH.exists() and not CLAUDE_PATH.is_symlink():
        errors.append("Missing CLAUDE.md")
        return errors
    if not CLAUDE_PATH.is_symlink():
        errors.append("CLAUDE.md must be a symlink to AGENTS.md")
        return errors

    target = Path(CLAUDE_PATH.readlink())
    if target != Path("AGENTS.md"):
        errors.append(f"CLAUDE.md must point to AGENTS.md, found {target}")
    elif not CLAUDE_PATH.resolve().samefile(AGENTS_PATH):
        errors.append("CLAUDE.md symlink does not resolve to AGENTS.md")
    return errors


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
    all_errors: list[str] = []

    print("Checking CLAUDE.md symlink...")
    all_errors.extend(check_claude_symlink())

    print("Checking tracked markdown links...")
    all_errors.extend(check_markdown_links())

    if all_errors:
        print(f"\n{len(all_errors)} issue(s) found:\n")
        for err in all_errors:
            print(f"  - {err}")
        return 1

    print("\nAll documentation integrity checks passed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
