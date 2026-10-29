#!/usr/bin/env python3
"""Report the scope of a branch against its pull request base.

The `make-pr-ready` skill uses this script to find what a branch contributes. A plain
`git diff origin/main...HEAD` is wrong in three common cases, and this script handles each one:

- Uncommitted work: the script adds the staged and unstaged changes to the committed changes.
- A merge in progress: the work tree then contains the changes of the base. The script compares
  the work tree with the base directly.
- A deleted file that a later change restores: the script does not report it as deleted.

Commands:
  summary      the changed files, deleted paths, generated-file drift, and working files
  files        the changed paths, one on each line
  deleted      the deleted and renamed paths, one on each line
  stale-refs   the tracked lines that still refer to a deleted path

The default base is `origin/main`. Run `git fetch` first, so that the base is current.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from pathlib import Path
import re
import subprocess
import sys

CANONICAL_REMOTE = "Verified-zkEVM/ArkLib"
GENERATED = "docs/kb/_generated/"
SWEEP_EXCLUDES = [":!docs/kb/_generated", ":!ArkLib.lean"]
# A basename that many directories share. A search for it finds only noise.
COMMON_BASENAMES = {"README.md", "index.md", "Basic.lean", "Defs.lean"}
CURATED_PREFIXES = ("docs/wiki/", "docs/skills/", "docs/design/", "docs/kb/papers/",
                    "docs/kb/sources/", "blueprint/", ".github/")
CURATED_FILES = {"README.md", "ROADMAP.md", "CONTRIBUTING.md", "BACKGROUND.md", "AGENTS.md"}


@dataclass(frozen=True)
class Change:
    status: str
    path: str
    old_path: str | None = None


def git(*args: str, check: bool = True) -> subprocess.CompletedProcess[str]:
    return subprocess.run(["git", *args], check=check, capture_output=True, text=True)


def merge_in_progress() -> bool:
    return git("rev-parse", "--verify", "-q", "MERGE_HEAD", check=False).returncode == 0


def parse_name_status(output: str) -> list[Change]:
    changes = []
    for line in output.splitlines():
        fields = line.split("\t")
        status = fields[0][0]
        if status in "RC":
            changes.append(Change(status, fields[2], fields[1]))
        else:
            changes.append(Change(status, fields[1]))
    return changes


def changes(base: str) -> list[Change]:
    """Return the changes that the branch contributes, with uncommitted work included."""
    if merge_in_progress():
        return parse_name_status(git("diff", "--name-status", "-M", base).stdout)
    by_path: dict[str, Change] = {}
    committed = parse_name_status(git("diff", "--name-status", "-M", f"{base}...HEAD").stdout)
    uncommitted = parse_name_status(git("diff", "--name-status", "-M", "HEAD").stdout)
    for change in committed + uncommitted:
        if change.old_path is not None:
            by_path.pop(change.old_path, None)
        by_path[change.path] = change
    # A file that the branch adds and then deletes again is not a change against the base.
    kept = [change for change in by_path.values()
            if change.status != "D" or in_base(base, change.path)]
    return sorted(kept, key=lambda change: (change.path, change.status))


def in_base(base: str, path: str) -> bool:
    return git("cat-file", "-e", f"{base}:{path}", check=False).returncode == 0


def deleted_paths(base: str) -> list[str]:
    """Return the deleted and renamed-away paths that do not exist in the work tree."""
    paths = set()
    for change in changes(base):
        if change.status == "D":
            paths.add(change.path)
        elif change.old_path is not None:
            paths.add(change.old_path)
    return sorted(path for path in paths if not Path(path).exists())


def generated_drift(base: str) -> tuple[list[str], list[str]]:
    """Return the committed and the uncommitted changes under the generated KB directory."""
    committed = git("diff", "--name-only", base, "HEAD", "--", GENERATED).stdout.split()
    uncommitted = git("diff", "--name-only", "HEAD", "--", GENERATED).stdout.split()
    return committed, uncommitted


def working_files(base: str) -> list[tuple[str, str]]:
    """Return the Markdown files outside the curated documentation, with their state."""
    found = []
    for change in changes(base):
        if change.status == "A" and change.path.endswith(".md"):
            found.append((change.path, "added"))
    untracked = git("ls-files", "--others", "--exclude-standard", "--", "*.md").stdout.split()
    found.extend((path, "untracked") for path in untracked)
    return [(path, state) for path, state in sorted(set(found))
            if not path.startswith(CURATED_PREFIXES) and path not in CURATED_FILES
            and Path(path).name != "README.md"]


def module_name(path: str) -> str | None:
    if not path.endswith(".lean"):
        return None
    return path[: -len(".lean")].replace("/", ".")


def stale_references(base: str) -> list[tuple[str, str, str]]:
    """Return (deleted path, pattern kind, matching line) for each reference to a deleted path."""
    tracked = git("ls-files").stdout.splitlines()
    found = []
    for path in deleted_paths(base):
        patterns = [("path", ["-F", "-e", path])]
        name = Path(path).name
        parent = Path(path).parent.name
        if name in COMMON_BASENAMES and parent:
            # A relative link names the parent directory: `a/README.md`.
            patterns.append(("parent and basename", ["-F", "-e", f"{parent}/{name}"]))
        elif name not in COMMON_BASENAMES:
            namesakes = [other for other in tracked if Path(other).name == name]
            kind = f"basename, also the name of {namesakes[0]}" if namesakes else "basename"
            patterns.append((kind, ["-F", "-e", name]))
        module = module_name(path)
        if module is not None:
            # Anchor the end, so that `A.B` does not match the live module `A.B.C`.
            patterns.append(("module", ["-E", "-e", re.escape(module) + r"($|[^.A-Za-z0-9_])"]))
        seen = set()
        for kind, arguments in patterns:
            result = git("grep", "-n", *arguments, "--", ".", *SWEEP_EXCLUDES, check=False)
            for line in result.stdout.splitlines():
                if line not in seen:
                    seen.add(line)
                    found.append((path, kind, line))
    return found


def check_base(base: str) -> list[str]:
    warnings = []
    if git("rev-parse", "--verify", "-q", base, check=False).returncode != 0:
        raise SystemExit(f"The base {base!r} does not exist. Fetch it first.")
    remote = base.split("/", 1)[0]
    url = git("remote", "get-url", remote, check=False).stdout.strip()
    if url and CANONICAL_REMOTE not in url:
        warnings.append(f"The remote {remote!r} is {url}, not {CANONICAL_REMOTE}. A fork can "
                        "have an old main branch. Fetch the canonical base and use it.")
    if merge_in_progress():
        warnings.append("A merge is in progress. The scope is the work tree compared with the "
                        "base. Make sure that MERGE_HEAD is the base.")
    return warnings


def summary(base: str) -> None:
    for warning in check_base(base):
        print(f"Warning: {warning}")
    print(f"# Changed files compared with {base}")
    for change in changes(base):
        source = f" (from {change.old_path})" if change.old_path else ""
        print(f"{change.status}\t{change.path}{source}")
    print("\n# Deleted or renamed paths")
    for path in deleted_paths(base):
        print(path)
    committed, uncommitted = generated_drift(base)
    print(f"\n# Changes under {GENERATED}")
    for path in committed:
        print(f"committed\t{path}\t(the CI guard fails: restore it from the base and commit)")
    for path in uncommitted:
        print(f"uncommitted\t{path}\t(restore it from the base before you commit)")
    print("\n# Markdown files outside the curated documentation (report them, do not delete them)")
    for path, state in working_files(base):
        print(f"{state}\t{path}")
    untracked = git("ls-files", "--others", "--exclude-standard").stdout.split()
    print("\n# Other untracked files (a commit does not include them until you stage them)")
    for path in untracked:
        if not path.endswith(".md"):
            print(path)


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("command", choices=["summary", "files", "deleted", "stale-refs"],
                        nargs="?", default="summary")
    parser.add_argument("--base", default="origin/main", help="the pull request base")
    args = parser.parse_args(argv[1:])
    if args.command == "summary":
        summary(args.base)
        return 0
    check_base(args.base)
    if args.command == "files":
        for change in changes(args.base):
            print(change.path)
    elif args.command == "deleted":
        for path in deleted_paths(args.base):
            print(path)
    else:
        for path, kind, line in stale_references(args.base):
            print(f"{path}\t{kind}\t{line}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
