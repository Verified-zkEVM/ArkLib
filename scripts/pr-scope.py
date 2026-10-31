#!/usr/bin/env python3
"""Report the scope of a branch against its pull request base.

The `make-pr-ready` skill uses this script to find what a branch contributes. A plain
`git diff origin/main...HEAD` is wrong in two common cases:

- Uncommitted work: the script compares the work tree, not `HEAD`, with the merge base of the
  base and `HEAD`. Thus a later edit does not hide an earlier rename or addition, and a file that
  a later change restores is not deleted.
- A merge in progress: the work tree then contains the changes of the base. The script compares
  the work tree with the base directly, because the base is the merge base after the merge.

The CI guard for generated files compares the merge base with the head of the pull request. This
script uses the same comparison, so it does not report a change that only the base made.

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


def merge_base(base: str) -> str:
    """Return the commit that the branch starts from, as the CI guard computes it.

    During a merge in progress, the base becomes the merge base when the merge is committed.
    """
    if merge_in_progress():
        return base
    return git("merge-base", base, "HEAD").stdout.strip()


def changes(base: str) -> list[Change]:
    """Return the changes that the branch contributes, with uncommitted work included."""
    # One comparison of the work tree with the merge base gives the net change. A union of the
    # committed and the uncommitted statuses loses a rename or an addition after a later edit.
    output = git("diff", "--name-status", "-M", merge_base(base)).stdout
    return sorted(parse_name_status(output), key=lambda change: (change.path, change.status))


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
    """Return the generated KB files that differ from the merge base, at `HEAD` and in the work
    tree. The first list is the view of the CI guard on the current head. The second list is its
    view after a commit of the work tree.
    """
    start = merge_base(base)
    committed = [] if merge_in_progress() else git(
        "diff", "--name-only", f"{start}...HEAD", "--", GENERATED).stdout.split()
    work_tree = git("diff", "--name-only", start, "--", GENERATED).stdout.split()
    return committed, work_tree


def restore_command(base: str) -> str:
    source = base if merge_in_progress() else f'"$(git merge-base {base} HEAD)"'
    return f"git restore --source={source} --staged --worktree -- {GENERATED}"


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
    committed, work_tree = generated_drift(base)
    print(f"\n# Changes under {GENERATED} compared with the merge base")
    for path in committed:
        print(f"HEAD\t{path}\t(the CI guard fails on the current head)")
    for path in work_tree:
        print(f"work tree\t{path}\t(the CI guard fails after a commit of the work tree)")
    if committed or work_tree:
        print(f"Restore the directory with `{restore_command(base)}`. Then commit the result.")
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
