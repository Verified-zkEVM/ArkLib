#!/usr/bin/env python3
"""Check a pull request title against the format in CONTRIBUTING.md.

The format is `<type>(<optional-scope>)<optional !>: <subject>`. The allowed types are the
backticked names in the `**Types:**` list of CONTRIBUTING.md, so that list is the only copy.

Usage: check-pr-title.py [TITLE]. Without an argument, the script reads `PR_TITLE` from the
environment. The exit code is 0 for a valid title and 1 for an invalid title.
"""

from __future__ import annotations

import os
from pathlib import Path
import re
import sys

CONTRIBUTING = Path(__file__).resolve().parent.parent / "CONTRIBUTING.md"


def allowed_types(contributing: Path = CONTRIBUTING) -> list[str]:
    """Return the types in the `**Types:**` list of CONTRIBUTING.md, in order."""
    text = contributing.read_text(encoding="utf-8")
    start = text.index("**Types:**")
    end = text.index("**Subject:**", start)
    types = re.findall(r"^\* `([a-z]+)`:", text[start:end], flags=re.MULTILINE)
    if not types:
        raise ValueError(f"no types found in {contributing}")
    return types


def is_name(word: str) -> bool:
    """Return whether `word` is a name that keeps its capital, for example `FRI` or `Poseidon2`.

    An acronym, a word with a digit, and a word with an uppercase letter after its first letter
    count as names. An ordinary capitalized word, for example `Proof`, does not.
    """
    word = word.strip("`'\",.:;()")
    return any(c.isdigit() for c in word) or any(c.isupper() for c in word[1:])


def problems(title: str, types: list[str]) -> list[str]:
    """Return the format problems of `title`. An empty list means that the title is valid."""
    match = re.fullmatch(r"([a-z]+)(\([^()\s][^()]*\))?(!)?: (.*)", title)
    if match is None:
        return ["The title must have the form `<type>(<optional-scope>): <subject>`."]
    found = []
    kind, subject = match.group(1), match.group(4)
    if kind not in types:
        found.append(f"The type `{kind}` is not one of: {', '.join(types)}.")
    if not subject.strip():
        found.append("The subject is empty.")
    elif subject != subject.strip():
        found.append("The subject starts or ends with a space.")
    if subject.endswith("."):
        found.append("The subject must not end with a period.")
    return found


def warnings(title: str) -> list[str]:
    """Return the advice for `title` that a script cannot decide, for example capitalization.

    A subject can start with a name, for example "Binary Basefold", so a capital letter is only a
    warning.
    """
    match = re.fullmatch(r"[a-z]+(\([^()]*\))?!?: (\S.*)", title)
    if match is None:
        return []
    first = match.group(2).split()[0]
    if first[0].isupper() and not is_name(first):
        return [f"The subject starts with `{first}`. Do not capitalize the first word unless "
                "it is a name."]
    return []


def escape(message: str) -> str:
    """Escape `message` for the data part of a GitHub workflow command."""
    return message.replace("%", "%25").replace("\r", "%0D").replace("\n", "%0A")


def main(argv: list[str]) -> int:
    title = argv[1] if len(argv) > 1 else os.environ.get("PR_TITLE", "")
    found = problems(title, allowed_types())
    github = os.environ.get("GITHUB_ACTIONS") == "true"
    for advice in warnings(title):
        print(f"::warning title=Pull request title::{escape(advice)}" if github
              else f"Warning: {advice}")
    for problem in found:
        message = f"Invalid pull request title {title!r}: {problem}"
        print(f"::error title=Pull request title::{escape(message)}" if github else message)
    if found:
        print("Refer to CONTRIBUTING.md, section \"Title Format\".")
        return 1
    print(f"The pull request title {title!r} has the correct format.")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
