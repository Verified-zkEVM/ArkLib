#!/usr/bin/env python3
"""Check prose against the measurable rules of the ArkLib writing standard.

The standard is `docs/wiki/writing.md`. This script checks the rules that a search can find:

- S1: sentence length (20 words in a numbered list item, 25 words elsewhere)
- P2: more than six sentences in a paragraph
- U1: semicolons, and U2: em dashes that join clauses
- W6: phrasal verbs, and W7: Latin abbreviations
- S5: contractions
- V1: perfect and progressive verb forms, and V2: a clause that starts with an "-ing" form
- S7: a sentence that starts with "This" or "These" and a verb, with no noun
- Vocabulary: the words to avoid in `docs/wiki/writing-vocabulary.md`.

Review checks the other rules. The checker counts words as the standard specifies: a code span,
a formula, a citation key, a link, a quotation, and a parenthesis each count as one word. Quoted
text, code, formulas, headings, and HTML comments are exempt from all rules. The words "now" and
"new" are not flagged alone, because both words also have ordinary meanings.

Usage:
  check-writing.py --base REF      the prose that changed since the merge base with REF
  check-writing.py FILE...         all prose in each file
  check-writing.py --stdin LABEL   all prose in standard input, for example a pull request body

In `--base` mode, the checker reads the tracked files in the working tree. It checks each
paragraph, list item, or table cell that contains an added line. It ignores untracked files.

Options: `--github` prints GitHub annotations. `--strict` exits with 1 if it finds a problem.
Without `--strict`, the exit code is 0, and 2 for a usage error.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
VOCABULARY = ROOT / "docs" / "wiki" / "writing-vocabulary.md"
EXCLUDED_PREFIXES = ("docs/kb/_generated/", "home_page/docs/", ".lake/")
EXCLUDED_FILES = {"ArkLib.lean"}

PROCEDURAL_LIMIT = 20
DESCRIPTIVE_LIMIT = 25
PARAGRAPH_LIMIT = 6

ABBREVIATIONS = {"e.g.", "i.e.", "etc.", "cf.", "vs.", "al.", "fig.", "no.", "resp.", "viz.",
                 "thm.", "lem.", "sec.", "eq.", "approx.", "def.", "prop.", "cor."}
PHRASAL_PAIRS = {
    "set up": "set|sets", "carry out": "carry|carries|carried",
    "figure out": "figure|figures|figured", "point out": "point|points|pointed",
    "rule out": "rule|rules|ruled", "fill in": "fill|fills|filled",
    "fill out": "fill|fills|filled", "look up": "look|looks|looked", "end up": "end|ends|ended",
    "find out": "find|finds|found", "pick up": "pick|picks|picked",
    "check out": "check|checks|checked", "come up with": "come|comes|came",
}
PHRASAL = re.compile(
    "|".join(rf"\b(?:{forms})\s+{re.escape(pair.split(' ', 1)[1])}\b"
             for pair, forms in PHRASAL_PAIRS.items()), re.IGNORECASE)
LATIN = re.compile(r"(?<![\w.])(?:e\.g\.|i\.e\.|etc\.|cf\.|resp\.|viz\.)", re.IGNORECASE)
CONTRACTION = re.compile(
    r"\b\w+n['’]t\b|\b\w+['’](?:re|ll|ve|d)\b"
    r"|\b(?:it|that|there|here|what|let|who|where)['’]s\b", re.IGNORECASE)
PARTICIPLES = ("been|done|made|given|shown|written|seen|found|built|taken|run|kept|left|set|put|"
               "proven|proved|chosen|known|become|begun|gone|got|gotten|lost|met|said|sent|told|"
               "thought|brought|understood|held")
PERFECT = re.compile(rf"\b(?:has|have|had)\s+(?:not\s+)?(\w+ed|{PARTICIPLES})\b", re.IGNORECASE)
# After a modal verb, "have" and a participle keep a hedge: "the build may have failed".
MODAL_BEFORE = re.compile(r"\b(?:may|might|could|would|should|must|can|will)(?:\s+not)?\s+$",
                          re.IGNORECASE)
# Adjectives in "-ed" that follow "has" or "have" as possession: "polynomials have bounded degree".
POSSESSED_ADJECTIVES = {"bounded", "unbounded", "fixed", "nested", "ordered", "distributed",
                        "prescribed", "limited", "mixed", "balanced", "weighted", "labeled",
                        "sorted", "indexed", "typed", "isolated", "repeated", "related", "named"}
NOT_PROGRESSIVE = {"nothing", "something", "anything", "everything", "missing", "remaining",
                   "string", "strings", "ring", "rings", "thing", "things", "during", "padding",
                   "binding", "encoding", "decoding", "folding", "batching", "hashing"}
PROGRESSIVE = re.compile(r"\b(?:is|are|was|were|be|been)\s+(\w+ing)\b", re.IGNORECASE)
BARE_THIS = re.compile(
    r"^(?:This|These)\s+(?:is|are|was|were|means|makes|ensures|lets|gives|shows|allows|"
    r"requires|keeps|fixes|adds|avoids|matches|also|will|can|way)\b")
# "During" is a preposition, not an "-ing" form of a verb.
ING_START = re.compile(r"^(?!During\b)[A-Z][a-z]+ing\b[^,.;:]{0,80},")
EM_DASH = re.compile(r"—|\s–\s|\s--\s")
HISTORY_SCOPE = re.compile(r"^(?:docs/wiki/|ArkLib/|ArkLibTest/)|\.lean$")


@dataclass
class Block:
    path: str
    line: int
    text: str
    procedural: bool
    paragraph: bool
    last_line: int


@dataclass
class Finding:
    path: str
    line: int
    rule: str
    message: str
    excerpt: str


# ---------------------------------------------------------------------------------------------
# Vocabulary


def avoid_words(vocabulary: Path = VOCABULARY) -> tuple[list[str], list[str]]:
    """Return the general words to avoid and the history words (rule C3) from the vocabulary.

    The words are the quoted terms in the first column of the "Words to avoid" table. A row whose
    second column names rule C3 gives history words, which apply only to library text.
    """
    text = vocabulary.read_text(encoding="utf-8")
    table = text[text.index("## Words to avoid"):]
    general: list[str] = []
    history: list[str] = []
    for row in table.splitlines():
        cells = [cell.strip() for cell in row.strip().strip("|").split("|")]
        if len(cells) < 2 or not cells[0].startswith('"'):
            continue
        words = re.findall(r'"([^"]+)"', cells[0])
        (history if "rule C3" in cells[1] else general).extend(words)
    history = [word for word in history if word.lower() not in {"now", "new"}]
    if not general:
        raise ValueError(f"no words to avoid found in {vocabulary}")
    return general, history


def word_pattern(words: list[str]) -> re.Pattern[str] | None:
    if not words:
        return None
    def alternative(word: str) -> str:
        # A single word also matches its inflected forms: "utilize" matches "utilizes".
        suffix = r"(?:s|es|d|ed|ing)?" if re.fullmatch(r"[a-z]+", word) else ""
        return re.escape(word) + suffix

    alternatives = sorted((alternative(word) for word in words), key=len, reverse=True)
    return re.compile(r"(?<![\w.])(?:" + "|".join(alternatives) + r")(?![\w])", re.IGNORECASE)


# ---------------------------------------------------------------------------------------------
# Extraction of prose blocks

LIST_ITEM = re.compile(r"^(\s*)(?:[-*+]|(\d+)[.)])\s+(.*)$")


def markdown_blocks(path: str, text: str, first_line: int = 1) -> list[Block]:
    """Split Markdown into paragraphs, list items, and table cells, with their line numbers."""
    blocks: list[Block] = []
    current: list[str] = []
    start = 0
    last = 0
    procedural = False
    paragraph = True
    fence = False
    comment = False
    header_row = True
    lines = text.split("\n")

    def flush() -> None:
        nonlocal current
        if current:
            blocks.append(Block(path, start, " ".join(current), procedural, paragraph, last))
        current = []

    index = 0
    if lines and lines[0].strip() == "---":
        for index in range(1, len(lines)):
            if lines[index].strip() == "---":
                index += 1
                break
        else:
            index = 0
    for offset in range(index, len(lines)):
        number = first_line + offset
        raw = lines[offset]
        stripped = raw.strip()
        if comment:
            if "-->" in stripped:
                comment = False
            continue
        if stripped.startswith("<!--"):
            flush()
            comment = "-->" not in stripped
            continue
        if stripped.startswith(("```", "~~~")):
            flush()
            fence = not fence
            continue
        if fence:
            continue
        stripped = re.sub(r"^(?:>\s?)+", "", stripped)
        if not stripped or stripped.startswith("#") or re.fullmatch(r"[-*_=]{3,}", stripped):
            flush()
            header_row = True
            continue
        if stripped.startswith("|"):
            flush()
            if re.fullmatch(r"\|[\s:|-]+\|?", stripped):
                continue
            if not header_row:
                for cell in stripped.strip("|").split("|"):
                    if cell.strip():
                        blocks.append(Block(path, number, cell.strip(), False, False, number))
            header_row = False
            continue
        header_row = True
        item = LIST_ITEM.match(raw)
        if item:
            flush()
            start = number
            procedural = item.group(2) is not None
            paragraph = False
            current.append(item.group(3))
            last = number
            continue
        if not current:
            start = number
            procedural = False
            paragraph = True
        current.append(stripped)
        last = number
    flush()
    return blocks


CHAR_LITERAL = re.compile(r"'(?:\\(?:u\{[0-9A-Fa-f]+\}|x[0-9A-Fa-f]{2}|.)|[^\\'\n])'")


def lean_blocks(path: str, text: str) -> list[Block]:
    """Return the prose blocks of the doc comments, block comments, and line comments."""
    blocks: list[Block] = []
    index = 0
    line = 1
    length = len(text)
    comment_lines: list[tuple[int, str]] = []

    def flush_line_comments() -> None:
        if comment_lines:
            first = comment_lines[0][0]
            body = "\n".join(content for _, content in comment_lines)
            blocks.extend(markdown_blocks(path, body, first))
            comment_lines.clear()

    while index < length:
        char = text[index]
        if char == "\n":
            line += 1
            index += 1
            continue
        literal = CHAR_LITERAL.match(text, index) if char == "'" else None
        if literal and not (index and (text[index - 1].isalnum() or text[index - 1] in "_'.")):
            # A character literal such as '"' does not start a string.
            index = literal.end()
            continue
        if char == '"':
            index += 1
            while index < length and text[index] != '"':
                if text[index] == "\\":
                    index += 1
                elif text[index] == "\n":
                    line += 1
                index += 1
            index += 1
            continue
        if text.startswith("/-", index):
            flush_line_comments()
            body_start = index + 2
            if text.startswith(("/--", "/-!"), index):
                body_start = index + 3
            depth = 1
            cursor = index + 2
            while cursor < length and depth:
                if text.startswith("/-", cursor):
                    depth += 1
                    cursor += 2
                elif text.startswith("-/", cursor):
                    depth -= 1
                    cursor += 2
                else:
                    cursor += 1
            body = text[body_start:cursor - 2]
            blocks.extend(markdown_blocks(path, body, line))
            line += text.count("\n", index, cursor)
            index = cursor
            continue
        if text.startswith("--", index):
            end = text.find("\n", index)
            end = length if end == -1 else end
            before = text[text.rfind("\n", 0, index) + 1:index]
            content = text[index + 2:end].strip()
            if before.strip():
                flush_line_comments()
                blocks.extend(markdown_blocks(path, content, line))
            else:
                if comment_lines and comment_lines[-1][0] != line - 1:
                    flush_line_comments()
                comment_lines.append((line, content))
            index = end
            continue
        if not char.isspace() and comment_lines and comment_lines[-1][0] != line:
            flush_line_comments()
        index += 1
    flush_line_comments()
    return blocks


def file_blocks(path: str, text: str) -> list[Block]:
    return lean_blocks(path, text) if path.endswith(".lean") else markdown_blocks(path, text)


# ---------------------------------------------------------------------------------------------
# Masking and sentences


def mask(text: str, collapse_parentheses: bool,
         parentheticals: list[str] | None = None) -> str:
    """Replace each exempt or one-word element with a placeholder word.

    When `collapse_parentheses` is true, each parenthesis becomes one word, and its text goes to
    `parentheticals`. An inner parenthesis is one word in the text of the outer one.
    """
    text = re.sub(r"<!--.*?-->", " ", text)
    text = re.sub(r"&[A-Za-z]+;|&#\d+;", " ", text)
    text = re.sub(r"\$\$.*?\$\$|\$[^$]+\$", " Formula ", text)
    text = re.sub(r"``.*?``|`[^`]*`", " Code ", text)
    text = re.sub(r"!?\[([^\]]*)\]\([^)]*\)", r"\1", text)
    text = re.sub(r"\[([^\]]+)\]\[[^\]]*\]", r"\1", text)
    text = re.sub(r"\[[A-Z][A-Za-z+-]*\d{2}[a-z]?(?:,[^\]]*)?\]", " Key ", text)
    text = re.sub(r"<https?://[^>]+>|https?://\S+", " Link ", text)
    text = re.sub(r"</?[A-Za-z][^>]*>", " ", text)
    text = re.sub(r'"[^"]*"|“[^”]*”', " Quote ", text)
    text = re.sub(r"\*\*|__|(?<!\w)[*_]|[*_](?!\w)", "", text)
    if collapse_parentheses:
        previous = None
        while previous != text:
            previous = text
            for inner in re.findall(r"\(([^()]*)\)", text):
                if parentheticals is not None:
                    parentheticals.append(re.sub(r"\s+", " ", inner).strip())
            text = re.sub(r"\([^()]*\)", " Paren ", text)
    return re.sub(r"\s+", " ", text).strip()


def sentences(text: str) -> list[str]:
    parts = re.split(r"(?<=[.!?])\s+(?=[A-Z0-9(\[])", text)
    merged: list[str] = []
    for part in parts:
        if merged and merged[-1].split()[-1].lower() in ABBREVIATIONS:
            merged[-1] = merged[-1] + " " + part
        else:
            merged.append(part)
    return [part for part in merged if part.strip()]


def word_count(sentence: str) -> int:
    return sum(1 for token in sentence.split() if re.search(r"[^\W_]", token))


# ---------------------------------------------------------------------------------------------
# Rules


def check_block(block: Block, general: re.Pattern[str] | None,
                history: re.Pattern[str] | None) -> list[Finding]:
    found: list[Finding] = []

    def add(rule: str, message: str, excerpt: str) -> None:
        found.append(Finding(block.path, block.line, rule, message, excerpt.strip()[:80]))

    parentheticals: list[str] = []
    counted = mask(block.text, collapse_parentheses=True, parentheticals=parentheticals)
    plain = mask(block.text, collapse_parentheses=False)
    limit = PROCEDURAL_LIMIT if block.procedural else DESCRIPTIVE_LIMIT
    counted_sentences = sentences(counted)
    # The text in parentheses counts as a separate sentence.
    for sentence in counted_sentences + [part for inner in parentheticals
                                         for part in sentences(inner)]:
        words = word_count(sentence)
        if words > limit:
            add("S1", f"The sentence has {words} words. The limit is {limit}.", sentence)
    if block.paragraph and len(counted_sentences) > PARAGRAPH_LIMIT:
        add("P2", f"The paragraph has {len(counted_sentences)} sentences. The limit is "
            f"{PARAGRAPH_LIMIT}.", counted_sentences[0])
    if ";" in plain:
        add("U1", "Do not use a semicolon. Write two sentences.", plain[plain.index(";") - 30:])
    for match in EM_DASH.finditer(plain):
        add("U2", "Do not join two clauses with a dash. Write two sentences.",
            plain[max(0, match.start() - 30):match.end() + 30])
    for pattern, rule, message in (
            (LATIN, "W7", "Write the English words for this Latin abbreviation."),
            (PHRASAL, "W6", "Use a single verb for this phrasal verb."),
            (CONTRACTION, "S5", "Write the full form of this contraction."),
            (general, "W1", "Use the replacement in writing-vocabulary.md for this word.")):
        if pattern is None:
            continue
        for match in pattern.finditer(plain):
            add(rule, message, match.group(0))
    for match in PERFECT.finditer(plain):
        hedged = MODAL_BEFORE.search(plain[:match.start()])
        if match.group(1).lower() not in POSSESSED_ADJECTIVES and not hedged:
            add("V1", "Use a simple tense, not the perfect form.", match.group(0))
    for match in PROGRESSIVE.finditer(plain):
        if match.group(1).lower() not in NOT_PROGRESSIVE:
            add("V1", "Use a simple tense, not the progressive form.", match.group(0))
    if history is not None and HISTORY_SCOPE.search(block.path):
        for match in history.finditer(plain):
            add("C3", "Describe the present state, not the history.", match.group(0))
    for sentence in sentences(plain):
        if BARE_THIS.match(sentence):
            add("S7", "Write the noun after \"This\" or \"These\".", sentence)
        if ING_START.match(sentence):
            add("V2", "Do not start a clause with an \"-ing\" form.", sentence)
    return found


def check_blocks(blocks: list[Block], vocabulary: Path = VOCABULARY) -> list[Finding]:
    general_words, history_words = avoid_words(vocabulary)
    general = word_pattern(general_words)
    history = word_pattern(history_words)
    found: list[Finding] = []
    for block in blocks:
        found.extend(check_block(block, general, history))
    return found


# ---------------------------------------------------------------------------------------------
# Changed lines


def git(*args: str) -> str:
    return subprocess.run(["git", *args], check=True, capture_output=True, text=True,
                          cwd=ROOT).stdout


def checked_path(path: str) -> bool:
    return (path.endswith((".md", ".lean")) and path not in EXCLUDED_FILES
            and not path.startswith(EXCLUDED_PREFIXES))


def added_lines(base: str) -> dict[str, set[int]]:
    """Map each changed tracked file to the line numbers that it adds since the merge base."""
    merge_base = git("merge-base", base, "HEAD").strip()
    diff = git("diff", "--unified=0", "--no-color", "--no-ext-diff", merge_base)
    result: dict[str, set[int]] = {}
    path = None
    for line in diff.splitlines():
        if line.startswith("+++ "):
            target = line[4:]
            path = target[2:] if target.startswith("b/") else None
            if path is not None and not checked_path(path):
                path = None
            continue
        hunk = re.match(r"@@ -\d+(?:,\d+)? \+(\d+)(?:,(\d+))? @@", line)
        if hunk and path is not None:
            first = int(hunk.group(1))
            count = int(hunk.group(2)) if hunk.group(2) is not None else 1
            result.setdefault(path, set()).update(range(first, first + count))
    return result


def changed_blocks(base: str) -> list[Block]:
    blocks: list[Block] = []
    for path, lines in sorted(added_lines(base).items()):
        text = (ROOT / path).read_text(encoding="utf-8")
        for block in file_blocks(path, text):
            if any(block.line <= number <= block.last_line for number in lines):
                blocks.append(block)
    return blocks


# ---------------------------------------------------------------------------------------------
# Output


def escape(message: str) -> str:
    return message.replace("%", "%25").replace("\r", "%0D").replace("\n", "%0A")


def report(found: list[Finding], github: bool, label_is_file: bool) -> None:
    for item in found:
        if github:
            location = f"file={item.path},line={item.line}," if label_is_file else ""
            print(f"::warning {location}title=Writing {item.rule}::"
                  f"{escape(item.message + ' ' + repr(item.excerpt))}")
        else:
            print(f"{item.path}:{item.line}: [{item.rule}] {item.message} {item.excerpt!r}")
    rules = sorted({item.rule for item in found})
    summary = (f"{len(found)} writing problem(s) for rules {', '.join(rules)}. Refer to "
               "docs/wiki/writing.md." if found else "No writing problems found.")
    print(summary)


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--base", help="check the prose that changed since the merge base")
    mode.add_argument("--stdin", metavar="LABEL", help="check Markdown from standard input")
    mode.add_argument("files", nargs="*", default=[], help="check all prose in these files")
    parser.add_argument("--github", action="store_true", help="print GitHub annotations")
    parser.add_argument("--strict", action="store_true", help="exit with 1 on a problem")
    parser.add_argument("--vocabulary", type=Path, default=VOCABULARY,
                        help="the vocabulary page (default: docs/wiki/writing-vocabulary.md)")
    args = parser.parse_args(argv[1:])
    label_is_file = True
    if args.base:
        blocks = changed_blocks(args.base)
    elif args.stdin:
        blocks = markdown_blocks(args.stdin, sys.stdin.read())
        label_is_file = False
    elif args.files:
        blocks = []
        for name in args.files:
            blocks.extend(file_blocks(name, Path(name).read_text(encoding="utf-8")))
    else:
        parser.error("give --base, --stdin, or at least one file")
    found = check_blocks(blocks, args.vocabulary)
    report(found, args.github, label_is_file)
    return 1 if found and args.strict else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
