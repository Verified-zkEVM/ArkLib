#!/usr/bin/env -S uv run --no-project --python 3.12 python
"""Report editing suggestions for selected rules of the ArkLib writing standard.

The standard is `docs/wiki/writing.md`. This script reports patterns that a search can find:

- S1: sentence length (20 words in a numbered list item, 25 words elsewhere)
- P2: more than six sentences in a paragraph
- U1: semicolons, and U2: em dashes that join clauses
- W6: phrasal verbs, and W7: Latin abbreviations
- S5: contractions
- V1: perfect and progressive verb forms, and V2: a clause that starts with an "-ing" form
- S7: a sentence that starts with "This" or "These" and a verb, with no noun
- Vocabulary: the words to avoid in `docs/wiki/writing-vocabulary.md`.

Review applies the standard to each finding and to rules that need judgment. Extraction, word
counts, and verb patterns are approximations. Numbered lists are treated as procedural for the
length check; their actual purpose still needs review. License text, quoted text, code, formulas,
headings, and HTML comments are excluded. No dictionary or meaning-preservation check is made.
The words "now" and "new" are not flagged alone, because both also have ordinary meanings.

Usage:
  check-writing.py --base REF      the prose that changed since the merge base with REF
  check-writing.py FILE...         all prose in each file
  check-writing.py --stdin LABEL   all prose in standard input, for example a pull request body

In `--base` mode, the checker reads the tracked files in the working tree. It checks each
paragraph, list item, or table cell that contains an added line. It ignores untracked files.

Options: `--github` prints GitHub annotations. `--strict` exits with 1 if it finds a problem.
Without `--strict`, findings exit with 0. Usage, Git and configuration errors exit with 2.
Non-UTF-8 source input and dangling symlinks produce advisory Input diagnostics.
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
    "|".join(rf"\b(?:{forms})\s+" + r"\s+".join(
        re.escape(word) for word in pair.split()[1:]) + r"\b"
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
                   "binding", "encoding", "decoding", "folding", "batching", "hashing",
                   "hiding", "increasing", "decreasing", "nondecreasing", "nonincreasing",
                   "vanishing", "accepting", "winning"}
NON_VERBAL_ING = NOT_PROGRESSIVE | {
    "hamming", "interleaving", "coupling", "tracing", "embedding", "unfolding",
    "rewriting", "normalizing", "lowering", "wrapping", "masking", "leading",
}
# These phrases are objects of possession, not perfect-tense actions.
POSSESSED_PHRASES = re.compile(
    r"(?:correlated\s+agreement|centered\s+norm|centred\s+norm|squared\s+norm|expected\s+value|"
    r"left(?:\s+and\s+right)?\s+children|right\s+children|known\s+degree)\b", re.IGNORECASE)
PROGRESSIVE = re.compile(r"\b(?:is|are|was|were|be|been)\s+(\w+ing)\b", re.IGNORECASE)
BARE_THIS = re.compile(
    r"^(?:This|These)\s+(?:is|are|was|were|means|makes|ensures|lets|gives|shows|allows|"
    r"requires|keeps|fixes|adds|avoids|matches|also|will|can)\b")
# "During" is a preposition, not an "-ing" form of a verb.
ING_START = re.compile(r"^(?!During\b)[A-Z][a-z]+ing\b[^,.;:]{0,80},")
EM_DASH = re.compile(r"—|\s–\s|\s--\s")
FORMATTED_TERM = r"(?:\[[^\]]+\]\((?:[^()]|\([^()]*\))*\)|``[^`]+``|`[^`]+`|\$[^$]+\$|\*\*[^*]+\*\*)"
DEFINITION_SEPARATOR = re.compile(
    rf"^\s*{FORMATTED_TERM}(?:\s*(?:,|and|or|/)\s*{FORMATTED_TERM})*"
    r"(?:\s*\((?:[^()]|\([^()]*\))*\))*\s*(?P<dash>—|–|--)\s+")
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
        pattern = re.escape(word).replace(r"\ ", r"\s+") + suffix
        if word.endswith("e") and not word.endswith("ee") and suffix:
            pattern = rf"(?:{pattern}|{re.escape(word[:-1])}ing)"
        return pattern

    alternatives = sorted((alternative(word) for word in words), key=len, reverse=True)
    return re.compile(r"(?<![\w.])(?:" + "|".join(alternatives) + r")(?![\w])", re.IGNORECASE)


# ---------------------------------------------------------------------------------------------
# Extraction of prose blocks

CODE_SPAN = re.compile(r"(?<!`)(`+)(?!`)(.*?)(?<!`)\1(?!`)", re.DOTALL)

LIST_ITEM = re.compile(r"^(\s*)(?:[-*+]|(\d+)[.)])\s+(.*)$")


def strip_html_comments(text: str, inside: bool, visible: str) -> tuple[str, bool]:
    """Remove HTML comments on one line, retaining code spans and character positions."""
    result = list(text)
    index = 0
    while index < len(text):
        if inside:
            end = text.find("-->", index)
            stop = len(text) if end < 0 else end + 3
            result[index:stop] = blank(text[index:stop])
            inside = end < 0
            index = stop
        elif visible.startswith("<!--", index):
            before = visible[:index]
            escaped = (len(before) - len(before.rstrip("\\"))) % 2
            if escaped:
                index += 1
            else:
                inside = True
        else:
            index += 1
    return "".join(result), inside


def markdown_blocks(path: str, text: str, first_line: int = 1) -> list[Block]:
    """Split Markdown into paragraphs, list items, and table cells, with their line numbers."""
    blocks: list[Block] = []
    current: list[str] = []
    start = 0
    last = 0
    procedural = False
    paragraph = True
    fence: tuple[str, int] | None = None
    header_row = True
    legal_section: int | None = None
    comment = False
    list_context = False
    lines = text.split("\n")
    visible_lines = CODE_SPAN.sub(lambda m: blank(m.group(), True), text).split("\n")

    def flush() -> None:
        nonlocal current
        if current:
            blocks.append(Block(path, start, "\n".join(current), procedural, paragraph, last))
        current = []

    index = 0
    if lines and lines[0].strip() == "---":
        for index in range(1, len(lines)):
            if lines[index].strip() == "---":
                if any(re.match(r"[A-Za-z_][\w-]*:", line) for line in lines[1:index]):
                    index += 1
                else:
                    index = 0  # Two thematic breaks do not imply YAML front matter.
                break
        else:
            index = 0
    for offset in range(index, len(lines)):
        number = first_line + offset
        raw = lines[offset]
        stripped = raw.strip()
        if fence is not None:
            character, width = fence
            if re.fullmatch(re.escape(character) + "{" + str(width) + r",}\s*", stripped):
                fence = None
            continue
        opening = re.match(r"(`{3,}|~{3,})", stripped) if not comment else None
        if opening:
            flush()
            fence = (opening.group()[0], len(opening.group()))
            continue
        if raw.startswith(("    ", "\t")) and not current and not comment and not list_context:
            continue
        raw, comment = strip_html_comments(raw, comment, visible_lines[offset])
        stripped = raw.strip()
        stripped = re.sub(r"^(?:>\s?)+", "", stripped)
        heading = re.fullmatch(r"(#{1,6})\s+(.+?)(?:\s+#+)?", stripped)
        if heading:
            flush()
            level = len(heading.group(1))
            if legal_section is not None and level <= legal_section:
                legal_section = None
            if legal_section is None and heading.group(2).casefold() in {
                    "license", "licence", "licensing"}:
                legal_section = level
            header_row = True
            continue
        if legal_section is not None:
            continue
        if not stripped or re.fullmatch(r"[-*_=]{3,}", stripped):
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
            list_context = True
            start = number
            procedural = item.group(2) is not None
            paragraph = False
            current.append(item.group(3))
            last = number
            continue
        if raw and not raw[0].isspace():
            list_context = False
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
        raw_string = re.match(r'r(#+)?"', text[index:]) if char == "r" else None
        if raw_string and not (index and (text[index - 1].isalnum() or text[index - 1] in "_'.")):
            terminator = '"' + (raw_string.group(1) or "")
            end = text.find(terminator, index + raw_string.end())
            end = length if end == -1 else end + len(terminator)
            line += text.count("\n", index, end)
            index = end
            continue
        if char == '"':
            index += 1
            while index < length and text[index] != '"':
                if text[index] == "\\":
                    if index + 1 < length and text[index + 1] == "\n":
                        line += 1
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
            body = text[body_start:cursor - 2 if depth == 0 else cursor]
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
    if Path(path).name.casefold() in {"license.md", "licence.md", "copying.md"}:
        return []
    return lean_blocks(path, text) if path.endswith(".lean") else markdown_blocks(path, text)


# ---------------------------------------------------------------------------------------------
# Masking and sentences


def blank(text: str, token: bool = False) -> str:
    """Hide content without changing its length or newline positions."""
    result = re.sub(r"[^\r\n]", " ", text)
    if token:
        positions = [i for i, char in enumerate(result) if char == " "]
        if positions:
            index = positions[min(1, len(positions) - 1)]
            result = result[:index] + "X" + result[index + 1:]
    return result


def mask(text: str, collapse_parentheses: bool,
         parentheticals: list[str] | None = None,
         parenthetical_offsets: list[int] | None = None) -> str:
    """Mask exempt elements with one word, preserving source offsets and newlines."""
    text = CODE_SPAN.sub(lambda m: blank(m.group(), True), text)
    for pattern, token in (
            (r"\$\$.*?\$\$|\$[^$]+\$", True),
            (r"&[A-Za-z]+;|&#\d+;", False)):
        text = re.sub(pattern, lambda m: blank(m.group(), token), text, flags=re.DOTALL)
    def link(match: re.Match[str]) -> str:
        start, end = match.span(1)
        return (blank(match.group()[:start - match.start()]) + match.group(1)
                + blank(match.group()[end - match.start():]))
    text = re.sub(r"!?\[([^\]]*)\]\((?:[^()]|\([^()]*\))*\)", link, text)
    text = re.sub(r"\[([^\]]+)\]\[[^\]]*\]", link, text)
    for pattern, token in (
            (r"\[[A-Z][A-Za-z+-]*\d{2}[a-z]?(?:,[^\]]*)?\]", True),
            (r"<https?://[^>]+>|https?://\S+", True),
            (r"</?[A-Za-z][^>]*>", False),
            (r'"[^"]*"|“[^”]*”', True),
            (r"\*\*|__|(?<!\w)[*_]|[*_](?!\w)", False)):
        text = re.sub(pattern, lambda m: blank(m.group(), token), text)
    if collapse_parentheses:
        while re.search(r"\([^()]*\)", text):
            def parenthesis(match: re.Match[str]) -> str:
                if parentheticals is not None:
                    parentheticals.append(match.group()[1:-1])
                if parenthetical_offsets is not None:
                    parenthetical_offsets.append(match.start() + 1)
                return blank(match.group(), True)
            text = re.sub(r"\([^()]*\)", parenthesis, text)
    return text


def sentence_spans(text: str) -> list[tuple[int, int]]:
    """Return sentence spans in the supplied text without losing source offsets."""
    spans: list[tuple[int, int]] = []
    start = 0
    boundaries = list(re.finditer(
        r"(?<=[.!?])\s+(?=[A-Z0-9(\[]|[a-z][\w-]*\.[\w-]+(?:\s|$))", text))
    for boundary in boundaries:
        part = text[start:boundary.start()]
        if part.split() and part.split()[-1].lower() in ABBREVIATIONS:
            continue
        spans.append((start, boundary.start()))
        start = boundary.end()
    spans.append((start, len(text)))
    return [(a + len(text[a:b]) - len(text[a:b].lstrip()),
             b - len(text[a:b]) + len(text[a:b].rstrip()))
            for a, b in spans if text[a:b].strip()]


def sentences(text: str) -> list[str]:
    return [text[a:b] for a, b in sentence_spans(text)]


def word_count(sentence: str) -> int:
    return sum(1 for token in sentence.split() if re.search(r"[^\W_]", token))


# ---------------------------------------------------------------------------------------------
# Rules


def check_block(block: Block, general: re.Pattern[str] | None,
                history: re.Pattern[str] | None) -> list[Finding]:
    found: list[Finding] = []

    def add(rule: str, message: str, offset: int, end: int | None = None,
            context: int = 0) -> None:
        excerpt = re.sub(r"\s+", " ", block.text[max(0, offset - context):end]).strip()[:80]
        line = block.line + block.text.count("\n", 0, offset)
        found.append(Finding(block.path, line, rule, message, excerpt))

    parentheticals: list[str] = []
    parenthetical_offsets: list[int] = []
    counted = mask(block.text, True, parentheticals, parenthetical_offsets)
    plain = mask(block.text, False)
    limit = PROCEDURAL_LIMIT if block.procedural else DESCRIPTIVE_LIMIT
    counted_spans = sentence_spans(counted)
    sentence_parts = [(counted, 0, counted_spans)] + [
        (inner, offset, sentence_spans(inner))
        for inner, offset in zip(parentheticals, parenthetical_offsets)]
    for text, offset, spans in sentence_parts:
        for start, end in spans:
            words = word_count(text[start:end])
            if words > limit:
                add("S1", f"The sentence has {words} words. The limit is {limit}.",
                    offset + start, offset + end)
    if block.paragraph and len(counted_spans) > PARAGRAPH_LIMIT:
        add("P2", f"The paragraph has {len(counted_spans)} sentences. The limit is "
            f"{PARAGRAPH_LIMIT}.", counted_spans[PARAGRAPH_LIMIT][0])
    if ";" in plain:
        add("U1", "Do not use a semicolon. Use a conjunction or write two sentences.",
            plain.index(";"), context=30)
    definition = DEFINITION_SEPARATOR.match(block.text)
    dash_plain = plain
    if definition:
        start, end = definition.span("dash")
        dash_plain = plain[:start] + blank(plain[start:end]) + plain[end:]
    if dash_plain.strip() not in {"—", "–", "--"}:
        for match in EM_DASH.finditer(dash_plain):
            offset = match.start() + len(match.group()) - len(match.group().lstrip())
            add("U2", "Review this dash. If it joins clauses, write two sentences.",
                offset, match.end() + 30, context=30)
    for pattern, rule, message in (
            (LATIN, "W7", "Write the English words for this Latin abbreviation."),
            (PHRASAL, "W6", "Consider a direct verb that preserves this meaning."),
            (CONTRACTION, "S5", "Write the full form of this contraction."),
            (general, "W1", "Review this wording using writing-vocabulary.md. Preserve its meaning.")):
        if pattern is None:
            continue
        for match in pattern.finditer(plain):
            if rule == "W1" and LATIN.fullmatch(match.group()):
                continue
            add(rule, message, match.start(), match.end())
    for match in PERFECT.finditer(plain):
        hedged = MODAL_BEFORE.search(plain[:match.start()])
        possession = POSSESSED_PHRASES.match(plain, match.start(1))
        if match.group(1).lower() not in POSSESSED_ADJECTIVES and not hedged and not possession:
            add("V1", "Prefer a simple tense if it preserves time and uncertainty.",
                match.start(), match.end())
    for match in PROGRESSIVE.finditer(plain):
        if match.group(1).lower() not in NOT_PROGRESSIVE:
            add("V1", "Review this possible progressive form. Prefer a simple construction.",
                match.start(), match.end())
    if history is not None and HISTORY_SCOPE.search(block.path):
        for match in history.finditer(plain):
            add("C3", "Describe the present state, not the history.", match.start(), match.end())
    for start, end in sentence_spans(plain):
        sentence = plain[start:end]
        if BARE_THIS.match(sentence):
            add("S7", "Name the noun if this reference is ambiguous.", start, end)
        if ING_START.match(sentence) and re.match(r"\w+", sentence).group().lower() not in NON_VERBAL_ING:
            add("V2", "Review this possible verb clause. A finite clause can be clearer.", start, end)
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
                          cwd=ROOT, encoding="utf-8", errors="surrogateescape").stdout


def checked_path(path: str) -> bool:
    return (path.endswith((".md", ".lean")) and path not in EXCLUDED_FILES
            and not path.startswith(EXCLUDED_PREFIXES))


def added_lines(base: str) -> dict[str, set[int]]:
    """Map each changed tracked file to the line numbers that it adds since the merge base."""
    merge_base = git("merge-base", base, "HEAD").strip()
    # NUL-delimited names do not depend on quoting or patch-header prefixes.
    # Keep both sides of a rename so unchanged prose is not treated as an addition.
    options = ("--no-ext-diff", "--no-textconv", "--find-renames")
    names = iter(git("diff", *options, "--name-status", "-z", "--diff-filter=ACMRT",
                     merge_base, "--").split("\0"))
    result: dict[str, set[int]] = {}
    for status in names:
        if not status:
            continue
        source = next(names)
        path = next(names) if status[0] in "RC" else source
        if not checked_path(path):
            continue
        paths = (source, path) if status[0] in "RC" else (path,)
        diff = git("--literal-pathspecs", "diff", *options, "--text", "--unified=0", "--no-color",
                   merge_base, "--", *paths)
        lines = result.setdefault(path, set())
        for hunk in re.finditer(r"^@@ -\d+(?:,\d+)? \+(\d+)(?:,(\d+))? @@", diff, re.MULTILINE):
            first = int(hunk.group(1))
            count = int(hunk.group(2)) if hunk.group(2) is not None else 1
            lines.update(range(first, first + count))
    return result


def read_source(path: Path, label: str, diagnostics: list[Finding]) -> str | None:
    """Report unsupported source input as advisory data, retaining other file checks."""
    try:
        return path.read_text(encoding="utf-8")
    except UnicodeDecodeError as error:
        line = error.object.count(b"\n", 0, error.start) + 1
        diagnostics.append(Finding(label, line, "Input", "This file is not UTF-8. Prose was not checked.", ""))
    except FileNotFoundError:
        if not path.is_symlink():
            raise
        diagnostics.append(Finding(label, 1, "Input", "This symlink has no target. Prose was not checked.", ""))
    return None


def changed_blocks(base: str, diagnostics: list[Finding] | None = None) -> list[Block]:
    blocks: list[Block] = []
    diagnostics = [] if diagnostics is None else diagnostics
    for path, lines in sorted(added_lines(base).items()):
        text = read_source(ROOT / path, path, diagnostics)
        if text is None:
            continue
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
            location = (f"file={escape(item.path).replace(':', '%3A').replace(',', '%2C')},"
                        f"line={item.line}," if label_is_file else "")
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
    diagnostics: list[Finding] = []
    try:
        if args.base:
            blocks = changed_blocks(args.base, diagnostics)
        elif args.stdin is not None:
            try:
                text = sys.stdin.read()
            except UnicodeDecodeError:
                diagnostics.append(Finding(args.stdin, 1, "Input", "Input is not UTF-8. Prose was not checked.", ""))
                text = ""
            if any(0xDC80 <= ord(char) <= 0xDCFF for char in text):
                diagnostics.append(Finding(args.stdin, 1, "Input", "Input is not UTF-8. Prose was not checked.", ""))
                text = ""
            blocks = markdown_blocks(args.stdin, text)
            label_is_file = False
        elif args.files:
            blocks = []
            for name in args.files:
                text = read_source(Path(name), name, diagnostics)
                if text is not None:
                    blocks.extend(file_blocks(name, text))
        else:
            parser.error("give --base, --stdin, or at least one file")
        found = diagnostics + check_blocks(blocks, args.vocabulary)
    except subprocess.CalledProcessError as error:
        parser.error(f"git failed: {error.stderr.strip()}")
    except (OSError, ValueError) as error:
        parser.error(str(error))
    report(found, args.github, label_is_file)
    return 1 if found and args.strict else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
