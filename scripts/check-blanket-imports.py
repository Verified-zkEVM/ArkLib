#!/usr/bin/env python3

"""Reject exact package-root modules in Lean import headers.

This is a small header lexer, not a line-oriented regular expression. It ignores nested block
comments, line comments, quoted strings, and raw strings, then parses the initial Lean module
header across arbitrary whitespace. Import modifiers and `all` are tokenized independently.
"""

from __future__ import annotations

import dataclasses
import pathlib
import sys


FORBIDDEN = {"ArkLib", "Mathlib", "VCVio", "CompPoly", "PolyFun", "Batteries"}


@dataclasses.dataclass(frozen=True)
class Token:
    value: str
    line: int


class LexError(Exception):
    pass


def lex(source: str) -> list[Token]:
    tokens: list[Token] = []
    index = 0
    line = 1
    length = len(source)

    def advance(count: int = 1) -> None:
        nonlocal index, line
        end = index + count
        line += source.count("\n", index, end)
        index = end

    while index < length:
        char = source[index]
        if char.isspace():
            advance()
            continue
        if source.startswith("--", index):
            newline = source.find("\n", index + 2)
            advance(length - index if newline < 0 else newline - index)
            continue
        if source.startswith("/-", index):
            start_line = line
            depth = 0
            while index < length:
                if source.startswith("/-", index):
                    depth += 1
                    advance(2)
                elif source.startswith("-/", index):
                    depth -= 1
                    advance(2)
                    if depth == 0:
                        break
                else:
                    advance()
            if depth != 0:
                raise LexError(f"unterminated block comment starting on line {start_line}")
            continue

        # Lean raw strings: r"...", r#"..."#, r##"..."##, and so on.
        if char == "r":
            cursor = index + 1
            while cursor < length and source[cursor] == "#":
                cursor += 1
            if cursor < length and source[cursor] == '"':
                hashes = source[index + 1 : cursor]
                closing = '"' + hashes
                end = source.find(closing, cursor + 1)
                if end < 0:
                    raise LexError(f"unterminated raw string starting on line {line}")
                advance(end + len(closing) - index)
                continue

        if char == '"':
            quote = char
            start_line = line
            advance()
            escaped = False
            while index < length:
                char = source[index]
                advance()
                if escaped:
                    escaped = False
                elif char == "\\":
                    escaped = True
                elif char == quote:
                    break
            else:
                raise LexError(f"unterminated quoted literal starting on line {start_line}")
            continue

        token_line = line
        if char == "«" or char == "_" or char.isalpha():
            start = index
            while True:
                if source[index] == "«":
                    end = source.find("»", index + 1)
                    if end < 0:
                        raise LexError(f"unterminated escaped identifier starting on line {line}")
                    advance(end + 1 - index)
                else:
                    while index < length:
                        char = source[index]
                        if char in {"_", "'"} or char.isalnum() or char.isalpha():
                            advance()
                        else:
                            break
                if index + 1 < length and source[index] == "." and (
                    source[index + 1] == "«"
                    or source[index + 1] == "_"
                    or source[index + 1].isalpha()
                ):
                    advance()
                    continue
                break
            value = source[start:index]
        else:
            value = char
            advance()
        tokens.append(Token(value, token_line))

    return tokens


def root_imports(tokens: list[Token]) -> list[Token]:
    """Return forbidden module-name tokens from the initial Lean import header."""

    found: list[Token] = []
    pos = 0
    if pos < len(tokens) and tokens[pos].value == "module":
        pos += 1
    if pos < len(tokens) and tokens[pos].value == "prelude":
        pos += 1

    while pos < len(tokens):
        if tokens[pos].value in {"public", "private"}:
            pos += 1
        if pos < len(tokens) and tokens[pos].value == "meta":
            pos += 1
        if pos >= len(tokens) or tokens[pos].value != "import":
            break
        pos += 1
        if pos < len(tokens) and tokens[pos].value == "all":
            pos += 1
        if pos >= len(tokens):
            break

        module = tokens[pos]
        pos += 1
        module_name = module.value
        if module_name.startswith("«") and module_name.endswith("»"):
            module_name = module_name[1:-1]
        if module_name in FORBIDDEN:
            found.append(module)

        # Lean 4.33 accepts one module per import command. Conservatively reject additional exact
        # roots on the same line too, so a future multi-module grammar cannot bypass this gate.
        while pos < len(tokens) and tokens[pos].line == module.line:
            if tokens[pos].value in FORBIDDEN:
                found.append(tokens[pos])
            pos += 1

    return found


def scan(path: pathlib.Path) -> list[str]:
    source = path.read_text(encoding="utf-8")
    lines = source.splitlines()
    violations = []
    try:
        tokens = lex(source)
    except LexError as error:
        raise LexError(f"{path}: {error}") from error
    for token in root_imports(tokens):
        text = lines[token.line - 1] if token.line <= len(lines) else ""
        violations.append(f"{path}:{token.line}:{text}")
    return violations


def main(argv: list[str]) -> int:
    violations: list[str] = []
    try:
        for argument in argv:
            violations.extend(scan(pathlib.Path(argument)))
    except (OSError, UnicodeError, LexError) as error:
        print(f"check-blanket-imports: {error}", file=sys.stderr)
        return 2
    if violations:
        print("\n".join(violations))
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
