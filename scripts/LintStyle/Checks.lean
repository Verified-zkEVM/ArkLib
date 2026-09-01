/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Lean.Elab.ParseImportsFast

/-!
# ArkLib source-style checks

This module contains the pure part of ArkLib's text-based source linter. The policy is deliberately
fail-closed and has no exception mechanism: a violation must be fixed in source.

Unicode mathematical notation is unrestricted. Common mathematical variation selectors U+FE00–
U+FE0F and U+E0100–U+E01EF remain valid; we reject ASCII/C1 controls, Unicode format controls,
bidirectional, joining, annotation/tag, blank filler, Mongolian free variation-selector, and
nonstandard spacing characters that can make reviewed source differ from what it appears to say.
-/

open Lean System

namespace ArkLib.LintStyle

/-- A source-policy violation. Line numbers are one-based. -/
structure Violation where
  code : String
  line : Nat
  message : String
deriving BEq, Repr

private def violation (code : String) (line : Nat) (message : String) : Violation :=
  { code, line, message }

private inductive ScanMode where
  | code
  | blockComment (depth : Nat)
  | quoted (escaped : Bool)
  | raw (hashes : Nat)
  | quotedIdent
deriving BEq, Repr

private def spaces (n : Nat) : List Char := List.replicate n ' '

private def countHashes : List Char → Nat × List Char
  | '#' :: rest =>
      let (n, tail) := countHashes rest
      (n + 1, tail)
  | rest => (0, rest)

private def dropHashes : Nat → List Char → Option (List Char)
  | 0, rest => some rest
  | n + 1, '#' :: rest => dropHashes n rest
  | _, _ => none

/-- Find the closing quote of an escaped character token and return its width and remaining input. -/
private def escapedCharLiteralEnd? : List Char → Option (Nat × List Char)
  | '\'' :: '\'' :: rest => some (2, rest)
  | '\'' :: rest => some (1, rest)
  | _ :: rest => (escapedCharLiteralEnd? rest).map fun (width, tail) => (width + 1, tail)
  | [] => none

/-- Replace comments and literals with spaces, preserving line structure.

When `preserveModuleDocs` is true, a module-doc opener encountered in top-level code is retained so
the header check can distinguish it from the same text nested inside an ordinary comment.
-/
private partial def sanitizeChars (chars : List Char) (mode : ScanMode)
    (preserveModuleDocs : Bool) : List Char × ScanMode :=
  match chars, mode with
  | [], mode => ([], mode)
  | '-' :: '-' :: rest, .code => (spaces rest.length, .code)
  | '/' :: '-' :: '!' :: rest, .code =>
      let (tail, mode) := sanitizeChars rest (.blockComment 1) preserveModuleDocs
      ((if preserveModuleDocs then "/-!".toList else spaces 3) ++ tail, mode)
  | '/' :: '-' :: rest, .code =>
      let (tail, mode) := sanitizeChars rest (.blockComment 1) preserveModuleDocs
      (' ' :: ' ' :: tail, mode)
  | '\'' :: '\\' :: rest, .code =>
      match escapedCharLiteralEnd? rest with
      | some (width, tail) =>
          let (out, mode) := sanitizeChars tail .code preserveModuleDocs
          (spaces (width + 2) ++ out, mode)
      | none =>
          let (out, mode) := sanitizeChars rest .code preserveModuleDocs
          ('\'' :: '\\' :: out, mode)
  | '\'' :: _ :: '\'' :: rest, .code =>
      let (out, mode) := sanitizeChars rest .code preserveModuleDocs
      (spaces 3 ++ out, mode)
  | '«' :: rest, .code =>
      let (out, mode) := sanitizeChars rest .quotedIdent preserveModuleDocs
      ('x' :: out, mode)
  | 'r' :: rest, .code =>
      let (hashes, afterHashes) := countHashes rest
      match afterHashes with
      | '"' :: tail =>
          let (out, mode) := sanitizeChars tail (.raw hashes) preserveModuleDocs
          (spaces (hashes + 2) ++ out, mode)
      | _ =>
          let (out, mode) := sanitizeChars rest .code preserveModuleDocs
          ('r' :: out, mode)
  | '"' :: rest, .code =>
      let (out, mode) := sanitizeChars rest (.quoted false) preserveModuleDocs
      (' ' :: out, mode)
  | c :: rest, .code =>
      let (out, mode) := sanitizeChars rest .code preserveModuleDocs
      (c :: out, mode)
  | '/' :: '-' :: rest, .blockComment depth =>
      let (out, mode) := sanitizeChars rest (.blockComment (depth + 1)) preserveModuleDocs
      (' ' :: ' ' :: out, mode)
  | '-' :: '/' :: rest, .blockComment 1 =>
      let (out, mode) := sanitizeChars rest .code preserveModuleDocs
      (' ' :: ' ' :: out, mode)
  | '-' :: '/' :: rest, .blockComment (depth + 2) =>
      let (out, mode) := sanitizeChars rest (.blockComment (depth + 1)) preserveModuleDocs
      (' ' :: ' ' :: out, mode)
  | _ :: rest, .blockComment depth =>
      let (out, mode) := sanitizeChars rest (.blockComment depth) preserveModuleDocs
      (' ' :: out, mode)
  | '\\' :: rest, .quoted false =>
      let (out, mode) := sanitizeChars rest (.quoted true) preserveModuleDocs
      (' ' :: out, mode)
  | _ :: rest, .quoted true =>
      let (out, mode) := sanitizeChars rest (.quoted false) preserveModuleDocs
      (' ' :: out, mode)
  | '"' :: rest, .quoted false =>
      let (out, mode) := sanitizeChars rest .code preserveModuleDocs
      (' ' :: out, mode)
  | _ :: rest, .quoted false =>
      let (out, mode) := sanitizeChars rest (.quoted false) preserveModuleDocs
      (' ' :: out, mode)
  | '"' :: rest, .raw hashes =>
      match dropHashes hashes rest with
      | some tail =>
          let (out, mode) := sanitizeChars tail .code preserveModuleDocs
          (spaces (hashes + 1) ++ out, mode)
      | none =>
          let (out, mode) := sanitizeChars rest (.raw hashes) preserveModuleDocs
          (' ' :: out, mode)
  | _ :: rest, .raw hashes =>
      let (out, mode) := sanitizeChars rest (.raw hashes) preserveModuleDocs
      (' ' :: out, mode)
  | '»' :: rest, .quotedIdent =>
      let (out, mode) := sanitizeChars rest .code preserveModuleDocs
      (' ' :: out, mode)
  | _ :: rest, .quotedIdent =>
      let (out, mode) := sanitizeChars rest .quotedIdent preserveModuleDocs
      (' ' :: out, mode)

private def sanitizeLinesWith (lines : Array String) (preserveModuleDocs : Bool) :
    Array String := Id.run do
  let mut mode := ScanMode.code
  let mut result := #[]
  for line in lines do
    let (chars, next) := sanitizeChars line.toList mode preserveModuleDocs
    result := result.push (String.ofList chars)
    mode := next
  return result

private def sanitizeLines (lines : Array String) : Array String :=
  sanitizeLinesWith lines false

private def leadingSpaces (s : String) : Nat :=
  (s.toList.takeWhile (· == ' ')).length

private def startsDeclaration (line : String) : Bool :=
  let line := line.trimAsciiStart.toString
  let line := if line.startsWith "protected " then (line.drop 10).toString else line
  (line.startsWith "def " || line.startsWith "lemma " || line.startsWith "theorem ") &&
    !line.contains ":="

private def moduleHeaderWords (codeLines : Array String) : List String :=
  ("\n".intercalate codeLines.toList).split Char.isWhitespace |>.map (·.toString) |>.toList |>
    List.filter (!·.isEmpty)

private def isModuleHeader (codeLines : Array String) (requireImport : Bool) : Bool := Id.run do
  let mut words := moduleHeaderWords codeLines
  if words.head? == some "module" then words := words.tail
  if words.head? == some "prelude" then words := words.tail
  let mut imports := 0
  for _ in [:words.length] do
    if words.isEmpty then break
    if words.head? == some "public" || words.head? == some "private" then words := words.tail
    if words.head? == some "meta" then words := words.tail
    if words.head? != some "import" then return false
    words := words.tail
    if words.head? == some "all" then words := words.tail
    if words.isEmpty then return false
    words := words.tail
    imports := imports + 1
  return words.isEmpty && (!requireImport || imports > 0)

private def isImportsOnly (codeLines : Array String) : Bool :=
  isModuleHeader codeLines true

private def isFlexibleFollowup (line : String) : Bool :=
  ["rfl", "ring", "aesop", "norm_num", "positivity", "abel", "omega", "linarith", "nlinarith"].any
    fun tactic => line.contains tactic

/-- True precisely for Unicode code points prohibited for source-review safety.

This is a denylist, not a notation allowlist. Letters with diacritics, combining mathematical
marks, arrows, relations, and project-defined notation remain valid.
-/
def isHazardousUnicode (c : Char) : Bool :=
  let n := c.toNat
  (n < 0x20 && n != 0x0a) ||
    (0x7f ≤ n && n ≤ 0x9f) ||
    n == 0x00a0 || n == 0x00ad || n == 0x034f || (0x0600 ≤ n && n ≤ 0x0605) ||
    n == 0x061c || n == 0x06dd || n == 0x070f || (0x0890 ≤ n && n ≤ 0x0891) ||
    n == 0x08e2 || n == 0x115f || n == 0x1160 || n == 0x1680 ||
    (0x17b4 ≤ n && n ≤ 0x17b5) ||
    (0x180b ≤ n && n ≤ 0x180f) ||
    (0x2000 ≤ n && n ≤ 0x200f) ||
    (0x2028 ≤ n && n ≤ 0x202f) ||
    (0x205f ≤ n && n ≤ 0x206f) ||
    n == 0x2800 || n == 0x3000 || n == 0x3164 || n == 0xfeff || n == 0xffa0 ||
    (0xfff9 ≤ n && n ≤ 0xfffb) || n == 0x110bd || n == 0x110cd ||
    (0x13430 ≤ n && n ≤ 0x1343f) || (0x1bca0 ≤ n && n ≤ 0x1bca3) ||
    (0x1d173 ≤ n && n ≤ 0x1d17a) || n == 0xe0001 || (0xe0020 ≤ n && n ≤ 0xe007f)

private def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('A'.toNat + n - 10)

private def hex (n : Nat) : String :=
  let rec go (n : Nat) : Nat → List Char → List Char
    | 0, acc => acc
    | digits + 1, acc => go (n / 16) digits (hexDigit (n % 16) :: acc)
  "U+" ++ String.ofList (go n (if n ≤ 0xffff then 4 else 6) [])

private def unicodeViolations (lines : Array String) : Array Violation := Id.run do
  let mut result := #[]
  for h : i in [:lines.size] do
    for c in lines[i].toList do
      if isHazardousUnicode c then
        result := result.push <| violation "ERR_UNSAFE_UNICODE" (i + 1)
          s!"Hazardous invisible, control, bidi, or nonstandard-space character {hex c.toNat}"
  return result

private def headerViolations (lines codeLines : Array String) : Array Violation := Id.run do
  if isImportsOnly codeLines then return #[]
  let moduleDocLines := sanitizeLinesWith lines true
  let mut result := #[]
  if lines.isEmpty || lines[0]! != "/-" then
    result := result.push <| violation "ERR_COP" 1 "Malformed or missing copyright header"
    return result
  let mut headerEnd? : Option Nat := none
  for h : i in [:lines.size] do
    if headerEnd?.isNone && lines[i] == "-/" then headerEnd? := some i
  let headerEnd ← match headerEnd? with
    | some headerEnd => pure headerEnd
    | none => return result.push <|
        violation "ERR_COP" 1 "Malformed or missing copyright header"
  let header := "\n".intercalate (lines.toList.take (headerEnd + 1))
  if !header.contains "Copyright" || !header.contains "Apache" || !header.contains "Authors: " then
    result := result.push <| violation "ERR_COP" 1 "Malformed or missing copyright header"
  for h : i in [:headerEnd + 1] do
    let line := lines[i]!
    if line.contains "Author" &&
        (!line.startsWith "Authors: " || line.contains "  " || line.contains " and " ||
          line.endsWith ".") then
      result := result.push <| violation "ERR_AUT" (i + 1)
        "Authors line should use `Authors: Name, Name` without a final period"
  let mut foundDoc := false
  let mut badLine := headerEnd + 2
  for h : i in [headerEnd + 1:lines.size] do
    if !foundDoc then
      let moduleDocLine := moduleDocLines[i]!.trimAscii.toString
      if moduleDocLine.startsWith "/-!" then
        let headerPrefix := (codeLines.toList.take i).drop (headerEnd + 1) |>.toArray
        if isModuleHeader headerPrefix false then foundDoc := true else badLine := i + 1; break
  if !foundDoc then
    result := result.push <| violation "ERR_MOD" badLine "Module docstring missing, or too late"
  return result

private def lineViolations (lines codeLines : Array String) : Array Violation := Id.run do
  let mut result := #[]
  for h : i in [:lines.size] do
    let line := lines[i]
    let code := codeLines[i]!
    let trimmed := code.trimAscii.toString
    if line.length > 100 && !line.contains "http" && !line.contains "#align" then
      result := result.push <| violation "ERR_LIN" (i + 1) "Line has more than 100 characters"
    if line.endsWith " " || line.endsWith "\t" then
      result := result.push <| violation "ERR_TWS" (i + 1) "Trailing whitespace detected"
    if line.contains " ;" then
      result := result.push <| violation "ERR_SEM" (i + 1) "Space before a semicolon"
    if trimmed == "by" && i > 0 then
      let previous := lines[i - 1]!.trimAsciiEnd.toString
      if !previous.endsWith "," && !previous.endsWith "=>" && !previous.endsWith "↦" then
        result := result.push <| violation "ERR_IBY" (i + 1) "Line is an isolated `by`"
    let originalTrimmed := line.trimAscii.toString
    if originalTrimmed == "." || originalTrimmed == "·" ||
        line.trimAsciiStart.toString.startsWith ". " then
      result := result.push <| violation "ERR_DOT" (i + 1)
        "Isolated focusing dot, or `.` used instead of `·`"
    if code.trimAsciiStart.toString.startsWith ":" then
      result := result.push <| violation "ERR_CLN" (i + 1)
        "Put `:` and `:=` before line breaks, not after"
    if line.contains "daptation note" && !line.contains "#adaptation_note" &&
        !line.contains "see adaptation note" then
      result := result.push <| violation "ERR_ADN" (i + 1)
        "Use the `#adaptation_note` command instead of a handwritten adaptation note"
    if i + 1 < lines.size && startsDeclaration code then
      let next := lines[i + 1]!
      let nextCode := codeLines[i + 1]!
      let nextTrimmed := nextCode.trimAsciiStart.toString
      if !nextTrimmed.isEmpty && !nextTrimmed.startsWith "#" then
        let expected := if nextTrimmed.startsWith "| " || code.endsWith "where" then 2 else 4
        if leadingSpaces next != expected then
          result := result.push <| violation "ERR_IND" (i + 2)
            s!"Continuation of a declaration must be indented {expected} spaces"
    if i + 1 < lines.size && trimmed == "simp" then
      let next := codeLines[i + 1]!
      let nextTrimmed := next.trimAscii.toString
      if !nextTrimmed.isEmpty && !next.trimAsciiStart.toString.startsWith "--" &&
          !isFlexibleFollowup next && leadingSpaces code == leadingSpaces next then
        result := result.push <| violation "ERR_NSP" (i + 1)
          "Non-terminal `simp`; use the explicit simp result suggested by `simp?`"
  return result

private def fileLengthViolations (lines : Array String) (importsOnly : Bool) : Array Violation :=
  if !importsOnly && lines.size > 1500 then
    #[violation "ERR_NUM_LIN" 1 s!"File contains {lines.size} lines; split it below 1500 lines"]
  else #[]

private structure SourceToken where
  text : String
  line : Nat

private partial def sourceTokens (chars current : List Char) (acc : List SourceToken)
    (line : Nat) : List SourceToken :=
  match chars with
  | [] =>
      let acc := if current.isEmpty then acc else
        { text := String.ofList current.reverse, line } :: acc
      acc.reverse
  | c :: rest =>
      if c.isWhitespace then
        let acc := if current.isEmpty then acc else
          { text := String.ofList current.reverse, line } :: acc
        sourceTokens rest [] acc (if c == '\n' then line + 1 else line)
      else if ['@', '[', ']', '(', ')', ',', '|', '`'].contains c then
        let acc := if current.isEmpty then acc else
          { text := String.ofList current.reverse, line } :: acc
        sourceTokens rest [] ({ text := c.toString, line } :: acc) line
      else
        sourceTokens rest (c :: current) acc line

/-- Find a `nolint` attribute head in sanitized source tokens.

`nolint` used as an argument, as in `@[inherit_doc nolint]`, is deliberately not rejected. -/
private def noLintAttributeLine? (tokens : List SourceToken) : Option Nat := Id.run do
  let mut squareDepth := 0
  let mut attributeDepth? : Option Nat := none
  let mut expectAttributeHead := false
  let mut previous := ""
  for token in tokens do
    if token.text == "[" then
      squareDepth := squareDepth + 1
      if previous == "@" || previous == "attribute" then
        attributeDepth? := some squareDepth
        expectAttributeHead := true
    else if token.text == "]" then
      if attributeDepth? == some squareDepth then
        attributeDepth? := none
        expectAttributeHead := false
      squareDepth := squareDepth - 1
    else if token.text == "," && attributeDepth? == some squareDepth then
      expectAttributeHead := true
    else if attributeDepth? == some squareDepth && expectAttributeHead then
      if token.text == "nolint" then return some token.line
      expectAttributeHead := false
    previous := token.text
  return none

private def isIdentContinue (c : Char) : Bool :=
  Lean.isIdRest c

private def startsToken (token : String) (chars : List Char) : Bool :=
  let tokenChars := token.toList
  tokenChars.isPrefixOf chars &&
    match chars.drop tokenChars.length with
    | next :: _ => !isIdentContinue next
    | [] => true

private partial def skipRawBlockComment (chars : List Char) (depth line : Nat) :
    List Char × Nat :=
  match chars with
  | [] => ([], line)
  | '/' :: '-' :: rest => skipRawBlockComment rest (depth + 1) line
  | '-' :: '/' :: rest =>
      if depth == 1 then (rest, line) else skipRawBlockComment rest (depth - 1) line
  | '\n' :: rest => skipRawBlockComment rest depth (line + 1)
  | _ :: rest => skipRawBlockComment rest depth line

private partial def skipRawLineComment (chars : List Char) (line : Nat) : List Char × Nat :=
  match chars with
  | [] => ([], line)
  | '\n' :: rest => (rest, line + 1)
  | _ :: rest => skipRawLineComment rest line

private partial def skipRawTrivia (chars : List Char) (line : Nat) : List Char × Nat :=
  match chars with
  | '-' :: '-' :: rest =>
      let (rest, line) := skipRawLineComment rest line
      skipRawTrivia rest line
  | '/' :: '-' :: rest =>
      let (rest, line) := skipRawBlockComment rest 1 line
      skipRawTrivia rest line
  | '\n' :: rest => skipRawTrivia rest (line + 1)
  | c :: rest => if c.isWhitespace then skipRawTrivia rest line else (chars, line)
  | [] => ([], line)

private def forbiddenRawOptionRoot? (chars : List Char) (line : Nat) :
    Option (String × Nat) :=
  let (chars, line) := skipRawTrivia chars line
  let quoted := chars.head? == some '«'
  let chars := if quoted then chars.tail else chars
  ["linter", "pp", "profiler", "trace"].findSome? fun root =>
    if startsToken root chars then
      let tail := chars.drop root.length
      if !quoted || tail.head? == some '»' then some (root, line) else none
    else none

private partial def rawOptionViolationsAux (chars : List Char) (line : Nat)
    (previousIsIdent : Bool) (acc : Array Violation) : Array Violation :=
  match chars with
  | [] => acc
  | c :: rest =>
      let acc :=
        if !previousIsIdent && startsToken "set_option" chars then
          match forbiddenRawOptionRoot? (chars.drop "set_option".length) line with
          | some (root, rootLine) => acc.push <| violation "ERR_OPT" rootLine
              s!"Forbidden `set_option {root}.*`; fix the source instead of changing or suppressing the linter"
          | none => acc
        else acc
      rawOptionViolationsAux rest (if c == '\n' then line + 1 else line)
        (isIdentContinue c) acc

/-- Fail-closed lexical backstop for forbidden option syntax.

This pass deliberately scans comments and literals too. That conservative policy keeps custom and
extensible interpolated-string syntax covered without trusting mutable parser/linter state in the
module being checked. Suppression examples belong in the out-of-scope test fixtures, not production
`ArkLib` sources.
-/
private def rawOptionViolations (lines : Array String) : Array Violation :=
  rawOptionViolationsAux ("\n".intercalate lines.toList).toList 1 false #[]

private inductive RawPolicyMode where
  | code
  | lineComment
  | blockComment (depth : Nat)

/-- Mask comments, but preserve all literal bodies and line structure.

Unlike `sanitizeChars`, this normalization intentionally exposes policy syntax in ordinary and
custom interpolated strings. It is a single pass, so unmatched attribute-like text cannot cause
quadratic rescanning.
-/
private partial def sanitizeRawPolicyChars (chars : List Char) (mode : RawPolicyMode) : List Char :=
  match chars, mode with
  | [], _ => []
  | '-' :: '-' :: rest, .code => ' ' :: ' ' :: sanitizeRawPolicyChars rest .lineComment
  | '/' :: '-' :: rest, .code =>
      ' ' :: ' ' :: sanitizeRawPolicyChars rest (.blockComment 1)
  | c :: rest, .code => c :: sanitizeRawPolicyChars rest .code
  | '\n' :: rest, .lineComment => '\n' :: sanitizeRawPolicyChars rest .code
  | _ :: rest, .lineComment => ' ' :: sanitizeRawPolicyChars rest .lineComment
  | '/' :: '-' :: rest, .blockComment depth =>
      ' ' :: ' ' :: sanitizeRawPolicyChars rest (.blockComment (depth + 1))
  | '-' :: '/' :: rest, .blockComment 1 =>
      ' ' :: ' ' :: sanitizeRawPolicyChars rest .code
  | '-' :: '/' :: rest, .blockComment (depth + 2) =>
      ' ' :: ' ' :: sanitizeRawPolicyChars rest (.blockComment (depth + 1))
  | '\n' :: rest, .blockComment depth =>
      '\n' :: sanitizeRawPolicyChars rest (.blockComment depth)
  | _ :: rest, .blockComment depth => ' ' :: sanitizeRawPolicyChars rest (.blockComment depth)

private def rawNoLintAttributeLine? (lines : Array String) : Option Nat :=
  let chars := sanitizeRawPolicyChars ("\n".intercalate lines.toList).toList .code
  let tokens := sourceTokens chars [] [] 1
  let rec quotationLine? : List SourceToken → Option Nat
    | tick :: openParen :: attr :: bar :: head :: rest =>
        if tick.text == "`" && openParen.text == "(" && attr.text == "attr" &&
            bar.text == "|" && head.text == "nolint" then some head.line
        else quotationLine? (openParen :: attr :: bar :: head :: rest)
    | _ => none
  noLintAttributeLine? tokens <|> quotationLine? tokens

private def suppressionViolations (lines codeLines : Array String) : Array Violation := Id.run do
  let code := "\n".intercalate codeLines.toList
  let tokens := sourceTokens code.toList [] [] 1
  let mut result := rawOptionViolations lines
  if let some line := rawNoLintAttributeLine? lines <|> noLintAttributeLine? tokens then
    result := result.push <| violation "ERR_NOLINT" line
      "`@[nolint]` suppressions are forbidden; fix the declaration"
  return result

/-- Apply pure text checks.

Suppression checks intentionally remain independent from the build plugin. The plugin provides
syntax-precise diagnostics (including extensible interpolations); this source pass ensures that
ordinary suppression syntax still fails if code in the module tampers with Lean's mutable linter
registry or captures elaborator diagnostics.
-/
def lintLines (lines : Array String) : Array Violation :=
  let codeLines := sanitizeLines lines
  unicodeViolations lines ++ lineViolations lines codeLines ++
    suppressionViolations lines codeLines ++
    fileLengthViolations lines (isImportsOnly codeLines) ++
    headerViolations lines codeLines

/-- Convert a violation count to a portable nonzero process exit code. -/
def violationExitCode (errorCount : Nat) : UInt32 :=
  (min errorCount 125).toUInt32

/-- Direct imports prohibited by ArkLib's import-discipline policy. -/
def importViolation? (name : Name) : Option (String × String) :=
  if [`ArkLib, `Mathlib, `VCVio, `CompPoly, `PolyFun, `Batteries].contains name then
    some ("ERR_ROOT_IMPORT", s!"Blanket package-root import `{name}`; import a stable owner module")
  else if name == `Mathlib.Tactic then
    some ("ERR_TAC", "Import the tactics actually used instead of `Mathlib.Tactic`")
  else if name == `Lake || name.getRoot == `Lake then
    some ("ERR_LAKE", "ArkLib library modules must not import Lake")
  else none

private def assertSelfTest (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError s!"lint-style self-test failed: {message}"

private def hasCode (code : String) (lines : Array String) : Bool :=
  (lintLines lines).any (·.code == code)

/-- Fast, deterministic checks for the source scanner and security policy. -/
def runSelfTests : IO Unit := do
  assertSelfTest (!isHazardousUnicode 'ŵ' && !isHazardousUnicode '⧺' &&
    !isHazardousUnicode '◌' && !isHazardousUnicode '\u0303' &&
    !isHazardousUnicode '\ufe0f' && !isHazardousUnicode (Char.ofNat 0xe0100))
    "mathematical notation must not be restricted by a closed allowlist"
  assertSelfTest (isHazardousUnicode '\u00a0' && isHazardousUnicode '\u200b' &&
    isHazardousUnicode '\u202e' && isHazardousUnicode '\u2066' &&
    isHazardousUnicode '\ufff9' && isHazardousUnicode '\u2800' &&
    isHazardousUnicode '\u3164' && isHazardousUnicode (Char.ofNat 0x13430) &&
    isHazardousUnicode (Char.ofNat 0x1bca0) && isHazardousUnicode (Char.ofNat 0x1d173) &&
    isHazardousUnicode (Char.ofNat 0xe007f))
    "invisible, annotation/tag, and bidirectional controls must be rejected"
  let sample := #["def ok := \"@[nolint] set_option linter.foo true\"",
    "/- outer /- @[nolint] -/ set_option pp.foo true -/"]
  let masked := sanitizeLines sample
  assertSelfTest (!masked[0]!.contains "nolint" && !masked[1]!.contains "set_option")
    "comments and strings must be masked, including nested comments"
  let raw := sanitizeLines #["def ok := r###\"@[nolint]\"###"]
  assertSelfTest (!raw[0]!.contains "nolint") "raw strings must be masked"
  for root in ["linter", "pp", "profiler", "trace"] do
    assertSelfTest (hasCode "ERR_OPT" #["#guard_msgs (drop error) in", "set_option",
      s!"  {root}.test false in", "def f := 1"])
      s!"captured plugin diagnostics must not bypass source rejection for {root}"
    assertSelfTest (hasCode "ERR_OPT" #["set_option /- outer /- nested -/ comment -/",
      s!"  «{root}».test false in (1 : Nat)"])
      s!"nested trivia and a quoted {root} root must not bypass the lexical backstop"
    assertSelfTest (hasCode "ERR_OPT" #[s!"def t := set_option {root}.test false in 1",
      s!"example : True := by set_option {root}.test false in trivial"])
      s!"term and tactic set_option forms must be rejected for {root}"
  assertSelfTest (hasCode "ERR_NOLINT" #["#guard_msgs (drop error) in",
    "@[nolint unusedArguments] def f (x : Nat) := 1"])
    "captured plugin diagnostics must not bypass source rejection for nolint"
  assertSelfTest (hasCode "ERR_NOLINT" #[
    "#eval Lean.Elab.Command.moduleLintersRef.set #[]",
    "wrapcmd \"{@[nolint unusedArguments] def f (x : Nat) := 1}\""])
    "custom command interpolation must not bypass nolint after registry mutation"
  assertSelfTest (hasCode "ERR_NOLINT" #[
    "#eval Lean.Elab.Command.moduleLintersRef.set #[]",
    "syntax \"bad\" : attr",
    "macro_rules | `(attr| bad) => `(attr| nolint unusedArguments)",
    "@[bad] def f (x : Nat) := 1"])
    "attribute syntax quotations must not bypass nolint after registry mutation"
  assertSelfTest (!hasCode "ERR_NOLINT" #["infix:65 \" | \" => Nat.add",
    "def attr := 1", "def nolint := 2", "#eval attr | nolint"])
    "ordinary identifiers around an infix bar must not look like an attribute quotation"
  assertSelfTest (hasCode "ERR_NOLINT" #[
    "#check (`(attr | nolint) : Lean.MacroM (Lean.TSyntax `term))"])
    "policy-like syntax quotations are reserved by the fail-closed lexical gate"
  assertSelfTest (!hasCode "ERR_NOLINT" #["def nolint : Nat := 0",
    "@[inherit_doc nolint] def f := 1"])
    "nolint used as an ordinary attribute argument must remain valid"
  assertSelfTest (hasCode "ERR_NOLINT" #["@[simp, nolint unusedArguments]",
    "def f (x : Nat) := 1"])
    "nolint must be rejected at every attribute-list head"
  assertSelfTest (hasCode "ERR_NOLINT" #["attribute /- outer /- nested -/ comment -/ [",
    "  nolint unusedArguments] f"])
    "attribute-command nolint with nested trivia must be rejected"
  assertSelfTest (hasCode "ERR_NOLINT" #["@[simp, /- gap -/ nolint unusedArguments]",
    "def f (x : Nat) := 1"])
    "later nolint attributes with comment trivia must be rejected"
  assertSelfTest (!hasCode "ERR_OPT" #["def set_optionx := 1",
    "set_option linterish.test false", "set_option maxRecDepth 1000"])
    "option checks must respect exact keyword and root boundaries"
  assertSelfTest (!hasCode "ERR_OPT" #["set_option ppα.test true",
    "set_option linterα.test true", "set_option profilerα.test true",
    "set_option traceα.test true"])
    "Unicode Lean identifier continuations must not be mistaken for forbidden roots"
  assertSelfTest (!hasCode "ERR_NOLINT" #["def nolint := 1", "def «nolint» := 2",
    "@[inherit_doc nolint] def f := 1"])
    "ordinary nolint identifiers and attribute arguments must remain valid"
  assertSelfTest (hasCode "ERR_NOLINT" #["def «@[nolint]» := 2"])
    "policy-like quoted identifiers are reserved by the fail-closed lexical gate"
  assertSelfTest (hasCode "ERR_NOLINT" #["-- «",
    "#eval Lean.Elab.Command.moduleLintersRef.set #[]",
    "wrapcmd \"{@[nolint unusedArguments] def f (x : Nat) := 1}\""])
    "an unmatched guillemet in a comment must not blind later interpolation checks"
  assertSelfTest (hasCode "ERR_NOLINT" #[
    "def inertDocumentation := \"@[nolint unusedArguments]\""])
    "production literals use the conservative fail-closed nolint-spelling policy"
  let unmatchedAttributeOpeners := "-- " ++
    String.ofList (List.flatten (List.replicate 48 ['@', '[']))
  assertSelfTest (!hasCode "ERR_NOLINT" (Array.replicate 1500 unmatchedAttributeOpeners))
    "a maximum-size file of unmatched attribute openers must be handled in one linear pass"
  assertSelfTest (hasCode "ERR_OPT" #["#exit", "set_option pp.universes false"])
    "the source backstop must scan past #exit"
  assertSelfTest (hasCode "ERR_OPT" #[
    "#eval Lean.Elab.Command.moduleLintersRef.set #[]",
    "set_option linter.unusedVariables false in def f (x : Nat) := 1"])
    "mutating the module-linter registry must not disable the independent source backstop"
  assertSelfTest (hasCode "ERR_OPT" #[
    "initialize Lean.Elab.Command.addModuleLinter { run := fun _ => modify fun s => { s with messages := {} } }",
    "set_option trace.profiler true in def f := 1"])
    "a later diagnostic-clearing module linter must not disable the source backstop"
  assertSelfTest (hasCode "ERR_OPT" #[
    "macro \"quotedSuppression\" : term => `(set_option pp.universes false in (1 : Nat))"])
    "suppression syntax in quotations and macro bodies must be rejected lexically"
  assertSelfTest (hasCode "ERR_OPT" #[
    "def customInterpolation := customInterp \"{set_option profiler true in (1 : Nat)}\""])
    "extensible interpolated-string source must remain covered if plugin state is mutated"
  assertSelfTest (hasCode "ERR_OPT" #[
    "def inertDocumentation := \"set_option pp.universes false\""])
    "production literals use the conservative fail-closed option-spelling policy"
  let validHeader := #["/-", "Copyright (c) 2026 ArkLib Contributors.",
    "Released under Apache 2.0 license.", "Authors: ArkLib Contributors", "-/"]
  assertSelfTest (!hasCode "ERR_MOD" (validHeader ++ #["/-! Real module docstring. -/",
    "def x := 1"]))
    "a top-level module docstring must satisfy the header policy"
  assertSelfTest (!hasCode "ERR_MOD" (validHeader ++ #["module", "public", "/- inline -/",
    "meta", "import Lean", "/-! Module-system docstring. -/", "def x := 1"]))
    "module-system headers with multiline, comment-interposed modifiers must precede docs"
  assertSelfTest (hasCode "ERR_MOD" (validHeader ++ #["/- outer comment", "/-! nested fake -/",
    "-/", "def x := 1"]))
    "a module-doc opener nested in an ordinary comment must not satisfy the header policy"
  assertSelfTest (violationExitCode 0 == 0 && violationExitCode 1 == 1 &&
    violationExitCode 125 == 125 && violationExitCode 126 == 125)
    "violations must map to a portable nonzero process exit code"
  let checks := #[
    ("ERR_COP", #["def x := 1"]),
    ("ERR_LIN", #[String.ofList (List.replicate 101 'x')]),
    ("ERR_TWS", #["def x := 1 "]),
    ("ERR_SEM", #["def x := 1 ; exact x"]),
    ("ERR_IBY", #["def x :=", "by"]),
    ("ERR_DOT", #[". exact h"]),
    ("ERR_CLN", #[": Nat"]),
    ("ERR_ADN", #["-- Adaptation note: legacy"]),
    ("ERR_IND", #["def x :", " Nat := 1"]),
    ("ERR_NSP", #["  simp", "  exact h"])
  ]
  for (code, lines) in checks do
    assertSelfTest (hasCode code lines) s!"expected fixture to trigger {code}"
  assertSelfTest (hasCode "ERR_NUM_LIN"
    (#["def x := 1"] ++ Array.replicate 1500 "")) "1500-line cap must be enforced"
  let allowed ← Lean.parseImports' "import ArkLib.Data.Math.Basic\n" "allowed.lean"
  assertSelfTest (allowed.imports.all (importViolation? ·.module |>.isNone))
    "specific owner-module imports must be accepted"
  let rejected ← Lean.parseImports' "module\npublic meta import all «ArkLib»\n" "rejected.lean"
  assertSelfTest (rejected.imports.any (importViolation? ·.module |>.isSome))
    "module-system blanket imports must be rejected"
  for root in [`Mathlib, `VCVio, `CompPoly, `PolyFun, `Batteries] do
    assertSelfTest (importViolation? root |>.isSome) s!"blanket import `{root}` must be rejected"
  let commented ← Lean.parseImports'
    "/- import ArkLib -/\nimport ArkLib.Data.Math.Basic\n" "commented.lean"
  assertSelfTest (commented.imports.all (importViolation? ·.module |>.isNone))
    "imports in comments must not be linted"

end ArkLib.LintStyle
