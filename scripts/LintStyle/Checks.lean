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
U+FE0F and U+E0100–U+E01EF remain valid; we reject control, bidirectional, joining, annotation/tag,
Mongolian free variation selectors, and nonstandard spacing characters that can make reviewed source
differ from what it appears to say.
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
    n == 0x00a0 || n == 0x00ad || n == 0x034f || n == 0x061c || n == 0x1680 ||
    (0x180b ≤ n && n ≤ 0x180f) ||
    (0x2000 ≤ n && n ≤ 0x200f) ||
    (0x2028 ≤ n && n ≤ 0x202f) ||
    (0x205f ≤ n && n ≤ 0x206f) ||
    n == 0x3000 || n == 0xfeff || (0xfff9 ≤ n && n ≤ 0xfffb) ||
    n == 0xe0001 || (0xe0020 ≤ n && n ≤ 0xe007f)

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

/-- Apply pure text checks. Syntax and import checks are performed separately with Lean's parser. -/
def lintLines (lines : Array String) : Array Violation :=
  let codeLines := sanitizeLines lines
  unicodeViolations lines ++ lineViolations lines codeLines ++
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
    isHazardousUnicode '\ufff9' && isHazardousUnicode (Char.ofNat 0xe007f))
    "invisible, annotation/tag, and bidirectional controls must be rejected"
  let sample := #["def ok := \"@[nolint] set_option linter.foo true\"",
    "/- outer /- @[nolint] -/ set_option pp.foo true -/"]
  let masked := sanitizeLines sample
  assertSelfTest (!masked[0]!.contains "nolint" && !masked[1]!.contains "set_option")
    "comments and strings must be masked, including nested comments"
  let raw := sanitizeLines #["def ok := r###\"@[nolint]\"###"]
  assertSelfTest (!raw[0]!.contains "nolint") "raw strings must be masked"
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
