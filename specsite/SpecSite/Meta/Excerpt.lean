/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VersoManual
import Verso.Code.External.Files

/-!
# Source excerpts by declaration name

`{decl n₁ n₂ …}` shows the source of the named declarations, highlighted by SubVerso with hovers,
binding highlights and, for tactic proofs, the proof state after each tactic. Since the names
resolve in the document's scope when the site builds, a renamed or deleted declaration fails the
build.

The excerpt finds a declaration's module from the environment and loads that module's highlighted
source from the project in `specsite/highlight/`, which runs `lake build +Module:highlighted`.
Nothing in `ArkLib/` or `Specs/` needs anchor comments: the command that defines the name is the
excerpt.

Flags:
* `+statement` cuts each declaration after its top-level `:=` and prints `…` for the body.
* `-docs` drops the doc comment in front of each declaration.

Above the code, a caption names the file and the lines, linked to the source on GitHub at the commit
the site was built from.
-/

namespace SpecSite

open Lean Elab
open Verso Doc Elab ArgParse
open Verso.Genre Manual
open SubVerso.Highlighting
open SubVerso.Module (ModuleItem)

/-- The repository whose files the captions link to. -/
def repoUrl : String := "https://github.com/Verified-zkEVM/ArkLib"

/-- The source directory of the prototype library, relative to the repository root. -/
def prototypeDir : String := "docs/design/interaction-layer/prototypes"

/-- The file of a module, relative to the repository root. Modules of the prototype library live
under `prototypeDir`; every other module is at its path from the root. -/
def moduleFile (mod : Name) : String :=
  let path := "/".intercalate (mod.components.map (·.toString)) ++ ".lean"
  if mod.getRoot == `Specs then prototypeDir ++ "/" ++ path else path

/-- The commit that the site is built from, for permanent links to the source. An empty string if
`git` is not available. -/
def gitHead : IO String := do
  let out ← IO.Process.output { cmd := "git", args := #["rev-parse", "HEAD"] }
  return if out.exitCode == 0 then out.stdout.trimAscii.copy else ""

-- Where an excerpt comes from, as a caption above its code.
block_extension Block.excerpt (file : String) (url : String) (lines : String) (names : String) where
  data := Json.arr #[.str file, .str url, .str lines, .str names]
  traverse _ _ _ := pure none
  toTeX := some fun _ goB _ _ contents => contents.mapM goB
  toHtml := some fun _ goB _ data contents => do
    let .arr #[.str file, .str url, .str lines, .str names] := data
      | Verso.reportError "Expected four strings for an excerpt" *> pure .empty
    let link : Html :=
      if url.isEmpty then .element "code" #[] (.text file)
      else .element "a" #[("href", url)] (.element "code" #[] (.text file))
    let cap : Html := .element "figcaption" #[] (.seq #[
      link, .element "span" #[("class", "spec-lines")] (.text lines),
      .element "span" #[("class", "spec-names")] (.text names)])
    pure <| .element "figure" #[("class", "spec-excerpt")] (.seq #[cap, .seq (← contents.mapM goB)])
  extraCss := [r#"
figure.spec-excerpt { margin: 1rem 0 1.25rem; }
figure.spec-excerpt > figcaption {
  display: flex; flex-wrap: wrap; gap: 0.25rem 0.9rem; align-items: baseline;
  font-size: 0.8rem; color: var(--verso-text-color, #333); opacity: 0.85; margin-bottom: 0.25rem;
}
figure.spec-excerpt > figcaption a { text-decoration: none; }
figure.spec-excerpt > figcaption .spec-names {
  font-family: var(--verso-code-font-family); opacity: 0.8;
}
figure.spec-excerpt pre { margin-top: 0; }
"#]

/-- The arguments of `{decl}`: the declarations and how to cut them. -/
structure DeclConfig where
  /-- The declarations, each with the identifier that named it. -/
  names : Array (Ident × Name)
  /-- Show only the statement of each declaration. -/
  statement : Bool
  /-- Keep the doc comment in front of each declaration. -/
  docs : Bool

instance : FromArgs DeclConfig DocElabM where
  fromArgs := DeclConfig.mk <$>
    (Array.mk <$> .many (.positional `name .documentableName)) <*>
    .flag `statement false <*>
    .flag `docs true

/-- The leaves of highlighted code in order, with every `seq` flattened. Spans and tactic blocks
stay whole. -/
partial def leaves : Highlighted → Array Highlighted
  | .seq xs => xs.foldl (init := #[]) fun acc x => acc ++ leaves x
  | hl => #[hl]

/-- Whether a leaf is blank text. -/
def isBlank : Highlighted → Bool
  | .text s => s.all Char.isWhitespace
  | _ => false

/-- A declaration without the whitespace in front of it. -/
def trimFront (hl : Highlighted) : Highlighted :=
  match (leaves hl).toList.dropWhile isBlank with
  | .text s :: rest => .seq (.text (s.dropWhile Char.isWhitespace).copy :: rest).toArray
  | ls => .seq ls.toArray

/-- Drop the doc comment at the front of a declaration and the blank text after it. -/
def dropDocComment (hl : Highlighted) : Highlighted :=
  match (leaves hl).toList.dropWhile isBlank with
  | .token ⟨.docComment, _⟩ :: rest => .seq (rest.dropWhile isBlank).toArray
  | _ => hl

/-- The text of a token leaf. -/
def tokenText : Highlighted → Option String
  | .token ⟨_, s⟩ => some s
  | _ => none

/-- Cut a declaration after its first `:=` outside brackets and print `…` for the body. If there is
no such `:=`, the declaration is unchanged. -/
def cutAtDefEq (hl : Highlighted) : Highlighted := Id.run do
  let ls := leaves hl
  let mut depth : Int := 0
  let mut out : Array Highlighted := #[]
  for l in ls do
    out := out.push l
    match tokenText l with
    | some s =>
      if ["(", "[", "{", "⟨", "⦃", "⟪"].contains s then depth := depth + 1
      else if [")", "]", "}", "⟩", "⦄", "⟫"].contains s then depth := depth - 1
      else if s == ":=" && depth == 0 then
        return .seq (out.push (.text " …"))
    | none => pure ()
  return hl

/-- The module that defines a name, from the environment. -/
def moduleOf (n : Name) : DocElabM Name := do
  let env ← getEnv
  let some idx := env.getModuleIdxFor? n
    | throwError "'{n}' is defined in this document, not in an imported module"
  return env.header.moduleNames[idx.toNat]!

/-- The item of a module that defines a name. Loading parses the module's highlighted source,
with the proof state after every tactic, which in a module with many tactic proofs costs more than
Lean's default heartbeat limit. The cost is bounded by the size of that file. For that reason the
load runs without the limit. -/
def itemFor (mod n : Name) : DocElabM ModuleItem := do
  let items ← withTheReader Core.Context (fun c => { c with maxHeartbeats := 0 }) <|
    Verso.Code.External.loadModuleContent (Syntax.mkStrLit "highlight") mod.toString
  let some item := items.find? (·.defines.contains n)
    | throwError "The highlighted source of '{mod}' has no command that defines '{n}'"
  return item

/-- The term of a highlighted excerpt. `quote` writes the excerpt out as one constructor term per
token and hover, which Lean then elaborates; a long statement with many hovers exceeds the default
heartbeat limit. This stores the excerpt in the document's table of highlighted code and quotes its
key, as Verso does for its own Lean blocks (`quoteHighlightViaSerialization`, which is private). -/
def quoteHighlighted (hl : Highlighted) : DocElabM Term := do
  match (← readThe DocElabContext).docReconstructionPlaceholder,
      (← getThe DocElabM.State).highlightDeduplicationTable with
  | some placeholder, some table =>
    let (key, table) := hl.export.run table
    modifyThe DocElabM.State ({ · with highlightDeduplicationTable := table })
    ``(Verso.Genre.Manual.InlineLean.reconstructHighlight $placeholder $(quote key))
  | _, _ => ``(SubVerso.Highlighting.hlFromExport! $(quote (SubVerso.Highlighting.hlToExport hl)))

/-- The source of declarations by name, with a caption that links to it. -/
@[block_command]
def decl : BlockCommandOf DeclConfig
  | ⟨names, statement, docs⟩ => do
    if names.isEmpty then throwError "Expected at least one declaration name"
    let mut parts : Array Highlighted := #[]
    let mut mods : Array Name := #[]
    let mut ranges : Array (Nat × Nat) := #[]
    for (_, n) in names do
      let mod ← moduleOf n
      let item ← itemFor mod n
      let mut hl := trimFront item.code
      unless docs do hl := dropDocComment hl
      if statement then hl := cutAtDefEq hl
      parts := parts.push hl
      mods := mods.push mod
      if let some (s, e) := item.range then ranges := ranges.push (s.line, e.line)
    -- Join the declarations with a blank line, each without its trailing newlines.
    let trimmed := parts.map fun hl =>
      let t := hl.takeStringRightWhile Char.isWhitespace
      hl.dropTextRight t.length
    let joined := trimmed.foldl (init := Highlighted.empty) fun acc hl =>
      if acc.isEmpty then hl else acc ++ .text "\n\n" ++ hl
    let file := moduleFile mods[0]!
    let sameFile := mods.all (moduleFile · == file)
    let head ← gitHead
    let (lines, url) :=
      match ranges.map (·.1) |>.min?, ranges.map (·.2) |>.max? with
      | some s, some e =>
        let lines := if s == e then s!"line {s}" else s!"lines {s}–{e}"
        let anchor := if sameFile then s!"#L{s}-L{e}" else ""
        (if sameFile then lines else "", if head.isEmpty then "" else
          s!"{repoUrl}/blob/{head}/{file}{anchor}")
      | _, _ => ("", "")
    let shown := ", ".intercalate (names.toList.map fun (_, n) => n.toString)
    let file := if sameFile then file else file ++ " and others"
    ``(Verso.Doc.Block.other
        (SpecSite.Block.excerpt $(quote file) $(quote url) $(quote lines) $(quote shown))
        #[Verso.Doc.Block.other
          (Verso.Genre.Manual.Block.lean $(← quoteHighlighted joined) {}) #[]])

end SpecSite
