/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VersoManual
import SpecSite.Meta.Excerpt
import SpecSite.Meta.Protocol

/-!
# The site's other blocks

* `:::card "Title" (n := "1") (status := "fixed")` frames a decision record: a numbered card with a
  status badge. Its contents are ordinary blocks, usually a description list.
* `::::stats` holds `:::stat "value"` blocks: a row of headline numbers, each with a sentence.
* `{sizes c}` evaluates the constant `c : SizeTable` and counts the lines of its files when the site
  builds. The table therefore cannot drift from the code.
* `::::columns` holds `:::column "Title" (tone := "before")` blocks, side by side on a wide
  screen.
* `{bench}` reads `prototypes/out/bench.md`, the output of `bench.sh`, when the site builds.
* `{theorems n₁ n₂ …}` lists theorems with their source lines and the axioms each one depends on.
  The build fails if one of them depends on `sorryAx` or on an axiom outside Lean's three standard
  ones.
-/

namespace SpecSite

open Lean Elab
open Verso Doc Elab ArgParse
open Verso.Genre Manual
open Verso.Output (Html)
open SubVerso.Highlighting

/-! ## Cards -/

/-- The CSS class of a status badge. -/
def statusClass (status : String) : Except String String :=
  if ["fixed", "partial", "open"].contains status then .ok s!"spec-{status}"
  else .error s!"Unknown status '{status}': expected fixed, partial or open"

-- A decision record: a numbered card with a title, a status badge and contents.
block_extension Block.card (n title status : String) where
  data := Json.arr #[.str n, .str title, .str status]
  traverse _ _ _ := pure none
  toTeX := some fun _ goB _ data contents => do
    let .arr #[.str n, .str title, .str status] := data
      | Verso.reportError "Expected three strings for a card" *> pure .empty
    let head := (if n.isEmpty then "" else n ++ ". ") ++ title ++
      (if status.isEmpty then "" else s!" ({status})")
    pure <| .seq #[.raw s!"\n\\paragraph\{{head}}\n", .seq (← contents.mapM goB)]
  toHtml := some fun _ goB _ data contents => do
    let .arr #[.str n, .str title, .str status] := data
      | Verso.reportError "Expected three strings for a card" *> pure .empty
    let badge : Html := match statusClass status with
      | .ok cls => .element "span" #[("class", s!"spec-status {cls}")] (.text status)
      | .error _ => .empty
    let num : Html := if n.isEmpty then .empty
      else .element "span" #[("class", "spec-card-n")] (.text n)
    let id := if n.isEmpty then #[] else #[("id", s!"card-{n}")]
    pure <| .element "section" (#[("class", "spec-card")] ++ id) (.seq #[
      .element "div" #[("class", "spec-card-head")]
        (.seq #[num, .element "span" #[] (.text title), badge]),
      .seq (← contents.mapM goB)])

/-- The arguments of `:::card`. -/
structure CardConfig where
  /-- The title. -/
  title : String
  /-- The card's number, shown before the title and used as its anchor `#card-n`. -/
  n : String
  /-- `fixed`, `partial` or `open`, or empty for no badge. -/
  status : String

instance : FromArgs CardConfig DocElabM where
  fromArgs := CardConfig.mk <$> .positional `title .string <*>
    .namedD `n .string "" <*> .namedD `status .string ""

/-- A numbered decision record with a status badge. -/
@[directive]
def card : DirectiveExpanderOf CardConfig
  | ⟨title, n, status⟩, contents => do
    unless status.isEmpty do
      if let .error e := statusClass status then throwError e
    let body ← contents.mapM elabBlock
    ``(Verso.Doc.Block.other (SpecSite.Block.card $(quote n) $(quote title) $(quote status))
        #[$body,*])

/-! ## Headline numbers -/

-- A row of headline numbers.
block_extension Block.stats where
  traverse _ _ _ := pure none
  toTeX := some fun _ goB _ _ contents => contents.mapM goB
  toHtml := some fun _ goB _ _ contents => do
    pure <| .element "div" #[("class", "spec-stats")] (.seq (← contents.mapM goB))

-- One headline number with the sentence that explains it.
block_extension Block.stat (value : String) where
  data := .str value
  traverse _ _ _ := pure none
  toTeX := some fun _ goB _ data contents => do
    let .str v := data | pure .empty
    pure <| .seq #[.raw s!"\n\\noindent\\textbf\{{v}} ", .seq (← contents.mapM goB)]
  toHtml := some fun _ goB _ data contents => do
    let .str v := data
      | Verso.reportError "Expected a string for a statistic" *> pure .empty
    pure <| .element "div" #[("class", "spec-stat")] (.seq #[
      .element "b" #[] (.text v), .element "span" #[] (.seq (← contents.mapM goB))])

/-- A row of headline numbers, each a `:::stat` block. -/
@[directive]
def stats : DirectiveExpanderOf Unit
  | (), contents => do
    let body ← contents.mapM elabBlock
    ``(Verso.Doc.Block.other SpecSite.Block.stats #[$body,*])

/-- The argument of `:::stat`: the number as it is shown. -/
structure StatConfig where
  /-- The number, with its unit. -/
  value : String

instance : FromArgs StatConfig DocElabM where
  fromArgs := StatConfig.mk <$> .positional `value .string

/-- One headline number. The contents explain it. -/
@[directive]
def stat : DirectiveExpanderOf StatConfig
  | ⟨value⟩, contents => do
    let body ← contents.mapM elabBlock
    ``(Verso.Doc.Block.other (SpecSite.Block.stat $(quote value)) #[$body,*])

/-! ## Side by side -/

-- Two or more columns side by side on a wide screen, stacked on a narrow one.
block_extension Block.columns where
  traverse _ _ _ := pure none
  toTeX := some fun _ goB _ _ contents => contents.mapM goB
  toHtml := some fun _ goB _ _ contents => do
    pure <| .element "div" #[("class", "spec-columns")] (.seq (← contents.mapM goB))

-- One column with a title. `tone` is `before`, `after` or empty.
block_extension Block.column (title tone : String) where
  data := Json.arr #[.str title, .str tone]
  traverse _ _ _ := pure none
  toTeX := some fun _ goB _ data contents => do
    let .arr #[.str title, _] := data | pure .empty
    pure <| .seq #[.raw s!"\n\\paragraph\{{title}}\n", .seq (← contents.mapM goB)]
  toHtml := some fun _ goB _ data contents => do
    let .arr #[.str title, .str tone] := data
      | Verso.reportError "Expected two strings for a column" *> pure .empty
    let cls := if tone.isEmpty then "spec-column" else s!"spec-column spec-{tone}"
    pure <| .element "section" #[("class", cls)] (.seq #[
      .element "div" #[("class", "spec-column-head")] (.text title),
      .seq (← contents.mapM goB)])

/-- Columns side by side, each a `:::column` block. -/
@[directive]
def columns : DirectiveExpanderOf Unit
  | (), contents => do
    let body ← contents.mapM elabBlock
    ``(Verso.Doc.Block.other SpecSite.Block.columns #[$body,*])

/-- The arguments of `:::column`. -/
structure ColumnConfig where
  /-- The column's title. -/
  title : String
  /-- `before`, `after` or empty: the color of the title. -/
  tone : String

instance : FromArgs ColumnConfig DocElabM where
  fromArgs := ColumnConfig.mk <$> .positional `title .string <*> .namedD `tone .string ""

/-- One column of a `::::columns` block. -/
@[directive]
def column : DirectiveExpanderOf ColumnConfig
  | ⟨title, tone⟩, contents => do
    unless ["", "before", "after"].contains tone do
      throwError "Unknown tone '{tone}': expected before or after"
    let body ← contents.mapM elabBlock
    ``(Verso.Doc.Block.other (SpecSite.Block.column $(quote title) $(quote tone)) #[$body,*])

/-! ## Line counts -/

/-- A group of files in a size table. -/
structure SizeGroup where
  /-- The group's name. -/
  name : String
  /-- Its files, relative to the repository root. -/
  files : List String
  /-- A short note on what the group contains. -/
  note : String := ""

/-- A table of line counts, counted when the site builds. -/
structure SizeTable where
  /-- The groups, one row each. -/
  groups : List SizeGroup
  /-- A directory, relative to the repository root, whose `.lean` files make up the last row, with
  that row's label. -/
  total : Option (String × String) := none
  /-- The sentence under the table. -/
  caption : String := ""

/-- The root of the repository that the site is built in. -/
def repoRoot : IO System.FilePath := do
  let out ← IO.Process.output { cmd := "git", args := #["rev-parse", "--show-toplevel"] }
  if out.exitCode != 0 then
    throw <| .userError "The site must be built inside the ArkLib repository"
  return out.stdout.trimAscii.copy

/-- The number of lines of a file. -/
def lineCount (path : System.FilePath) : IO Nat := do
  let s ← IO.FS.readFile path
  let n := (s.splitOn "\n").length
  return if s.endsWith "\n" then n - 1 else n

/-- The `.lean` files under a directory, recursively, sorted. -/
partial def leanFiles (dir : System.FilePath) : IO (Array System.FilePath) := do
  let mut out := #[]
  for e in ← dir.readDir do
    if ← e.path.isDir then out := out ++ (← leanFiles e.path)
    else if e.path.extension == some "lean" then out := out.push e.path
  return out.qsort (·.toString < ·.toString)

/-- The link to a file in the repository at the commit the site is built from. -/
def fileUrl (head file : String) : String :=
  if head.isEmpty then "" else s!"{repoUrl}/blob/{head}/{file}"

-- A size table. Its data holds the counted rows: name, note, files with lines, and the total.
block_extension Block.sizes (data : String) where
  data := .str data
  traverse _ _ _ := pure none
  toTeX := some fun _ _ _ data _ => do
    let .str s := data | pure .empty
    let .ok j := Json.parse s | pure .empty
    let rows := (j.getObjValAs? (Array Json) "rows").toOption.getD #[]
    let lines := rows.filterMap fun r => do
      let name ← (r.getObjValAs? String "name").toOption
      let n ← (r.getObjValAs? Nat "lines").toOption
      pure s!"{name} & {n} \\\\"
    pure <| .raw <|
      "\n\\begin{tabular}{lr}\n" ++ "\n".intercalate lines.toList ++ "\n\\end{tabular}\n"
  toHtml := some fun _ _ _ data _ => do
    let .str s := data | Verso.reportError "Expected a string for a size table" *> pure .empty
    let .ok j := Json.parse s | Verso.reportError "A size table's data is not JSON" *> pure .empty
    let rows := (j.getObjValAs? (Array Json) "rows").toOption.getD #[]
    let fmt (n : Nat) : String :=
      -- Thousands separators, as in "2,351".
      let ds := (toString n).toList.reverse
      let rec go : List Char → Nat → List Char
        | [], _ => []
        | c :: cs, i => (if i > 0 && i % 3 == 0 then [',', c] else [c]) ++ go cs (i + 1)
      String.ofList (go ds 0).reverse
    let fileHtml (f : Json) : Html := Id.run do
      let path := (f.getObjValAs? String "path").toOption.getD ""
      let url := (f.getObjValAs? String "url").toOption.getD ""
      let n := (f.getObjValAs? Nat "lines").toOption.getD 0
      let short := (path.splitOn "/").getLast!
      let label : Html := .element "code" #[("title", s!"{path}: {n} lines")] (.text short)
      if url.isEmpty then label else .element "a" #[("href", url)] label
    let rowHtml (r : Json) : Html := Id.run do
      let name := (r.getObjValAs? String "name").toOption.getD ""
      let note := (r.getObjValAs? String "note").toOption.getD ""
      let files := (r.getObjValAs? (Array Json) "files").toOption.getD #[]
      let n := (r.getObjValAs? Nat "lines").toOption.getD 0
      let total := (r.getObjValAs? Bool "total").toOption.getD false
      let filesCell : Html := if total then .text note
        else .seq (files.toList.map fileHtml |>.intersperse (.text " ")).toArray
      .element "tr" (if total then #[("class", "spec-total")] else #[]) (.seq #[
        .element "td" #[] (.seq #[.text name,
          if note.isEmpty || total then .empty
          else .element "div" #[("class", "spec-note")] (.text note)]),
        .element "td" #[] filesCell,
        .element "td" #[("class", "spec-num")] (.text (fmt n))])
    let caption := (j.getObjValAs? String "caption").toOption.getD ""
    pure <| .element "div" #[("class", "spec-sizes")] (.element "table" #[] (.seq #[
      if caption.isEmpty then .empty else .element "caption" #[] (.text caption),
      .element "thead" #[] (.element "tr" #[] (.seq #[
        .element "th" #[] (.text "Part"), .element "th" #[] (.text "Files"),
        .element "th" #[("class", "spec-num")] (.text "Lines")])),
      .element "tbody" #[] (.seq (rows.map rowHtml))]))

/-- Evaluate a constant of type `SizeTable`. -/
unsafe def evalSizeTableUnsafe (n : Name) : DocElabM SizeTable :=
  evalConstCheck SizeTable ``SizeTable n

/-- Evaluate a constant of type `SizeTable`, with the compiled code of the module that defines
it. -/
@[implemented_by evalSizeTableUnsafe]
opaque evalSizeTable (n : Name) : DocElabM SizeTable

/-- The argument of `{sizes}`: the constant that holds the table. -/
structure SizesConfig where
  /-- The table, with the identifier that named it. -/
  table : Ident × Name

instance : FromArgs SizesConfig DocElabM where
  fromArgs := SizesConfig.mk <$> .positional `table .documentableName

/-- A table of line counts, counted when the site builds. -/
@[block_command]
def sizes : BlockCommandOf SizesConfig
  | ⟨(_, n)⟩ => do
    let tbl ← evalSizeTable n
    let root ← repoRoot
    let head ← gitHead
    let mut rows : Array Json := #[]
    for g in tbl.groups do
      let mut files : Array Json := #[]
      let mut total := 0
      for f in g.files do
        let path := root / f
        unless ← path.pathExists do throwError "'{f}' does not exist (in group '{g.name}')"
        let k ← lineCount path
        total := total + k
        files := files.push <| Json.mkObj
          [("path", f), ("url", fileUrl head f), ("lines", toJson k)]
      rows := rows.push <| Json.mkObj
        [("name", g.name), ("note", g.note), ("files", Json.arr files), ("lines", toJson total)]
    if let some (label, dir) := tbl.total then
      let fs ← leanFiles (root / dir)
      let k ← fs.foldlM (init := 0) fun acc f => (acc + ·) <$> lineCount f
      rows := rows.push <| Json.mkObj [("name", label),
        ("note", s!"{fs.size} files under {dir}"), ("lines", toJson k), ("total", true)]
    let data := (Json.mkObj [("rows", Json.arr rows), ("caption", tbl.caption)]).compress
    ``(Verso.Doc.Block.other (SpecSite.Block.sizes $(quote data)) #[])

/-! ## Benchmarks -/

/-- The cells of a Markdown table row, or `none` for a line that is not a row. -/
def mdCells (line : String) : Option (List String) :=
  let l := line.trimAscii.copy
  if l.startsWith "|" && l.endsWith "|" && l.length ≥ 2 then
    some ((String.ofList (l.toList.drop 1).dropLast).splitOn "|" |>.map (·.trimAscii.copy))
  else none

-- The benchmark table. Its data is the header line of `bench.md` and the rows of its table.
block_extension Block.bench (data : String) where
  data := .str data
  traverse _ _ _ := pure none
  toTeX := some fun _ _ _ _ _ => pure .empty
  toHtml := some fun _ _ _ data _ => do
    let .str s := data | Verso.reportError "Expected a string for the bench table" *> pure .empty
    let .ok j := Json.parse s
      | Verso.reportError "The bench table's data is not JSON" *> pure .empty
    let rows := (j.getObjValAs? (Array (Array String)) "rows").toOption.getD #[]
    let head := (j.getObjValAs? (Array String) "head").toOption.getD #[]
    let note := (j.getObjValAs? String "note").toOption.getD ""
    let numeric (i : Nat) := i == 2 || i == 4
    let cell (tag : String) (i : Nat) (c : String) : Html :=
      .element tag (if numeric i then #[("class", "spec-num")] else #[]) (.text c)
    pure <| .element "div" #[("class", "spec-sizes")] (.element "table" #[] (.seq #[
      .element "caption" #[] (.text note),
      .element "thead" #[] (.element "tr" #[] (.seq (head.mapIdx fun i c => cell "th" i c))),
      .element "tbody" #[] (.seq (rows.map fun r =>
        .element "tr" #[] (.seq (r.mapIdx fun i c => cell "td" i c))))]))

/-- The benchmark table of the prototype, read from `prototypes/out/bench.md` when the site
builds. -/
@[block_command]
def bench : BlockCommandOf Unit
  | () => do
    let path := (← repoRoot) / prototypeDir / "out" / "bench.md"
    let text ← IO.FS.readFile path
    let lines := text.splitOn "\n"
    let tbl := lines.filterMap mdCells
    let some head := tbl.head? | throwError "'{path}' has no table"
    let rows := tbl.drop 1 |>.filter fun r => !r.all (·.all fun c => c == '-' || c == ':')
    if rows.isEmpty then throwError "'{path}' has no benchmark rows"
    let note := (lines.find? (·.startsWith "Generated by")).getD ""
    let data := (Json.mkObj [("head", toJson head.toArray),
      ("rows", toJson (rows.map (·.toArray)).toArray), ("note", note)]).compress
    ``(Verso.Doc.Block.other (SpecSite.Block.bench $(quote data)) #[])

/-! ## Theorems and their axioms -/

/-- The axioms that a checked theorem may depend on. -/
def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The arguments of `{theorems}`: the theorems, in the order of the table's rows. -/
structure TheoremsConfig where
  /-- The theorems, each with the identifier that named it. -/
  names : Array (Ident × Name)

instance : FromArgs TheoremsConfig DocElabM where
  fromArgs := TheoremsConfig.mk <$> (Array.mk <$> .many (.positional `name .documentableName))

/-- A table of theorems with their source and their axioms. The build fails if a theorem depends on
`sorryAx` or on a nonstandard axiom. -/
@[block_command]
def theorems : BlockCommandOf TheoremsConfig
  | ⟨names⟩ => do
    if names.isEmpty then throwError "Expected at least one theorem"
    let head ← gitHead
    let mut cells : Array Term := #[]
    for h : i in [0:3] do
      let t := #["Theorem", "Where", "Axioms"][i]
      cells := cells.push (← ``(#[Verso.Doc.Block.para #[Verso.Doc.Inline.text $(quote t)]]))
    for (id, n) in names do
      let env ← getEnv
      unless (env.find? n).any (·.isThm) do throwErrorAt id "'{n}' is not a theorem"
      let axs ← Lean.collectAxioms n
      if axs.contains ``sorryAx then throwErrorAt id "'{n}' depends on sorryAx"
      let odd := axs.filter (!standardAxioms.contains ·)
      unless odd.isEmpty do throwErrorAt id "'{n}' depends on nonstandard axioms {odd}"
      let mod ← moduleOf n
      let file := moduleFile mod
      let line ← match ← findDeclarationRanges? n with
        | some r => pure r.selectionRange.pos.line
        | none => pure 0
      let short := (file.splitOn "/").getLast!
      let where_ := if line == 0 then short else s!"{short}:{line}"
      let url := if head.isEmpty then "" else s!"{repoUrl}/blob/{head}/{file}#L{line}"
      let hl ← Verso.Genre.Manual.InlineLean.constTok n n.toString
      let axText := if axs.isEmpty then "none" else ", ".intercalate
        ((axs.qsort (·.toString < ·.toString)).toList.map (·.toString))
      let nameStr := n.toString
      cells := cells.push (← `(#[Verso.Doc.Block.para #[Verso.Doc.Inline.other
        {Verso.Genre.Manual.InlineLean.Inline.name with data := ToJson.toJson $(quote hl)}
        #[Verso.Doc.Inline.code $(quote nameStr)]]]))
      cells := cells.push (← ``(#[Verso.Doc.Block.para #[Verso.Doc.Inline.link
        #[Verso.Doc.Inline.code $(quote where_)] $(quote url)]]))
      cells := cells.push (← ``(#[Verso.Doc.Block.para #[Verso.Doc.Inline.text $(quote axText)]]))
    let items ← cells.mapM fun c => ``(Verso.Doc.ListItem.mk $c)
    ``(Verso.Doc.Block.other
        (Verso.Genre.Manual.Block.table 3 true none none)
        #[Verso.Doc.Block.ul #[$items,*]])

end SpecSite
