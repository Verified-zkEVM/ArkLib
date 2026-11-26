/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Specs.Core
import Lean.Data.Json

/-!
# Exporting a skeleton

This module turns the skeleton of a specification into data and into a figure. The examples call
`writeExample` from their `main`.

* `Skel.toJson` writes the skeleton as JSON with schema `arklib-protocol-skeleton/1`.
* `Skel.toTex` writes a `cryptocode` figure, folded (one round of each block, with round variable
  `i`) or expanded (every round, with its number).
* `writeExample dir name title ks` writes `name.json`, `name.tex` (folded) and
  `name-expanded.tex`.

## The JSON schema

```
{ "schema": "arklib-protocol-skeleton/1", "name", "title", "body": [node] }
node     = { "kind": "move", "move": "message" | "oracle" | "challenge",
             "owner": "prover" | "verifier", "name": name, "type", "honest": note, "note": note }
         | { "kind": "input", "name": name, "type" }
         | { "kind": "check", "label", "formula": formula, "note": note }
         | { "kind": "let", "name": name, "type", "formula": formula, "note": note }
         | { "kind": "stage", "name", "input": formula, "output": formula, "body": [node] }
         | { "kind": "round", "block", "round", "count", "countName", "error": note,
             "body": [node] }
         | { "kind": "branch", "on": name, "type", "honest": note,
             "cases": [ { "value", "body": [node] } ] }
         | { "kind": "opaque", "on": name, "type", "honest": note }
         | { "kind": "end", "of": "stage" | "round" }
name     = { "base", "sub": null | { "kind": "at" | "below", "index": index }
                           | { "kind": "sym", "symbol" }, "tex" }
index    = { "round": k } | { "num": k } | { "count": k, "symbol" }
formula  = { "syntax": syn, "tex" }
syn      = { "op": "var", "name": name } | { "op": "lit", "tex" }
         | { "op": "add" | "sub" | "mul" | "eq" | "and" | "neg", "args": [syn] }
         | { "op": "pow", "exp", "args": [syn] }
         | { "op": "sum" | "prod", "var": name, "domain", "body": syn }
         | { "op": "query", "oracle": name, "arg": syn } | { "op": "app", "fn", "arg": syn }
         | { "op": "index", "args": [syn, syn] }
note     = null | { "text", "checked": false }
```

A `round` index is the absolute round of its block, so a consumer can render it folded or
expanded as `Name.tex` does. Every `"tex"` field is the expanded rendering.

## Design choices

* The JSON nests stages and rounds, while the skeleton in `Specs.Core` keeps flat begin and end
  markers. *Why:* a consumer reads a stage or a round as one node with its body, and the skeleton
  stays a simple list that `simp` and `rfl` reduce.
* A branch ends the sequence it occurs in, and each case continues the rest of the protocol. An
  end marker inside a case whose stage or round opened before the branch stays a node of kind
  `end`. *Why:* the case's skeleton is the rest of the protocol, so the stage or round closes in
  every case, and the export does not guess where.
* Every annotation (a move's note, the name of an honest function, a block's error) exports as
  `{"text": …, "checked": false}` and prints with `\specannot`, which the figure defines in gray.
  *Why:* nothing in Lean checks this text, unlike the formulas of checks, local values and claims,
  which come from the checked term.
* The folded figure prints the first round of each block, with the round as `i` and the round
  count as its symbol, and skips the later rounds of that block. *Why:* a paper shows one generic
  round, and the names in the skeleton carry the absolute round, so `Name.tex` prints `g_i`,
  `c_{i+1}` and, after the block, `c_n`.
* The folded figure identifies a block by its stage path and its name. *Why:* two stages may run
  the same block (Spartan's `outer` and `inner` both run `sumcheck`), and each stage's rounds
  belong in the figure.
* A stage prints its input claim where it opens and its output claim where it closes. *Why:* the
  output claim names values of the block's last round, which the folded figure prints with the
  round count only after the block.
-/

set_option linter.hashCommand false

namespace Specs
open Lean (Json)

/-! ## JSON -/

/-- An index as JSON: a round of a block or a fixed number. -/
def Ix.toJson : Ix → Json
  | .rnd k => Json.mkObj [("round", Lean.toJson k)]
  | .num k => Json.mkObj [("num", Lean.toJson k)]
  | .count k sym => Json.mkObj [("count", Lean.toJson k), ("symbol", sym)]

/-- A subscript as JSON. -/
def Subscript.toJson : Subscript → Json
  | .none => Json.null
  | .at e => Json.mkObj [("kind", "at"), ("index", e.toJson)]
  | .below e => Json.mkObj [("kind", "below"), ("index", e.toJson)]
  | .sym s => Json.mkObj [("kind", "sym"), ("symbol", s)]

/-- A name as JSON, with its expanded TeX. -/
def Name.toJson (nm : Name) : Json :=
  Json.mkObj [("base", nm.base), ("sub", nm.sub.toJson), ("tex", nm.tex Mode.expanded)]

/-- The JSON name of an operation. -/
def BinOp.name : BinOp → String
  | .add => "add"
  | .sub => "sub"
  | .mul => "mul"
  | .eq => "eq"
  | .and => "and"

/-- A syntax tree as JSON. -/
def Syn.toJson : Syn → Json
  | .var nm => Json.mkObj [("op", "var"), ("name", nm.toJson)]
  | .lit t => Json.mkObj [("op", "lit"), ("tex", t)]
  | .bin op a b => Json.mkObj [("op", op.name), ("args", Json.arr #[a.toJson, b.toJson])]
  | .neg a => Json.mkObj [("op", "neg"), ("args", Json.arr #[a.toJson])]
  | .pow a k => Json.mkObj [("op", "pow"), ("exp", Lean.toJson k), ("args", Json.arr #[a.toJson])]
  | .sum x dom body => Json.mkObj [("op", "sum"), ("var", x.toJson), ("domain", dom),
      ("body", body.toJson)]
  | .query h q => Json.mkObj [("op", "query"), ("oracle", h.toJson), ("arg", q.toJson)]
  | .app name x => Json.mkObj [("op", "app"), ("fn", name), ("arg", x.toJson)]
  | .prod x dom body => Json.mkObj [("op", "prod"), ("var", x.toJson), ("domain", dom),
      ("body", body.toJson)]
  | .index f i => Json.mkObj [("op", "index"), ("args", Json.arr #[f.toJson, i.toJson])]

/-- A formula as JSON: its syntax tree and its expanded TeX. -/
def Syn.toFormulaJson (φ : Syn) : Json :=
  Json.mkObj [("syntax", φ.toJson), ("tex", φ.tex Mode.expanded)]

/-- Annotation text as JSON. Nothing checks it, so it carries `"checked": false`. Empty text is
`null`. -/
def annotationJson (s : String) : Json :=
  if s.isEmpty then Json.null else Json.mkObj [("text", s), ("checked", false)]

/-- The JSON name of a move kind. -/
def MoveKind.name : MoveKind → String
  | .message => "message"
  | .oracle => "oracle"
  | .challenge => "challenge"

/-- The party that sends a move. -/
def MoveKind.owner : MoveKind → String
  | .challenge => "verifier"
  | _ => "prover"

/-- An item as a JSON node. A begin marker becomes a node without its body. -/
def Item.toJson : Item → Json
  | .move k nm ty hn note => Json.mkObj [("kind", "move"), ("move", k.name),
      ("owner", k.owner), ("name", nm.toJson), ("type", ty), ("honest", annotationJson hn),
      ("note", annotationJson note)]
  | .input nm ty => Json.mkObj [("kind", "input"), ("name", nm.toJson), ("type", ty)]
  | .check label φ note => Json.mkObj [("kind", "check"), ("label", label),
      ("formula", φ.toFormulaJson), ("note", annotationJson note)]
  | .let_ nm ty φ note => Json.mkObj [("kind", "let"), ("name", nm.toJson), ("type", ty),
      ("formula", φ.toFormulaJson), ("note", annotationJson note)]
  | .beginRound b i count cn err => Json.mkObj [("kind", "round"), ("block", b),
      ("round", Lean.toJson i), ("count", Lean.toJson count), ("countName", cn),
      ("error", annotationJson err)]
  | .endRound => Json.mkObj [("kind", "end"), ("of", "round")]
  | .beginStage name φ ψ => Json.mkObj [("kind", "stage"), ("name", name),
      ("input", φ.toFormulaJson), ("output", ψ.toFormulaJson)]
  | .endStage => Json.mkObj [("kind", "end"), ("of", "stage")]

/-- An open stage or round while the export nests the items: its node and its children so far.
The bottom frame of a stack is the root, with node `null`. -/
structure Frame where
  /-- The node of the stage or round. -/
  node : Json
  /-- The children so far. -/
  kids : Array Json := #[]

/-- The root frame. -/
def Frame.root : Frame := { node := Json.null }

/-- The node of a frame with its children as its body. -/
def Frame.closed (f : Frame) : Json := f.node.setObjVal! "body" (Json.arr f.kids)

/-- Add a child to the innermost frame. -/
def Frame.add (j : Json) : List Frame → List Frame
  | [] => [{ Frame.root with kids := #[j] }]
  | f :: fs => { f with kids := f.kids.push j } :: fs

/-- Close the innermost frame into its parent. With only the root open, the end marker becomes a
node of its own. -/
def Frame.close (marker : Json) : List Frame → List Frame
  | f :: g :: fs => Frame.add f.closed (g :: fs)
  | stack => Frame.add marker stack

/-- Process one item: open, close or add to the innermost frame. -/
def Frame.push (stack : List Frame) (it : Item) : List Frame :=
  match it with
  | .beginRound .. | .beginStage .. => { node := it.toJson } :: stack
  | .endRound | .endStage => Frame.close it.toJson stack
  | _ => Frame.add it.toJson stack

/-- Close `f` and every frame below it, and return the children of the root. -/
def Frame.closeAll (f : Frame) : List Frame → Array Json
  | [] => f.kids
  | g :: fs => Frame.closeAll { g with kids := g.kids.push f.closed } fs

/-- Close every open frame and return the children of the root. -/
def Frame.finish : List Frame → Array Json
  | [] => #[]
  | f :: fs => f.closeAll fs

mutual
/-- The nodes of a skeleton, nested by stage and round, inside the open frames `stack`. -/
def Skel.nodes (stack : List Frame) : Skel → Array Json
  | .done => Frame.finish stack
  | .cons it rest => rest.nodes (Frame.push stack it)
  | .branch nm ty hn cases => Frame.finish (Frame.add (Json.mkObj [("kind", "branch"),
      ("on", nm.toJson), ("type", ty), ("honest", annotationJson hn),
      ("cases", Json.arr (Skel.casesNodes cases).toArray)]) stack)
  | .opaque nm ty hn => Frame.finish (Frame.add (Json.mkObj [("kind", "opaque"),
      ("on", nm.toJson), ("type", ty), ("honest", annotationJson hn)]) stack)

/-- The cases of a branch as JSON, each with the nodes of its skeleton. -/
def Skel.casesNodes : List (String × Skel) → List Json
  | [] => []
  | (v, k) :: cs =>
    Json.mkObj [("value", v), ("body", Json.arr (k.nodes [Frame.root]))] :: Skel.casesNodes cs
end

/-- The skeleton as JSON with schema `arklib-protocol-skeleton/1`. -/
def Skel.toJson (name title : String) (ks : Skel) : Json :=
  Json.mkObj [("schema", "arklib-protocol-skeleton/1"), ("name", name), ("title", title),
    ("body", Json.arr (ks.nodes [Frame.root]))]

/-! ## The figure -/

/-- The state of the figure while the export walks the skeleton. -/
structure TexState where
  /-- The mode that names render in. -/
  mode : Mode
  /-- The blocks whose first round the folded figure already shows, each as its stage path and
  name (`outer/sumcheck`). -/
  shown : List String := []
  /-- The depth of skipped rounds: positive while the folded figure skips a round. -/
  skip : ℕ := 0
  /-- The displayed round outside each open round, to restore at its end. -/
  rounds : List (Option ℕ) := []
  /-- The open stages, with their output claims. -/
  stages : List (String × Syn) := []
  /-- Divisions that open before the next line. -/
  pending : Array String := #[]
  /-- The lines so far, each with the division that opens before it. -/
  lines : Array (Option String × String) := #[]

/-- Annotation text in the figure: gray, with `\specannot`. -/
def texAnnot (s : String) : String := "\\specannot{" ++ s ++ "}"

/-- Append a note to a line, if there is one. -/
def withNote (line note : String) : String :=
  if note.isEmpty then line else line ++ " \\quad " ++ texAnnot note

namespace TexState

/-- Add a line, with the pending divisions before it. -/
def emit (st : TexState) (line : String) : TexState :=
  let div := if st.pending.isEmpty then none else some (String.intercalate "; " st.pending.toList)
  { st with lines := st.lines.push (div, line), pending := #[] }

/-- Add a division before the next line. -/
def divide (st : TexState) (d : String) : TexState := { st with pending := st.pending.push d }

/-- Print the pending divisions on an empty line. -/
def flush (st : TexState) : TexState := if st.pending.isEmpty then st else st.emit " \\< \\< "

/-- The line of a move. The prover's column names the honest function, as annotation text. -/
def moveLine (m : Mode) (k : MoveKind) (nm : Name) (ty hn note : String) : String :=
  let n := nm.tex m
  let prover := if hn.isEmpty then "" else n ++ " \\gets " ++ texAnnot hn
  withNote (match k with
    | .message => prover ++ " \\< \\sendmessageright*{" ++ n ++ " \\in " ++ ty ++ "} \\< "
    | .oracle => prover ++ " \\< \\sendmessageright*{[\\![" ++ n ++ "]\\!] \\in " ++ ty ++
        "} \\< "
    | .challenge => " \\< \\sendmessageleft*{" ++ n ++ "} \\< " ++ n ++ " \\sample " ++ ty) note

/-- Process one item. -/
def item (st : TexState) (it : Item) : TexState :=
  if st.skip > 0 then
    match it with
    | .beginRound .. => { st with skip := st.skip + 1 }
    | .endRound => { st with skip := st.skip - 1 }
    | _ => st
  else
    let m := st.mode
    match it with
    | .move k nm ty hn note => st.emit (moveLine m k nm ty hn note)
    | .input nm ty =>
      st.emit (" \\< \\< \\text{input oracle } [\\![" ++ nm.tex m ++ "]\\!] \\in " ++ ty)
    | .check _ φ note => st.emit (withNote (" \\< \\< \\text{check } " ++ φ.tex m) note)
    | .let_ nm _ φ note => st.emit (withNote (" \\< \\< " ++ nm.tex m ++ " := " ++ φ.tex m) note)
    | .beginRound b i count cn err =>
      if m.folded then
        let key := String.intercalate "/" ((st.stages.map (·.1)).reverse ++ [b])
        if st.shown.contains key then { st with skip := 1 }
        else
          let err := if err.isEmpty then "" else "; error $" ++ texAnnot err ++ "$"
          let st := st.divide ("\\textsf{" ++ b ++ "}: round $" ++ m.var ++ "$ of $" ++ cn ++
            "$" ++ err)
          { st with shown := key :: st.shown, rounds := m.round :: st.rounds,
                    mode := { m with round := some i, counts := (count, cn) :: m.counts } }
      else
        let st := st.divide ("\\textsf{" ++ b ++ "}: round " ++ toString i)
        { st with rounds := m.round :: st.rounds }
    | .endRound =>
      match st.rounds with
      | r :: rs => { st with rounds := rs, mode := { m with round := r } }
      | [] => st
    | .beginStage name φ ψ =>
      { st.divide ("stage \\textsf{" ++ name ++ "}: $" ++ φ.tex m ++ "$") with
        stages := (name, ψ) :: st.stages }
    | .endStage =>
      match st.stages with
      | (name, ψ) :: ss =>
        { st.divide ("end of stage \\textsf{" ++ name ++ "}: $" ++ ψ.tex m ++ "$") with
          stages := ss }
      | [] => st

end TexState

mutual
/-- Walk a skeleton for the figure. -/
def Skel.texGo (st : TexState) : Skel → TexState
  | .done => st.flush
  | .cons it rest => rest.texGo (st.item it)
  | .branch nm ty hn cases =>
    Skel.texCases nm (st.emit (TexState.moveLine st.mode .message nm ty hn "")) cases
  | .opaque nm ty hn =>
    (st.emit (TexState.moveLine st.mode .message nm ty hn "")).emit
      (" \\< \\< \\text{the rest depends on } " ++ nm.tex st.mode)

/-- Walk the cases of a branch on `nm`, each from the state at the branch. -/
def Skel.texCases (nm : Name) (st : TexState) : List (String × Skel) → TexState
  | [] => st
  | (v, k) :: cs =>
    let st' := k.texGo (st.divide ("case $" ++ nm.tex st.mode ++ " = " ++ v ++ "$"))
    Skel.texCases nm { st with lines := st'.lines } cs
end

/-- The `cryptocode` figure of a skeleton, folded or expanded. A dotted division opens each
stage, round and case. `cryptocode` needs `\pclb` instead of `\\` before a division. -/
def Skel.toTex (title : String) (folded : Bool) (ks : Skel) : String :=
  let st := ks.texGo { mode := { folded := folded } }
  let lines := #[(none, "\\textbf{Prover} \\< \\< \\textbf{Verifier}")] ++ st.lines
  let body := (List.range lines.size).map fun k =>
    let (div, line) := lines[k]!
    let pre := match div with
      | some d => "\\pcintertext[dotted]{" ++ d ++ "}\n"
      | none => ""
    let post := if k + 1 == lines.size then ""
      else if (lines[k + 1]!).1.isSome then " \\pclb" else " \\\\"
    pre ++ line ++ post
  "% Generated by docs/design/interaction-layer/prototypes/Specs/Export.lean.\n" ++
    "% Requires \\usepackage{amsmath,amssymb} and \\usepackage{cryptocode}.\n" ++
    "\\providecommand{\\specannot}[1]{\\textcolor{gray}{#1}}\n" ++
    "\\begin{figure}\n\\centering\n\\procedure{" ++ title ++ "}{%\n" ++
    String.intercalate "\n" body ++
    "\n}\n\\caption{" ++ title ++ (if folded then ", one round of each block" else "") ++
    ", generated from the skeleton. Gray text is annotation that Lean does not check.}\n" ++
    "\\end{figure}\n"

/-- Write the JSON file and the folded and expanded figures of one example into `dir`. -/
def writeExample (dir : System.FilePath) (name title : String) (ks : Skel) : IO Unit := do
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir / (name ++ ".json")) ((ks.toJson name title).pretty ++ "\n")
  IO.FS.writeFile (dir / (name ++ ".tex")) (ks.toTex title true)
  IO.FS.writeFile (dir / (name ++ "-expanded.tex")) (ks.toTex title false)

/-! ## Tests -/

/-- A test skeleton: a stage with a two-round block of one oracle message, one challenge and one
check, with a note on the challenge. -/
private def testSkel : Skel :=
  let round (i : ℕ) (rest : Skel) : Skel :=
    .cons (.beginRound "loop" i 2 "n" "1/|F|") <|
    .cons (.move .oracle (ix "g" i) "R[X]" "\\mathsf{f}" "") <|
    .cons (.move .challenge (ix "r" i) "R" "" "uniform") <|
    .cons (.check "eq" (.bin .eq (.query (ix "g" i) (.var (ix "r" i))) (.var (ix "c" i))) "") <|
    .cons .endRound rest
  .cons (.beginStage "s" (.var (ix "c" 0)) (.var (ix "c" 2))) <|
    round 0 <| round 1 <| .cons .endStage .done

/-- Two stages that run the same one-round block `loop`. -/
private def testTwoStages : Skel :=
  let stage (s : String) (rest : Skel) : Skel :=
    .cons (.beginStage s (.var (ix "c" 0)) (.var (ix "c" 1))) <|
    .cons (.beginRound "loop" 0 1 "n" "") <|
    .cons (.move .challenge (ix "r" 0) "R" "" "") <|
    .cons .endRound <| .cons .endStage rest
  stage "a" <| stage "b" .done

/-- The number of occurrences of `pat` in `s`. -/
private def occurrences (s pat : String) : ℕ := (s.splitOn pat).length - 1

/-- The kind of the first node of the JSON body. -/
private def firstKind (j : Json) : Option String :=
  match (j.getObjValD "body").getArrVal? 0 with
  | .ok n => (n.getObjValD "kind").getStr?.toOption
  | .error _ => none

#guard firstKind (testSkel.toJson "t" "T") == some "stage"
#guard occurrences (testSkel.toJson "t" "T").compress "\"checked\":false" == 6
#guard occurrences (testSkel.toJson "t" "T").compress "\"kind\":\"round\"" == 2
#guard occurrences (testSkel.toTex "T" true) "\\text{check } g_{i}(r_{i}) = c_{i}" == 1
#guard occurrences (testSkel.toTex "T" true) "end of stage \\textsf{s}: $c_{n}$" == 1
#guard occurrences (testSkel.toTex "T" true) "\\specannot{uniform}" == 1
#guard occurrences (testSkel.toTex "T" false) "\\text{check } g_{1}(r_{1}) = c_{1}" == 1
#guard occurrences (testSkel.toTex "T" false) "\\specannot{uniform}" == 2
#guard occurrences (testTwoStages.toTex "T" true) "\\textsf{loop}: round $i$" == 2

#print axioms Skel.toJson
#print axioms Skel.toTex

end Specs
