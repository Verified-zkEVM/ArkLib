/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Lean

/-!
# The accessor paths of a skeleton

The widget's transcript view shows, next to each move, the accessor that reaches it in Lean, such
as `tr⟦sumcheck, 1, g⟧`. The page computes these paths from the JSON skeleton. This module computes
the same paths in Lean, from the same JSON and by the same rule, so that the protocol block can
elaborate each one against the specification when the site builds. The page then shows the type
Lean gave each path, and its check on load compares its own paths with these.

The rule is Lean's (`Specs/Run.lean`, `findMove`): an accessor reads the first move, in skeleton
order, whose enclosing stages, loops and rounds contain the path's names as a subsequence and whose
name matches the label: its base, or its base with its subscript (`v_A`, `"\\alpha_2"`). A branch
case contributes `m = v` to the path but not to the subsequence test.

Each function here mirrors the function of the same name in `assets/protocol.js`.
-/

namespace SpecSite.Accessors

open Lean

/-- Symbols bound around a move: loop variables, loop counts and branch values. -/
abbrev Env := List (String × Int)

/-- The value of a symbol. -/
def Env.get? (e : Env) (k : String) : Option Int := (e.find? (·.1 == k)).map (·.2)

/-- Bind a symbol, replacing an earlier binding. -/
def Env.set (e : Env) (k : String) (v : Int) : Env := (k, v) :: e.filter (·.1 != k)

/-- A move, check or local value in transcript order, with its label context and bound symbols. -/
structure Item where
  /-- The skeleton node. -/
  node : Json
  /-- The names of the enclosing stages, loops, rounds and branch cases. -/
  ctx : Array String
  /-- The symbols bound at the node. -/
  env : Env

/-- A string field of a JSON object, or the empty string. -/
def str (j : Json) (k : String) : String := (j.getObjValAs? String k).toOption.getD ""

/-- The kind of a skeleton node. -/
def kind (j : Json) : String := str j "kind"

/-- The body of a skeleton node, or an empty array. -/
def body (j : Json) : Array Json := (j.getObjValAs? (Array Json) "body").toOption.getD #[]

/-- A JSON value as the page prints it with `${…}`: a string as itself, anything else as JSON. -/
def plain : Json → String
  | .str s => s
  | j => j.compress

/-- The items of a skeleton body in transcript order, with every loop unrolled to its count and
the branch case `caseIdx` taken (the last case if there are fewer). -/
partial def flattenGo (caseIdx : Nat) (nodes : Array Json) (ctx : Array String) (env cnt : Env) :
    StateM (Array Item) Env := do
  let mut env := env
  for n in nodes do
    match kind n with
    | "move" | "check" | "let" => modify (·.push ⟨n, ctx, env⟩)
    | "stage" => env ← flattenGo caseIdx (body n) (ctx.push (str n "name")) env cnt
    | "loop" =>
      let count := str n "count"
      let num := (cnt.get? count).getD 0
      let e := env.set count num
      for j in [0:num.toNat] do
        let _ ← flattenGo caseIdx (body n) ((ctx.push (str n "block")).push (toString j))
          (e.set (str n "var") j) cnt
      env := e
    | "branch" | "opaque" =>
      let on := n.getObjValD "on"
      modify (·.push ⟨Json.mkObj [("kind", "move"), ("move", "message"), ("owner", "prover"),
        ("name", on)], ctx, env⟩)
      if kind n == "opaque" then continue
      let cases := (n.getObjValAs? (Array Json) "cases").toOption.getD #[]
      if h : cases.size = 0 then continue
      else
        let c := cases[min caseIdx (cases.size - 1)]'(by omega)
        let v := plain (c.getObjValD "value")
        let base := str on "base"
        let hasSub := !(on.getObjValD "sub").isNull
        let cnt2 := match v.toInt? with
          | some k => if hasSub then cnt else cnt.set base k
          | none => cnt
        let _ ← flattenGo caseIdx (body c) (ctx.push s!"{base} = {v}") env cnt2
    | _ => pure ()
  return env

/-- The items of a skeleton in transcript order (see `flattenGo`). -/
def flatten (skel counts : Json) (caseIdx : Nat) : Array Item :=
  let cnt : Env := match counts with
    | .obj kvs => kvs.toList.filterMap fun (k, v) => (v.getInt?.toOption).map (k, ·)
    | _ => []
  ((flattenGo caseIdx (body skel) #[] [] cnt).run #[]).2

/-- Whether a label is written as an identifier rather than a string. -/
def isIdent (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => (c.isAlpha || c == '_') && cs.all fun c => c.isAlphanum || c == '_' || c == '\''

/-- Whether a context entry is a branch case. -/
def isCase (c : String) : Bool := (c.splitOn " = ").length > 1

/-- Drop consecutive repeats. -/
def dedupe (cs : Array String) : Array String :=
  cs.foldl (init := #[]) fun out c => if out.back? == some c then out else out.push c

/-- Whether `l` is a subsequence of `ctx`. -/
def isSubseq (l ctx : Array String) : Bool :=
  (ctx.foldl (init := 0) fun k c => if h : k < l.size then (if l[k] == c then k + 1 else k) else k)
    == l.size

/-- The subscript of a name as text, with bound symbols replaced by their values. -/
def subText (nm : Json) (env : Env) : Option String :=
  let s := nm.getObjValD "sub"
  match str s "kind" with
  | "sym" => some (str s "symbol")
  | "at" =>
    let i := s.getObjValD "index"
    match (i.getObjValAs? Int "num").toOption with
    | some k => some (toString k)
    | none =>
      let off := (i.getObjValAs? Int "offset").toOption.getD 0
      (env.get? (str i "symbol")).map fun v => toString (v + off)
  | _ => none

/-- Whether a label names a move with name `nm`. -/
def hits (nm : Json) (env : Env) (lab : String) : Bool :=
  str nm "base" == lab ||
    match subText nm env with
    | some t => lab == s!"{str nm "base"}_{t}" || lab == s!"{str nm "base"}_\{{t}}"
    | none => false

/-- The accessor of the item at `idx`, if a label path reads it. -/
def accessorFor (items : Array Item) (idx : Nat) : Option String := do
  let it ← items[idx]?
  let nm := it.node.getObjValD "name"
  let path := dedupe it.ctx
  let names := path.filter (!isCase ·)
  let first (lab : String) : Option Nat := items.findIdx? fun o =>
    kind o.node == "move" && isSubseq names (o.ctx.filter (!isCase ·)) &&
      hits (o.node.getObjValD "name") o.env lab
  let base := str nm "base"
  let labs := [some base, (subText nm it.env).map fun t => s!"{base}_{t}"].filterMap id
  let lab ← labs.find? fun lab => first lab == some idx
  let labText := if isIdent lab then lab else (Json.str lab).compress
  return "tr⟦" ++ ", ".intercalate (path.toList ++ [labText]) ++ "⟧"

/-- The first branch in a skeleton body, in the order of `firstBranch` in the page's script. -/
partial def firstBranch (nodes : Array Json) : Option Json :=
  nodes.findSome? fun n => if kind n == "branch" then some n else firstBranch (body n)

/-- The number of cases of the first branch in a skeleton body, or 1 if it has none. -/
def caseCount (nodes : Array Json) : Nat :=
  match firstBranch nodes with
  | some b => max 1 ((b.getObjValAs? (Array Json) "cases").toOption.getD #[]).size
  | none => 1

/-- Every accessor that the page's transcript view shows for a skeleton at `counts`, over every
branch case, without repeats. -/
def accessors (skel counts : Json) : Array String := Id.run do
  let mut out : Array String := #[]
  for c in [0:caseCount (body skel)] do
    let items := flatten skel counts c
    for h : i in [0:items.size] do
      if kind items[i].node == "move" then
        if let some a := accessorFor items i then
          unless out.contains a do out := out.push a
  return out

end SpecSite.Accessors
