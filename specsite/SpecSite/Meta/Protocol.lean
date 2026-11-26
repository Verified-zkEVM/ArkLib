/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VersoManual
import SpecSite.Data
import SpecSite.Meta.Accessors

/-!
# The protocol widget

`{protocols e₁ e₂ …}` shows the examples `e₁ e₂ …` (constants of type `SpecSite.Example`) in one
interactive widget with five views: the figure, the claim flow, the transcript with accessor paths,
the LaTeX source and the JSON skeleton.

The command evaluates each example when the site builds. As a result, the widget reads what Lean
computes from the specification at that moment: the JSON skeleton, the folded figure and the
expanded figure at several sizes. The page embeds this data as JSON. `assets/protocol.js` draws the
views from it, and on load it checks its own port of Lean's printer against every string Lean
produced.

The command also checks the transcript view. For every move that the view shows, at the example's
sizes and in every branch case, it computes the accessor path by the page's rule
(`SpecSite.Accessors`) and elaborates `fun tr : (s).Tr => tr⟦…⟧` against the example's
specification `s`. The build fails if Lean rejects a path. The page shows the type that Lean gave
each path, and its check on load compares its own paths with Lean's.

The TeX output of the site prints each example's folded `cryptocode` figure.
-/

namespace SpecSite

open Lean Elab
open Verso Doc Elab ArgParse
open Verso.Genre Manual
open Verso.Output (Html)

/-- The script of the widget. -/
def protocolJs : JsFile where
  filename := "specsite-protocol.js"
  defer := true
  contents := ⟨include_str "../../assets/protocol.js"⟩
  sourceMap? := none

/-- The style sheet of the widget and of the other blocks of the site. -/
def protocolCss : CssFile where
  filename := "specsite.css"
  contents := ⟨include_str "../../assets/specsite.css"⟩

/-- JSON as the text of a `<script>` element. A `<` in a string becomes `\u003c`. That way the
text cannot close the element. Outside strings, JSON has no `<`. -/
def scriptJson (j : Json) : String :=
  j.compress.replace "<" "\\u003c"

-- The widget: a placeholder that the script fills from the embedded JSON. Without JavaScript, the
-- placeholder shows each example's folded LaTeX.
block_extension Block.protocols (data : String) where
  data := .str data
  traverse _ _ _ := pure none
  toTeX := some fun _ _ _ data _ => do
    let .str s := data
      | Verso.reportError "Expected a string for the protocol widget" *> pure .empty
    let .ok (.arr exs) := Json.parse s
      | Verso.reportError "The protocol widget's data is not a JSON array" *> pure .empty
    let figs := exs.filterMap fun e => (e.getObjValAs? String "tex").toOption
    pure <| .raw ("\n".intercalate figs.toList)
  usePackages := ["\\usepackage{cryptocode}", "\\usepackage{xcolor}"]
  extraJsFiles := {protocolJs}
  extraCssFiles := {protocolCss}
  toHtml := some fun _ _ _ data _ => do
    let .str s := data
      | Verso.reportError "Expected a string for the protocol widget" *> pure .empty
    let .ok j := Json.parse s
      | Verso.reportError "The protocol widget's data is not JSON" *> pure .empty
    let fallback : Array Html := match j with
      | .arr exs => exs.filterMap fun e => do
          let tex ← (e.getObjValAs? String "tex").toOption
          pure (.element "pre" #[("class", "spec-src")] (.text tex))
      | _ => #[]
    pure <| .element "div" #[("class", "spec-widget")] (.seq #[
      .element "script" #[("type", "application/json"), ("class", "spec-widget-data")]
        (.raw (scriptJson j)),
      .element "div" #[("class", "spec-widget-fallback")] (.seq #[
        .element "p" #[] (.text "The interactive figure needs JavaScript. \
          Here is each protocol's folded figure as LaTeX."),
        .seq fallback])])

/-- The arguments of `{protocols}`: the examples, in the order of the widget's tabs. -/
structure ProtocolsConfig where
  /-- The examples, each with the identifier that named it. -/
  examples : Array (Ident × Name)

instance : FromArgs ProtocolsConfig DocElabM where
  fromArgs := ProtocolsConfig.mk <$> (Array.mk <$> .many (.positional `example .documentableName))

/-- Evaluate a constant of type `Example`. -/
unsafe def evalExampleUnsafe (n : Name) : DocElabM Example :=
  evalConstCheck Example ``Example n

/-- Evaluate a constant of type `Example`, with the compiled code of the module that defines it. -/
@[implemented_by evalExampleUnsafe]
opaque evalExample (n : Name) : DocElabM Example

/-- Elaborate a term from its text, with errors thrown rather than logged. -/
def elabText (src : String) (expected? : Option Expr := none) : TermElabM Expr := do
  let stx ← match Parser.runParserCategory (← getEnv) `term src with
    | .ok stx => pure stx
    | .error e => throwError "`{src}` does not parse: {e}"
  let saved := (← getThe Core.State).messages
  let e ← Term.withoutErrToSorry <| withEnableInfoTree false do
    let e ← Term.elabTerm stx expected?
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  let msgs := (← getThe Core.State).messages
  modifyThe Core.State fun s => { s with messages := saved }
  if msgs.hasErrors then
    let errs ← (msgs.toList.filter (·.severity == .error)).mapM (·.data.toString)
    throwError "`{src}`: {"; ".intercalate errs}"
  return e

/-- Replace each closed natural-number subterm that evaluates to a numeral by the numeral, so that
`Fin (size 2 0)` reads `Fin 16`. -/
def numerals (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun x => do
    if x.hasLooseBVars || x.hasFVar || x.hasMVar || x.nat?.isSome || x.rawNatLit?.isSome then
      return .continue
    let ty ← try Meta.inferType x catch _ => return .continue
    unless ← Meta.isDefEq ty (mkConst ``Nat) do return .continue
    let r ← Meta.whnf x
    match r.rawNatLit? <|> r.nat? with
    | some n => return .done (mkNatLit n)
    | none => return .continue)

/-- A move's type as the protocol writes it. The transcript wraps each move's type in the
interaction layer's polynomial functors (`rolePoly.B (oracleSig.toFunA (challenge ℚ))`). This
unfolds the functions of the `PFunctor` and `Interaction` namespaces at the head, and reduces a
projection at the head (`.2`, `Prod.snd`) to the field it reads, without reducing the field. It
does the same under an `Option`, and then evaluates closed numerals. -/
partial def readable (e : Expr) : MetaM Expr := do
  let e ← Meta.whnfHeadPred e fun x =>
    return x.getAppFn.constName?.any fun n =>
      (`PFunctor).isPrefixOf n || (`Interaction).isPrefixOf n
  if let .proj _ i s := e then
    if let some x ← Meta.projectCore? (← Meta.whnf s) i then return ← readable x
  if let some n := e.getAppFn.constName? then
    if let some info ← getProjectionFnInfo? n then
      let args := e.getAppArgs
      if h : info.numParams < args.size then
        if let some x ← Meta.projectCore? (← Meta.whnf args[info.numParams]) info.i then
          return ← readable (mkAppN x (args.extract (info.numParams + 1) args.size))
  if e.isAppOfArity ``Option 1 then
    return mkApp e.appFn! (← readable e.appArg!)
  numerals e

/-- The type that Lean gives the accessor `acc` on a transcript of the specification `spec`, with
its head unfolded by `readable`. -/
def accessorType (spec acc : String) : TermElabM String := do
  let e ← elabText s!"fun tr : ({spec}).Tr => {acc}"
  let ty ← Meta.inferType e
  Meta.forallBoundedTelescope ty (some 1) fun _ b => do
    if b.hasLooseBVars || b.hasExprMVar then throwError "`{acc}` has a dependent type"
    return toString (← Meta.ppExpr (← readable b))

/-- Check that an example's `spec` term has the example's skeleton, by evaluating the skeleton's
JSON from the term. -/
def checkSpec (e : Example) (skel : Json) : TermElabM Unit := do
  let src := s!"({e.spec}).skeleton.toJson {(Json.str e.key).compress} \
    {(Json.str e.title).compress}"
  let x ← elabText src (some (mkConst ``Json))
  let j ← unsafe Meta.evalExpr Json (mkConst ``Json) x
  unless j == skel do
    throwError "The example `{e.key}` names the specification `{e.spec}`, whose skeleton is not \
      the example's skeleton"

/-- Elaborate every accessor that the transcript view shows for an example, and return each with
its type, as a JSON object from accessor to type. -/
def checkAccessors (e : Example) (j : Json) : TermElabM Json := do
  let skel := j.getObjValD "skeleton"
  checkSpec e skel
  let accs := Accessors.accessors skel (j.getObjValD "counts")
  let mut out : Array (String × Json) := #[]
  let mut bad : Array MessageData := #[]
  for a in accs do
    try
      out := out.push (a, .str (← accessorType e.spec a))
    catch ex =>
      bad := bad.push m!"{a}: {ex.toMessageData}"
  unless bad.isEmpty do
    throwError "Lean rejects {bad.size} of the {accs.size} accessors that the transcript view of \
      `{e.key}` shows:{indentD (MessageData.joinSep bad.toList "\n")}"
  return Json.mkObj out.toList

/-- The interactive figure of one or more examples, computed when the site builds. -/
@[block_command]
def protocols : BlockCommandOf ProtocolsConfig
  | ⟨examples⟩ => do
    if examples.isEmpty then throwError "Expected at least one example"
    let mut out : Array Json := #[]
    for (_, n) in examples do
      let e ← evalExample n
      let j := e.toJson
      if e.spec.isEmpty then out := out.push j
      else out := out.push (j.setObjVal! "accessors" (← checkAccessors e j))
    let data := (Json.arr out).compress
    ``(Verso.Doc.Block.other (SpecSite.Block.protocols $(quote data)) #[])

end SpecSite
