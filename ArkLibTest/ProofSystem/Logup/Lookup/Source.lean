/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Lookup.Source
import ArkLib.ProofSystem.Logup.Interaction.Config
import ArkLib.Data.Probability.KoalaBear
import Mathlib.Algebra.Field.ZMod
import Lean.Compiler.IR

/-! # Actual retained multiplicities, synthetic weights and nested helper-source routing -/

open _root_.Interaction.Oracle OracleComp OracleSpec CompPoly Logup.Lookup
open Lean Elab Command

namespace LogupLookupSourceTest
abbrev F := ZMod 17
instance : Fact (Nat.Prime 17) := ⟨by decide⟩
def f : F →+* F := RingHom.id F

def data (_ : Fin 1 ⊕ Fin 1) : CMlPolynomialEval F 1 := #v[5, 7]
def mu : Vector (CMlPolynomialEval F 1) 1 := #v[#v[2, 4]]
def helpers : Vector (CMlPolynomialEval F 1) 1 := #v[#v[9, 13]]
abbrev originalAccess := (valuesFamily f 1 1 1).spec.toPFunctor
def originalHandler : QueryImpl (ofPFunctor originalAccess) Id :=
  (valuesFamily f 1 1 1).behaviorOfRealizations data
def originalView : VirtualOracle (ofPFunctor originalAccess) (valuesFamily f 1 1 1) :=
  VirtualOracle.id _
abbrev muAccess := Access.extend originalAccess (multiplicityInterface f 1 1)
def muHandler (msg : Vector (CMlPolynomialEval F 1) 1) : QueryImpl (ofPFunctor muAccess) Id :=
  Access.extendImpl originalAccess (multiplicityInterface f 1 1) originalHandler msg

theorem original_realizes : originalView.eval originalHandler =
    (valuesFamily f 1 1 1).behaviorOfRealizations data := VirtualOracle.eval_id originalHandler

/-- No lookup correctness, positivity or histogram premise restricts the retained multiplicity. -/
theorem source_realizes (msg : Vector (CMlPolynomialEval F 1) 1) :
    (weightedView f 1 1 1 originalAccess originalView).eval (muHandler msg) =
      (Logup.Interaction.inputFamily f 1 2).behaviorOfRealizations (weightedData data msg) :=
  weightedView_realizes f 1 1 1 originalAccess originalView originalHandler data
    original_realizes msg

abbrev retainedAccess := Access.extend muAccess (Logup.Interaction.helperInterface (E := F) 1 1)
def retainedHandler (msg hs : Vector (CMlPolynomialEval F 1) 1) :
    QueryImpl (ofPFunctor retainedAccess) Id :=
  Access.extendImpl muAccess (Logup.Interaction.helperInterface (E := F) 1 1) (muHandler msg) hs

def recorder (msg hs : Vector (CMlPolynomialEval F 1) 1) :
    QueryImpl (ofPFunctor retainedAccess) (StateM (List Nat)) := fun q => do
  let tag := match q with
    | .inl (.inl t) => match t.1 with | .inl _ => 0 | .inr _ => 1
    | .inl (.inr _) => 2
    | .inr _ => 3
  modify (· ++ [tag])
  return retainedHandler msg hs q

def afterHelperView : VirtualOracle (ofPFunctor retainedAccess)
    (Logup.Interaction.inputFamily f 1 2) :=
  (weightedView f 1 1 1 originalAccess originalView).substSource
    (Access.queryPrior muAccess (Logup.Interaction.helperInterface (E := F) 1 1))

def observedInput (kind : Fin 2) (column : Fin 2) : F × List Nat :=
  (simulateQ (recorder mu helpers) (afterHelperView.query ⟨(kind, column), fun _ => 2⟩)).run []

def cfg : Logup.Interaction.Config 1 2 2 := (Logup.Interaction.Config.create? 1 2 2).get (by decide)
def observedQ (msg hs : Vector (CMlPolynomialEval F 1) 1) : F × List Nat :=
  (simulateQ (recorder msg hs) (Logup.Interaction.queryQ f 1 2 1 cfg.groups 5
    (fun _ => 3) (fun _ => 3) muAccess
    (weightedView f 1 1 1 originalAccess originalView) (fun _ => 2))).run []

/-- The existing Q theorem consumes the actual combined source for every mu and every helper. -/
theorem q_realizes (msg hs : Vector (CMlPolynomialEval F 1) 1) :
    (Logup.Interaction.qView f 1 2 1 cfg.groups 5 (fun _ => 3) (fun _ => 3) 2 muAccess
      (weightedView f 1 1 1 originalAccess originalView)).eval (retainedHandler msg hs) =
      (Sumcheck.Interaction.MultivariateRound.polynomialFamily F 1 4).behaviorOfRealizations
        (fun _ => Logup.Interaction.qPolynomial f 1 2 1 cfg.groups 5 (fun _ => 3)
          (fun _ => 3) 2 cfg.length_group_le (weightedData data msg) hs) :=
  Logup.Interaction.qView_realizes f 1 2 1 cfg.groups 5 (fun _ => 3) (fun _ => 3) 2
    cfg.length_group_le muAccess (weightedView f 1 1 1 originalAccess originalView)
    (muHandler msg) (weightedData data msg) (source_realizes msg) hs

namespace Extension
abbrev B := KoalaBear.Field
abbrev E := KoalaBear.Ext6
def f : B →+* E := algebraMap B E
def data (_ : Fin 1 ⊕ Fin 1) : CMlPolynomialEval B 1 := #v[0, 1]
def mu : Vector (CMlPolynomialEval B 1) 1 := #v[#v[1, 3]]
abbrev access := (valuesFamily f 1 1 1).spec.toPFunctor
def impl : QueryImpl (ofPFunctor access) Id := (valuesFamily f 1 1 1).behaviorOfRealizations data
def view : VirtualOracle (ofPFunctor access) (valuesFamily f 1 1 1) := VirtualOracle.id _
def closed : QueryImpl (ofPFunctor (Access.extend access (multiplicityInterface f 1 1))) Id :=
  Access.extendImpl access (multiplicityInterface f 1 1) impl mu

def observedValue : E := simulateQ closed
  (queryWeighted f 1 1 1 access view 0 0 (fun _ => KoalaBear.ext6Gen))
def observedWeight : E := simulateQ closed
  (queryWeighted f 1 1 1 access view 1 1 (fun _ => KoalaBear.ext6Gen))

theorem source_realizes (msg : Vector (CMlPolynomialEval B 1) 1) :
    (weightedView f 1 1 1 access view).eval
      (Access.extendImpl access (multiplicityInterface f 1 1) impl msg) =
      (Logup.Interaction.inputFamily f 1 2).behaviorOfRealizations (weightedData data msg) :=
  weightedView_realizes f 1 1 1 access view impl data (VirtualOracle.eval_id impl) msg
end Extension

run_cmd do
  unless observedInput 0 0 == (9, [0]) do throwError "query value lost original source provenance"
  unless observedInput 0 1 == (9, [1]) do throwError "table value lost original source provenance"
  unless observedInput 1 0 == (1, []) do throwError "synthetic unit weight opened a source"
  unless observedInput 1 1 == (11, [2]) do
    throwError "table weight opened newest helper rather than retained prior multiplicity"
  unless observedQ mu helpers == (13, [0, 1, 2, 3]) do
    throwError "composed Q source changed signed reconstruction or source query order"
  unless observedQ mu #v[#v[1, 1]] == (7, [0, 1, 2, 3]) do
    throwError "composed Q source ignored the actual changed helper"
  unless observedQ #v[#v[0, 0]] helpers == (11, [0, 1, 2, 3]) do
    throwError "composed Q source ignored the actual changed multiplicity"
  unless KoalaBear.Ext6.coeffsEquiv.symm Extension.observedValue == #v[0, 1, 0, 0, 0, 0] do
    throwError "base value source was not evaluated at non-base theta"
  unless KoalaBear.Ext6.coeffsEquiv.symm Extension.observedWeight == #v[-1, -2, 0, 0, 0, 0] do
    throwError "base multiplicity MLE did not map and negate before extension-field reconstruction"

run_cmd do
  for name in #[``valuesFamily, ``multiplicityInterface, ``queryWeighted, ``weightedView,
      ``recorder, ``afterHelperView, ``observedInput, ``observedQ,
      ``Extension.observedValue, ``Extension.observedWeight] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "missing actual lookup source executable IR: {name}"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``weightedView_realizes, ``original_realizes, ``source_realizes, ``q_realizes,
      ``Extension.source_realizes] do
    unless (← collectAxioms name).all allowed.contains do
      throwError "lookup source has an unexpected axiom: {name}"

end LogupLookupSourceTest
