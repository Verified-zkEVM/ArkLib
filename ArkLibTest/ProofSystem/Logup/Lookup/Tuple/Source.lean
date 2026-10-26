/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import ArkLib.ProofSystem.Logup.Lookup.Tuple.Source
import ArkLib.ProofSystem.Logup.Interaction.Config
import ArkLib.Data.Probability.KoalaBear
import Mathlib.Algebra.Field.ZMod
import Lean.Compiler.IR

/-! # Stored tuple coefficients, off-cube interpolation and retained multiplicity/helper slots -/

open _root_.Interaction.Oracle OracleComp OracleSpec CompPoly Logup.Lookup Logup.Lookup.Tuple
open Lean Elab Command
namespace LogupTupleSourceTest
abbrev F := ZMod 17
instance : Fact (Nat.Prime 17) := ⟨by decide⟩
def f : F →+* F := RingHom.id F

def schema : TaggedTuple.Schema F 2 2 :=
  (TaggedTuple.Schema.mk? #v[2, 1] #v[2, 3]).get (by decide)
def layout : ProviderLayout 2 2 := (ProviderLayout.create? 2 2 #[0, 1]).get (by decide)
def keys : Vector (CMlPolynomialEval schema.Key 1) 3 :=
  #v[#v[⟨0, #v[0, 1]⟩, ⟨1, #v[0]⟩],
    #v[⟨0, #v[0, 0]⟩, ⟨0, #v[0, 0]⟩],
    #v[⟨1, #v[0]⟩, ⟨1, #v[0]⟩]]
def prepared : PreparedProvider schema layout 1 1 :=
  PreparedProvider.prepare schema layout keys (by decide)
def mu : Vector (CMlPolynomialEval F 1) 2 := #v[#v[0, 0], #v[2, 0]]
def helpers : Vector (CMlPolynomialEval F 1) 2 := #v[#v[9, 13], #v[4, 6]]
abbrev originalAccess := (coefficientFamily f 1 1 2 2).spec.toPFunctor
def impl : QueryImpl (ofPFunctor originalAccess) Id :=
  (coefficientFamily f 1 1 2 2).behaviorOfRealizations
    (fun sj => prepared.coefficientTable sj.1 sj.2)
def view : VirtualOracle (ofPFunctor originalAccess) (coefficientFamily f 1 1 2 2) :=
  VirtualOracle.id _
abbrev muAccess := Access.extend originalAccess (multiplicityInterface f 1 2)
def muHandler (msg : Vector (CMlPolynomialEval F 1) 2) : QueryImpl (ofPFunctor muAccess) Id :=
  Access.extendImpl originalAccess (multiplicityInterface f 1 2) impl msg

/-- The genuine coefficient source realizes compressed weighted data for every beta and mu. -/
theorem source_realizes (beta : F) (msg : Vector (CMlPolynomialEval F 1) 2) :
    (Tuple.weightedView f 1 1 2 2 beta originalAccess view).eval (muHandler msg) =
      (Logup.Interaction.inputFamily f 1 3).behaviorOfRealizations
        (prepared.weightedData f beta msg) :=
  Tuple.weightedView_realizes prepared f beta originalAccess view impl
    (VirtualOracle.eval_id impl) msg

abbrev retainedAccess := Access.extend muAccess (Logup.Interaction.helperInterface (E := F) 1 2)
def retainedHandler (msg hs : Vector (CMlPolynomialEval F 1) 2) :
    QueryImpl (ofPFunctor retainedAccess) Id :=
  Access.extendImpl muAccess (Logup.Interaction.helperInterface (E := F) 1 2) (muHandler msg) hs

def recorder (msg hs : Vector (CMlPolynomialEval F 1) 2) :
    QueryImpl (ofPFunctor retainedAccess) (StateM (List Nat)) := fun q => do
  let tag := match q with
    | .inl (.inl t) => (finSumFinEquiv t.1.1).val * 3 + t.1.2.val
    | .inl (.inr t) => 100 + t.1.val
    | .inr t => 200 + t.1.val
  modify (· ++ [tag])
  return retainedHandler msg hs q

def afterHelperView : VirtualOracle (ofPFunctor retainedAccess)
    (Logup.Interaction.inputFamily f 1 3) :=
  (Tuple.weightedView f 1 1 2 2 3 originalAccess view).substSource
    (Access.queryPrior muAccess (Logup.Interaction.helperInterface (E := F) 1 2))
def observedInput (kind : Fin 2) (column : Fin 3) : F × List Nat :=
  (simulateQ (recorder mu helpers) (afterHelperView.query ⟨(kind, column), fun _ => 2⟩)).run []
def cfg : Logup.Interaction.Config 1 3 2 := (Logup.Interaction.Config.create? 1 3 2).get (by decide)
def observedQ (msg hs : Vector (CMlPolynomialEval F 1) 2) : F × List Nat :=
  (simulateQ (recorder msg hs) (Logup.Interaction.queryQ f 1 3 2 cfg.groups 5
    (fun _ => 3) (fun _ => 3) muAccess
    (Tuple.weightedView f 1 1 2 2 3 originalAccess view) (fun _ => 2))).run []

/-- The existing Q theorem opens these exact prior coefficients/mu and the newest helpers. -/
theorem q_realizes (beta : F) (msg hs : Vector (CMlPolynomialEval F 1) 2) :
    (Logup.Interaction.qView f 1 3 2 cfg.groups 5 (fun _ => 3) (fun _ => 3) 2 muAccess
      (Tuple.weightedView f 1 1 2 2 beta originalAccess view)).eval (retainedHandler msg hs) =
      (Sumcheck.Interaction.MultivariateRound.polynomialFamily F 1 4).behaviorOfRealizations
        (fun _ => Logup.Interaction.qPolynomial f 1 3 2 cfg.groups 5 (fun _ => 3)
          (fun _ => 3) 2 cfg.length_group_le (prepared.weightedData f beta msg) hs) :=
  Logup.Interaction.qView_realizes f 1 3 2 cfg.groups 5 (fun _ => 3) (fun _ => 3) 2
    cfg.length_group_le muAccess (Tuple.weightedView f 1 1 2 2 beta originalAccess view)
    (muHandler msg) (prepared.weightedData f beta msg) (source_realizes beta msg) hs

namespace Extension
abbrev B := KoalaBear.Field
abbrev E := KoalaBear.Ext6
def f : B →+* E := algebraMap B E
def schema : TaggedTuple.Schema B 2 2 :=
  (TaggedTuple.Schema.mk? #v[2, 1] #v[2, 3]).get (by decide)
def keys : Vector (CMlPolynomialEval schema.Key 1) 3 :=
  #v[#v[⟨0, #v[0, 1]⟩, ⟨1, #v[0]⟩],
    #v[⟨0, #v[0, 0]⟩, ⟨0, #v[0, 0]⟩],
    #v[⟨1, #v[0]⟩, ⟨1, #v[0]⟩]]
def prepared : PreparedProvider schema layout 1 1 :=
  PreparedProvider.prepare schema layout keys (by decide)
abbrev access := (coefficientFamily f 1 1 2 2).spec.toPFunctor
def impl : QueryImpl (ofPFunctor access) Id :=
  (coefficientFamily f 1 1 2 2).behaviorOfRealizations
    (fun sj => prepared.coefficientTable sj.1 sj.2)
def view : VirtualOracle (ofPFunctor access) (coefficientFamily f 1 1 2 2) :=
  VirtualOracle.id _
def observedValue : E := simulateQ impl
  (queryValue f 1 1 2 2 KoalaBear.ext6Gen access view (.inl 0) (fun _ => KoalaBear.ext6Gen))

theorem source_realizes (beta : E) (msg : Vector (CMlPolynomialEval B 1) 2) :
    (Tuple.weightedView f 1 1 2 2 beta access view).eval
      (Access.extendImpl access (multiplicityInterface f 1 2) impl msg) =
      (Logup.Interaction.inputFamily (RingHom.id E) 1 3).behaviorOfRealizations
        (prepared.weightedData f beta msg) :=
  Tuple.weightedView_realizes prepared f beta access view impl (VirtualOracle.eval_id impl) msg
end Extension

run_cmd do
  unless CMlPolynomialEval.eval₂Mle (prepared.coefficientTable (.inl 0) 2) f #v[2] == 4 &&
      CMlPolynomialEval.eval₂Mle (prepared.coefficientTable (.inl 0) 1) f #v[2] == -1 do
    throwError "off-cube coefficient source replaced varying tag/payload with a semantic key"
  unless observedInput 0 0 == (16, [0, 1, 2]) do
    throwError "tuple source did not open each original coefficient once in power order"
  unless observedInput 0 1 == (1, [3, 4, 5]) &&
      observedInput 0 2 == (10, [6, 7, 8]) do
    throwError "tuple source lost declared table-piece order or zero padding"
  unless observedInput 1 0 == (1, []) && observedInput 1 1 == (0, [100]) &&
      observedInput 1 2 == (2, [101]) do
    throwError "tuple weights did not use exact retained base multiplicities"
  let trace := [0, 1, 2, 3, 4, 5, 6, 7, 8, 100, 101, 200, 201]
  unless observedQ mu helpers == (9, trace) do
    throwError "tuple Q changed scalar reconstruction or nested source order"
  unless observedQ mu #v[#v[1, 1], #v[1, 1]] == (8, trace) do
    throwError "tuple Q ignored the newest helper source"
  unless observedQ #v[#v[0, 0], #v[0, 0]] helpers == (6, trace) do
    throwError "tuple Q substituted same-shaped helper data for retained multiplicities"
  unless KoalaBear.Ext6.coeffsEquiv.symm Extension.observedValue == #v[0, 1, 1, 1, 0, 0] do
    throwError "tuple source failed actual base-to-extension coefficient MLE/Horner evaluation"

run_cmd do
  for name in #[``coefficientFamily, ``queryValue, ``valuesView,
      ``PreparedProvider.fingerprintData, ``PreparedProvider.weightedData,
      ``Tuple.queryWeighted, ``Tuple.weightedView, ``observedInput, ``observedQ,
      ``Extension.observedValue] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "missing tuple source executable IR: {name}"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``queryValue_eval, ``valuesView_realizes, ``Tuple.weightedView_realizes,
      ``source_realizes, ``q_realizes, ``Extension.source_realizes] do
    unless (← collectAxioms name).all allowed.contains do
      throwError "tuple source has an unexpected axiom: {name}"
end LogupTupleSourceTest
