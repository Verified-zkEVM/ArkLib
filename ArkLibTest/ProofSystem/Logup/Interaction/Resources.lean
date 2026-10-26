/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import ArkLib.ProofSystem.Logup.Interaction.Resources
import ArkLibTest.ProofSystem.Logup.Interaction.Source
import ArkLibTest.ProofSystem.Logup.Lookup.Source
import ArkLibTest.ProofSystem.Logup.Lookup.Tuple.Source
import Lean.Compiler.IR

/-! # Actual source fanout, retained provenance and selected local kernel profiles -/

open Interaction.Oracle OracleComp OracleSpec CompPoly
open Logup.Interaction.Resources
namespace SourceResourcesTests
namespace Weighted
open Logup.Interaction.SourceTest

def logged := simulateQ (retainedHandler helpers)
  (Logup.Interaction.queryQ embedding 1 1 1 groups 0 (fun _ => 0) (fun _ => 1)
    originalAccess originalView (fun _ => KoalaBear.ext6Gen)).withQueryLog

theorem count : logged.2.length = 3 :=
  queryQ_identity_log_length embedding 1 1 1 groups 0 (fun _ => 0) (fun _ => 1)
    originalHandler helpers (fun _ => KoalaBear.ext6Gen)

def zeroLogged := simulateQ ZeroRows.retainedHandler
  (Logup.Interaction.queryQ embedding 0 1 1 ZeroRows.groups 3 Fin.elim0 (fun _ => 5)
    ZeroRows.originalAccess ZeroRows.originalView Fin.elim0).withQueryLog

theorem zero_count : zeroLogged.2.length = 3 :=
  queryQ_identity_log_length embedding 0 1 1 ZeroRows.groups 3 Fin.elim0 (fun _ => 5)
    ZeroRows.originalHandler ZeroRows.helpers Fin.elim0
end Weighted

namespace Scalar
open LogupLookupSourceTest

def doubled : VirtualOracle (ofPFunctor originalAccess) (Logup.Lookup.valuesFamily f 1 1 1) :=
  ⟨fun q => do
    let _ ← originalView.query q
    originalView.query q⟩
def query (input : VirtualOracle (ofPFunctor originalAccess)
    (Logup.Lookup.valuesFamily f 1 1 1)) :=
  Logup.Interaction.queryQ f 1 2 1 cfg.groups 5 (fun _ => 3) (fun _ => 3) muAccess
    (Logup.Lookup.weightedView f 1 1 1 originalAccess input) (fun _ => 2)
def logged (input : VirtualOracle (ofPFunctor originalAccess)
    (Logup.Lookup.valuesFamily f 1 1 1)) :=
  simulateQ (retainedHandler mu helpers) (query input).withQueryLog

theorem identity_count : (logged originalView).2.length = 4 :=
  scalar_queryQ_identity_log_length f 1 1 1 1 cfg.groups 5 (fun _ => 3) (fun _ => 3)
    originalHandler mu helpers (fun _ => 2)

set_option backward.isDefEq.respectTransparency false in
theorem doubled_count : (logged doubled).2.length = 6 := by
  have hc := scalar_queryQ_log_length f 1 1 1 1 cfg.groups 5 (fun _ => 3) (fun _ => 3)
    originalAccess doubled originalHandler mu helpers (fun _ => 2)
  change (logged doubled).2.length = _ at hc
  rw [hc]
  have h (i : Fin 2) :
      (simulateQ originalHandler
        (doubled.query ⟨finSumFinEquiv.symm i, fun _ => 2⟩).withQueryLog).2.length = 2 := by rfl
  simp only [h]
  decide
end Scalar

namespace Tuple
open LogupTupleSourceTest

def doubled : VirtualOracle (ofPFunctor originalAccess)
    (Logup.Lookup.Tuple.coefficientFamily f 1 1 2 2) :=
  ⟨fun q => do
    let _ ← view.query q
    view.query q⟩
def query (input : VirtualOracle (ofPFunctor originalAccess)
    (Logup.Lookup.Tuple.coefficientFamily f 1 1 2 2)) :=
  Logup.Interaction.queryQ f 1 3 2 cfg.groups 5 (fun _ => 3) (fun _ => 3) muAccess
    (Logup.Lookup.Tuple.weightedView f 1 1 2 2 3 originalAccess input) (fun _ => 2)
def logged (input : VirtualOracle (ofPFunctor originalAccess)
    (Logup.Lookup.Tuple.coefficientFamily f 1 1 2 2)) :=
  simulateQ (retainedHandler mu helpers) (query input).withQueryLog

theorem identity_count : (logged view).2.length = 13 :=
  tuple_queryQ_identity_log_length f 1 2 1 2 2 cfg.groups 3 5 (fun _ => 3) (fun _ => 3)
    impl mu helpers (fun _ => 2)

set_option backward.isDefEq.respectTransparency false in
theorem doubled_count : (logged doubled).2.length = 22 := by
  have hc := tuple_queryQ_log_length f 1 2 1 2 2 cfg.groups 3 5 (fun _ => 3) (fun _ => 3)
    originalAccess doubled impl mu helpers (fun _ => 2)
  change (logged doubled).2.length = _ at hc
  rw [hc]
  have h (i : Fin 3) (j : Fin 3) :
      (simulateQ impl
        (doubled.query ⟨(finSumFinEquiv.symm i, j), fun _ => 2⟩).withQueryLog).2.length = 2 := by
    rfl
  simp only [h]
  decide

def coeffs (slot : Fin 1 ⊕ Fin 2) : Vector F 3 :=
  Vector.ofFn fun j => simulateQ impl (doubled.query ⟨(slot, j), fun _ => 2⟩)
def hornerProfile (slot : Fin 1 ⊕ Fin 2) :=
  profileArithmetic (Arithmetic.evalHornerProgram (coeffs slot).toArray (3 : F))
set_option backward.isDefEq.respectTransparency false in
def reconstructionProfile :=
  let source := Logup.Lookup.Tuple.weightedView f 1 1 2 2 3 originalAccess doubled
  let input (kind : Fin 2) (i : Fin 3) : F := simulateQ (retainedHandler mu helpers)
    (Logup.Interaction.queryInput f 1 3 retainedAccess
      (source.substSource (Access.queryPrior muAccess
        (Logup.Interaction.helperInterface (E := F) 1 2))) kind i (fun _ => 2))
  let helper (k : Fin 2) : F := simulateQ (retainedHandler mu helpers)
    (Logup.Interaction.queryHelper 1 2 muAccess k (fun _ => 2))
  profileArithmetic (Logup.Reconstruction.program (n := 1) cfg.groups 5 (fun _ => 3) (fun _ => 3)
    (fun _ => 2) (input 0) (input 1) helper)

set_option backward.isDefEq.respectTransparency false in
theorem reconstructionProfile_eq : reconstructionProfile =
    (simulateQ (retainedHandler mu helpers) (query doubled),
      Logup.Reconstruction.cost cfg.groups 1) :=
  queryQ_profile f 1 3 2 cfg.groups 5 (fun _ => 3) (fun _ => 3) muAccess
    (Logup.Lookup.Tuple.weightedView f 1 1 2 2 3 originalAccess doubled)
    (retainedHandler mu helpers) (fun _ => 2)

def tags (input : VirtualOracle (ofPFunctor originalAccess)
    (Logup.Lookup.Tuple.coefficientFamily f 1 1 2 2)) : List Nat :=
  (logged input).2.map fun entry => match entry.1 with
    | .inl (.inl t) => (finSumFinEquiv t.1.1).val * 3 + t.1.2.val
    | .inl (.inr t) => 100 + t.1.val
    | .inr t => 200 + t.1.val
end Tuple

namespace ZeroWidth
abbrev F := LogupTupleSourceTest.F
def f : F →+* F := RingHom.id F
abbrev original := (Logup.Lookup.Tuple.coefficientFamily f 0 0 1 0).spec.toPFunctor
def impl : QueryImpl (ofPFunctor original) Id := fun _ => (7 : F)
def view := VirtualOracle.id (Logup.Lookup.Tuple.coefficientFamily f 0 0 1 0)
def mu : Vector (CMlPolynomialEval F 0) 1 := #v[#v[3]]
def helpers : Vector (CMlPolynomialEval F 0) 0 := #v[]
abbrev retained := Access.extend original (Logup.Lookup.multiplicityInterface f 0 1)
def logged := simulateQ
  (Access.extendImpl retained (Logup.Interaction.helperInterface (E := F) 0 0)
    (Access.extendImpl original (Logup.Lookup.multiplicityInterface f 0 1) impl mu) helpers)
  (Logup.Interaction.queryQ f 0 1 0 #v[] 7 Fin.elim0 Fin.elim0 retained
    (Logup.Lookup.Tuple.weightedView f 0 0 1 0 0 original view) Fin.elim0).withQueryLog

theorem count : logged.2.length = 2 :=
  tuple_queryQ_identity_log_length f 0 0 0 1 0 #v[] 0 7 Fin.elim0 Fin.elim0
    impl mu helpers Fin.elim0
end ZeroWidth

open Lean Elab Command in
run_cmd do
  unless Weighted.logged.2.length == 3 && Weighted.zeroLogged.2.length == 3 do
    throwError "weighted n1/n0 actual source query count changed"
  unless (Scalar.logged LogupLookupSourceTest.originalView).1 == 13 &&
      (Scalar.logged Scalar.doubled).1 == 13 && (Scalar.logged Scalar.doubled).2.length == 6 do
    throwError "scalar original backend fanout changed retained-mu reconstruction or query census"
  unless (Tuple.logged LogupTupleSourceTest.view).1 == 9 &&
      (Tuple.logged Tuple.doubled).1 == 9 && (Tuple.logged Tuple.doubled).2.length == 22 do
    throwError "tuple coefficient backend fanout changed Q or retained multiplicity/helper counts"
  unless Tuple.tags LogupTupleSourceTest.view == List.range 9 ++ [100, 101, 200, 201] &&
      Tuple.tags Tuple.doubled == (List.range 9).flatMap (fun i => [i, i]) ++
        [100, 101, 200, 201] do
    throwError "raw coefficient/mu/helper provenance or actual repeated-query order changed"
  for slot in [Sum.inl (0 : Fin 1), Sum.inr (0 : Fin 2), Sum.inr (1 : Fin 2)] do
    let profiled := Tuple.hornerProfile slot
    unless profiled.1 == simulateQ LogupTupleSourceTest.impl
        (Logup.Lookup.Tuple.queryValue LogupTupleSourceTest.f 1 1 2 2 3
          LogupTupleSourceTest.originalAccess Tuple.doubled slot (fun _ => 2)) &&
        profiled.2 .add == 2 && profiled.2 .mul == 2 &&
        profiled.2 .coefficientRead == 3 && profiled.2 .sub == 0 do
      throwError "buffered-source Horner priced a different value or reader"
  unless Tuple.reconstructionProfile.1 == 9 && Tuple.reconstructionProfile.2 .add == 8 &&
      Tuple.reconstructionProfile.2 .sub == 7 && Tuple.reconstructionProfile.2 .mul == 9 &&
      Tuple.reconstructionProfile.2 .inv == 0 do
    throwError "Q local profile priced backend work, source negations or a different scalar circuit"
  unless ZeroWidth.logged.1 == 0 && ZeroWidth.logged.2.length == 2 do
    throwError "M0/n0/W0 source skipped its stored tag or retained multiplicity"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``queryQ_log_length, ``queryQ_identity_log_length,
      ``scalar_queryWeighted_log_length, ``scalar_queryQ_log_length,
      ``scalar_queryQ_identity_log_length, ``tuple_queryValue_log_length,
      ``tuple_queryWeighted_log_length, ``tuple_queryQ_log_length,
      ``tuple_queryQ_identity_log_length, ``queryQ_profile, ``tuple_queryValue_profile,
      ``tuple_queryValue_total_profile, ``lookup_weight_sites,
      ``Weighted.count, ``Weighted.zero_count, ``Scalar.identity_count, ``Scalar.doubled_count,
      ``Tuple.identity_count, ``Tuple.doubled_count, ``Tuple.reconstructionProfile_eq,
      ``ZeroWidth.count] do
    unless (← collectAxioms name).all allowed.contains do
      throwError "unexpected actual source resource axiom: {name}"
  for name in #[``Weighted.logged, ``Weighted.zeroLogged, ``Scalar.doubled, ``Scalar.logged,
      ``Tuple.doubled, ``Tuple.logged, ``Tuple.hornerProfile, ``Tuple.reconstructionProfile,
      ``Tuple.tags, ``ZeroWidth.logged] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "missing actual source resource caller IR: {name}"
  logInfo "actual weighted/scalar/tuple fanout, n0/W0, retained routing and local profiles passed"
end SourceResourcesTests
