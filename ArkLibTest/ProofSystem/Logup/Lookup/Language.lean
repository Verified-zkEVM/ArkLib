/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Lookup.Language
import Mathlib.Algebra.Field.ZMod
import Lean.Compiler.IR

/-! # Multiple table pieces, explicit indices and characteristic-separated lookup counts -/

open CompPoly Logup.Lookup
open scoped BigOperators
open Lean Elab Command

namespace LogupLookupLanguageTest

abbrev F := ZMod 17
instance : Fact (Nat.Prime 17) := ⟨by decide⟩

def data : Data F 1 1 2 := Sum.elim
  (fun _ => #v[5, 7]) (fun p => if p = 0 then #v[3, 3] else #v[5, 7])
def indices : Vector (Fin 4) 2 := #v[2, 3]
def mu : Vector (CMlPolynomialEval F 1) 2 := #v[#v[0, 0], #v[1, 1]]

theorem valid : ValidIndices data indices := by unfold ValidIndices; decide
theorem accepted : checkIndices data indices = true := (checkIndices_eq_true _ _).mpr valid
theorem invalid_rejected : checkIndices data #v[0, 1] = false := by decide

theorem mu_eq_histogram : mu = multiplicities indices := by decide

/-- Membership in the second declared piece is sufficient; the first piece remains unused. -/
theorem second_piece_language : InLanguage data :=
  inLanguage_iff_exists_validIndices data |>.mpr ⟨indices, valid⟩

/-- Directly checked arbitrary-message balance exercises the converse, without a lookup premise. -/
theorem direct_converse : InLanguage data := by
  apply inLanguage_of_weighted_fiber_eq_zero 17 data mu (by decide)
  simp_rw [weighted_fiber_eq_sub, Finset.sumFiber_eq_sum_ite]
  decide

theorem histogram_balance (key : F) :
    ((Finset.univ : Finset (Fin 1 → Fin 2)).product
      (Finset.univ : Finset (Fin 3))).sumFiber
      (fun i => (weightedData data (multiplicities indices) (0, i.2)).get (finFunctionFinEquiv i.1))
      (fun i => (weightedData data (multiplicities indices) (1, i.2)).get (finFunctionFinEquiv i.1))
      key = 0 := weighted_fiber_multiplicities_eq_zero data indices valid key

/-- Column-major flattening is asymmetric in both dimensions, with four Boolean rows per column. -/
def layoutData : Data Int 2 2 3 := Sum.elim
  (fun q => if q = 0 then #v[0, 1, 2, 3] else #v[10, 11, 12, 13])
  (fun p => if p = 0 then #v[20, 21, 22, 23]
    else if p = 1 then #v[10, 11, 12, 13] else #v[0, 1, 2, 3])
def layoutIndices : Vector (Fin 12) 8 := #v[8, 9, 10, 11, 4, 5, 6, 7]
def layoutMu : Vector (CMlPolynomialEval Int 2) 3 := multiplicities layoutIndices

theorem layout_valid : ValidIndices layoutData layoutIndices := by unfold ValidIndices; decide
theorem natural_total : (Vector.histogram layoutIndices).toList.sum = 8 := by decide

def noQueries : Data Int 1 0 1 := Sum.elim Fin.elim0 (fun _ => #v[3, 4])
def noTable : Data F 0 1 0 := Sum.elim (fun _ => #v[0]) Fin.elim0

theorem noQueries_language : InLanguage noQueries := by unfold InLanguage; decide
theorem noTable_not_language : ¬ InLanguage noTable := by unfold InLanguage; decide

theorem noTable_any_weights_false (weights : Vector (CMlPolynomialEval F 0) 0) :
    ∃ key, ((Finset.univ : Finset (Fin 0 → Fin 2)).product
      (Finset.univ : Finset (Fin 1))).sumFiber
      (fun i => (weightedData noTable weights (0, i.2)).get (finFunctionFinEquiv i.1))
      (fun i => (weightedData noTable weights (1, i.2)).get
        (finFunctionFinEquiv i.1)) key ≠ 0 := by
  simpa only [RingHom.id_apply] using exists_mapped_weighted_fiber_ne_zero
    (RingHom.id F) 17 noTable weights (by decide) noTable_not_language

namespace CharacteristicTwo
abbrev F := ZMod 2
instance : Fact (Nat.Prime 2) := ⟨by decide⟩
def data : Data F 1 1 1 := Sum.elim (fun _ => #v[0, 0]) (fun _ => #v[1, 1])
def mu : Vector (CMlPolynomialEval F 1) 1 := #v[#v[0, 0]]

theorem false_language : ¬ InLanguage data := by unfold InLanguage; decide
theorem budget_fails : ¬ 1 * 2 ^ 1 < 2 := by decide

/-- Two absent copies cancel after casting; this is precisely the missing query budget. -/
theorem balanced : ∀ key : F,
    ((Finset.univ : Finset (Fin 1 → Fin 2)).product
      (Finset.univ : Finset (Fin 2))).sumFiber
      (fun i => (weightedData data mu (0, i.2)).get (finFunctionFinEquiv i.1))
      (fun i => (weightedData data mu (1, i.2)).get (finFunctionFinEquiv i.1)) key = 0 := by
  simp_rw [weighted_fiber_eq_sub (n := 1) (M := 1) (P := 1) data mu,
    Finset.sumFiber_eq_sum_ite]
  decide

/-- The same false base lookup stays balanced after every field embedding into an extension. -/
theorem balanced_in_extension {E : Type} [Field E] [DecidableEq E] (f : F →+* E) (key : E) :
    ((Finset.univ : Finset (Fin 1 → Fin 2)).product
      (Finset.univ : Finset (Fin 2))).sumFiber
      (fun i => f ((weightedData data mu (0, i.2)).get (finFunctionFinEquiv i.1)))
      (fun i => f ((weightedData data mu (1, i.2)).get (finFunctionFinEquiv i.1))) key = 0 := by
  have hzero (k : F) :
      ((Finset.univ : Finset (Fin 1 → Fin 2)).product
        (Finset.univ : Finset (Fin 2))).sumFiber
        (fun i => (weightedData data mu (0, i.2)).get (finFunctionFinEquiv i.1))
        (fun i => f ((weightedData data mu (1, i.2)).get (finFunctionFinEquiv i.1))) k = 0 := by
    calc
      _ = f (((Finset.univ : Finset (Fin 1 → Fin 2)).product
          (Finset.univ : Finset (Fin 2))).sumFiber
          (fun i => (weightedData data mu (0, i.2)).get (finFunctionFinEquiv i.1))
          (fun i => (weightedData data mu (1, i.2)).get (finFunctionFinEquiv i.1)) k) :=
        Finset.sumFiber_map f.toAddMonoidHom _ _ _ _
      _ = 0 := by rw [balanced, map_zero]
  exact Finset.sumFiber_comp_eq_zero _ _ _ f hzero key
end CharacteristicTwo

run_cmd do
  unless checkIndices data indices do throwError "valid second-piece witness rejected"
  unless !(checkIndices data #v[0, 1]) do throwError "invalid first-piece witness accepted"
  unless multiplicities (B := F) indices == mu do
    throwError "second-piece histogram did not preserve unused duplicate positions"
  unless columnEntries (fun q => layoutData (.inl q)) == #v[0, 1, 2, 3, 10, 11, 12, 13] do
    throwError "query column/row orientation changed"
  unless columnEntries (fun p => layoutData (.inr p)) ==
      #v[20, 21, 22, 23, 10, 11, 12, 13, 0, 1, 2, 3] do
    throwError "physical table piece/row orientation changed"
  unless checkIndices layoutData layoutIndices do throwError "asymmetric indexed witness rejected"
  unless layoutMu == #v[#v[0, 0, 0, 0], #v[1, 1, 1, 1], #v[1, 1, 1, 1]] do
    throwError "histogram reshaping changed piece order"
  unless checkIndices noQueries (#v[] : Vector (Fin 2) 0) do
    throwError "empty query witness rejected"
  unless multiplicities (B := Int) (P := 1) (n := 1)
      (#v[] : Vector (Fin 2) 0) == #v[#v[0, 0]] do
    throwError "empty query histogram is not zero"
  unless columnEntries (fun i => weightedData data mu (1, i)) == #v[1, 1, 0, 0, -1, -1] do
    throwError "signed collection did not retain query1/table negative multiplicity"

run_cmd do
  for name in #[``columnEntries, ``checkIndices, ``multiplicities, ``weightedData,
      ``layoutMu] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "missing lookup language executable IR: {name}"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``columnEntries_get, ``columnEntries_get_pair, ``weightedData_value,
      ``weightedData_query_weight, ``weightedData_table_weight, ``inLanguage_iff_entries,
      ``weighted_fiber_eq_sub, ``checkIndices_eq_true, ``inLanguage_iff_exists_validIndices,
      ``columnEntries_multiplicities, ``inLanguage_of_weighted_fiber_eq_zero,
      ``weighted_fiber_multiplicities_eq_zero, ``exists_mapped_weighted_fiber_ne_zero,
      ``mapped_weighted_fiber_multiplicities_eq_zero, ``valid, ``accepted, ``invalid_rejected,
      ``mu_eq_histogram, ``second_piece_language, ``direct_converse, ``histogram_balance,
      ``layout_valid, ``natural_total, ``noQueries_language, ``noTable_not_language,
      ``noTable_any_weights_false, ``CharacteristicTwo.false_language,
      ``CharacteristicTwo.budget_fails, ``CharacteristicTwo.balanced,
      ``CharacteristicTwo.balanced_in_extension] do
    unless (← collectAxioms name).all allowed.contains do
      throwError "lookup language has an unexpected axiom: {name}"

end LogupLookupLanguageTest
