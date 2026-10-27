/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import ArkLib.Data.Vector.LookupNormalization
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FinCases
import Lean.Compiler.IR

/-! # Normalized versus indexed multiplicities over infinite keys and small characteristics -/

open scoped BigOperators
open Lean Elab Command

namespace LookupNormalizationTest

def table : Vector Nat 2 := #v[0, 0]
def queries : Vector Nat 1 := #v[0]
def indices : Vector (Fin 2) 1 := #v[0]
theorem correct : ∀ i : Fin 1, table[(indices[i.val]).val] = queries[i.val] := by decide

/-- Every characteristic-two extension still has the zero normalizer2. -/
theorem charTwo_get_zero {E : Type*} [Field E] [CharP E 2] (j : Fin 2) :
    (Vector.normalizedLookupWeights E table queries)[j.val] = 0 := by
  have htwo : (2 : E) = 0 := by
    exact (CharP.cast_eq_zero_iff E 2 2).mpr (dvd_refl 2)
  fin_cases j <;> simp [Vector.normalizedLookupWeights, table, queries, htwo]

/-- The normalization failure persists in every characteristic-two field, not only F2 itself. -/
theorem charTwo_fiber_fails {E : Type*} [Field E] [CharP E 2] :
    Finset.univ.sumFiber (fun j : Fin 2 ↦ table[j.val])
      (fun j ↦ (Vector.normalizedLookupWeights E table queries)[j.val]) 0 ≠
      (queries.toList.count 0 : E) := by
  have hzero : Finset.univ.sumFiber (fun j : Fin 2 ↦ table[j.val])
      (fun j ↦ (Vector.normalizedLookupWeights E table queries)[j.val]) 0 = 0 := by
    unfold Finset.sumFiber
    apply Finset.sum_eq_zero
    intro j _
    exact charTwo_get_zero j
  rw [hzero]
  simp [queries]

namespace CharFive
abbrev F := ZMod 5
instance : Fact (Nat.Prime 5) := ⟨by decide⟩
def normalized : Vector F 2 := Vector.normalizedLookupWeights F table queries
def indexed : Vector F 2 := (Vector.histogram indices).map fun (n : Nat) ↦ (n : F)
theorem normalizers : ∀ j : Fin 2, (table.toList.count table[j.val] : F) ≠ 0 := by decide

/-- Unused duplicate positions can be zero in an indexed witness, while normalization splits1. -/
theorem unequal_messages : normalized ≠ indexed := by
  intro heq
  have hfirst := congrArg (fun v : Vector F 2 ↦ v[0]) heq
  simp only [normalized, indexed, Vector.normalizedLookupWeights, Vector.getElem_map] at hfirst
  have hhist : (Vector.histogram indices)[0] = 1 :=
    (Vector.getElem_histogram indices (0 : Fin 2)).trans (by decide)
  rw [hhist] at hfirst
  have hbad : (1 : F) / 2 = 1 := by simpa [table, queries, indices] using hfirst
  apply (show (1 : F) ≠ 2 by decide)
  simpa only [one_mul] using (div_eq_iff (show (2 : F) ≠ 0 by decide)).mp hbad

/-- Equality is per key, including keys absent from either finite occurrence list. -/
theorem equal_fibers (k : Nat) :
    Finset.univ.sumFiber (fun j : Fin 2 ↦ table[j.val]) (fun j ↦ normalized[j.val]) k =
    Finset.univ.sumFiber (fun j : Fin 2 ↦ table[j.val]) (fun j ↦ indexed[j.val]) k := by
  simpa only [normalized, indexed, Vector.getElem_map] using
    Vector.sumFiber_normalizedLookupWeights_eq_histogram table queries indices correct normalizers k

/-- A separate table-length budget suffices; no finite ambient key type is needed. -/
theorem numeric_budget (k : Nat) :
    Finset.univ.sumFiber (fun j : Fin 2 ↦ table[j.val]) (fun j ↦ normalized[j.val]) k =
      (queries.toList.count k : F) :=
  Vector.sumFiber_normalizedLookupWeights_of_length_lt_char 5 table queries indices correct
    (by decide) k
end CharFive

namespace CharTwo
abbrev F := ZMod 2
instance : Fact (Nat.Prime 2) := ⟨by decide⟩
def normalized : Vector F 2 := Vector.normalizedLookupWeights F table queries
def indexed : Vector F 2 := (Vector.histogram indices).map fun (n : Nat) ↦ (n : F)
theorem normalizers_fail :
    ¬ ∀ j : Fin 2, (table.toList.count table[j.val] : F) ≠ 0 := by decide

theorem normalized_fails_balance :
    Finset.univ.sumFiber (fun j : Fin 2 ↦ table[j.val]) (fun j ↦ normalized[j.val]) 0 ≠
      (queries.toList.count 0 : F) := by
  exact charTwo_fiber_fails (E := F)

theorem indexed_balances :
    Finset.univ.sumFiber (fun j : Fin 2 ↦ table[j.val]) (fun j ↦ indexed[j.val]) 0 =
      (queries.toList.count 0 : F) := by
  simpa only [indexed, Vector.getElem_map] using
    Vector.sumFiber_cast_histogram (R := F) table queries indices correct 0

-- A query budget, even with no queries, does not imply nonzero table normalizers.
example : (#v[] : Vector Nat 0).toList.length < 2 := by decide
example : ¬ table.toList.length < 2 := by decide
end CharTwo

/-- The empty comparison has no field-equality or finite-key requirement. -/
theorem empty_fiber {E : Type*} [Field E] (k : Nat) :
    Finset.univ.sumFiber (fun j : Fin 0 ↦ (#v[] : Vector Nat 0)[j.val])
      (fun j ↦ (Vector.normalizedLookupWeights E (#v[] : Vector Nat 0)
        (#v[] : Vector Nat 0))[j.val]) k = 0 := by
  exact (Vector.sumFiber_normalizedLookupWeights
    (#v[] : Vector Nat 0) (#v[] : Vector Nat 0) (#v[] : Vector (Fin 0) 0)
    (fun i ↦ Fin.elim0 i) (fun j ↦ Fin.elim0 j) k).trans (by simp)

run_cmd do
  unless Vector.histogram indices == #v[1, 0] do
    throwError "indexed histogram changed duplicate-table positions"
  unless CharFive.normalized == #v[3, 3] do
    throwError "F5 normalized multiplicities are not both one-half"
  unless CharFive.indexed == #v[1, 0] do
    throwError "F5 indexed multiplicities changed"
  unless CharTwo.normalized == #v[0, 0] do
    throwError "characteristic-two normalization unexpectedly repaired a zero denominator"
  unless CharTwo.indexed == #v[1, 0] do
    throwError "indexed characteristic-two histogram lost its valid unit count"
  unless Vector.normalizedLookupWeights CharFive.F (#v[] : Vector Nat 0)
      (#v[] : Vector Nat 0) == #v[] do
    throwError "empty normalized comparison changed"

run_cmd do
  for name in #[``Vector.normalizedLookupWeights, ``CharFive.normalized, ``CharFive.indexed,
      ``CharTwo.normalized, ``CharTwo.indexed] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "missing normalized comparison executable IR: {name}"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Vector.getElem_normalizedLookupWeights, ``Vector.sumFiber_normalizedLookupWeights,
      ``Vector.sumFiber_normalizedLookupWeights_eq_histogram,
      ``Vector.sumFiber_normalizedLookupWeights_of_length_lt_char, ``correct,
      ``CharFive.normalizers, ``CharFive.unequal_messages, ``CharFive.equal_fibers,
      ``CharFive.numeric_budget, ``CharTwo.normalizers_fail, ``CharTwo.normalized_fails_balance,
      ``CharTwo.indexed_balances, ``charTwo_get_zero, ``charTwo_fiber_fails, ``empty_fiber] do
    unless (← collectAxioms name).all allowed.contains do
      throwError "normalized comparison has an unexpected axiom: {name}"

end LookupNormalizationTest
