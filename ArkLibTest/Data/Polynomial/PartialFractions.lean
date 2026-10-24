/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.Polynomial.PartialFractions
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum

/-! # Acceptance checks for finite partial fractions -/

open Polynomial PartialFractions Finset

namespace PartialFractions.Test

example {F : Type*} [Field F] (value weight : ℕ → F) :
    commonDenominator ∅ value = 1 ∧ clearedNumerator ∅ value weight = 0 ∧
      reciprocalSum ∅ value weight = 0 := by
  simp [commonDenominator, clearedNumerator, reciprocalSum]

example {F : Type*} [Field F] (v w : F) :
    clearedNumerator {0} (fun _ : ℕ ↦ v) (fun _ ↦ w) = C w := by
  simp [clearedNumerator]

/-- Opposite weights on the same pole cancel without any characteristic restriction. -/
example {F : Type*} [Field F] (v w : F) :
    reciprocalSum univ (fun _ : Bool ↦ v) (fun b ↦ if b then w else -w) = 0 := by
  simp [reciprocalSum, neg_div]

/-- The field is infinite, and different poles cannot cancel despite total weight zero. -/
example : reciprocalSum univ (fun b : Bool ↦ if b then (2 : ℚ) else 5)
    (fun b ↦ if b then (3 : ℚ) else -3) ≠ 0 := by
  intro h
  have hzero := (reciprocalSum_eq_zero_iff _ _ _).mp h (2 : ℚ)
  norm_num [sumFiber_eq_sum_ite] at hzero

/-- Repeated poles are retained in the denominator even when their weights cancel. -/
example (v w : ℚ) :
    clearedNumerator univ (fun _ : Bool ↦ v) (fun b ↦ if b then w else -w) = 0 := by
  rw [clearedNumerator_eq_zero_iff]
  intro k
  by_cases h : v = k <;> simp [sumFiber_eq_sum_ite, h]

example {F : Type*} [Field F] (v : F) :
    commonDenominator univ (fun _ : Bool ↦ v) = (X - C v) ^ 2 := by
  simp [commonDenominator, pow_two]

/-- Symbolic nonvanishing does not imply nonvanishing at a challenge equal to a pole. -/
example (v : ℚ) : commonDenominator {0} (fun _ : ℕ ↦ v) ≠ 0 ∧
    eval v (commonDenominator {0} (fun _ : ℕ ↦ v)) = 0 := by
  constructor
  · exact commonDenominator_ne_zero _ _
  · simp [commonDenominator]

example {F : Type*} [Field F] (value weight : Fin 3 → F) :
    (clearedNumerator univ value weight).natDegree ≤ 2 := by
  simpa using natDegree_clearedNumerator_le univ value weight

abbrev F₂ := ZMod 2

instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- Two unit weights at one pole cancel in characteristic two. -/
example : reciprocalSum univ (fun _ : Bool ↦ (9 : F₂)) (fun _ ↦ 1) = 0 := by
  rw [reciprocalSum_eq_zero_iff]
  intro k
  by_cases h : (9 : F₂) = k
  · simpa [sumFiber_eq_sum_ite, h] using (show (2 : F₂) = 0 by decide)
  · simp [sumFiber_eq_sum_ite, h]

example : clearedNumerator univ (fun _ : Bool ↦ (9 : F₂)) (fun _ ↦ 1) = 0 := by
  rw [clearedNumerator_eq_zero_iff]
  intro k
  by_cases h : (9 : F₂) = k
  · simpa [sumFiber_eq_sum_ite, h] using (show (2 : F₂) = 0 by decide)
  · simp [sumFiber_eq_sum_ite, h]

/-- The executable symbolic fold agrees with both denominator-clearing views. -/
example {ι F : Type*} [Field F] [DecidableEq ι] (s : Finset ι) (value weight : ι → F) :
    FractionPair.sum (s.toList.map fun i ↦
      (⟨C (weight i), X - C (value i)⟩ : FractionPair F[X])) =
        ⟨clearedNumerator s value weight, commonDenominator s value⟩ :=
  fold_eq_clearedFraction s value weight

example : clearedNumerator univ (fun _ : Bool ↦ (1 : ℚ)) (fun _ ↦ 1) =
    2 * (X - C 1) := by
  simp [clearedNumerator, two_mul, sub_add_sub_comm, one_add_one_eq_two]

/-- A pole can make the scalar fold numerator zero for an unbalanced occurrence list. -/
example : (FractionPair.sum ((univ : Finset Bool).toList.map fun _ ↦
    (⟨(1 : ℚ), 1 - 1⟩ : FractionPair ℚ))).numerator = 0 := by
  rw [← eval_clearedNumerator_eq_fold_numerator univ (fun _ : Bool ↦ (1 : ℚ)) (fun _ ↦ 1) 1]
  simp [clearedNumerator]

example : clearedNumerator univ (fun _ : Bool ↦ (1 : ℚ)) (fun _ ↦ 1) ≠ 0 := by
  intro h
  have hzero := (clearedNumerator_eq_zero_iff _ _ _).mp h (1 : ℚ)
  norm_num [sumFiber_eq_sum_ite] at hzero

open Lean Elab Command

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in #[``reciprocalSum, ``commonDenominator, ``clearedNumerator,
      ``commonDenominator_ne_zero, ``map_clearedNumerator,
      ``sum_div_X_sub_C_eq_zero_iff, ``reciprocalSum_eq_sum_fibers,
      ``reciprocalSum_eq_zero_iff, ``clearedNumerator_eq_zero_iff,
      ``natDegree_clearedNumerator_le, ``fold_eq_clearedFraction,
      ``eval_clearedNumerator_eq_fold_numerator] do
    let axioms ← collectAxioms n
    unless axioms.all allowed.contains do
      throwError "`{n}` depends on unexpected axioms: {axioms}"

end PartialFractions.Test
