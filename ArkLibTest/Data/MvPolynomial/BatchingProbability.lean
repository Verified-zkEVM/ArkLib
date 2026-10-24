/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.MvPolynomial.BatchingProbability
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Acceptance checks for affine and selected-table batching bounds. -/

open scoped BigOperators ProbabilityTheory ENNReal
open Finset

namespace BatchingProbability.Test

abbrev F := ZMod 5
instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Exhaustively count an affine equation over two independently sampled field coordinates. -/
def affineCount (c : F) (a : Fin 2 → F) : ℕ :=
  #{l : Fin 2 → F | c + ∑ j, a j * l j = 0}

example : affineCount 1 (fun _ ↦ 0) = 0 := by decide
example : affineCount 0 (fun j ↦ if j = 0 then 1 else 2) = 5 := by decide
example : affineCount 1 (fun j ↦ if j = 0 then 1 else 2) = 5 := by decide

-- The excluded zero equation has probability one, rather than at most one fifth.
example : affineCount 0 (fun _ ↦ 0) = 25 := by decide

example : Pr{let l ← $ᵗ (Fin 2 → F)}[(1 : F) + ∑ j, (0 : F) * l j = 0] ≤
    (Fintype.card F : ENNReal)⁻¹ :=
  Probability.prob_affine_dotProduct_eq_zero_le 1 (fun _ ↦ 0) (Or.inl (by decide))

example : Pr{let l ← $ᵗ (Fin 0 → F)}[(1 : F) + ∑ j, j.elim0 * l j = 0] ≤
    (Fintype.card F : ENNReal)⁻¹ :=
  Probability.prob_affine_dotProduct_eq_zero_le 1 (fun j ↦ j.elim0) (Or.inl (by decide))

/-- Only the last of three residual tables is nonzero; its multilinear extension is X0. -/
def oneResidual (k : Fin 3) (u : Fin 1 → Fin 2) : F :=
  if k = 2 then (u 0).val else 0

example : Pr{let r ← $ᵗ ((Fin 1 → F) × (Fin 3 → F))}[
    (0 : F) + ∑ k, MvPolynomial.eval r.1 (MvPolynomial.MLE (oneResidual k)) * r.2 k = 0] ≤
      (1 : ENNReal) / Fintype.card F + (Fintype.card F : ENNReal)⁻¹ := by
  simpa only [Nat.cast_one] using
    Probability.prob_MLE_affine_batch_eq_zero_le 0 oneResidual
      (Or.inr ⟨2, fun _ ↦ 1, by decide⟩)

-- Independent enumeration of X0*lambda2 has 225 zeros among 625 challenge pairs.
run_cmd do
  let count := #{r : (Fin 1 → F) × (Fin 3 → F) | r.1 0 * r.2 2 = 0}
  unless count == 225 do
    throwError "Expected 225 zero pairs, got {count}"
example : #{r : F × F | r.1 * r.2 = 0} = 9 := by decide

/-- This table needs the full two-variable residual root bound. -/
def productResidual (u : Fin 2 → Fin 2) : F := (u 0).val * (u 1).val

theorem productResidual_mle : MvPolynomial.MLE productResidual =
    MvPolynomial.X (0 : Fin 2) * MvPolynomial.X 1 := by
  symm
  apply MvPolynomial.eq_MLE_of_degreeOf_le_one_of_eval_zeroOne_eq productResidual
  · intro i
    apply (MvPolynomial.degreeOf_mul_le i _ _).trans
    fin_cases i <;> simp [MvPolynomial.degreeOf_X]
  · intro u
    simp [productResidual]

example : Pr{let r ← $ᵗ ((Fin 2 → F) × (Fin 1 → F))}[
    (0 : F) + ∑ k, MvPolynomial.eval r.1 (MvPolynomial.MLE productResidual) * r.2 k = 0] ≤
      ((2 : ℕ) : ENNReal) / Fintype.card F + (Fintype.card F : ENNReal)⁻¹ :=
  Probability.prob_MLE_affine_batch_eq_zero_le (n := 2) (K := 1) 0
    (fun _ ↦ productResidual) (Or.inr ⟨0, fun _ ↦ 1, by decide⟩)

-- The selected residual itself has 9 zeros among 25 points, exceeding a 1/5 root bound.
theorem productResidual_root_count :
    #{z : Fin 2 → F | MvPolynomial.eval z (MvPolynomial.MLE productResidual) = 0} = 9 := by
  simp only [productResidual_mle, MvPolynomial.eval_mul, MvPolynomial.eval_X]
  decide

example : Pr{let z ← $ᵗ (Fin 2 → F)}[
    MvPolynomial.eval z (MvPolynomial.MLE productResidual) = 0] = (9 : ENNReal) / 25 := by
  rw [SampleableType.prEvent_uniformSample, productResidual_root_count]
  norm_num [Fintype.card_fun, ZMod.card]

example : (9 : ℚ) / 25 > 1 / 5 := by norm_num

example : Pr{let r ← $ᵗ ((Fin 0 → F) × (Fin 0 → F))}[
    (1 : F) + ∑ k : Fin 0, MvPolynomial.eval r.1 k.elim0 * r.2 k = 0] ≤
      ((0 : ℕ) : ENNReal) / Fintype.card F + (Fintype.card F : ENNReal)⁻¹ :=
  Probability.prob_affine_batch_eq_zero_le (n := 0) (K := 0) (d := 0) 1
    (fun k ↦ k.elim0) (Or.inl (by decide))

abbrev F₂ := ZMod 2
instance : Fact (Nat.Prime 2) := ⟨by decide⟩

-- Zero row variables are valid, including in characteristic two.
example : Pr{let r ← $ᵗ ((Fin 0 → F₂) × (Fin 1 → F₂))}[
    (0 : F₂) + ∑ k, MvPolynomial.eval r.1 (MvPolynomial.MLE (fun _ ↦ (1 : F₂))) * r.2 k = 0] ≤
      (0 : ENNReal) / Fintype.card F₂ + (Fintype.card F₂ : ENNReal)⁻¹ := by
  simpa only [Nat.cast_zero] using
    Probability.prob_MLE_affine_batch_eq_zero_le (n := 0) (K := 1) 0 (fun _ _ ↦ (1 : F₂))
      (Or.inr ⟨0, fun i ↦ i.elim0, by decide⟩)

example : #{l : Fin 1 → F₂ | l 0 = 0} = 1 := by decide

-- If the residual table may adapt after z, its nonzero MLE X-z vanishes at z every time.
example (z : F) : ∃ u : Fin 2, (u.val : F) - z ≠ 0 := by
  by_cases hz : z = 0
  · subst z
    exact ⟨1, by decide⟩
  · exact ⟨0, by simpa using neg_ne_zero.mpr hz⟩

example : #{r : F × F | (r.1 - r.1) * r.2 = 0} = 25 := by decide

-- If S may adapt after lambda, even a fixed nonzero coefficient can be canceled every time.
example : #{l : F | (-l) + (1 : F) * l = 0} = 5 := by decide

#eval affineCount 1 (fun j ↦ if j = 0 then 1 else 2)
#eval #{r : (Fin 1 → F) × (Fin 3 → F) | r.1 0 * r.2 2 = 0}
#eval #{r : F × F | (r.1 - r.1) * r.2 = 0}

open Lean Elab Command

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in #[``Probability.prob_affine_dotProduct_eq_zero_le,
      ``Probability.prob_affine_batch_eq_zero_le,
      ``Probability.prob_MLE_affine_batch_eq_zero_le, ``productResidual_mle,
      ``productResidual_root_count] do
    let axioms ← collectAxioms n
    unless axioms.all allowed.contains do
      throwError "`{n}` depends on unexpected axioms: {axioms}"

end BatchingProbability.Test
