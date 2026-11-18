/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

module

public import ArkLib.Data.CodingTheory.ReedMuller.AffineCombiner.Basic
public import Mathlib.Basic.ENNReal.Inv

/-!
# Lower bound for the Reed–Muller combiner error

Let `K₀ ⊆ F` be finite fields of sizes `q₀ ≤ q`, and let `n = q₀ᵏ` be the grid size.
At agreement loss `n / q₀ = q₀ᵏ⁻¹`, the Reed–Muller error is at least `1 / qᵏ`.
So the exponent `k` in the leading term `4 / (η qᵏ)` of Theorem 7.1 cannot be improved.
This is the remark after Theorem 7.1 in Section 7 of [CWYZ26].
Theorem 7.1 itself is not proved here.
The [paper page](../../../../../docs/kb/papers/CWYZ26.md) records the correspondence.

Take `f = 0` and `g = X₁ᵈ`.
The `q` coefficient vectors `(α₀, 0, …, 0)` have the constant multiplier `α₀`.
The candidate `α₀ X₁ᵈ` then agrees with the combined word on all `n` grid points.
An admissible second witness `G₀` differs from `X₁ᵈ`.
By Schwartz–Zippel on the grid, `X₁ᵈ - G₀` has at most `d q₀ᵏ⁻¹` grid zeros.
So `G₀` disagrees with `g` on at least `(q₀ - d) q₀ᵏ⁻¹ ≥ 2 q₀ᵏ⁻¹` points.
This exceeds the loss.

The paper derives `d ≤ q₀ - 2` from the hypotheses of Theorem 7.1.
Here it is the hypothesis `d + 2 ≤ q₀`.
The paper also assumes `1 ≤ d`, which the bound does not need.

## Main statements

* `ReedMuller.le_affineMcaError_of_add_two_le`: the bound `1 / qᵏ`.

## References

* [Chiesa, A., Weissenberg, G., Yogev, E., and Zheng, K. Z.,
    *Affine combiners for Reed–Solomon proximity gaps*][CWYZ26]
-/

@[expose] public section

namespace ReedMuller

open MvPolynomial Finset

variable {K₀ : Type*} [Field K₀] [Fintype K₀] {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra K₀ F]

/-- Let `K₀ ⊆ F` be finite fields of sizes `q₀` and `q`, and let `n = q₀ᵏ` with `k ≥ 1`.

Suppose `d + 2 ≤ q₀` and `A ≤ n`.

Then the Reed–Muller error at agreement loss `n / q₀ = q₀ᵏ⁻¹` is at least `1 / qᵏ`. -/
theorem le_affineMcaError_of_add_two_le {k d A : ℕ} (hk : 1 ≤ k)
    (hdq : d + 2 ≤ Fintype.card K₀) (hA : A ≤ Fintype.card K₀ ^ k) :
    1 / (Fintype.card F : ENNReal) ^ k ≤
      affineMcaError K₀ F k d A (Fintype.card K₀ ^ (k - 1)) := by
  classical
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  set g : (Fin (k + 1) → K₀) → F := fun z ↦ eval (gridPoint F z) (X 0 ^ d)
  have hexc : ∀ c : F, IsAffineExceptional (0 : (Fin (k + 1) → K₀) → F) g d A
      (Fintype.card K₀ ^ (k + 1 - 1)) (Pi.single 0 c) (C c * X 0 ^ d) := by
    intro c
    have hL : ∀ z : Fin (k + 1) → K₀,
        eval (gridPoint F z) (affineMultiplier (Pi.single 0 c)) = c := by
      intro z
      simp [Fin.succ_ne_zero]
    have hagree : agreementSet (combinedWord 0 g
        (affineMultiplier (Pi.single 0 c))) (C c * X 0 ^ d) = univ := by
      ext z
      simp [hL, g]
    refine ⟨?_, ?_, ?_⟩
    · exact (totalDegree_mul _ _).trans (by simp [totalDegree_X_pow])
    · rw [hagree, card_univ, Fintype.card_fun, Fintype.card_fin]
      exact hA
    · rintro F₀ G₀ - hG ⟨-, hloss⟩
      have hne : X 0 ^ d - G₀ ≠ 0 := by
        intro h
        rcases hG with hG | hG
        · rw [hG, sub_zero] at h
          exact pow_ne_zero d (X_ne_zero 0) h
        · rw [← sub_eq_zero.mp h, totalDegree_X_pow] at hG
          exact lt_irrefl d hG
      have hdeg : (X 0 ^ d - G₀).totalDegree ≤ d := by
        refine (totalDegree_sub _ _).trans (max_le (by simp [totalDegree_X_pow]) ?_)
        rcases hG with rfl | hG
        · simp
        · exact hG.le
      have hzeros := card_grid_eval_eq_zero_le (K₀ := K₀) hne
      have hsub : ({z | eval (gridPoint F z) (X 0 ^ d - G₀) ≠ 0} : Finset _) ⊆
          agreementLoss 0 g (affineMultiplier (Pi.single 0 c)) (C c * X 0 ^ d)
            F₀ G₀ := by
        intro z hz
        rw [mem_filter, map_sub, sub_ne_zero] at hz
        rw [mem_agreementLoss]
        exact ⟨by simp [hL, g], Or.inr (Ne.symm hz.2)⟩
      have hsplit := card_filter_add_card_filter_not
        (s := (univ : Finset (Fin (k + 1) → K₀)))
        (fun z ↦ eval (gridPoint F z) (X 0 ^ d - G₀) = 0)
      rw [card_univ, Fintype.card_fun, Fintype.card_fin] at hsplit
      have h1 := card_le_card hsub
      have hpos : 0 < Fintype.card K₀ ^ k := pow_pos Fintype.card_pos _
      simp only [add_tsub_cancel_right] at hloss
      have h2 : (X 0 ^ d - G₀).totalDegree * Fintype.card K₀ ^ k ≤ d * Fintype.card K₀ ^ k :=
        Nat.mul_le_mul_right _ hdeg
      rw [pow_succ] at hsplit
      simp only [add_tsub_cancel_right] at hzeros
      nlinarith
  have hcount : Fintype.card F ≤ #{α : Fin (k + 1 + 1) → F | ∃ P,
      IsAffineExceptional 0 g d A (Fintype.card K₀ ^ (k + 1 - 1)) α P} := by
    have hinj : Function.Injective fun c : F ↦ (Pi.single 0 c : Fin (k + 1 + 1) → F) :=
      fun c c' h ↦ by simpa using congrFun h 0
    rw [← card_univ, ← card_image_of_injective univ hinj]
    refine card_le_card fun α hα ↦ ?_
    obtain ⟨c, -, rfl⟩ := mem_image.mp hα
    exact mem_filter.mpr ⟨mem_univ _, _, hexc c⟩
  refine le_trans ?_ (le_affineMcaError d A _ 0 g)
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  calc 1 / (Fintype.card F : ENNReal) ^ (k + 1)
      = ENNReal.ofReal ((Fintype.card F : ℝ) / (Fintype.card F : ℝ) ^ (k + 1 + 1)) := by
        rw [pow_succ _ (k + 1), div_mul_cancel_right₀ hq.ne', ← one_div,
          ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_one,
          ENNReal.ofReal_pow hq.le, ENNReal.ofReal_natCast]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by gcongr)

end ReedMuller
