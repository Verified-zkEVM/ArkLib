/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.PermutationFingerprintDegree
public import ArkLib.Data.Probability.Instances
public import ArkLib.Data.MvPolynomial.Interpolation
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Ring

/-! # Labeled permutation fingerprints

A product of affine factors binds each value to its distinct position label. Equality of the
formal products characterizes invariance under the permutation, over any field.
-/

@[expose] public section

namespace PermutationFingerprint

open MvPolynomial
open scoped BigOperators

variable {U R : Type*} [Fintype U] [CommRing R]

/-- The difference of the two labeled products at a pair of challenges. -/
def fingerprint (W : U → R) (ι : U ↪ R) (σ : Equiv.Perm U) (β γ : R) : R :=
  (∏ u, (W u + β * ι u + γ)) - ∏ u, (W u + β * ι (σ u) + γ)

/-- The formal fingerprint in the two challenge variables.
Mathlib's finitely supported polynomial arithmetic is noncomputable. -/
noncomputable def polynomial (W : U → R) (ι : U ↪ R) (σ : Equiv.Perm U) :
    MvPolynomial (Fin 2) R :=
  (∏ u, (C (W u) + X 0 * C (ι u) + X 1)) -
    ∏ u, (C (W u) + X 0 * C (ι (σ u)) + X 1)

/-- Evaluation of the formal fingerprint is the executable product difference. -/
@[simp]
theorem eval_polynomial (W : U → R) (ι : U ↪ R) (σ : Equiv.Perm U)
    (r : Fin 2 → R) :
    eval r (polynomial W ι σ) = fingerprint W ι σ (r 0) (r 1) := by
  simp [polynomial, fingerprint]

/-- Permutation-invariant values give equal labeled products. -/
theorem products_eq_of_invariant (W : U → R) (ι : U ↪ R) (σ : Equiv.Perm U)
    (hW : W ∘ σ = W) (β γ : R) :
    (∏ u, (W u + β * ι u + γ)) = ∏ u, (W u + β * ι (σ u) + γ) := by
  have h := Equiv.prod_comp σ (fun u => W u + β * ι u + γ)
  have hw : ∀ u, W (σ u) = W u := fun u => congrFun hW u
  simpa only [hw] using h.symm

/-- Every challenge accepts a permutation-invariant assignment. -/
theorem fingerprint_eq_zero (W : U → R) (ι : U ↪ R) (σ : Equiv.Perm U)
    (hW : W ∘ σ = W) (β γ : R) : fingerprint W ι σ β γ = 0 :=
  sub_eq_zero.mpr (products_eq_of_invariant W ι σ hW β γ)

/-- Permutation-invariant values give the zero formal fingerprint. -/
theorem polynomial_eq_zero (W : U → R) (ι : U ↪ R) (σ : Equiv.Perm U)
    (hW : W ∘ σ = W) : polynomial W ι σ = 0 := by
  apply sub_eq_zero.mpr
  have h := Equiv.prod_comp σ (fun u =>
    (C (W u) + X 0 * C (ι u) + X 1 : MvPolynomial (Fin 2) R))
  have hw : ∀ u, W (σ u) = W u := fun u => congrFun hW u
  simpa only [hw] using h.symm

/-- The common highest homogeneous part cancels, saving one degree. -/
theorem totalDegree_polynomial_le (W : U → R) (ι : U ↪ R) (σ : Equiv.Perm U) :
    (polynomial W ι σ).totalDegree ≤ Fintype.card U - 1 :=
  totalDegree_sub_permuted_prod_le W ι σ

section Field

variable {F : Type*} [Field F]

/-- Substitution along the line belonging to one position recovers its value at the predecessor. -/
theorem invariant_of_polynomial_eq_zero (W : U → F) (ι : U ↪ F) (σ : Equiv.Perm U)
    (h : polynomial W ι σ = 0) : W ∘ σ = W := by
  classical
  have heq := sub_eq_zero.mp h
  have hpred : ∀ t, W (σ.symm t) = W t := by
    intro t
    let s : Fin 2 → Polynomial F :=
      fun i => if i = 0 then Polynomial.X else
        -Polynomial.X * Polynomial.C (ι t) - Polynomial.C (W t)
    have hs := congrArg (eval₂Hom Polynomial.C s) heq
    simp only [map_prod, map_add, map_mul, eval₂Hom_C, eval₂Hom_X'] at hs
    have hz : (∏ u, (Polynomial.C (W u) + s 0 * Polynomial.C (ι u) + s 1)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ t)
      simp only [s, ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false]
      ring
    rw [hz] at hs
    obtain ⟨u, _, hu⟩ := Finset.prod_eq_zero_iff.mp hs.symm
    have hcoeff : ι (σ u) - ι t = 0 := by
      simpa [s, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_mul_X,
        ← sub_eq_add_neg] using congrArg (fun p : Polynomial F => p.coeff 1) hu
    have hconst : W u - W t = 0 := by
      simpa [s, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_mul_X,
        ← sub_eq_add_neg] using congrArg (fun p : Polynomial F => p.coeff 0) hu
    have hlabel : σ u = t := ι.injective (sub_eq_zero.mp hcoeff)
    have hu' : u = σ.symm t := by rw [← hlabel]; simp
    rw [← hu']
    exact sub_eq_zero.mp hconst
  funext u
  simpa using (hpred (σ u)).symm

/-- A false permutation claim gives a nonzero polynomial, independently of field size. -/
theorem polynomial_ne_zero (W : U → F) (ι : U ↪ F) (σ : Equiv.Perm U)
    (hW : W ∘ σ ≠ W) : polynomial W ι σ ≠ 0 :=
  fun h => hW (invariant_of_polynomial_eq_zero W ι σ h)

/-- Injective labels provide a large enough grid to recover the polynomial identity. -/
theorem invariant_iff_fingerprint_eq_zero (W : U → F) (ι : U ↪ F) (σ : Equiv.Perm U) :
    W ∘ σ = W ↔ ∀ β γ, fingerprint W ι σ β γ = 0 := by
  classical
  constructor
  · exact fun h β γ => fingerprint_eq_zero W ι σ h β γ
  · intro h
    cases isEmpty_or_nonempty U with
    | inl hU => exact funext fun u => isEmptyElim u
    | inr hU =>
      apply invariant_of_polynomial_eq_zero W ι σ
      apply MvPolynomial.eq_zero_of_degreeOf_lt_card_of_eval_eq_zero_of_fin
        (fun _ => Finset.univ.map ι)
      · intro i
        have hdeg := (degreeOf_le_totalDegree (polynomial W ι σ) i).trans
          (totalDegree_polynomial_le W ι σ)
        simpa using hdeg.trans_lt (Nat.sub_lt Fintype.card_pos (by decide : 0 < 1))
      · intro x _
        simpa using h (x 0) (x 1)

end Field

section Probability

open scoped ProbabilityTheory ENNReal NNReal

variable {F : Type} [Field F] [Fintype F] [SampleableType F]

/-- A false permutation claim passes a joint uniform challenge with probability at most
`(|U| - 1) / |F|`, in the nonnegative-real error convention. -/
theorem prob_fingerprint_eq_zero_le (W : U → F) (ι : U ↪ F) (σ : Equiv.Perm U)
    (hW : W ∘ σ ≠ W) :
    Pr{let r ← $ᵗ (F × F)}[fingerprint W ι σ r.1 r.2 = 0] ≤
      (((Fintype.card U - 1 : ℕ) : ℝ≥0) / Fintype.card F : ℝ≥0) := by
  have hb := Probability.prob_schwartz_zippel_mv_polynomial_of_totalDegree_le
    (polynomial W ι σ) (polynomial_ne_zero W ι σ hW)
    (totalDegree_polynomial_le W ι σ)
  rw [ENNReal.coe_div (by simp), ENNReal.coe_natCast, ENNReal.coe_natCast]
  rw [← SampleableType.prEvent_uniformSample_equiv (finTwoArrowEquiv F)
    (fun r => fingerprint W ι σ r.1 r.2 = 0)]
  simpa using hb

end Probability
end PermutationFingerprint
