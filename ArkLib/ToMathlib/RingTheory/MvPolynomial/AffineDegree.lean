/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertPolynomial

/-!
# The affine degree of an ideal

Let `k` be a field, `σ` a finite type and `I` an ideal of `MvPolynomial σ k`. Write
`P = MvPolynomial.affineHilbertPolynomial I` and `d = natDegree P`. The affine degree of `I` is
`d! * leadingCoeff P`, a rational number. For large `N` the affine Hilbert function is
`affineDegree I * N ^ d / d! + O(N ^ (d - 1))`, so `affineDegree I` is the normalized leading
term of the growth of the quotient `MvPolynomial σ k ⧸ I` under the total-degree filtration.

The affine degree is nonnegative, and positive exactly for proper ideals; the unit ideal has
degree `0`. The polynomial ring has degree `1`. A finite-dimensional quotient has degree equal to
its dimension over `k`, and a nonzero principal ideal `span {f}` has degree `totalDegree f`.
Along an inclusion `I ≤ J` of ideals whose polynomials have the same natural degree, the degree
of `J` is at most that of `I`.

The bound on the number of points of a zero-dimensional zero locus by the affine degree is
`MvPolynomial.ncard_zeroLocus_le_affineDegree` in
`ArkLib.ToMathlib.RingTheory.Nullstellensatz.AffineHilbertPolynomial`.

## Main statements

* `MvPolynomial.affineDegree`: the definition.
* `MvPolynomial.affineDegree_nonneg`, `MvPolynomial.affineDegree_pos_iff`,
  `MvPolynomial.affineDegree_top`: sign.
* `MvPolynomial.affineDegree_bot`: the polynomial ring has degree `1`.
* `MvPolynomial.affineDegree_eq_finrank`: finite-dimensional quotients.
* `MvPolynomial.affineDegree_span_singleton`: hypersurfaces.
* `MvPolynomial.affineDegree_le_of_le`: comparison along inclusions of the same dimension.
-/

@[expose] public section

noncomputable section

open Polynomial

namespace MvPolynomial

variable {k σ : Type*} [Field k] [Finite σ]

/-- The affine degree of `I`: `d! * leadingCoeff P`, where `P` is the affine Hilbert polynomial
of `I` and `d` its natural degree. The factor `d!` makes the polynomial ring have degree `1`
(`affineDegree_bot`) and a finite-dimensional quotient have degree equal to its dimension
(`affineDegree_eq_finrank`). -/
def affineDegree (I : Ideal (MvPolynomial σ k)) : ℚ :=
  ((affineHilbertPolynomial I).natDegree.factorial : ℚ) * (affineHilbertPolynomial I).leadingCoeff

/-- The affine degree is nonnegative, because the affine Hilbert polynomial is eventually
nonnegative on the natural numbers and so has a nonnegative leading coefficient. -/
theorem affineDegree_nonneg (I : Ideal (MvPolynomial σ k)) : 0 ≤ affineDegree I :=
  mul_nonneg (Nat.cast_nonneg _)
    (leadingCoeff_nonneg_of_eventually_eval_natCast_nonneg
      (eventually_eval_affineHilbertPolynomial_nonneg I))

/-- The unit ideal has affine degree `0`, since its affine Hilbert polynomial is zero. -/
@[simp]
theorem affineDegree_top : affineDegree (⊤ : Ideal (MvPolynomial σ k)) = 0 := by
  simp [affineDegree]

/-- A proper ideal has positive affine degree, since its affine Hilbert polynomial has positive
leading coefficient. -/
theorem affineDegree_pos {I : Ideal (MvPolynomial σ k)} (hI : I ≠ ⊤) : 0 < affineDegree I :=
  mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos _)) (leadingCoeff_affineHilbertPolynomial_pos hI)

/-- The affine degree is positive exactly for proper ideals. -/
theorem affineDegree_pos_iff {I : Ideal (MvPolynomial σ k)} : 0 < affineDegree I ↔ I ≠ ⊤ :=
  ⟨fun h hI ↦ by simp [hI] at h, affineDegree_pos⟩

/-- The affine degree vanishes exactly for the unit ideal. -/
@[simp]
theorem affineDegree_eq_zero_iff {I : Ideal (MvPolynomial σ k)} : affineDegree I = 0 ↔ I = ⊤ := by
  rw [← not_iff_not, ← Ne, ← Ne, ← affineDegree_pos_iff]
  exact ⟨(affineDegree_nonneg I).lt_of_ne', ne_of_gt⟩

/-- When the affine Hilbert polynomial is constant, the affine degree is that constant. -/
theorem affineDegree_of_natDegree_eq_zero {I : Ideal (MvPolynomial σ k)}
    (hdeg : (affineHilbertPolynomial I).natDegree = 0) :
    affineDegree I = (affineHilbertPolynomial I).coeff 0 := by
  rw [affineDegree, hdeg, Nat.factorial_zero, Nat.cast_one, one_mul, leadingCoeff, hdeg]

/-- A finite-dimensional quotient has affine degree equal to its dimension over `k`, since its
affine Hilbert polynomial is that constant (`affineHilbertPolynomial_eq_C_finrank`). -/
theorem affineDegree_eq_finrank (I : Ideal (MvPolynomial σ k))
    [Module.Finite k (MvPolynomial σ k ⧸ I)] :
    affineDegree I = (Module.finrank k (MvPolynomial σ k ⧸ I) : ℚ) := by
  rw [affineDegree, affineHilbertPolynomial_eq_C_finrank, natDegree_C, Nat.factorial_zero,
    Nat.cast_one, one_mul, leadingCoeff_C]

/-- The polynomial ring has affine degree `1`: in `n` variables its affine Hilbert polynomial
`Polynomial.preHilbertPoly ℚ n 0` has natural degree `n` and leading coefficient `1 / n!`. -/
@[simp]
theorem affineDegree_bot : affineDegree (⊥ : Ideal (MvPolynomial σ k)) = 1 := by
  rw [affineDegree, affineHilbertPolynomial_bot, natDegree_preHilbertPoly,
    leadingCoeff_preHilbertPoly]
  exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))

/-- A nonzero principal ideal `span {f}` has affine degree `totalDegree f`.

In `n` variables the affine Hilbert polynomial of `span {f}` is the backward difference with step
`b = totalDegree f` of `Polynomial.preHilbertPoly ℚ n 0`, which for `b > 0` has natural degree
`n - 1` and leading coefficient `b * n / n!`. For `b = 0`, `f` is a nonzero constant, the ideal is
the unit ideal and both sides are `0`. The hypothesis `f ≠ 0` is needed: `span {0} = ⊥` has
degree `1`, while `totalDegree 0 = 0`. -/
theorem affineDegree_span_singleton {f : MvPolynomial σ k} (hf : f ≠ 0) :
    affineDegree (Ideal.span {f}) = (f.totalDegree : ℚ) := by
  rw [affineDegree, affineHilbertPolynomial_span_singleton hf]
  rcases Nat.eq_zero_or_pos f.totalDegree with hb | hb
  · simp [hb, backwardDifference_zero_left]
  have hσ : 0 < Nat.card σ := by
    obtain ⟨e, he, hepos⟩ : ∃ e ∈ f.support, 0 < e.degree := by
      by_contra! h
      exact hb.ne' (Nat.le_zero.mp (Finset.sup_le h))
    obtain ⟨i, -⟩ := (Finsupp.support_nonempty_iff (f := e)).mpr fun h0 ↦ by
      rw [h0, map_zero] at hepos
      exact lt_irrefl 0 hepos
    have : Nonempty σ := ⟨i⟩
    exact Nat.card_pos
  obtain ⟨hdeg, hlc⟩ := natDegree_backwardDifference_eq_and_leadingCoeff_of_ne_zero
    (Nat.cast_ne_zero.mpr hb.ne') (P := preHilbertPoly ℚ (Nat.card σ) 0)
    (by rwa [natDegree_preHilbertPoly])
  rw [hdeg, hlc, natDegree_preHilbertPoly, leadingCoeff_preHilbertPoly]
  obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero hσ.ne'
  rw [hr, Nat.succ_sub_one, Nat.factorial_succ]
  push_cast
  field_simp

/-- Along an inclusion `I ≤ J` whose affine Hilbert polynomials have the same natural degree, the
affine degree of `J` is at most that of `I`, because the leading coefficients compare the same
way (`leadingCoeff_affineHilbertPolynomial_le_of_le`). The equal-degree hypothesis is needed:
`⊥ ≤ span {X 0 ^ 2}` in one variable, with degrees `1` and `2`. -/
theorem affineDegree_le_of_le {I J : Ideal (MvPolynomial σ k)} (hIJ : I ≤ J)
    (hdeg : (affineHilbertPolynomial J).natDegree = (affineHilbertPolynomial I).natDegree) :
    affineDegree J ≤ affineDegree I := by
  rw [affineDegree, affineDegree, hdeg]
  exact mul_le_mul_of_nonneg_left (leadingCoeff_affineHilbertPolynomial_le_of_le hIJ hdeg)
    (Nat.cast_nonneg _)

end MvPolynomial
