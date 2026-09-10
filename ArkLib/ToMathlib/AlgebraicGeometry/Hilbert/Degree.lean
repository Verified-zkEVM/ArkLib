/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.ToMathlib.AlgebraicGeometry.PrincipalCut.Polynomial
public import ArkLib.ToMathlib.AlgebraicGeometry.PrincipalCut.ComponentCoefficient

/-!
# Degree from the actual affine Hilbert polynomial

Degree is the factorial-normalized leading coefficient of the unique polynomial
of actual filtration dimensions. Its elementary bounds and terminal point counts
are proved here; no geometric degree laws are postulated.
-/

@[expose] public section

noncomputable section

namespace AffineHilbert

open MvPolynomial Polynomial Filter

variable {F σ : Type*} [Field F] [Finite σ]

/-- The factorial-normalized leading coefficient of the actual affine Hilbert polynomial. -/
def affineDegree (I : Ideal (MvPolynomial σ F)) : ℚ :=
  ((hilbertPolynomial I).natDegree.factorial : ℚ) * (hilbertPolynomial I).leadingCoeff

/-- Actual affine degree is nonnegative. -/
theorem affineDegree_nonneg (I : Ideal (MvPolynomial σ F)) : 0 ≤ affineDegree I := by
  have hnonneg : ∀ᶠ N : ℕ in atTop, 0 ≤ (hilbertPolynomial I).eval (N : ℚ) := by
    filter_upwards [hilbertPolynomial_eventually_eval I] with N hN
    rw [hN]
    positivity
  have hc := coeff_nonneg_of_natDegree_le_of_eventually_eval_nat_nonneg
    (P := hilbertPolynomial I) le_rfl hnonneg
  rw [Polynomial.coeff_natDegree] at hc
  exact mul_nonneg (by positivity) hc

/-- A proper affine ideal has strictly positive degree. -/
theorem affineDegree_pos {I : Ideal (MvPolynomial σ F)} (hI : I ≠ ⊤) :
    0 < affineDegree I := by
  have hne : affineDegree I ≠ 0 := mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero _)
    (Polynomial.leadingCoeff_ne_zero.mpr (hilbertPolynomial_ne_zero hI))
  exact (affineDegree_nonneg I).lt_of_ne' hne

/-- Affine space has degree one. -/
theorem affineDegree_bot : affineDegree (⊥ : Ideal (MvPolynomial σ F)) = 1 := by
  rw [affineDegree, hilbertPolynomial_bot, Polynomial.natDegree_preHilbertPoly,
    Polynomial.leadingCoeff_preHilbertPoly]
  exact mul_inv_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero (Nat.card σ))

/-- For finite quotients the actual degree equals their vector-space dimension. -/
theorem affineDegree_eq_finrank (I : Ideal (MvPolynomial σ F))
    [Module.Finite F (MvPolynomial σ F ⧸ I)] :
    affineDegree I = (Module.finrank F (MvPolynomial σ F ⧸ I) : ℚ) := by
  rw [affineDegree, hilbertPolynomial_eq_constant, Polynomial.natDegree_C,
    Nat.factorial_zero, Nat.cast_one, one_mul, Polynomial.leadingCoeff_C]

/-- Degree-zero Hilbert terminals have finite extension-field point sets, bounded
by their actual affine degree. -/
theorem finite_zeroLocus_and_ncard_le_affineDegree {E : Type*} [Field E] [Algebra F E]
    (I : Ideal (MvPolynomial σ F)) (hdeg : (hilbertPolynomial I).natDegree = 0) :
    (MvPolynomial.zeroLocus E I).Finite ∧
      ((MvPolynomial.zeroLocus E I).ncard : ℚ) ≤ affineDegree I := by
  have := moduleFinite_of_hilbertPolynomial_natDegree_zero I hdeg
  refine ⟨MvPolynomial.finite_zeroLocus_of_finite_quotient I, ?_⟩
  rw [affineDegree_eq_finrank]
  exact_mod_cast MvPolynomial.ncard_zeroLocus_le_finrank_quotient (E := E) I

end AffineHilbert

namespace AffineHilbert

open MvPolynomial Polynomial

variable {F σ : Type*} [Field F] [Finite σ]

/-- A nonzero proper polynomial hypersurface has degree equal to its total degree. -/
theorem affineDegree_span_singleton {f : MvPolynomial σ F} (hf : f ≠ 0)
    (hproper : Ideal.span ({f} : Set (MvPolynomial σ F)) ≠ ⊤) :
    affineDegree (Ideal.span {f}) = (f.totalDegree : ℚ) := by
  classical
  let _ : Fintype σ := Fintype.ofFinite σ
  let _ : LinearOrder σ := (Fintype.equivFin σ).linearOrder
  have hb := totalDegree_pos_of_span_singleton_ne_top hf hproper
  have hcard := hilbertPolynomial_span_singleton_natDegree_add_one hf hproper
  have hr : 0 < Fintype.card σ := by
    rw [Nat.card_eq_fintype_card] at hcard
    omega
  let P : ℚ[X] := Polynomial.preHilbertPoly ℚ (Fintype.card σ) 0
  have hd : 0 < P.natDegree := by simpa only [P, Polynomial.natDegree_preHilbertPoly] using hr
  have hP : P ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hd
  obtain ⟨hdeg, hlc⟩ := backwardDifference_natDegree_eq_and_leadingCoeff hb hP hd
  rw [affineDegree, hilbertPolynomial_span_singleton hf]
  change ((backwardDifference f.totalDegree P).natDegree.factorial : ℚ) *
    (backwardDifference f.totalDegree P).leadingCoeff = (f.totalDegree : ℚ)
  rw [hdeg, hlc]
  simp only [P, Polynomial.natDegree_preHilbertPoly, Polynomial.leadingCoeff_preHilbertPoly]
  obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  rw [hr, Nat.succ_sub_one, Nat.factorial_succ]
  push_cast
  field_simp

end AffineHilbert
