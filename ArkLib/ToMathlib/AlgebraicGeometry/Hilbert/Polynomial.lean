/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.ToMathlib.AlgebraicGeometry.Hilbert.StandardMonomials
public import ArkLib.ToMathlib.AlgebraicGeometry.Hilbert.MonomialCounting
public import ArkLib.ToMathlib.AlgebraicGeometry.PrincipalCut.Degree
public import ArkLib.ToMathlib.AlgebraicGeometry.ZeroLocus.ZeroDimensional
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Order.Interval.Set.Infinite

/-!
# Canonical Hilbert polynomials of affine quotients

Standard monomials and finite-cone inclusion-exclusion prove eventual polynomiality
of the actual total-degree filtration. Uniqueness makes the polynomial independent
of the finite ordering chosen in its existence proof. Finite-dimensional quotients
have constant polynomial equal to their dimension. The principal-cut inequality then
applies to these canonical polynomials without any eventual-polynomial premises.
-/

@[expose] public section

noncomputable section

namespace AffineHilbert

/-- Two rational polynomials agreeing on a tail of natural numbers are equal. -/
theorem polynomial_eq_of_eval_nat_ge {P Q : Polynomial ℚ} {N₀ : ℕ}
    (h : ∀ N ≥ N₀, P.eval (N : ℚ) = Q.eval (N : ℚ)) : P = Q := by
  apply Polynomial.eq_of_infinite_eval_eq
  have hinj : Function.Injective (fun N : ℕ ↦ (N : ℚ)) := Nat.cast_injective
  apply ((Set.Ici_infinite N₀).image hinj.injOn).mono
  rintro x ⟨N, hN, rfl⟩
  exact h N hN

end AffineHilbert

namespace AffineHilbert

variable {F σ : Type*} [Field F] [Finite σ]

/-- The actual degree filtration on every affine quotient has an eventual rational
Hilbert polynomial of degree at most the number of variables. -/
theorem exists_hilbertPolynomial (I : Ideal (MvPolynomial σ F)) :
    ∃ P : Polynomial ℚ, P.natDegree ≤ Nat.card σ ∧
      ∃ N₀ : ℕ, ∀ N ≥ N₀, P.eval (N : ℚ) = (hilbertFunction I N : ℚ) := by
  classical
  let _ : Fintype σ := Fintype.ofFinite σ
  let _ : LinearOrder σ := (Fintype.equivFin σ).linearOrder
  obtain ⟨B, hB⟩ := exists_finset_forbidden_standardExponents I
  obtain ⟨P, hdeg, N₀, hP⟩ :=
    MonomialHilbertCounting.exists_eventual_standardExponent_countingPolynomial σ B
  refine ⟨P, hdeg, N₀, fun N hN ↦ ?_⟩
  rw [hP N hN, hilbertFunction_eq_standard_count]
  congr 2
  ext e
  simp only [MonomialHilbertCounting.standardExponentSet, Set.mem_ofPred_eq, hB]
  exact and_comm

/-- The canonical eventual Hilbert polynomial of an actual affine ideal quotient. -/
def hilbertPolynomial (I : Ideal (MvPolynomial σ F)) : Polynomial ℚ :=
  (exists_hilbertPolynomial I).choose

theorem hilbertPolynomial_natDegree_le (I : Ideal (MvPolynomial σ F)) :
    (hilbertPolynomial I).natDegree ≤ Nat.card σ :=
  (exists_hilbertPolynomial I).choose_spec.1

theorem hilbertPolynomial_eventually (I : Ideal (MvPolynomial σ F)) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (hilbertPolynomial I).eval (N : ℚ) = (hilbertFunction I N : ℚ) :=
  (exists_hilbertPolynomial I).choose_spec.2

/-- The eventual polynomial is characterized by the actual filtration dimensions. -/
theorem hilbertPolynomial_unique (I : Ideal (MvPolynomial σ F)) {P : Polynomial ℚ}
    (hP : ∃ N₀ : ℕ, ∀ N ≥ N₀, P.eval (N : ℚ) = (hilbertFunction I N : ℚ)) :
    P = hilbertPolynomial I := by
  obtain ⟨NP, hP⟩ := hP
  obtain ⟨NI, hI⟩ := hilbertPolynomial_eventually I
  apply polynomial_eq_of_eval_nat_ge (N₀ := max NP NI)
  intro N hN
  rw [hP N ((le_max_left NP NI).trans hN), hI N ((le_max_right NP NI).trans hN)]

end AffineHilbert

namespace AffineHilbert

variable {F σ : Type*} [Field F] [Finite σ]

omit [Finite σ] in
/-- A finite-dimensional affine quotient is exhausted by one finite degree level. -/
theorem quotientDegreeLE_eventually_top (I : Ideal (MvPolynomial σ F))
    [Module.Finite F (MvPolynomial σ F ⧸ I)] :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, quotientDegreeLE I N = ⊤ := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := F) (M := MvPolynomial σ F ⧸ I)
  have hrep : ∀ x : MvPolynomial σ F ⧸ I, ∃ p : MvPolynomial σ F,
      Ideal.Quotient.mkₐ F I p = x := fun x ↦ Ideal.Quotient.mk_surjective x
  choose p hp using hrep
  refine ⟨s.sup (fun x ↦ (p x).totalDegree), fun N hN ↦ ?_⟩
  apply top_unique
  rw [← hs]
  apply Submodule.span_le.mpr
  intro x hx
  exact ⟨p x, (MvPolynomial.mem_restrictTotalDegree σ N (p x)).mpr
    ((Finset.le_sup hx).trans hN), hp x⟩

/-- For a finite quotient, the Hilbert polynomial is its vector-space dimension. -/
theorem hilbertPolynomial_eq_constant (I : Ideal (MvPolynomial σ F))
    [Module.Finite F (MvPolynomial σ F ⧸ I)] :
    hilbertPolynomial I = Polynomial.C (Module.finrank F (MvPolynomial σ F ⧸ I) : ℚ) := by
  symm
  apply hilbertPolynomial_unique
  obtain ⟨N₀, hN₀⟩ := quotientDegreeLE_eventually_top I
  refine ⟨N₀, fun N hN ↦ ?_⟩
  rw [Polynomial.eval_C, hilbertFunction, hN₀ N hN, finrank_top]

end AffineHilbert

namespace AffineHilbert

variable {F σ : Type*} [Field F] [Finite σ]

theorem hilbertPolynomial_eventually_eval (I : Ideal (MvPolynomial σ F)) :
    ∀ᶠ N : ℕ in Filter.atTop,
      (hilbertPolynomial I).eval (N : ℚ) = (hilbertFunction I N : ℚ) := by
  exact Filter.eventually_atTop.mpr (hilbertPolynomial_eventually I)

/-- A proper principal cut satisfies the genuine Hilbert-polynomial degree and
coefficient bounds, with the empty quotient represented by the zero polynomial. -/
theorem principalCut_hilbertPolynomial_zero_or_degree_and_coeff
    {I : Ideal (MvPolynomial σ F)} (hI : I.IsPrime)
    {f : MvPolynomial σ F} (hfI : f ∉ I) {b : ℕ} (hfdeg : f.totalDegree ≤ b) :
    hilbertPolynomial (I ⊔ Ideal.span {f}) = 0 ∨
      (hilbertPolynomial (I ⊔ Ideal.span {f})).natDegree ≤
          (hilbertPolynomial I).natDegree - 1 ∧
        (hilbertPolynomial (I ⊔ Ideal.span {f})).coeff ((hilbertPolynomial I).natDegree - 1) ≤
          (b : ℚ) * (hilbertPolynomial I).natDegree * (hilbertPolynomial I).leadingCoeff :=
  principalCut_eventualPolynomial_zero_or_degree_and_coeff hI hfI hfdeg
    (hilbertPolynomial_eventually_eval I)
    (hilbertPolynomial_eventually_eval (I ⊔ Ideal.span {f}))

/-- Zero-dimensional affine point counts are bounded by the constant coefficient of
this actual Hilbert polynomial, over every extension field. -/
theorem finite_zeroLocus_and_ncard_le_hilbertPolynomial {E : Type*}
    [Field E] [Algebra F E] (I : Ideal (MvPolynomial σ F))
    [Ring.KrullDimLE 0 (MvPolynomial σ F ⧸ I)] :
    (MvPolynomial.zeroLocus E I).Finite ∧
      ((MvPolynomial.zeroLocus E I).ncard : ℚ) ≤ (hilbertPolynomial I).coeff 0 := by
  have : Module.Finite F (MvPolynomial σ F ⧸ I) :=
    (Module.finite_iff_krullDimLE_zero F (MvPolynomial σ F ⧸ I)).mpr inferInstance
  refine ⟨MvPolynomial.finite_zeroLocus_of_finite_quotient I, ?_⟩
  rw [hilbertPolynomial_eq_constant, Polynomial.coeff_C_zero]
  exact_mod_cast MvPolynomial.ncard_zeroLocus_le_finrank_quotient (E := E) I

end AffineHilbert

namespace AffineHilbert

variable {F σ : Type*} [Field F] [Finite σ]

/-- Passing to a larger ideal can only shrink each actual filtered quotient. -/
theorem hilbertFunction_antitone {I J : Ideal (MvPolynomial σ F)} (hIJ : I ≤ J) (N : ℕ) :
    hilbertFunction J N ≤ hilbertFunction I N := by
  let φ : quotientDegreeLE I N →ₗ[F] quotientDegreeLE J N :=
    ((Ideal.Quotient.factorₐ F hIJ).toLinearMap.domRestrict (quotientDegreeLE I N)).codRestrict
      (quotientDegreeLE J N) (fun x ↦ by
        obtain ⟨p, hp, hpx⟩ := x.property
        refine ⟨p, hp, ?_⟩
        change Ideal.Quotient.mkₐ F J p = Ideal.Quotient.factorₐ F hIJ x
        rw [← hpx]
        rfl)
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨p, hp, hpy⟩ := y.property
    refine ⟨⟨Ideal.Quotient.mkₐ F I p, ⟨p, hp, rfl⟩⟩, Subtype.ext ?_⟩
    exact hpy
  exact LinearMap.finrank_le_finrank_of_surjective hφ

/-- A proper ideal has a nonzero Hilbert polynomial. -/
theorem hilbertPolynomial_ne_zero {I : Ideal (MvPolynomial σ F)} (hI : I ≠ ⊤) :
    hilbertPolynomial I ≠ 0 := by
  intro hz
  obtain ⟨N₀, hN₀⟩ := hilbertPolynomial_eventually I
  have he := hN₀ N₀ le_rfl
  rw [hz, Polynomial.eval_zero] at he
  have hpos := one_le_hilbertFunction I hI N₀
  have he0 : hilbertFunction I N₀ = 0 := by exact_mod_cast he.symm
  omega

/-- Ideal inclusion compares degrees and equal-degree leading coefficients of the
canonical Hilbert polynomials. -/
theorem hilbertPolynomial_degree_and_leadingCoeff_antitone
    {I J : Ideal (MvPolynomial σ F)} (hIJ : I ≤ J) (hJ : J ≠ ⊤) :
    (hilbertPolynomial J).natDegree ≤ (hilbertPolynomial I).natDegree ∧
      ((hilbertPolynomial J).natDegree = (hilbertPolynomial I).natDegree →
        (hilbertPolynomial J).leadingCoeff ≤ (hilbertPolynomial I).leadingCoeff) := by
  apply natDegree_le_of_eventually_eval_nat_le (hilbertPolynomial_ne_zero hJ)
  · filter_upwards [hilbertPolynomial_eventually_eval J] with N hN
    rw [hN]
    positivity
  · filter_upwards [hilbertPolynomial_eventually_eval I,
      hilbertPolynomial_eventually_eval J] with N hIN hJN
    rw [hIN, hJN]
    exact_mod_cast hilbertFunction_antitone hIJ N

end AffineHilbert

namespace AffineHilbert

variable {F σ : Type*} [Field F] [Finite σ]

omit [Finite σ] in
/-- The total-degree filtration is increasing. -/
theorem quotientDegreeLE_mono (I : Ideal (MvPolynomial σ F)) {N M : ℕ} (hNM : N ≤ M) :
    quotientDegreeLE I N ≤ quotientDegreeLE I M := by
  rintro x ⟨p, hp, hpx⟩
  exact ⟨p, (MvPolynomial.mem_restrictTotalDegree σ M p).mpr
    (((MvPolynomial.mem_restrictTotalDegree σ N p).mp hp).trans hNM), hpx⟩

/-- A constant Hilbert polynomial forces the actual coordinate quotient to be finite. -/
theorem moduleFinite_of_hilbertPolynomial_natDegree_zero
    (I : Ideal (MvPolynomial σ F)) (hdeg : (hilbertPolynomial I).natDegree = 0) :
    Module.Finite F (MvPolynomial σ F ⧸ I) := by
  obtain ⟨N₀, hN₀⟩ := hilbertPolynomial_eventually I
  have hc := Polynomial.eq_C_of_natDegree_le_zero (le_of_eq hdeg)
  have hrank : ∀ N ≥ N₀, hilbertFunction I N = hilbertFunction I N₀ := by
    intro N hN
    have hleft := hN₀ N hN
    have hright := hN₀ N₀ le_rfl
    rw [hc, Polynomial.eval_C] at hleft hright
    exact_mod_cast hleft.symm.trans hright
  have htop : quotientDegreeLE I N₀ = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    let M := max N₀ p.totalDegree
    have hle : N₀ ≤ M := le_max_left _ _
    have heq : quotientDegreeLE I N₀ = quotientDegreeLE I M :=
      Submodule.eq_of_le_of_finrank_eq (quotientDegreeLE_mono I hle) (hrank M hle).symm
    rw [heq]
    exact ⟨p, (MvPolynomial.mem_restrictTotalDegree σ M p).mpr (le_max_right _ _), rfl⟩
  have hfinite : Module.Finite F (⊤ : Submodule F (MvPolynomial σ F ⧸ I)) := by
    rw [← htop]
    infer_instance
  exact Module.Finite.of_surjective (⊤ : Submodule F (MvPolynomial σ F ⧸ I)).subtype
    (fun x ↦ ⟨⟨x, Submodule.mem_top⟩, rfl⟩)

end AffineHilbert
