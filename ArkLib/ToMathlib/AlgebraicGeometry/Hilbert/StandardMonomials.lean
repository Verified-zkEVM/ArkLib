/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.ToMathlib.AlgebraicGeometry.Hilbert.Function
public import Mathlib.Data.Finsupp.PWO
public import Mathlib.RingTheory.MvPolynomial.Groebner
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex

/-!
# Standard monomials for actual affine quotient filtrations

Division by the nonzero elements of an ideal gives a standard representative without
increasing total degree. Standard representatives are unique, because a nonzero element
of the ideal cannot have a standard leading monomial. This constructs the actual normal
space used to reduce affine Hilbert functions to monomial counting.
-/

@[expose] public section

noncomputable section

namespace AffineHilbert

open MvPolynomial MonomialOrder
open scoped MonomialOrder BigOperators

variable {F σ : Type*} [Field F] [LinearOrder σ] [WellFoundedGT σ]

/-- Exponents not divisible by any leading exponent of a nonzero ideal element. -/
def standardExponents (I : Ideal (MvPolynomial σ F)) : Set (σ →₀ ℕ) :=
  {e | ∀ p ∈ I, p ≠ 0 → ¬ degLex.degree p ≤ e}

/-- The genuine linear space spanned by the ideal's standard monomials. -/
def standardSpace (I : Ideal (MvPolynomial σ F)) : Submodule F (MvPolynomial σ F) :=
  restrictSupport F (standardExponents I)

/-- A standard polynomial in the ideal must be zero. -/
theorem eq_zero_of_mem_standardSpace_of_mem_ideal (I : Ideal (MvPolynomial σ F))
    (p : MvPolynomial σ F) (hp : p ∈ standardSpace I) (hI : p ∈ I) : p = 0 := by
  by_contra hp0
  exact hp (degLex.degree_mem_support hp0) p hI hp0 le_rfl

/-- Every polynomial has a standard representative of no larger total degree, modulo the ideal. -/
theorem exists_standard_representative (I : Ideal (MvPolynomial σ F)) (p : MvPolynomial σ F) :
    ∃ q ∈ standardSpace I, p - q ∈ I ∧ q.totalDegree ≤ p.totalDegree := by
  classical
  let B : Set (MvPolynomial σ F) := {b | b ∈ I ∧ b ≠ 0}
  have hb : ∀ b ∈ B, IsUnit (degLex.leadingCoeff b) :=
    fun b hb ↦ degLex.isUnit_leadingCoeff.mpr hb.2
  obtain ⟨g, q, hp, hdeg, hq⟩ := degLex.div_set hb p
  have hstd : q ∈ standardSpace I := by
    intro e he b hbI hb0
    exact hq e he b ⟨hbI, hb0⟩
  have hmem : Finsupp.linearCombination (MvPolynomial σ F) (fun b : B ↦ b.val) g ∈ I := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
    apply I.sum_mem
    intro b _
    exact I.smul_mem (g b) b.property.1
  have hsumdeg :
      (Finsupp.linearCombination (MvPolynomial σ F) (fun b : B ↦ b.val) g).totalDegree ≤
        p.totalDegree := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
    apply totalDegree_finsetSum_le
    intro b _
    simpa only [smul_eq_mul, mul_comm] using degLex_totalDegree_monotone (hdeg b)
  refine ⟨q, hstd, ?_, ?_⟩
  · rw [hp, add_sub_cancel_right]
    exact hmem
  · have hsub : q = p - Finsupp.linearCombination (MvPolynomial σ F) (fun b : B ↦ b.val) g := by
      rw [hp]
      ring
    rw [hsub]
    exact (totalDegree_sub _ _).trans (max_le le_rfl hsumdeg)

/-- Distinct standard representatives cannot define the same quotient class. -/
theorem standard_representative_unique (I : Ideal (MvPolynomial σ F))
    {p q : MvPolynomial σ F} (hp : p ∈ standardSpace I) (hq : q ∈ standardSpace I)
    (hpq : p - q ∈ I) : p = q := by
  exact sub_eq_zero.mp (eq_zero_of_mem_standardSpace_of_mem_ideal I (p - q)
    ((standardSpace I).sub_mem hp hq) hpq)

/-- The quotient map restricted to the actual standard-monomial space. -/
def standardQuotientMap (I : Ideal (MvPolynomial σ F)) :
    standardSpace I →ₗ[F] (MvPolynomial σ F ⧸ I) :=
  (Ideal.Quotient.mkₐ F I).toLinearMap.domRestrict (standardSpace I)

/-- Every quotient class has exactly one standard representative. -/
theorem standardQuotientMap_bijective (I : Ideal (MvPolynomial σ F)) :
    Function.Bijective (standardQuotientMap I) := by
  constructor
  · intro p q hpq
    apply Subtype.ext
    apply standard_representative_unique I p.property q.property
    exact Ideal.Quotient.eq.mp hpq
  · intro x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨q, hq, hpq, _⟩ := exists_standard_representative I p
    refine ⟨⟨q, hq⟩, ?_⟩
    exact (Ideal.Quotient.eq.mpr hpq).symm

/-- Standard monomials restricted to a genuine total-degree piece. -/
def standardDegreeLE (I : Ideal (MvPolynomial σ F)) (N : ℕ) :
    Submodule F (MvPolynomial σ F) :=
  restrictSupport F {e | e ∈ standardExponents I ∧ e.degree ≤ N}

/-- Membership in the bounded standard space records both independent restrictions. -/
theorem mem_standardDegreeLE (I : Ideal (MvPolynomial σ F)) (N : ℕ)
    (p : MvPolynomial σ F) :
    p ∈ standardDegreeLE I N ↔ p ∈ standardSpace I ∧ p.totalDegree ≤ N := by
  constructor
  · intro hp
    constructor
    · intro e he
      exact (hp he).1
    · apply Finset.sup_le
      intro e he
      exact (hp he).2
  · rintro ⟨hstd, hdeg⟩ e he
    exact ⟨hstd he, (le_totalDegree he).trans hdeg⟩

/-- The quotient map on the bounded standard space lands in the actual quotient filtration. -/
def standardFilteredMap (I : Ideal (MvPolynomial σ F)) (N : ℕ) :
    standardDegreeLE I N →ₗ[F] quotientDegreeLE I N :=
  ((Ideal.Quotient.mkₐ F I).toLinearMap.domRestrict (standardDegreeLE I N)).codRestrict
    (quotientDegreeLE I N) (fun p ↦ by
      refine ⟨p.val, ?_, rfl⟩
      exact (mem_restrictTotalDegree σ N p.val).mpr
        ((mem_standardDegreeLE I N p.val).mp p.property).2)

/-- Degree-controlled division makes the bounded standard map bijective. -/
theorem standardFilteredMap_bijective (I : Ideal (MvPolynomial σ F)) (N : ℕ) :
    Function.Bijective (standardFilteredMap I N) := by
  constructor
  · intro p q hpq
    apply Subtype.ext
    apply standard_representative_unique I
      ((mem_standardDegreeLE I N p.val).mp p.property).1
      ((mem_standardDegreeLE I N q.val).mp q.property).1
    exact Ideal.Quotient.eq.mp (congrArg Subtype.val hpq)
  · intro x
    obtain ⟨p, hp, hpx⟩ := x.property
    obtain ⟨q, hq, hpq, hdeg⟩ := exists_standard_representative I p
    have hqN : q ∈ standardDegreeLE I N := (mem_standardDegreeLE I N q).mpr
      ⟨hq, hdeg.trans ((mem_restrictTotalDegree σ N p).mp hp)⟩
    refine ⟨⟨q, hqN⟩, Subtype.ext ?_⟩
    change Ideal.Quotient.mk I q = x.val
    rw [← hpx]
    exact (Ideal.Quotient.eq.mpr hpq).symm

/-- The affine Hilbert function counts the actual standard exponents of bounded degree.
This reduces eventual-polynomial questions to finite monomial counting. -/
theorem hilbertFunction_eq_standard_count [Finite σ]
    (I : Ideal (MvPolynomial σ F)) (N : ℕ) :
    hilbertFunction I N = {e : σ →₀ ℕ | e ∈ standardExponents I ∧ e.degree ≤ N}.ncard := by
  classical
  let e := LinearEquiv.ofBijective (standardFilteredMap I N) (standardFilteredMap_bijective I N)
  rw [hilbertFunction, ← e.finrank_eq]
  have hfinite : {e : σ →₀ ℕ | e ∈ standardExponents I ∧ e.degree ≤ N}.Finite :=
    (Finsupp.finite_of_degree_le N).subset (fun _ he ↦ he.2)
  let := hfinite.fintype
  exact (Module.finrank_eq_card_basis (basisRestrictSupport F
    {e | e ∈ standardExponents I ∧ e.degree ≤ N})).trans (by simp)

/-- Standard exponents form a lower set for divisibility. -/
theorem standardExponents_lower (I : Ideal (MvPolynomial σ F))
    {a b : σ →₀ ℕ} (hab : a ≤ b) (hb : b ∈ standardExponents I) :
    a ∈ standardExponents I := by
  intro p hp hp0 hpa
  exact hb p hp hp0 (hpa.trans hab)

/-- Dickson's lemma gives a finite forbidden-divisor description of standard monomials. -/
theorem exists_finset_forbidden_standardExponents [Finite σ]
    (I : Ideal (MvPolynomial σ F)) :
    ∃ B : Finset (σ →₀ ℕ), ∀ e,
      e ∈ standardExponents I ↔ ∀ b ∈ B, ¬b ≤ e := by
  classical
  let bad : (σ →₀ ℕ) → Prop := fun e ↦ e ∉ standardExponents I
  have hantichain : IsAntichain (· ≤ ·) {b | Minimal bad b} := by
    intro a ha b hb hab hle
    exact hab (le_antisymm hle (hb.2 ha.1 hle))
  have hfinite : {b | Minimal bad b}.Finite :=
    WellQuasiOrderedLE.finite_of_isAntichain hantichain
  refine ⟨hfinite.toFinset, fun e ↦ ⟨?_, ?_⟩⟩
  · intro he b hb hbe
    have hbad : bad b := (hfinite.mem_toFinset.mp hb).1
    exact hbad (standardExponents_lower I hbe he)
  · intro he
    by_contra hbad
    obtain ⟨b, hbe, hb⟩ := exists_minimal_le_of_wellFoundedLT bad e hbad
    exact he b (hfinite.mem_toFinset.mpr hb) hbe

end AffineHilbert

end
