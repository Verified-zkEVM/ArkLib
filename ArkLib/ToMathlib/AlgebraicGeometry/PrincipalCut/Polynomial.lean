/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.ToMathlib.AlgebraicGeometry.Hilbert.Polynomial

/-!
# Hilbert polynomial degree of a polynomial hypersurface

A principal ideal has precisely one forbidden leading monomial. Counting its
standard monomials gives the backward difference of the full polynomial-ring
Hilbert polynomial, and hence the exact degree drop.
-/

@[expose] public section

noncomputable section

namespace AffineHilbert

open MvPolynomial MonomialOrder Polynomial
open scoped MonomialOrder

variable {F σ : Type*} [Field F] [Fintype σ] [LinearOrder σ]

omit [Fintype σ] in
/-- The standard monomials for a nonzero principal ideal avoid its generator's
leading monomial. -/
theorem standardExponents_span_singleton [Finite σ] {f : MvPolynomial σ F} (hf : f ≠ 0)
    (e : σ →₀ ℕ) :
    e ∈ standardExponents (Ideal.span {f}) ↔ ¬degLex.degree f ≤ e := by
  constructor
  · intro he
    exact he f (Ideal.subset_span (Set.mem_singleton f)) hf
  · intro he p hp hp0 hle
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton.mp hp
    have hq : q ≠ 0 := by
      intro hz
      simp [hz] at hp0
    rw [degLex.degree_mul hf hq] at hle
    exact he ((show degLex.degree f ≤ degLex.degree f + degLex.degree q from
      fun i ↦ Nat.le_add_right _ _).trans hle)

/-- Translation identifies shifted binomial counting polynomials. -/
theorem preHilbertPoly_eq_taylor (r b : ℕ) :
    Polynomial.preHilbertPoly ℚ r b =
      Polynomial.taylor (-(b : ℚ)) (Polynomial.preHilbertPoly ℚ r 0) := by
  apply polynomial_eq_of_eval_nat_ge (N₀ := b)
  intro N hN
  rw [Polynomial.preHilbertPoly_eq_choose_sub_add ℚ r hN]
  rw [Polynomial.taylor_apply, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C]
  rw [show (N : ℚ) + -(b : ℚ) = ((N - b : ℕ) : ℚ) by
    rw [Nat.cast_sub hN]
    ring]
  rw [Polynomial.preHilbertPoly_eq_choose_sub_add ℚ r (Nat.zero_le (N - b))]
  simp

/-- The one-forbidden-cone counting polynomial is a backward difference. -/
theorem countingPolynomial_singleton (e : σ →₀ ℕ) :
    MonomialHilbertCounting.countingPolynomial σ {e} =
      backwardDifference e.degree (Polynomial.preHilbertPoly ℚ (Fintype.card σ) 0) := by
  classical
  have hpow : ({e} : Finset (σ →₀ ℕ)).powerset = {∅, {e}} := by
    ext T
    simp [Finset.subset_singleton_iff]
  unfold MonomialHilbertCounting.countingPolynomial
  rw [hpow]
  simp only [Finset.mem_singleton, Finset.empty_ne_singleton, not_false_eq_true,
    Finset.sum_insert, Finset.card_empty, pow_zero, one_smul, Finset.sum_singleton,
    Finset.card_singleton, pow_one, neg_smul, MonomialHilbertCounting.forbiddenSup,
    Finset.sup_empty, Finset.sup_singleton, id_eq, backwardDifference]
  rw [preHilbertPoly_eq_taylor (Fintype.card σ) e.degree]
  simp only [show (⊥ : σ →₀ ℕ) = 0 from rfl, show (0 : σ →₀ ℕ).degree = 0 from rfl]
  ring

/-- The canonical Hilbert polynomial of a hypersurface is its exact counting difference. -/
theorem hilbertPolynomial_span_singleton {f : MvPolynomial σ F} (hf : f ≠ 0) :
    hilbertPolynomial (Ideal.span {f}) =
      backwardDifference f.totalDegree (Polynomial.preHilbertPoly ℚ (Fintype.card σ) 0) := by
  classical
  rw [← MvPolynomial.degree_degLexDegree (f := f), ← countingPolynomial_singleton]
  symm
  apply hilbertPolynomial_unique
  refine ⟨MonomialHilbertCounting.forbiddenThreshold {degLex.degree f}, fun N hN ↦ ?_⟩
  rw [MonomialHilbertCounting.countingPolynomial_eval_eq_card σ _ N hN,
    hilbertFunction_eq_standard_count]
  congr 1
  have heq : {e : σ →₀ ℕ | e ∈ standardExponents (Ideal.span {f}) ∧ e.degree ≤ N} =
      (MonomialHilbertCounting.standardExponentFinset σ {degLex.degree f} N : Set (σ →₀ ℕ)) := by
    ext e
    simp only [Set.mem_ofPred_eq, standardExponents_span_singleton hf,
      Finset.mem_coe, MonomialHilbertCounting.mem_standardExponentFinset,
      Finset.mem_singleton, forall_eq]
    exact and_comm
  rw [heq, Set.ncard_coe_finset]

end AffineHilbert

namespace AffineHilbert

open MvPolynomial Polynomial

variable {F σ : Type*} [Field F] [Finite σ]

/-- The polynomial ring has its usual binomial Hilbert polynomial. -/
theorem hilbertPolynomial_bot :
    hilbertPolynomial (⊥ : Ideal (MvPolynomial σ F)) =
      Polynomial.preHilbertPoly ℚ (Nat.card σ) 0 := by
  classical
  let _ : Fintype σ := Fintype.ofFinite σ
  let _ : LinearOrder σ := (Fintype.equivFin σ).linearOrder
  symm
  apply hilbertPolynomial_unique
  refine ⟨0, fun N _ ↦ ?_⟩
  rw [Polynomial.preHilbertPoly_eq_choose_sub_add ℚ _ (Nat.zero_le N),
    hilbertFunction_eq_standard_count]
  have heq : {e : σ →₀ ℕ | e ∈ standardExponents (⊥ : Ideal (MvPolynomial σ F)) ∧
      e.degree ≤ N} = (MonomialHilbertCounting.degreeBall σ N : Set (σ →₀ ℕ)) := by
    ext e
    simp [standardExponents]
  rw [heq, Set.ncard_coe_finset, MonomialHilbertCounting.card_degreeBall]
  simp [Nat.card_eq_fintype_card]

/-- The Hilbert polynomial degree of the polynomial ring is its number of variables. -/
theorem hilbertPolynomial_bot_natDegree :
    (hilbertPolynomial (⊥ : Ideal (MvPolynomial σ F))).natDegree = Nat.card σ := by
  rw [hilbertPolynomial_bot, Polynomial.natDegree_preHilbertPoly]

/-- A nonconstant polynomial cuts the polynomial ring's Hilbert degree by exactly one. -/
theorem hilbertPolynomial_span_singleton_natDegree {f : MvPolynomial σ F}
    (hf : f ≠ 0) (hb : 0 < f.totalDegree) (hσ : 0 < Nat.card σ) :
    (hilbertPolynomial (Ideal.span {f})).natDegree = Nat.card σ - 1 := by
  classical
  let _ : Fintype σ := Fintype.ofFinite σ
  let _ : LinearOrder σ := (Fintype.equivFin σ).linearOrder
  rw [hilbertPolynomial_span_singleton hf]
  have hd : 0 < (Polynomial.preHilbertPoly ℚ (Fintype.card σ) 0).natDegree := by
    simpa only [Polynomial.natDegree_preHilbertPoly, Nat.card_eq_fintype_card] using hσ
  have hP := Polynomial.ne_zero_of_natDegree_gt hd
  have hdegree := (backwardDifference_natDegree_eq_and_leadingCoeff hb hP hd).1
  simpa only [Polynomial.natDegree_preHilbertPoly, Nat.card_eq_fintype_card] using hdegree

end AffineHilbert

namespace AffineHilbert

open MvPolynomial

variable {F σ : Type*} [Field F] [Finite σ]

omit [Finite σ] in
/-- A nonzero polynomial defining a proper ideal has positive total degree. -/
theorem totalDegree_pos_of_span_singleton_ne_top {f : MvPolynomial σ F}
    (hf : f ≠ 0) (hproper : Ideal.span ({f} : Set (MvPolynomial σ F)) ≠ ⊤) :
    0 < f.totalDegree := by
  by_contra! hdeg
  have hC := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero hdeg)
  have hc : f.coeff 0 ≠ 0 := by
    intro hz
    apply hf
    simpa only [hz, map_zero] using hC
  apply hproper
  apply Ideal.span_singleton_eq_top.mpr
  rw [hC]
  exact (isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C

/-- The exact dimension drop for every nonzero proper polynomial hypersurface. -/
theorem hilbertPolynomial_span_singleton_natDegree_add_one {f : MvPolynomial σ F}
    (hf : f ≠ 0) (hproper : Ideal.span ({f} : Set (MvPolynomial σ F)) ≠ ⊤) :
    (hilbertPolynomial (Ideal.span {f})).natDegree + 1 = Nat.card σ := by
  classical
  let _ : Fintype σ := Fintype.ofFinite σ
  let _ : LinearOrder σ := (Fintype.equivFin σ).linearOrder
  have hb := totalDegree_pos_of_span_singleton_ne_top hf hproper
  have he : MonomialOrder.degLex.degree f ≠ 0 := by
    intro hz
    rw [← MvPolynomial.degree_degLexDegree, hz] at hb
    simp at hb
  obtain ⟨i, _⟩ := Finsupp.support_nonempty_iff.mpr he
  let _ : Nonempty σ := ⟨i⟩
  have hσ : 0 < Nat.card σ := Nat.card_pos
  rw [hilbertPolynomial_span_singleton_natDegree hf hb hσ]
  omega

end AffineHilbert
