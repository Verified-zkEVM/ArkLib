/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.MvPolynomial.OrdinaryFactorDegrees
public import ArkLib.ToMathlib.MvPolynomial.PDeriv
public import ArkLib.ToMathlib.MvPolynomial.RootContraction
public import ArkLib.ToMathlib.Polynomial.PaddedDerivativeResultant
public import Mathlib.FieldTheory.Separable

/-!
# Separability of the distinct positive-root product

The product of the distinct irreducible factors having positive degree in a distinguished
variable becomes separable when viewed as a univariate polynomial over the fraction field in
the other variables.  The characteristic guard is stated against the root degree of the source;
it covers characteristic zero and positive characteristic uniformly.
-/

@[expose] public section

namespace MvPolynomial

noncomputable section

open UniqueFactorizationMonoid Polynomial

variable {K σ : Type*} [Field K]

local instance : DecidableEq (Associates (MvPolynomial (Option σ) K)) :=
  instDecidableEqAssociatesOption_arkLib

/-- The positive-root squarefree product as a polynomial in the distinguished variable. -/
def ordinaryRootPolynomial (Q : MvPolynomial (Option σ) K) :
    Polynomial (MvPolynomial σ K) :=
  optionEquivLeft K σ (ordinaryRootProduct Q)

@[simp]
theorem natDegree_ordinaryRootPolynomial (Q : MvPolynomial (Option σ) K) :
    (ordinaryRootPolynomial Q).natDegree = degreeOf none (ordinaryRootProduct Q) := by
  exact natDegree_optionEquivLeft K (ordinaryRootProduct Q)

private theorem pderiv_ne_zero_of_natCast_degree_ne_zero
    (P : MvPolynomial (Option σ) K) (hpos : 0 < degreeOf none P)
    (hcast : (degreeOf none P : K) ≠ 0) :
    pderiv none P ≠ 0 := by
  classical
  have hsupp : P.support.Nonempty := support_nonempty.mpr <|
    ne_zero_of_degreeOf_ne_zero (p := P) (i := none) (Nat.ne_of_gt hpos)
  obtain ⟨m, hm, heq⟩ := Finset.exists_mem_eq_sup P.support hsupp fun m ↦ m none
  rw [← degreeOf_eq_sup none P] at heq
  have hmnone : m none ≠ 0 := by omega
  let m' := m - Finsupp.single none 1
  have hm'_add : m' + Finsupp.single none 1 = m :=
    Finsupp.sub_add_single_one_cancel hmnone
  have hm'none : m' none + 1 = m none := by
    dsimp [m']
    rw [Finsupp.single_eq_same]
    omega
  have hcast' : (m none : K) ≠ 0 := by simpa [heq] using hcast
  have hcast_eq : (↑(m' none) + 1 : K) = (m none : K) := by
    rw [← Nat.cast_one, ← Nat.cast_add, hm'none]
  intro hderiv
  have hcoeff : coeff m' (pderiv none P) = 0 := by rw [hderiv, coeff_zero]
  rw [coeff_pderiv, hm'_add, hcast_eq] at hcoeff
  exact mul_ne_zero (mem_support_iff.mp hm) hcast' hcoeff

private theorem factor_degree_natCast_ne_zero
    (Q : MvPolynomial (Option σ) K) (hQ : Q ≠ 0)
    (hchar : ringChar K = 0 ∨ degreeOf none Q < ringChar K)
    {a : Associates (MvPolynomial (Option σ) K)}
    (ha : a ∈ ordinaryRootFactorClasses Q) :
    (degreeOf none (ordinaryFactorRepresentative a) : K) ≠ 0 := by
  have hpos := (ordinaryRootFactorClasses_spec Q ha).2
  have hsum := ordinary_root_degree_sum_le Q hQ
  have hle : degreeOf none (ordinaryFactorRepresentative a) ≤ degreeOf none Q := by
    exact (Finset.single_le_sum
      (fun b _hb ↦ Nat.zero_le (degreeOf none (ordinaryFactorRepresentative b))) ha).trans hsum
  intro hzero
  have hdiv := (ringChar.spec K _).mp hzero
  rcases hchar with hchar | hchar
  · rw [hchar, zero_dvd_iff] at hdiv
    omega
  · exact Nat.not_dvd_of_pos_of_lt hpos (hle.trans_lt hchar) hdiv

/-- Under the manuscript characteristic guard, the distinct positive-root product is separable
over the fraction field in all remaining variables. -/
theorem ordinaryRootPolynomial_map_fraction_separable
    (Q : MvPolynomial (Option σ) K) (hQ : Q ≠ 0)
    (hchar : ringChar K = 0 ∨ degreeOf none Q < ringChar K) :
    ((ordinaryRootPolynomial Q).map
      (algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)))).Separable := by
  classical
  let L := FractionRing (MvPolynomial σ K)
  let s := ordinaryRootFactorClasses Q
  let P : Associates (MvPolynomial (Option σ) K) → MvPolynomial (Option σ) K :=
    ordinaryFactorRepresentative
  let A : Associates (MvPolynomial (Option σ) K) → Polynomial (MvPolynomial σ K) :=
    fun a ↦ optionEquivLeft K σ (P a)
  let f : Associates (MvPolynomial (Option σ) K) → Polynomial L :=
    fun a ↦ (A a).map (algebraMap (MvPolynomial σ K) L)
  have hAirr (a) (ha : a ∈ s) : Irreducible (A a) := by
    exact (ordinaryRootFactorClasses_spec Q ha).1.map (optionEquivLeft K σ)
  have hAdegree (a) (ha : a ∈ s) : 0 < (A a).natDegree := by
    simpa only [A, P, natDegree_optionEquivLeft] using
      (ordinaryRootFactorClasses_spec Q ha).2
  have hAprimitive (a) (ha : a ∈ s) : (A a).IsPrimitive :=
    (hAirr a ha).isPrimitive (Nat.ne_of_gt (hAdegree a ha))
  have hfirr (a) (ha : a ∈ s) : Irreducible (f a) := by
    exact (hAprimitive a ha).irreducible_iff_irreducible_map_fraction_map.mp (hAirr a ha)
  have hfseparable (a) (ha : a ∈ s) : (f a).Separable := by
    rw [separable_iff_derivative_ne_zero (hfirr a ha)]
    change ((A a).map (algebraMap (MvPolynomial σ K) L)).derivative ≠ 0
    rw [derivative_map]
    apply (Polynomial.map_ne_zero_iff
      (IsFractionRing.injective (MvPolynomial σ K) L)).mpr
    rw [← optionEquivLeft_pderiv_none]
    change (optionEquivLeft K σ) (pderiv none (P a)) ≠ (optionEquivLeft K σ) 0
    apply (optionEquivLeft K σ).injective.ne
    apply pderiv_ne_zero_of_natCast_degree_ne_zero (P a)
    · exact (ordinaryRootFactorClasses_spec Q ha).2
    · exact factor_degree_natCast_ne_zero Q hQ hchar ha
  have hfpairwise (a) (ha : a ∈ s) (b) (hb : b ∈ s) (hab : a ≠ b) :
      IsCoprime (f a) (f b) := by
    rw [(hfirr a ha).coprime_iff_not_dvd]
    intro hdvd
    have hAdvd : A a ∣ A b :=
      ((hAprimitive a ha).dvd_iff_fraction_map_dvd_fraction_map L).mpr hdvd
    have hassocA : Associated (A a) (A b) :=
      (hAirr a ha).associated_of_dvd (hAirr b hb) hAdvd
    have hassocP : Associated (P a) (P b) := by
      simpa only [A, P, AlgEquiv.symm_apply_apply] using
        hassocA.map (optionEquivLeft K σ).symm
    apply hab
    rw [← mk_ordinaryFactorRepresentative a, ← mk_ordinaryFactorRepresentative b]
    exact Associates.mk_eq_mk_iff_associated.mpr hassocP
  have hsep : (∏ a ∈ s, f a).Separable :=
    separable_prod' hfpairwise hfseparable
  have hoption :
      (optionEquivLeft K σ) (∏ a ∈ s, P a) = ∏ a ∈ s, A a := by
    simpa only [A] using map_prod (optionEquivLeft K σ) P s
  change (Polynomial.map (algebraMap (MvPolynomial σ K) L)
    ((optionEquivLeft K σ) (∏ a ∈ s, P a))).Separable
  rw [hoption]
  have hmap : Polynomial.map (algebraMap (MvPolynomial σ K) L) (∏ a ∈ s, A a) =
      ∏ a ∈ s, Polynomial.map (algebraMap (MvPolynomial σ K) L) (A a) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        rw [Finset.prod_insert ha, Finset.prod_insert ha, Polynomial.map_mul, ih]
  rw [hmap]
  simpa only [f] using hsep

/-- Consequently the original-size padded derivative resultant of the positive-root product is
nonzero, including the constant-product boundary. -/
theorem paddedDerivativeResultant_ordinaryRootPolynomial_ne_zero
    (Q : MvPolynomial (Option σ) K) (hQ : Q ≠ 0)
    (hchar : ringChar K = 0 ∨ degreeOf none Q < ringChar K) :
    Polynomial.paddedDerivativeResultant (ordinaryRootPolynomial Q)
        (degreeOf none (ordinaryRootProduct Q)) ≠ 0 := by
  apply Polynomial.paddedDerivativeResultant_ne_zero_of_map_separable
    (L := FractionRing (MvPolynomial σ K))
    (ordinaryRootPolynomial Q) (natDegree_ordinaryRootPolynomial Q)
  exact ordinaryRootPolynomial_map_fraction_separable Q hQ hchar

end

end MvPolynomial
