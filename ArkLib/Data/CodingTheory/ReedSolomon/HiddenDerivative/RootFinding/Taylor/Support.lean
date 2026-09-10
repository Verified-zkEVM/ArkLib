/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.MvPolynomial.SupportWeight
public import ArkLib.Data.MvPolynomial.WeightedDegree
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.Polynomial.HasseDeriv

/-!
# Taylor-weight support of differential residuals

In the residual of an order-`r` differential equation, the coefficient variable `c_j`
first occurs at Taylor order at least `j-r`. Consequently every residual monomial of
Taylor order `h` has later-coefficient weight at most `h`. This is the support restriction
used to bound denominators and numerator degrees of the rational Taylor lift in [DKTZ26].
The polynomials here are literal universal Hasse jets, with binomial coefficients.

## References

* [Dao, Q., Kominers, S. D., Thaler, J., Zheng, K. Z., *Reed--Solomon List Decoding and Mutual
  Correlated Agreement up to Capacity*][DKTZ26], Appendix A.3, Lemma A.5.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative

noncomputable section

open MvPolynomial
open scoped BigOperators

variable {F : Type*} [CommSemiring F]

/-- The universal `j`-th Hasse jet of `∑ l<K, c_l ξ^l`, retaining `ξ` as `none`. -/
def universalTaylorJet (K j : ℕ) : MvPolynomial (Option (Fin K)) F :=
  ∑ l ∈ Finset.univ.filter (fun l : Fin K ↦ j ≤ l.val),
    monomial (Finsupp.single (some l) 1 + Finsupp.single none (l.val - j))
      (Nat.choose l.val j : F)

/-- The universal coefficient polynomial in the Taylor variable. -/
def universalTaylorPolynomial (K : ℕ) : Polynomial (MvPolynomial (Fin K) F) :=
  ∑ l : Fin K, Polynomial.monomial l.val (X l)

/-- The universal jet is the literal Hasse derivative after separating the Taylor variable. -/
theorem optionEquivLeft_universalTaylorJet (K j : ℕ) :
    optionEquivLeft F (Fin K) (universalTaylorJet (F := F) K j) =
      Polynomial.hasseDeriv j (universalTaylorPolynomial K) := by
  classical
  simp only [universalTaylorJet, universalTaylorPolynomial, map_sum,
    optionEquivLeft_monomial, Polynomial.hasseDeriv_monomial]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro l _
  by_cases hj : j ≤ l.val
  · simp only [if_pos hj, Finsupp.add_apply, Finsupp.single_apply,
      Option.some_ne_none, ↓reduceIte, zero_add, Finsupp.some_add,
      Finsupp.some_single_some, Finsupp.some_single_none, add_zero]
    congr 1
    rw [← C_mul_X_eq_monomial, map_natCast]
  · simp [hj, Nat.choose_eq_zero_of_lt (by omega : l.val < j)]

/-- A Hasse jet of order at most `r` satisfies the later-coefficient Taylor-weight bound. -/
theorem universalTaylorJet_mem_supportWeightLE (K j r : ℕ) (hj : j ≤ r) :
    universalTaylorJet (F := F) K j ∈ supportWeightLE
      (Finsupp.weight (fun i : Option (Fin K) ↦ i.elim 0 (fun l ↦ l.val - r)))
      (Finsupp.applyAddHom none) := by
  classical
  apply Subalgebra.sum_mem
  intro l hl
  apply monomial_mem_supportWeightLE
  simp only [map_add, Finsupp.weight_single, one_smul, Option.elim_some,
    Option.elim_none, smul_zero, add_zero, Finsupp.applyAddHom_apply,
    Finsupp.single_apply, Option.some_ne_none, ↓reduceIte, zero_add]
  omega

/-- Substitute the universal Taylor jets into a differential polynomial. The source `none`
coordinate is the independent variable, translated by `center`. -/
def universalTaylorResidual {r : ℕ} (K : ℕ) (center : F)
    (Q : MvPolynomial (Option (Fin (r + 1))) F) : MvPolynomial (Option (Fin K)) F :=
  aeval (fun i ↦ i.elim (C center + X none) (fun j ↦ universalTaylorJet K j.val)) Q

/-- Universal differential substitution preserves the comparison between later-coefficient
weight and Taylor order. There is no degree or characteristic assumption on `Q`. -/
theorem universalTaylorResidual_mem_supportWeightLE {r : ℕ} (K : ℕ) (center : F)
    (Q : MvPolynomial (Option (Fin (r + 1))) F) :
    universalTaylorResidual K center Q ∈ supportWeightLE
      (Finsupp.weight (fun i : Option (Fin K) ↦ i.elim 0 (fun l ↦ l.val - r)))
      (Finsupp.applyAddHom none) := by
  apply aeval_mem_supportWeightLE
  intro i
  cases i with
  | none =>
    apply Subalgebra.add_mem
    · exact (supportWeightLE _ _).algebraMap_mem center
    · apply monomial_mem_supportWeightLE
      simp [Finsupp.weight_single]
  | some j => exact universalTaylorJet_mem_supportWeightLE K j.val r (by omega)

/-- Every monomial in Taylor coefficient `h` of the universal residual satisfies
`∑ l, (l-r) * exponent(c_l) ≤ h`, the weight restriction in the rational-lift recurrence. -/
theorem weight_le_of_mem_universalTaylorResidual_coeff {r : ℕ} (K : ℕ) (center : F)
    (Q : MvPolynomial (Option (Fin (r + 1))) F) (h : ℕ) (m : Fin K →₀ ℕ)
    (hm : m ∈ ((optionEquivLeft F (Fin K) (universalTaylorResidual K center Q)).coeff h).support) :
    Finsupp.weight (fun l : Fin K ↦ l.val - r) m ≤ h :=
  weight_le_of_mem_coeff_optionEquivLeft _ _
    (universalTaylorResidual_mem_supportWeightLE K center Q) h m hm

/-- Every universal jet is linear in the coefficient variables, independently of Taylor order. -/
theorem weightedTotalDegree_universalTaylorJet_le (K j : ℕ) :
    (universalTaylorJet (F := F) K j).weightedTotalDegree
      (fun i : Option (Fin K) ↦ i.elim 0 (fun _ ↦ 1)) ≤ 1 := by
  classical
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
  apply Submodule.sum_mem
  intro l hl
  apply (monomial_mem_restrictWeightedDegree _ _ _ _).mpr
  left
  simp only [map_add, Finsupp.weight_single, Option.elim_some, Option.elim_none,
    smul_zero, add_zero, one_smul, le_refl]

/-- Differential substitution has coefficient-variable degree at most the total source jet
degree. The independent-variable degree contributes nothing to this bound. -/
theorem weightedTotalDegree_universalTaylorResidual_le {r : ℕ} (K : ℕ) (center : F)
    (Q : MvPolynomial (Option (Fin (r + 1))) F) :
    (universalTaylorResidual K center Q).weightedTotalDegree
        (fun i : Option (Fin K) ↦ i.elim 0 (fun _ ↦ 1)) ≤
      Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) := by
  apply weightedTotalDegree_aeval_le_of_le
  intro i
  cases i with
  | none =>
    apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
    apply Submodule.add_mem
    · exact C_mem_restrictWeightedDegree _ _ _
    · exact X_mem_restrictWeightedDegree _ _ _ (by simp)
  | some j => exact weightedTotalDegree_universalTaylorJet_le K j.val

/-- Each residual coefficient has ordinary total degree at most the source total jet degree.
Together with the Taylor-weight restriction, this supplies both support inequalities used
in the rational Taylor numerator recurrence. -/
theorem totalDegree_universalTaylorResidual_coeff_le {r : ℕ} (K : ℕ) (center : F)
    (Q : MvPolynomial (Option (Fin (r + 1))) F) (h : ℕ) :
    ((optionEquivLeft F (Fin K) (universalTaylorResidual K center Q)).coeff h).totalDegree ≤
      Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) := by
  rw [← weightedTotalDegree_one]
  exact (weightedTotalDegree_coeff_optionEquivLeft_le _ _ _).trans
    (weightedTotalDegree_universalTaylorResidual_le K center Q)

end

end ReedSolomon.HiddenDerivative
