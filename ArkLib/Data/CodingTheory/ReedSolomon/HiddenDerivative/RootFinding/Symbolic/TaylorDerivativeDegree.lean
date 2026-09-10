/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Symbolic.TaylorBidegree
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Taylor.IndexWeight

/-!
# Derivative-variable degree of the first-order Taylor lift

For a first-order equation of derivative degree `v`, the cleared numerator of coefficient
`l` has derivative degree at most `(2*(l-1)-1)*(v-1)+l`. The extra `l` comes from the
coefficient-index bound on the actual universal residual; no choice of a different rational
representation is made. Padding to a common denominator exponent gives `τ*(v-1)+l`.
-/

@[expose] public section

namespace MvPolynomial

noncomputable section

open scoped BigOperators

/-- Clearing denominators preserves a separate variable-degree bound, with the source
monomial charged its weighted sum of numerator allowances. -/
theorem degreeOf_clearedSubstitution {R σ ι : Type*} [CommRing R]
    (i : σ) (S : MvPolynomial σ R) (N : ι → MvPolynomial σ R) (d w : ι → ℕ)
    (H b v : ℕ) (Q : MvPolynomial ι R)
    (hS : S.degreeOf i ≤ b) (hN : ∀ j, (N j).degreeOf i ≤ d j * b + w j)
    (hden : ∀ m ∈ Q.support, Finsupp.weight d m ≤ H)
    (hw : ∀ m ∈ Q.support, Finsupp.weight w m ≤ v) :
    (clearedSubstitution C S N d H Q).degreeOf i ≤ H * b + v := by
  classical
  apply (degreeOf_sum_le _ _ _).trans
  apply Finset.sup_le
  intro m hm
  have hprod : (∏ j ∈ m.support, N j ^ m j).degreeOf i ≤
      Finsupp.weight d m * b + Finsupp.weight w m := by
    apply (degreeOf_prod_le _ _ _).trans
    calc
      _ ≤ ∑ j ∈ m.support, m j * (d j * b + w j) := by
        apply Finset.sum_le_sum
        intro j _
        exact (degreeOf_pow_le _ _ _).trans (Nat.mul_le_mul_left _ (hN j))
      _ = _ := by
        simp only [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul]
        rw [Finset.sum_mul, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
  have hpow := (degreeOf_pow_le i S (H - Finsupp.weight d m)).trans
    (Nat.mul_le_mul_left _ hS)
  have hbudget := Nat.sub_add_cancel (hden m hm)
  have hmul := degreeOf_mul_le i
    (C (coeff m Q) * ∏ j ∈ m.support, N j ^ m j)
    (S ^ (H - Finsupp.weight d m))
  have hcoeff := degreeOf_mul_le i (C (coeff m Q)) (∏ j ∈ m.support, N j ^ m j)
  rw [degreeOf_C, zero_add] at hcoeff
  nlinarith [hw m hm]

end

end MvPolynomial

namespace MvPolynomial

noncomputable section

open Polynomial
open scoped BigOperators

/-- Turning the coefficient parameter into a variable cannot increase the degree of any
original variable. -/
theorem flattenChallenge_degreeOf_le {F σ : Type*} [Field F]
    (P : MvPolynomial σ F[X]) (i : σ) :
    (flattenChallenge P).degreeOf (some i) ≤ P.degreeOf i := by
  classical
  have hc (p : F[X]) :
      (flattenChallenge (MvPolynomial.C p : MvPolynomial σ F[X])).degreeOf (some i) = 0 := by
    rw [flattenChallenge_C]
    have he : Polynomial.aeval (X none : MvPolynomial (Option σ) F) p =
        ∑ n ∈ p.support, MvPolynomial.C (p.coeff n) * X none ^ n := by
      simpa [Polynomial.sum_def] using congrArg
        (Polynomial.aeval (X none : MvPolynomial (Option σ) F)) p.sum_monomial_eq.symm
    rw [he]
    apply Nat.eq_zero_of_le_zero
    apply (degreeOf_sum_le _ _ _).trans
    apply Finset.sup_le
    intro n _
    apply (degreeOf_mul_le _ _ _).trans
    simp only [degreeOf_C, zero_add]
    exact (degreeOf_pow_le _ _ _).trans (by simp [degreeOf_X])
  have he : flattenChallenge P =
      ∑ m ∈ P.support, flattenChallenge (MvPolynomial.C (coeff m P)) *
        ∏ j ∈ m.support, (X (some j) : MvPolynomial (Option σ) F) ^ m j := by
    conv_lhs => rw [P.as_sum]
    simp only [map_sum, monomial_eq, map_mul, Finsupp.prod, map_prod, map_pow,
      flattenChallenge_X]
  rw [he]
  apply (degreeOf_sum_le _ _ _).trans
  apply Finset.sup_le
  intro m hm
  apply (degreeOf_mul_le _ _ _).trans
  rw [hc, zero_add]
  apply (degreeOf_prod_le _ _ _).trans
  calc
    _ ≤ ∑ j ∈ m.support, m j * (if i = j then 1 else 0) := by
      apply Finset.sum_le_sum
      intro j _
      exact (degreeOf_pow_le _ _ _).trans (by simp [degreeOf_X])
    _ = m i := by
      simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finsupp.mem_support_iff,
        ne_eq, ite_not, ite_eq_right_iff]
      exact Eq.symm
    _ ≤ P.degreeOf i := monomial_le_degreeOf i hm

end

end MvPolynomial

open PolynomialDifferential

namespace ReedSolomon.HiddenDerivative

noncomputable section

open MvPolynomial Polynomial

variable {F : Type*} [Field F]

/-- The first-order separant lowers derivative-variable degree by one. -/
theorem degreeOf_initialJetSeparantOver_firstOrder (center : F[X])
    (Q : DifferentialPolynomial F[X] 1) :
    (initialJetSeparantOver center Q).degreeOf 1 ≤ Q.degreeOf (some 1) - 1 := by
  rw [← weightedTotalDegree_piSingle]
  apply le_trans (weightedTotalDegree_aeval_le_of_le
    (Pi.single (some (1 : Fin 2)) 1) (Pi.single (1 : Fin 2) 1) _ _ ?_)
  · simpa [separant] using weightedTotalDegree_pderiv_le_sub
      (Pi.single (some (1 : Fin 2)) 1) (some (1 : Fin 2)) Q
  · intro i
    cases i with
    | none => simp
    | some j =>
      fin_cases j <;> simp [weightedTotalDegree_piSingle, degreeOf_X]

/-- The literal cleared Taylor numerator retains the derivative-variable degree bound. -/
theorem degreeOf_rationalTaylorNumeratorOver_firstOrder
    (center : F[X]) (Q : DifferentialPolynomial F[X] 1) (v : ℕ)
    (hv : 0 < v) (hjet : Q.degreeOf (some 1) ≤ v) (l : ℕ) :
    (rationalTaylorNumeratorOver (F := F) center Q l).degreeOf 1 ≤
      (2 * (l - 1) - 1) * (v - 1) + l := by
  classical
  induction l using Nat.strong_induction_on with
  | h l ih =>
    rw [rationalTaylorNumeratorOver]
    split_ifs with hl
    · have hl' : l = 0 ∨ l = 1 := by omega
      rcases hl' with rfl | rfl <;> simp [degreeOf_X]
    · have hh : 0 < l - 1 := by omega
      have hlr : 1 + (l - 1) = l := by omega
      have hden := denominator_weight_le_of_mem_universalTaylorResidual_coeff
        (r := 1) (h := l - 1) hh center Q
      rw [hlr] at hden
      have hd := degreeOf_clearedSubstitution (1 : Fin 2)
        (initialJetSeparantOver center Q)
        (fun i : Fin l ↦ rationalTaylorNumeratorOver (F := F) center Q i.val)
        (fun i ↦ 2 * (i.val - 1) - 1) Fin.val (2 * (l - 1) - 2) (v - 1) (l - 1 + v)
        ((optionEquivLeft F[X] (Fin l)
          (universalTaylorResidual l center Q)).coeff (l - 1))
        ((degreeOf_initialJetSeparantOver_firstOrder center Q).trans
          (Nat.sub_le_sub_right hjet 1))
        (fun i ↦ ih i.val i.isLt) hden (fun m hm ↦ by
          have hw := indexWeight_le_of_mem_universalTaylorResidual_coeff l center Q
            (l - 1) m hm
          rw [firstOrder_jetIndexDegree] at hw
          exact hw.trans (Nat.add_le_add_left hjet _))
      have hm := degreeOf_mul_le (1 : Fin 2)
        (-MvPolynomial.C (algebraMap F F[X] ((l.choose 1 : F)⁻¹)))
        (clearedSubstitution C (initialJetSeparantOver center Q)
          (fun i : Fin l ↦ rationalTaylorNumeratorOver (F := F) center Q i.val)
          (fun i ↦ 2 * (i.val - 1) - 1) (2 * (l - 1) - 2)
          ((optionEquivLeft F[X] (Fin l)
            (universalTaylorResidual l center Q)).coeff (l - 1)))
      simp only [degreeOf_neg, degreeOf_C, zero_add] at hm
      have he : 2 * (l - 1) - 1 = (2 * (l - 1) - 2) + 1 := by omega
      have hvsub := Nat.sub_add_cancel (Nat.succ_le_of_lt hv)
      rw [he]
      exact hm.trans (hd.trans (by nlinarith))

/-- A common Taylor numerator has derivative degree at most `τ*(v-1)+l`. -/
theorem degreeOf_commonTaylorNumeratorOver_firstOrder
    (center : F[X]) (Q : DifferentialPolynomial F[X] 1) (v K τ : ℕ)
    (hτ : TaylorExponentSufficient 1 K τ)
    (hv : 0 < v) (hjet : Q.degreeOf (some 1) ≤ v) (l : Fin K) :
    (commonTaylorNumeratorOver (F := F) center Q K l (τ := τ)).degreeOf 1 ≤
      τ * (v - 1) + l.val := by
  have hd := degreeOf_rationalTaylorNumeratorOver_firstOrder center Q v hv hjet l.val
  have hs := (degreeOf_initialJetSeparantOver_firstOrder center Q).trans
    (Nat.sub_le_sub_right hjet 1)
  have hp := (degreeOf_pow_le (1 : Fin 2) (initialJetSeparantOver center Q)
    (τ - (2 * (l.val - 1) - 1))).trans (Nat.mul_le_mul_left _ hs)
  have hm := degreeOf_mul_le (1 : Fin 2)
    (rationalTaylorNumeratorOver (F := F) center Q l.val)
    (initialJetSeparantOver center Q ^ (τ - (2 * (l.val - 1) - 1)))
  have he := Nat.sub_add_cancel (hτ l)
  unfold commonTaylorNumeratorOver
  nlinarith

end

end ReedSolomon.HiddenDerivative
