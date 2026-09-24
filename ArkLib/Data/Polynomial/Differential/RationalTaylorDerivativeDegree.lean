/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.MvPolynomial.WeightedDegree
public import ArkLib.Data.Polynomial.Differential.RationalTaylorAlgebra
public import ArkLib.Data.Polynomial.Differential.TaylorIndexWeight
public import ArkLib.ToMathlib.MvPolynomial.ClearedSubstitution

/-!
# Derivative-variable degree of rational Taylor numerators

The Taylor index-weight degree of a differential polynomial controls the degree in its highest
jet variable of the separant and of the rational Taylor numerators. The common numerator bound
then follows for every sufficient denominator exponent.

## Main statements

* `degreeOf_initialJetSeparant_le`: the separant has degree at most one less in the highest jet
  variable.
* `degreeOf_rationalTaylorNumeratorOver_le`: a bound on the Taylor index-weight degree gives a
  bound on every rational Taylor numerator.
* `degreeOf_commonTaylorNumeratorOver_le`: every numerator padded to a sufficient exponent has a
  bound of `τ * (v - 1) + l` in the highest jet variable.

## References

* [DKT26]
-/

@[expose] public section

namespace PolynomialDifferential

noncomputable section

open MvPolynomial

variable {F : Type*} {r : ℕ}

/-- The initial separant has degree at most one less in the highest jet variable. -/
theorem degreeOf_initialJetSeparant_le [CommSemiring F] [Nontrivial F]
    (center : Polynomial F)
    (Q : DifferentialPolynomial (Polynomial F) r) :
    (initialJetSeparant center Q).degreeOf (Fin.last r) ≤
      Q.degreeOf (some (Fin.last r)) - 1 := by
  rw [← weightedTotalDegree_piSingle]
  apply le_trans (weightedTotalDegree_aeval_le_of_le
    (Pi.single (some (Fin.last r)) 1) (Pi.single (Fin.last r) 1) _ _ ?_)
  · simpa [initialJetSeparant, separant] using weightedTotalDegree_pderiv_le_sub
      (Pi.single (some (Fin.last r)) 1) (some (Fin.last r)) Q
  · intro i
    cases i with
    | none => simp
    | some j =>
      by_cases hj : j = Fin.last r
      · subst j
        simp [weightedTotalDegree_piSingle]
      · simp [weightedTotalDegree_piSingle, degreeOf_X, Ne.symm hj]

/-- If the Taylor index-weight degree of `Q` is at most `v`, its rational Taylor numerator has
degree at most `(2(l - r) - 1) * (v - 1) + l` in the highest jet variable. -/
theorem degreeOf_rationalTaylorNumeratorOver_le
    [Field F] (center : Polynomial F) (Q : DifferentialPolynomial (Polynomial F) r) (v : ℕ)
    (hr : 0 < r) (hv : 0 < v)
    (hQ : Q.weightedTotalDegree (indexWeight (r + 1)) ≤ v) (l : ℕ) :
    (rationalTaylorNumeratorOver F center Q l).degreeOf (Fin.last r) ≤
      (2 * (l - r) - 1) * (v - 1) + l := by
  have hjet : Q.degreeOf (some (Fin.last r)) ≤ v :=
    (degreeOf_le_weightedTotalDegree _ _ (by simp [indexWeight]; omega) Q).trans hQ
  have hsep := (degreeOf_initialJetSeparant_le center Q).trans
    (Nat.sub_le_sub_right hjet 1)
  induction l using Nat.strong_induction_on with
  | h l ih =>
    rw [rationalTaylorNumeratorOver]
    split_ifs with hl
    · have hdegree :
          (X (⟨l, hl⟩ : Fin (r + 1)) : MvPolynomial (Fin (r + 1)) (Polynomial F)).degreeOf
            (Fin.last r) ≤ l := by
        by_cases heq : l = r
        · subst l
          have he : (⟨r, hl⟩ : Fin (r + 1)) = Fin.last r := by
            ext
            rfl
          simp [he]
          omega
        · have hlt : l < r := by omega
          have he : (⟨l, hl⟩ : Fin (r + 1)) ≠ Fin.last r := by
            intro h
            have hv := congrArg Fin.val h
            simp at hv
            omega
          simp [degreeOf_X, Ne.symm he]
      have he : 2 * (l - r) - 1 = 0 := by omega
      rw [he]
      simp only [zero_mul, zero_add]
      exact hdegree
    · have hden : ∀ m ∈ ((optionEquivLeft (Polynomial F) (Fin l)
          (universalTaylorResidual l center Q)).coeff (l - r)).support,
          Finsupp.weight (fun i : Fin l ↦ 2 * (i.val - r) - 1) m ≤ 2 * (l - r) - 2 := by
        intro m hm
        exact denominator_weight_le_of_mem_universalTaylorResidual_coeff
          (r := r) (K := l) (h := l - r) (by omega) center Q m hm
      have hw : ∀ m ∈ ((optionEquivLeft (Polynomial F) (Fin l)
          (universalTaylorResidual l center Q)).coeff (l - r)).support,
          Finsupp.weight Fin.val m ≤ (l - r) + v := by
        intro m hm
        exact (indexWeight_le_of_mem_universalTaylorResidual_coeff l center Q
          (l - r) m hm).trans (Nat.add_le_add_left hQ _)
      have hd := degreeOf_clearedSubstitution (Fin.last r)
        (initialJetSeparant center Q)
        (fun i : Fin l ↦ rationalTaylorNumeratorOver F center Q i.val)
        (fun i ↦ 2 * (i.val - r) - 1) Fin.val (2 * (l - r) - 2) (v - 1) (l - r + v)
        ((optionEquivLeft (Polynomial F) (Fin l)
          (universalTaylorResidual l center Q)).coeff (l - r)) hsep
        (fun i ↦ ih i.val i.isLt) hden hw
      have hm := degreeOf_mul_le (Fin.last r)
        (-MvPolynomial.C (algebraMap F (Polynomial F) ((l.choose r : F)⁻¹)))
        (clearedSubstitution C (initialJetSeparant center Q)
          (fun i : Fin l ↦ rationalTaylorNumeratorOver F center Q i.val)
          (fun i ↦ 2 * (i.val - r) - 1) (2 * (l - r) - 2)
          ((optionEquivLeft (Polynomial F) (Fin l)
            (universalTaylorResidual l center Q)).coeff (l - r)))
      simp only [degreeOf_neg, degreeOf_C, zero_add] at hm
      have he : 2 * (l - r) - 1 = (2 * (l - r) - 2) + 1 := by omega
      have hvsub := Nat.sub_add_cancel (Nat.succ_le_of_lt hv)
      have hlr : r + (l - r) = l := by omega
      rw [he]
      exact hm.trans (hd.trans (by nlinarith [hlr, hr, hvsub]))

/-- In first order, a degree bound on `Y₁` gives the rational Taylor numerator bound. -/
theorem degreeOf_rationalTaylorNumeratorOver_firstOrder
    [Field F] (center : Polynomial F) (Q : DifferentialPolynomial (Polynomial F) 1) (v : ℕ)
    (hv : 0 < v) (hjet : Q.degreeOf (some 1) ≤ v) (l : ℕ) :
    (rationalTaylorNumeratorOver F center Q l).degreeOf 1 ≤
      (2 * (l - 1) - 1) * (v - 1) + l := by
  have hQ : Q.weightedTotalDegree (indexWeight 2) ≤ v := by
    rw [weightedTotalDegree_indexWeight_eq_jetDegree_one, jetDegree]
    exact hjet
  simpa using degreeOf_rationalTaylorNumeratorOver_le center Q v (by omega) hv hQ l

/-- If `τ` is sufficient for the chart, every padded Taylor numerator has degree at most
`τ * (v - 1) + l` in the highest jet variable. -/
theorem degreeOf_commonTaylorNumeratorOver_le
    [Field F] (center : Polynomial F) (Q : DifferentialPolynomial (Polynomial F) r)
    (v K τ : ℕ) (hτ : TaylorExponentSufficient r K τ) (hr : 0 < r) (hv : 0 < v)
    (hQ : Q.weightedTotalDegree (indexWeight (r + 1)) ≤ v) (l : Fin K) :
    (commonTaylorNumeratorOver F center Q τ l).degreeOf (Fin.last r) ≤
      τ * (v - 1) + l.val := by
  have hd := degreeOf_rationalTaylorNumeratorOver_le center Q v hr hv hQ l.val
  have hjet : Q.degreeOf (some (Fin.last r)) ≤ v :=
    (degreeOf_le_weightedTotalDegree _ _ (by simp [indexWeight]; omega) Q).trans hQ
  have hs := (degreeOf_initialJetSeparant_le center Q).trans
    (Nat.sub_le_sub_right hjet 1)
  have hp := (degreeOf_pow_le (Fin.last r) (initialJetSeparant center Q)
    (τ - (2 * (l.val - r) - 1))).trans (Nat.mul_le_mul_left _ hs)
  have hm := degreeOf_mul_le (Fin.last r)
    (rationalTaylorNumeratorOver F center Q l.val)
    (initialJetSeparant center Q ^ (τ - (2 * (l.val - r) - 1)))
  have he := Nat.sub_add_cancel (hτ l)
  unfold commonTaylorNumeratorOver
  nlinarith

/-- In first order, a degree bound on `Y₁` gives the common Taylor numerator bound. -/
theorem degreeOf_commonTaylorNumeratorOver_firstOrder
    [Field F] (center : Polynomial F) (Q : DifferentialPolynomial (Polynomial F) 1)
    (v K τ : ℕ) (hτ : TaylorExponentSufficient 1 K τ) (hv : 0 < v)
    (hjet : Q.degreeOf (some 1) ≤ v) (l : Fin K) :
    (commonTaylorNumeratorOver F center Q τ l).degreeOf 1 ≤ τ * (v - 1) + l.val := by
  have hQ : Q.weightedTotalDegree (indexWeight 2) ≤ v := by
    rw [weightedTotalDegree_indexWeight_eq_jetDegree_one, jetDegree]
    exact hjet
  simpa using degreeOf_commonTaylorNumeratorOver_le center Q v K τ hτ (by omega) hv hQ l

end

end PolynomialDifferential
