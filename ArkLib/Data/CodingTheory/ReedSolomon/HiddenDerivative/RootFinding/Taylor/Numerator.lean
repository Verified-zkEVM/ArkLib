/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Taylor.Denominator
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.DegreeBounds.SpecializationDegree
public import Mathlib.Tactic.LinearCombination
public import ArkLib.ToMathlib.MvPolynomial.ClearedSubstitution
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Taylor.SupportEvaluation
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Regular.Iteration
/-!
# Explicit rational Taylor numerators

Each later Taylor coefficient is represented with denominator a power of the initial
separant. The numerator is constructed recursively by substituting the previous literal
numerators into the truncated universal residual and clearing its denominator. The
resulting degree bound and comparison with every regular polynomial solution prove the
rational Taylor parametrization used in [DKTZ26]. Binomial nonvanishing is stated exactly,
so the comparison applies in any field through every invertible pivot.

## References

* [Dao, Q., Kominers, S. D., Thaler, J., Zheng, K. Z., *Reed--Solomon List Decoding and Mutual
  Correlated Agreement up to Capacity*][DKTZ26], Appendix A.3, Lemma A.5.
-/

@[expose] public section

open PolynomialDifferential


namespace ReedSolomon.HiddenDerivative

noncomputable section

open MvPolynomial

variable {F : Type*} [Field F] {r : ℕ}

/-- An exponent is sufficient for a length-`K` Taylor chart when it dominates the exact
denominator exponent of every reconstructed coefficient. Natural subtraction makes the
exponent zero on initial coordinates. -/
def TaylorExponentSufficient (r K τ : ℕ) : Prop :=
  ∀ l : Fin K, 2 * (l.val - r) - 1 ≤ τ

/-- Increasing a sufficient common-denominator exponent preserves sufficiency. -/
theorem TaylorExponentSufficient.mono {K τ τ' : ℕ}
    (hτ : TaylorExponentSufficient r K τ) (h : τ ≤ τ') :
    TaylorExponentSufficient r K τ' :=
  fun l ↦ (hτ l).trans h

/-- The coarse exponent `2K` is sufficient at every differential order. -/
theorem taylorExponentSufficient_two_mul (r K : ℕ) :
    TaylorExponentSufficient r K (2 * K) := by
  intro l
  omega

/-- Once the chart contains at least two coefficients, all exact recurrence exponents fit
under `2K - 3`. This includes `K = 2`, where the common exponent is one. First-order
clients use this bound uniformly for their order-zero and order-one stages. -/
theorem taylorExponentSufficient_two_mul_sub_three (r : ℕ) {K : ℕ} (hK : 2 ≤ K) :
    TaylorExponentSufficient r K (2 * K - 3) := by
  intro l
  omega

/-- The separant as a polynomial in the initial jet coordinates at a fixed center. -/
def initialJetSeparant (center : F) (Q : DifferentialPolynomial F r) :
    MvPolynomial (Fin (r + 1)) F :=
  aeval (fun i ↦ i.elim (C center) X) (separant Q (Fin.last r))

/-- The initial separant loses one unit of total jet degree. -/
theorem totalDegree_initialJetSeparant_le (center : F) (Q : DifferentialPolynomial F r) :
    (initialJetSeparant center Q).totalDegree ≤
      Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) - 1 := by
  rw [← weightedTotalDegree_one]
  apply le_trans (weightedTotalDegree_aeval_le_of_le
    (fun i : Option (Fin (r + 1)) ↦ i.elim 0 (fun _ ↦ 1))
    (1 : Fin (r + 1) → ℕ) _ _ ?_)
  · exact weightedTotalDegree_pderiv_le_sub _ _ Q
  · intro i
    cases i with
    | none => simp
    | some j => simp only [Option.elim_some, weightedTotalDegree_one, totalDegree_X, le_refl]

/-- The literal common-separant numerator of coefficient `l`. Initial coefficients are
coordinate variables; subsequent coefficients use the truncated residual at order `l-r`. -/
def rationalTaylorNumerator (center : F) (Q : DifferentialPolynomial F r)
    (l : ℕ) : MvPolynomial (Fin (r + 1)) F :=
  if hl : l < r + 1 then X ⟨l, hl⟩ else
    -C ((l.choose r : F)⁻¹) *
      clearedSubstitution C (initialJetSeparant center Q)
        (fun i : Fin l ↦ rationalTaylorNumerator center Q i.val)
        (fun i ↦ 2 * (i.val - r) - 1) (2 * (l - r) - 2)
        ((optionEquivLeft F (Fin l) (universalTaylorResidual l center Q)).coeff (l - r))
termination_by l

/-- The recursive numerator has the manuscript's linear-in-order degree bound. -/
theorem totalDegree_rationalTaylorNumerator_le (center : F) (Q : DifferentialPolynomial F r)
    (hv : 0 < Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1))) (l : ℕ) :
    (rationalTaylorNumerator center Q l).totalDegree ≤
      (2 * (l - r) - 1) *
        (Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) - 1) + 1 := by
  induction l using Nat.strong_induction_on with
  | h l ih =>
    rw [rationalTaylorNumerator]
    split_ifs with hl
    · simp only [totalDegree_X]
      omega
    · have hh : 0 < l - r := by omega
      have hlr : r + (l - r) = l := by omega
      have hden : ∀ m ∈
          ((optionEquivLeft F (Fin l) (universalTaylorResidual l center Q)).coeff
            (l - r)).support,
          Finsupp.weight (fun i : Fin l ↦ 2 * (i.val - r) - 1) m ≤ 2 * (l - r) - 2 := by
        intro m hm
        have ht := denominator_weight_le_of_mem_universalTaylorResidual_coeff
          (r := r) (h := l - r) hh center Q
        rw [hlr] at ht
        exact ht m hm
      have hN : ∀ i : Fin l,
          (rationalTaylorNumerator center Q i.val).totalDegree ≤
            (2 * (i.val - r) - 1) *
              (Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) - 1) + 1 :=
        fun i ↦ ih i.val i.isLt
      have hd := totalDegree_clearedSubstitution
        (initialJetSeparant center Q)
        (fun i : Fin l ↦ rationalTaylorNumerator center Q i.val)
        (fun i ↦ 2 * (i.val - r) - 1) (2 * (l - r) - 2)
        (Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) - 1)
        (Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)))
        ((optionEquivLeft F (Fin l) (universalTaylorResidual l center Q)).coeff (l - r))
        (totalDegree_initialJetSeparant_le center Q)
        hN hden
        (totalDegree_universalTaylorResidual_coeff_le l center Q (l - r))
      have hp := totalDegree_mul
        (-C ((l.choose r : F)⁻¹))
        (clearedSubstitution C (initialJetSeparant center Q)
          (fun i : Fin l ↦ rationalTaylorNumerator center Q i.val)
          (fun i ↦ 2 * (i.val - r) - 1) (2 * (l - r) - 2)
          ((optionEquivLeft F (Fin l) (universalTaylorResidual l center Q)).coeff (l - r)))
      simp only [totalDegree_neg, totalDegree_C, zero_add] at hp
      have he : 2 * (l - r) - 1 = (2 * (l - r) - 2) + 1 := by omega
      rw [he]
      have hvsub := Nat.sub_add_cancel (Nat.succ_le_of_lt hv)
      nlinarith [hp.trans hd]

/-- Evaluate the rational Taylor parametrization on an initial jet. -/
def rationalTaylorCoefficient (center : F) (Q : DifferentialPolynomial F r)
    (jet : Fin (r + 1) → F) (l : ℕ) : F :=
  aeval jet (rationalTaylorNumerator center Q l) /
    aeval jet (initialJetSeparant center Q) ^ (2 * (l - r) - 1)

/-- The rational parametrization retains every initial jet coordinate. -/
theorem rationalTaylorCoefficient_initial (center : F) (Q : DifferentialPolynomial F r)
    (jet : Fin (r + 1) → F) (l : Fin (r + 1)) :
    rationalTaylorCoefficient center Q jet l.val = jet l := by
  rw [rationalTaylorCoefficient, rationalTaylorNumerator, dif_pos l.isLt]
  have hl : l.val - r = 0 := by omega
  simp [hl]

/-- A later rational coefficient solves the literal truncated residual's affine equation. -/
theorem rationalTaylorCoefficient_residual (center : F) (Q : DifferentialPolynomial F r)
    (jet : Fin (r + 1) → F) (l : ℕ) (hl : r < l)
    (hS : aeval jet (initialJetSeparant center Q) ≠ 0)
    (hbin : (l.choose r : F) ≠ 0) :
    aeval (fun i : Fin l ↦ rationalTaylorCoefficient center Q jet i.val)
        ((optionEquivLeft F (Fin l) (universalTaylorResidual l center Q)).coeff (l - r)) +
      ((l.choose r : F) * rationalTaylorCoefficient center Q jet l) *
        aeval jet (initialJetSeparant center Q) = 0 := by
  have hh : 0 < l - r := by omega
  have hlr : r + (l - r) = l := by omega
  have hden : ∀ m ∈
      ((optionEquivLeft F (Fin l) (universalTaylorResidual l center Q)).coeff
        (l - r)).support,
      Finsupp.weight (fun i : Fin l ↦ 2 * (i.val - r) - 1) m ≤ 2 * (l - r) - 2 := by
    have ht := denominator_weight_le_of_mem_universalTaylorResidual_coeff
      (r := r) (h := l - r) hh center Q
    rw [hlr] at ht
    exact ht
  have hmap := map_clearedSubstitution C (aeval jet).toRingHom
    (initialJetSeparant center Q) hS
    (fun i : Fin l ↦ rationalTaylorNumerator center Q i.val)
    (fun i ↦ 2 * (i.val - r) - 1) (2 * (l - r) - 2)
    ((optionEquivLeft F (Fin l) (universalTaylorResidual l center Q)).coeff (l - r)) hden
  have hcomp : (aeval jet).toRingHom.comp C = RingHom.id F := by
    ext x
    simp
  rw [hcomp] at hmap
  change (aeval jet) _ = (aeval jet) _ ^ _ * aeval
    (fun i : Fin l ↦ rationalTaylorCoefficient center Q jet i.val) _ at hmap
  have hn : ¬l < r + 1 := by omega
  conv_lhs =>
    arg 2
    arg 1
    arg 2
    rw [rationalTaylorCoefficient, rationalTaylorNumerator, dif_neg hn]
  simp only [map_mul, map_neg, aeval_C, Algebra.algebraMap_self, RingHom.id_apply]
  rw [hmap]
  have he : 2 * (l - r) - 1 = (2 * (l - r) - 2) + 1 := by omega
  rw [he, pow_succ]
  field_simp
  ring

open scoped BigOperators

/-- The finite Taylor coefficient prefix, translated back to the original center. -/
def centeredCoefficientPrefix (center : F) (c : ℕ → F) (K : ℕ) : Polynomial F :=
  Polynomial.taylor (-center) (∑ i : Fin K, Polynomial.monomial i.val (c i.val))

/-- Centering the prefix recovers its explicit monomial sum. -/
theorem taylor_centeredCoefficientPrefix (center : F) (c : ℕ → F) (K : ℕ) :
    Polynomial.taylor center (centeredCoefficientPrefix center c K) =
      ∑ i : Fin K, Polynomial.monomial i.val (c i.val) := by
  unfold centeredCoefficientPrefix
  rw [Polynomial.taylor_taylor, add_neg_cancel, Polynomial.taylor_zero]

/-- The centered prefix keeps precisely the coefficients below its length. -/
theorem coeff_taylor_centeredCoefficientPrefix (center : F) (c : ℕ → F) (K i : ℕ) :
    (Polynomial.taylor center (centeredCoefficientPrefix center c K)).coeff i =
      if i < K then c i else 0 := by
  classical
  rw [taylor_centeredCoefficientPrefix, Polynomial.finsetSum_coeff]
  by_cases hi : i < K
  · rw [if_pos hi]
    rw [Finset.sum_eq_single (⟨i, hi⟩ : Fin K)]
    · simp
    · intro j _ hj
      rw [Polynomial.coeff_monomial, if_neg]
      exact fun h ↦ hj (Fin.ext h)
    · simp
  · rw [if_neg hi]
    apply Finset.sum_eq_zero
    intro j _
    rw [Polynomial.coeff_monomial, if_neg]
    intro h
    exact hi (h ▸ j.isLt)

/-- A Taylor prefix has degree below its length, including an empty prefix. -/
theorem degree_centeredCoefficientPrefix_lt (center : F) (c : ℕ → F) (K : ℕ) :
    (centeredCoefficientPrefix center c K).degree < K := by
  rw [centeredCoefficientPrefix, Polynomial.degree_taylor]
  simpa only [Polynomial.C_mul_X_pow_eq_monomial] using
    Polynomial.degree_sum_fin_lt (fun i : Fin K ↦ c i.val)

/-- A sufficiently long prefix retains the initial Hasse jet. -/
theorem polynomialJet_centeredCoefficientPrefix (center : F) (c : ℕ → F) (K : ℕ)
    (hK : r < K) :
    polynomialJet (d := r) center (centeredCoefficientPrefix center c K) =
      fun i ↦ c i.val := by
  funext i
  rw [polynomialJet, Polynomial.hasseJet_eq_taylor_coeff,
    coeff_taylor_centeredCoefficientPrefix, if_pos (by omega)]

/-- Appending one coefficient is the canonical regular lift. -/
theorem centeredCoefficientPrefix_succ (center : F) (c : ℕ → F) (h : ℕ) :
    centeredCoefficientPrefix center c (h + r + 1) =
      regularLiftCandidate center (c (h + r)) h r
        (centeredCoefficientPrefix center c (h + r)) := by
  apply (Polynomial.taylor_injective center)
  rw [regularLiftCandidate, map_add, Polynomial.taylor_hassePerturbation]
  rw [taylor_centeredCoefficientPrefix, taylor_centeredCoefficientPrefix,
    Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  rw [Polynomial.C_mul_X_pow_eq_monomial]

/-- Evaluating the initial separant is exactly the canonical separant evaluation. -/
theorem aeval_initialJetSeparant (center : F) (Q : DifferentialPolynomial F r)
    (jet : Fin (r + 1) → F) :
    aeval jet (initialJetSeparant center Q) =
      jetEvaluation (separant Q (Fin.last r)) center jet := by
  have he : (aeval jet).comp (aeval (fun i : Option (Fin (r + 1)) ↦
      i.elim (C center) X)) = aeval (fun i ↦ i.elim center jet) := by
    apply algHom_ext
    intro i
    cases i <;> simp
  have ht := DFunLike.congr_fun he (separant Q (Fin.last r))
  have hfun : (fun i : Option (Fin (r + 1)) ↦ i.elim center jet) =
      (fun i ↦ match i with | none => center | some j => jet j) := by
    funext i
    cases i <;> rfl
  rw [hfun] at ht
  exact ht

/-- A universal residual coefficient specialized to a coefficient sequence is the residual
coefficient of its centered prefix. -/
theorem aeval_universalTaylorResidual_coeff (center : F) (Q : DifferentialPolynomial F r)
    (c : ℕ → F) (K h : ℕ) :
    aeval (fun i : Fin K ↦ c i.val)
        ((optionEquivLeft F (Fin K) (universalTaylorResidual K center Q)).coeff h) =
      (shiftedJetSubstitution center (centeredCoefficientPrefix center c K) Q).coeff h := by
  have he := specializeTaylorCoefficients_universalTaylorResidual center
    (centeredCoefficientPrefix center c K) (degree_centeredCoefficientPrefix_lt center c K) Q
  have hc : (fun i : Fin K ↦
      (Polynomial.taylor center (centeredCoefficientPrefix center c K)).coeff i.val) =
        fun i ↦ c i.val := by
    funext i
    rw [coeff_taylor_centeredCoefficientPrefix, if_pos i.isLt]
  rw [hc] at he
  have ht := congrArg (fun P : Polynomial F ↦ P.coeff h) he
  change (((optionEquivLeft F (Fin K) (universalTaylorResidual K center Q)).map
    (aeval (fun i : Fin K ↦ c i.val)).toRingHom).coeff h) = _ at ht
  rw [Polynomial.coeff_map] at ht
  exact ht

/-- Every polynomial solution satisfies the exact affine equation for its next Taylor
coefficient, with the intercept given by the truncated universal residual. -/
theorem solution_taylorCoefficient_residual (center : F) (Q : DifferentialPolynomial F r)
    (P : Polynomial F) (hsolution : differentialSpecialization Q P = 0)
    (l : ℕ) (hl : r < l) :
    aeval (fun i : Fin l ↦ (Polynomial.taylor center P).coeff i.val)
        ((optionEquivLeft F (Fin l) (universalTaylorResidual l center Q)).coeff (l - r)) +
      ((l.choose r : F) * (Polynomial.taylor center P).coeff l) *
        jetEvaluation (separant Q (Fin.last r)) center (polynomialJet center P) = 0 := by
  let c : ℕ → F := (Polynomial.taylor center P).coeff
  have heq : l - r + r = l := by omega
  have hprefix : Polynomial.X ^ ((l - r + 1) + r) ∣
      Polynomial.taylor center (centeredCoefficientPrefix center c (l + 1)) -
        Polynomial.taylor center P := by
    rw [Polynomial.X_pow_dvd_iff]
    intro i hi
    rw [Polynomial.coeff_sub, coeff_taylor_centeredCoefficientPrefix,
      if_pos (by omega : i < l + 1)]
    exact sub_self _
  have hdiv := X_pow_dvd_shiftedJetSubstitution_sub_of_X_pow_add_dvd Q
    (centeredCoefficientPrefix center c (l + 1)) P center (l - r + 1) hprefix
  have hzero : shiftedJetSubstitution center P Q = 0 := by
    rw [← taylor_differentialSpecialization, hsolution, map_zero]
  have hc := Polynomial.X_pow_dvd_iff.mp hdiv (l - r) (by omega)
  rw [hzero, sub_zero] at hc
  have hsuc : regularLiftCandidate center (c l) (l - r) r
      (centeredCoefficientPrefix center c l) = centeredCoefficientPrefix center c (l + 1) := by
    simpa only [heq] using (centeredCoefficientPrefix_succ (r := r) center c (l - r)).symm
  have hlinear := coeff_shiftedJetSubstitution_regularLiftCandidate (by omega : 0 < l - r)
    Q center (c l) (centeredCoefficientPrefix center c l)
  rw [hsuc, hc, heq] at hlinear
  have hjet : polynomialJet (d := r) center (centeredCoefficientPrefix center c l) =
      polynomialJet center P := by
    rw [polynomialJet_centeredCoefficientPrefix center c l hl]
    funext i
    rw [polynomialJet, Polynomial.hasseJet_eq_taylor_coeff]
  rw [hjet] at hlinear
  rw [aeval_universalTaylorResidual_coeff]
  exact hlinear.symm

/-- On the regular locus, every actual polynomial solution has exactly the rationally
constructed Taylor coefficients wherever the binomial pivot is nonzero. -/
theorem rationalTaylorCoefficient_eq_solution (center : F) (Q : DifferentialPolynomial F r)
    (P : Polynomial F) (hsolution : differentialSpecialization Q P = 0)
    (hseparant : jetEvaluation (separant Q (Fin.last r)) center (polynomialJet center P) ≠ 0)
    (l : ℕ) (hbin : ∀ i, r < i → i ≤ l → (i.choose r : F) ≠ 0) :
    rationalTaylorCoefficient center Q (polynomialJet center P) l =
      (Polynomial.taylor center P).coeff l := by
  induction l using Nat.strong_induction_on with
  | h l ih =>
    by_cases hl : l < r + 1
    · have ht := rationalTaylorCoefficient_initial center Q (polynomialJet center P) ⟨l, hl⟩
      rw [polynomialJet, Polynomial.hasseJet_eq_taylor_coeff] at ht
      exact ht
    · have hlr : r < l := by omega
      have hs : aeval (polynomialJet center P) (initialJetSeparant center Q) ≠ 0 := by
        rwa [aeval_initialJetSeparant]
      have hactual := solution_taylorCoefficient_residual center Q P hsolution l hlr
      have hrational := rationalTaylorCoefficient_residual center Q (polynomialJet center P)
        l hlr hs (hbin l hlr le_rfl)
      have hprior : (fun i : Fin l ↦ rationalTaylorCoefficient center Q
          (polynomialJet center P) i.val) =
            fun i ↦ (Polynomial.taylor center P).coeff i.val := by
        funext i
        exact ih i.val i.isLt (fun j hj hjl ↦ hbin j hj (hjl.trans i.isLt.le))
      rw [hprior, aeval_initialJetSeparant] at hrational
      have hdiff : ((l.choose r : F) *
          (rationalTaylorCoefficient center Q (polynomialJet center P) l -
            (Polynomial.taylor center P).coeff l)) *
          jetEvaluation (separant Q (Fin.last r)) center (polynomialJet center P) = 0 := by
        linear_combination hrational - hactual
      have hleft := (mul_eq_zero.mp hdiff).resolve_right hseparant
      exact sub_eq_zero.mp ((mul_eq_zero.mp hleft).resolve_left (hbin l hlr le_rfl))

end

end ReedSolomon.HiddenDerivative
