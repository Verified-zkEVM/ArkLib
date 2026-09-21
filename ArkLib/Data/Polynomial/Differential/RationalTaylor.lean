/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Differential.TaylorResidual
public import ArkLib.ToMathlib.MvPolynomial.ClearedSubstitution
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Tactic.LinearCombination

/-!
# Rational Taylor coefficients with separant denominators

Let `Q` be a differential polynomial of order `r` over a field and fix a center `a`. The Taylor
coefficient `c_l` at `a` of a solution `P` with `l > r` is determined by the earlier coefficients
through an affine equation. Its linear part is `(l choose r) * c_l` times the separant
`∂Q/∂Y_r` evaluated at the initial jet `(c₀, ..., c_r)`, and its constant part is the
coefficient of `ξ ^ (l - r)` in the universal Taylor residual evaluated at `c₀, ..., c_(l-1)`.
Solving these equations in order expresses each `c_l` as a rational function of the initial jet.

This file makes that rational function explicit. `rationalTaylorNumerator a Q l` is a polynomial
in the initial jet coordinates, and the coefficient is
`rationalTaylorNumerator a Q l / S ^ (2(l - r) - 1)`, where `S` is the separant at the initial
jet. The numerator is defined by recursion on `l`: substitute the earlier numerators into the
residual coefficient and clear the common separant power with
`MvPolynomial.clearedSubstitution`. The denominator budget
`denominator_weight_le_of_mem_universalTaylorResidual_coeff` shows that `2(l - r) - 2` powers
suffice for the residual coefficient.

## Main statements

* `PolynomialDifferential.initialJetSeparant` and `aeval_initialJetSeparant`: the separant as a
  polynomial in the initial jet.
* `PolynomialDifferential.rationalTaylorNumerator` and
  `totalDegree_rationalTaylorNumerator_le`: the numerator has total degree at most
  `(2(l - r) - 1) * (jetTotalDegree Q - 1) + 1`.
* `PolynomialDifferential.rationalTaylorCoefficient`, with `rationalTaylorCoefficient_initial`
  (it keeps the initial jet) and `rationalTaylorCoefficient_residual` (it solves each affine
  equation when the separant and the binomial pivot are nonzero).
* `rationalTaylorCoefficient_residual_prefix`: the same equation stated for the centered
  coefficient prefix built from the rational coefficients.
* `eq_rationalTaylorCoefficient_of_residual`: any coefficient sequence that extends the initial
  jet and solves the affine equations agrees with the rational coefficients.
* `TaylorExponentSufficient` and its instances: common separant exponents for a finite chart.

## References

[DKTZ26], Appendix A.3, Lemma A.5. The declarations are ported from
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/Taylor/Numerator.lean` at ArkLib
revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

* `TaylorExponentSufficient`, `TaylorExponentSufficient.mono`,
  `taylorExponentSufficient_two_mul`, `taylorExponentSufficient_two_mul_sub_three`, and
  `taylorExponentSufficient_firstOrder_tight` are unchanged, except that the source hypothesis
  `2 ≤ K` of `taylorExponentSufficient_two_mul_sub_three` is removed. The source's
  `firstOrder_tight_exponent_le_legacy` (`2 * D - 3 ≤ 2 * D - 1`) is not ported; it is `omega`.
* `initialJetSeparant`, `aeval_initialJetSeparant`, `rationalTaylorNumerator`,
  `rationalTaylorCoefficient`, `rationalTaylorCoefficient_initial`, and
  `rationalTaylorCoefficient_residual` are unchanged in content. `initialJetSeparant` is defined
  over any commutative semiring.
* `totalDegree_initialJetSeparant_le` and `totalDegree_rationalTaylorNumerator_le` are stated with
  the core `jetTotalDegree`. The source hypothesis `0 < jetTotalDegree Q` of the numerator bound is
  removed: when it fails the residual coefficients are constants and the bound still holds.
* `eq_rationalTaylorCoefficient_of_residual` is the induction inside the source's
  `rationalTaylorCoefficient_eq_solution`, separated from the fact that an actual polynomial
  solution satisfies the affine equations.
* `rationalTaylorCoefficient_residual_prefix` is new; it combines
  `rationalTaylorCoefficient_residual` with `aeval_universalTaylorResidual_coeff`.

Deferred to the next slice: the source's `solution_taylorCoefficient_residual` and
`rationalTaylorCoefficient_eq_solution`, which need the coefficient formula for a one-coefficient
Taylor perturbation (`coeff_shiftedJetSubstitution_regularLiftCandidate` in
`.../RootFinding/Regular/Lifting.lean`) and the contact lemma
`X_pow_dvd_shiftedJetSubstitution_sub_of_X_pow_add_dvd` in `.../RootFinding/Regular/Iteration.lean`.

* [Dao, Q., Kominers, S. D., Thaler, J., Zheng, K. Z., *Reed--Solomon List Decoding and Mutual
  Correlated Agreement up to Capacity*][DKTZ26]
-/

@[expose] public section

namespace PolynomialDifferential

noncomputable section

open MvPolynomial
open scoped BigOperators

/-! ### Common separant exponents -/

/-- A common separant exponent `τ` is sufficient for a length-`K` chart when it dominates the
denominator exponent `2(l - r) - 1` of every coefficient `c_l` with `l < K`. With natural
subtraction the exponent is zero for the initial coordinates `l ≤ r`. -/
def TaylorExponentSufficient (r K τ : ℕ) : Prop :=
  ∀ l : Fin K, 2 * (l.val - r) - 1 ≤ τ

/-- A larger common exponent is still sufficient. -/
theorem TaylorExponentSufficient.mono {r K τ τ' : ℕ}
    (hτ : TaylorExponentSufficient r K τ) (h : τ ≤ τ') :
    TaylorExponentSufficient r K τ' :=
  fun l ↦ (hτ l).trans h

/-- The exponent `2K` is sufficient at every differential order. -/
theorem taylorExponentSufficient_two_mul (r K : ℕ) :
    TaylorExponentSufficient r K (2 * K) := by
  intro l
  omega

/-- The exponent `2K - 3` is sufficient at every differential order. The worst case is `r = 0`
and `l = K - 1`, where the exponent is exactly `2K - 3` for `K ≥ 2`. For `K ≤ 1` the only
possible coordinate is `l = 0`, whose exponent is zero, so natural subtraction needs no length
hypothesis. -/
theorem taylorExponentSufficient_two_mul_sub_three (r K : ℕ) :
    TaylorExponentSufficient r K (2 * K - 3) := by
  intro l
  omega

/-- For a first-order equation and a chart of length `D + 1`, the exponent `2D - 3` is
sufficient, and it is attained at `l = D` when `D ≥ 2`. At `D ≤ 1` no coefficient after the initial
pair is reconstructed and the exponent is zero. -/
theorem taylorExponentSufficient_firstOrder_tight (D : ℕ) :
    TaylorExponentSufficient 1 (D + 1) (2 * D - 3) := by
  intro l
  omega

/-! ### The separant at the initial jet -/

section CommSemiring

variable {F : Type*} [CommSemiring F] {r : ℕ}

/-- The separant `∂Q/∂Y_r` with the independent variable set to `center`, as a polynomial in the
initial jet coordinates `Y_0, ..., Y_r`. -/
def initialJetSeparant (center : F) (Q : DifferentialPolynomial F r) :
    MvPolynomial (Fin (r + 1)) F :=
  aeval (fun i ↦ i.elim (C center) X) (separant Q (Fin.last r))

/-- The initial separant has total degree at most `jetTotalDegree Q - 1`. -/
theorem totalDegree_initialJetSeparant_le (center : F) (Q : DifferentialPolynomial F r) :
    (initialJetSeparant center Q).totalDegree ≤ jetTotalDegree Q - 1 := by
  have hw : (jetDegreeWeight : JetVariable r → ℕ) = fun i ↦ i.elim 0 (fun _ ↦ 1) := by
    funext i
    cases i <;> rfl
  rw [← weightedTotalDegree_one]
  refine le_trans (weightedTotalDegree_aeval_le_of_le
    (fun i : Option (Fin (r + 1)) ↦ i.elim 0 (fun _ ↦ 1))
    (1 : Fin (r + 1) → ℕ) _ _ ?_) ?_
  · intro i
    cases i with
    | none => simp
    | some j =>
      simp only [Option.elim_some, weightedTotalDegree_one]
      exact (totalDegree_monomial_le _ _).trans (by simp)
  · rw [← hw]
    exact separant_total_le Q (Fin.last r)

/-- Evaluating the initial separant at a jet is `jetEvaluation` of the separant at `center`. -/
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

end CommSemiring

/-! ### Numerators and rational coefficients -/

variable {F : Type*} [Field F] {r : ℕ}

/-- The numerator of the rational Taylor coefficient `c_l`, a polynomial in the initial jet.

For `l ≤ r` it is the coordinate `Y_l`. For `l > r` it is
`-(l choose r)⁻¹` times the cleared substitution of the earlier numerators, with denominator
exponents `2(i - r) - 1` and budget `2(l - r) - 2`, into the coefficient of `ξ ^ (l - r)` of the
universal residual on the chart of length `l`. If `(l choose r) = 0` in `F`, the inverse is zero
and so is the numerator; the rational equations then hold only under the pivot hypothesis of
`rationalTaylorCoefficient_residual`. -/
def rationalTaylorNumerator (center : F) (Q : DifferentialPolynomial F r)
    (l : ℕ) : MvPolynomial (Fin (r + 1)) F :=
  if hl : l < r + 1 then X ⟨l, hl⟩ else
    -C ((l.choose r : F)⁻¹) *
      clearedSubstitution C (initialJetSeparant center Q)
        (fun i : Fin l ↦ rationalTaylorNumerator center Q i.val)
        (fun i ↦ 2 * (i.val - r) - 1) (2 * (l - r) - 2)
        ((optionEquivLeft F (Fin l) (universalTaylorResidual l center Q)).coeff (l - r))
termination_by l

/-- The residual coefficient used at step `l` fits the denominator budget `2(l - r) - 2`. -/
private theorem residual_coeff_denominator_budget (center : F) (Q : DifferentialPolynomial F r)
    (l : ℕ) :
    ∀ m ∈ ((optionEquivLeft F (Fin l) (universalTaylorResidual l center Q)).coeff
        (l - r)).support,
      Finsupp.weight (fun i : Fin l ↦ 2 * (i.val - r) - 1) m ≤ 2 * (l - r) - 2 :=
  fun m hm ↦ denominator_weight_le_of_mem_universalTaylorResidual_coeff
    (by omega : l ≤ r + (l - r)) center Q m hm

/-- The numerator of `c_l` has total degree at most `(2(l - r) - 1) * (jetTotalDegree Q - 1) + 1`.
For `l ≤ r` the bound is `1`, the degree of a coordinate. There is no hypothesis on `Q`: when
`jetTotalDegree Q = 0` the residual coefficients are constants and the bound is `1`. -/
theorem totalDegree_rationalTaylorNumerator_le (center : F) (Q : DifferentialPolynomial F r)
    (l : ℕ) :
    (rationalTaylorNumerator center Q l).totalDegree ≤
      (2 * (l - r) - 1) * (jetTotalDegree Q - 1) + 1 := by
  induction l using Nat.strong_induction_on with
  | h l ih =>
    rw [rationalTaylorNumerator]
    split_ifs with hl
    · exact (totalDegree_monomial_le _ _).trans (by simp)
    · have hN : ∀ i : Fin l,
          (rationalTaylorNumerator center Q i.val).totalDegree ≤
            (2 * (i.val - r) - 1) * (jetTotalDegree Q - 1) + 1 :=
        fun i ↦ ih i.val i.isLt
      have hd := totalDegree_clearedSubstitution
        (initialJetSeparant center Q)
        (fun i : Fin l ↦ rationalTaylorNumerator center Q i.val)
        (fun i ↦ 2 * (i.val - r) - 1) (2 * (l - r) - 2)
        (jetTotalDegree Q - 1) (jetTotalDegree Q)
        ((optionEquivLeft F (Fin l) (universalTaylorResidual l center Q)).coeff (l - r))
        (totalDegree_initialJetSeparant_le center Q) hN
        (residual_coeff_denominator_budget center Q l)
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
      have hv : jetTotalDegree Q ≤ (jetTotalDegree Q - 1) + 1 := by omega
      nlinarith [hp.trans hd]

/-- The rational Taylor coefficient `c_l` at an initial jet: the numerator evaluated at the jet,
divided by the separant at the jet to the power `2(l - r) - 1`. If the separant vanishes at the
jet, every coefficient with `l > r` is zero because division by zero is zero; the coefficients
are meaningful only where the separant is nonzero. -/
def rationalTaylorCoefficient (center : F) (Q : DifferentialPolynomial F r)
    (jet : Fin (r + 1) → F) (l : ℕ) : F :=
  aeval jet (rationalTaylorNumerator center Q l) /
    aeval jet (initialJetSeparant center Q) ^ (2 * (l - r) - 1)

/-- The rational coefficients start with the initial jet. -/
theorem rationalTaylorCoefficient_initial (center : F) (Q : DifferentialPolynomial F r)
    (jet : Fin (r + 1) → F) (l : Fin (r + 1)) :
    rationalTaylorCoefficient center Q jet l.val = jet l := by
  rw [rationalTaylorCoefficient, rationalTaylorNumerator, dite_eq_left_of_eq_true (eq_true l.isLt)]
  have hl : l.val - r = 0 := by omega
  simp [hl]

/-- For `l > r`, the rational coefficient `c_l` solves the affine equation
`R_(l-r)(c₀, ..., c_(l-1)) + (l choose r) * c_l * S = 0`, where `R_(l-r)` is the coefficient of
`ξ ^ (l - r)` in the universal residual and `S` is the separant at the jet.

Both hypotheses are needed. If `S = 0` the equation has no linear term. If `(l choose r) = 0` in
`F`, which happens for example in characteristic `2` at `r = 1`, `l = 2`, the linear term vanishes
and the rational coefficient is zero, while the constant term need not be. -/
theorem rationalTaylorCoefficient_residual (center : F) (Q : DifferentialPolynomial F r)
    (jet : Fin (r + 1) → F) (l : ℕ) (hl : r < l)
    (hS : aeval jet (initialJetSeparant center Q) ≠ 0)
    (hbin : (l.choose r : F) ≠ 0) :
    aeval (fun i : Fin l ↦ rationalTaylorCoefficient center Q jet i.val)
        ((optionEquivLeft F (Fin l) (universalTaylorResidual l center Q)).coeff (l - r)) +
      ((l.choose r : F) * rationalTaylorCoefficient center Q jet l) *
        aeval jet (initialJetSeparant center Q) = 0 := by
  have hmap := map_clearedSubstitution C (aeval jet).toRingHom
    (initialJetSeparant center Q) hS
    (fun i : Fin l ↦ rationalTaylorNumerator center Q i.val)
    (fun i ↦ 2 * (i.val - r) - 1) (2 * (l - r) - 2)
    ((optionEquivLeft F (Fin l) (universalTaylorResidual l center Q)).coeff (l - r))
    (residual_coeff_denominator_budget center Q l)
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
    rw [rationalTaylorCoefficient, rationalTaylorNumerator, dite_eq_right_of_eq_false (eq_false hn)]
  simp only [map_mul, map_neg, aeval_C, Algebra.algebraMap_self, RingHom.id_apply]
  rw [hmap]
  have he : 2 * (l - r) - 1 = (2 * (l - r) - 2) + 1 := by omega
  rw [he, pow_succ]
  field_simp
  ring

/-- The affine equation of `rationalTaylorCoefficient_residual`, with the residual term written as
the Taylor coefficient of order `l - r` at `center` of `Q` specialized at the centered prefix of
the first `l` rational coefficients. -/
theorem rationalTaylorCoefficient_residual_prefix (center : F) (Q : DifferentialPolynomial F r)
    (jet : Fin (r + 1) → F) (l : ℕ) (hl : r < l)
    (hS : jetEvaluation (separant Q (Fin.last r)) center jet ≠ 0)
    (hbin : (l.choose r : F) ≠ 0) :
    (Polynomial.taylor center (differentialSpecialization Q
        (Polynomial.centeredCoefficientPrefix center
          (rationalTaylorCoefficient center Q jet) l))).coeff (l - r) +
      ((l.choose r : F) * rationalTaylorCoefficient center Q jet l) *
        jetEvaluation (separant Q (Fin.last r)) center jet = 0 := by
  rw [← aeval_initialJetSeparant] at hS ⊢
  rw [← aeval_universalTaylorResidual_coeff]
  exact rationalTaylorCoefficient_residual center Q jet l hl hS hbin

/-- Uniqueness of the rational parametrization. Let `c : ℕ → F` start with the initial jet and,
for every `r < l ≤ L`, solve the affine equation of `rationalTaylorCoefficient_residual`. If the
separant at the jet and the binomial pivots `(l choose r)` for `r < l ≤ L` are nonzero, then
`c l` is the rational coefficient for every `l ≤ L`.

The source applied this argument only to the Taylor coefficients of an actual solution; the
statement here isolates the algebra from the solution property. -/
theorem eq_rationalTaylorCoefficient_of_residual (center : F) (Q : DifferentialPolynomial F r)
    (jet : Fin (r + 1) → F) (c : ℕ → F) (L : ℕ)
    (hinit : ∀ i : Fin (r + 1), c i.val = jet i)
    (hS : aeval jet (initialJetSeparant center Q) ≠ 0)
    (hbin : ∀ l, r < l → l ≤ L → (l.choose r : F) ≠ 0)
    (hc : ∀ l, r < l → l ≤ L →
      aeval (fun i : Fin l ↦ c i.val)
          ((optionEquivLeft F (Fin l) (universalTaylorResidual l center Q)).coeff (l - r)) +
        ((l.choose r : F) * c l) * aeval jet (initialJetSeparant center Q) = 0)
    (l : ℕ) (hlL : l ≤ L) :
    c l = rationalTaylorCoefficient center Q jet l := by
  induction l using Nat.strong_induction_on with
  | h l ih =>
    by_cases hl : l < r + 1
    · rw [hinit ⟨l, hl⟩, rationalTaylorCoefficient_initial center Q jet ⟨l, hl⟩]
    · have hlr : r < l := by omega
      have hrat := rationalTaylorCoefficient_residual center Q jet l hlr hS (hbin l hlr hlL)
      have hprior : (fun i : Fin l ↦ rationalTaylorCoefficient center Q jet i.val) =
          fun i ↦ c i.val := by
        funext i
        exact (ih i.val i.isLt (i.isLt.le.trans hlL)).symm
      rw [hprior] at hrat
      have hdiff : ((l.choose r : F) * (c l - rationalTaylorCoefficient center Q jet l)) *
          aeval jet (initialJetSeparant center Q) = 0 := by
        linear_combination hc l hlr hlL - hrat
      have hleft := (mul_eq_zero.mp hdiff).resolve_right hS
      exact sub_eq_zero.mp ((mul_eq_zero.mp hleft).resolve_left (hbin l hlr hlL))

end

end PolynomialDifferential
