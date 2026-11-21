/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.Interpolation
import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.InterpolationParams
import Mathlib.Algebra.Field.ZMod

/-!
# Acceptance cases for multiplier interpolation

The numerical cases check the full-constraint sufficient condition.
The free-budget example distinguishes that condition from (4.5) in [CWYZ26].
A quadratic multiplier over `𝔽₁₁` checks the interpolation beyond affine lines.

## References

* [Chiesa, A., Weissenberg, G., Yogev, E., and Zheng, K. Z.,
    *Affine combiners for Reed–Solomon proximity gaps*][CWYZ26]
-/

open ReedSolomon Polynomial

/-- The parameters feed the interpolation: an interpolant exists at those budgets. -/
example {F : Type*} [Field F] [DecidableEq F] {ι : Type*} [Fintype ι] (domain : ι ↪ F)
    (f g : ι → F) {d e : ℕ} {η : ℝ} (h : AffineParams d (Fintype.card ι) e η) :
    ∃ Q, IsMultiplierInterpolant domain f g e d (affineThreshold d (Fintype.card ι) η)
      (affineMultiplicity η) (affineYZBudget d (Fintype.card ι) η)
      (affineRootBudget d (Fintype.card ι) e η) Q :=
  exists_isMultiplierInterpolant domain f g h.surplus

-- The 146 unknowns exceed the truncated count 145, but not the full constraint count 150.
open Polynomial.SymbolicInterpolation in
example : (monomialSupport 1 (4 * 5 - 3) (2 + 1) (3 + 1)).card = 146 ∧
    5 * (constraintSupport 4 (3 + 1)).card = 150 ∧
    5 * (∑ s ∈ Finset.range (min (4 - 1) 2 + 1), (4 - s) * (3 + 1 - s)) = 145 := by
  norm_num [card_monomialSupport, card_constraintSupport, Finset.sum_range_succ]

/-- The weight `(1, e, d)` gives `X^i Y^t Z^j` the weight `i + e t + d j`. -/
example (e d : ℕ) (w : AffineVar →₀ ℕ) :
    Finsupp.weight (multiplierWeight e d) w = w none * d + w (some 0) * 1 + w (some 1) * e := by
  simp [weight_affineVar]

private instance : Fact (Nat.Prime 11) := ⟨by decide⟩

-- Over `𝔽₁₁` with `d = 1`, `e = 2`, `A = 10`, `m = 1`, `D = M = 1`:
-- the 23 unknowns exceed the 11 · 2 = 22 constraints.
open Polynomial.SymbolicInterpolation in
example : Fintype.card (ZMod 11) * (constraintSupport 1 (1 + 1)).card = 22 ∧
    (monomialSupport 1 (1 * 10 - 2 * 1) (1 + 1) (1 + 1)).card = 23 := by
  norm_num [card_monomialSupport, card_constraintSupport, Finset.sum_range_succ]

open Polynomial.SymbolicInterpolation in
/-- With quadratic multipliers the constructed interpolant has positive degree in `Z`. -/
private theorem exists_quadraticInterpolant (f g : ZMod 11 → ZMod 11) :
    ∃ Q, IsMultiplierInterpolant (Function.Embedding.refl (ZMod 11)) f g 2 1 10 1 1 1 Q ∧
      0 < Q.degreeOf none :=
  exists_isMultiplierInterpolant_degreeOf_none_pos _ f g (by norm_num [ZMod.card]) (by
    norm_num [card_monomialSupport, card_constraintSupport, Finset.sum_range_succ])

-- The next example uses an interpolant for `f = -X²` and `g = 1`.
example : ∃ Q, IsMultiplierInterpolant (Function.Embedding.refl (ZMod 11))
    (fun x ↦ -x ^ 2) 1 2 1 10 1 1 1 Q := by
  obtain ⟨Q, hQ, _⟩ := exists_quadraticInterpolant (fun x ↦ -x ^ 2) 1
  exact ⟨Q, hQ⟩

/-- The candidate `0` agrees with `f + X² g` everywhere when `f = -X²` and `g = 1`. -/
private theorem agree_neg_sq : 10 ≤ (polynomialAgreementSet (Function.Embedding.refl (ZMod 11))
    (combinedWord (Function.Embedding.refl (ZMod 11)) (fun x ↦ -x ^ 2) 1 (X ^ 2)) 0).card := by
  rw [show polynomialAgreementSet _ _ _ = Finset.univ by
    ext x
    simp [combinedWord]]
  simp

-- Every such interpolant vanishes along the quadratic multiplier `X²` at every agreeing
-- candidate of degree at most one; here at the candidate `0`.
example (Q : MvPolynomial AffineVar (ZMod 11))
    (hQ : IsMultiplierInterpolant (Function.Embedding.refl _) (fun x ↦ -x ^ 2) 1 2 1 10 1 1 1 Q) :
    multiplierEval (X ^ 2) 0 Q = 0 :=
  hQ.vanish _ 0 (by simp) (by simp) agree_neg_sq

-- A degree-two evaluation has degree at most the `(1, 2, d)`-weighted degree.
example (P : (ZMod 11)[X]) (hP : P.natDegree ≤ 1) (Q : MvPolynomial AffineVar (ZMod 11)) :
    (multiplierEval (X ^ 2) P Q).natDegree ≤ Q.weightedTotalDegree (multiplierWeight 2 1) :=
  natDegree_multiplierEval_le (by simp) hP Q

/-- info: 'ReedSolomon.exists_isMultiplierInterpolant' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.exists_isMultiplierInterpolant

/-- info: 'ReedSolomon.exists_isAffineInterpolant' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.exists_isAffineInterpolant

/-- info: 'ReedSolomon.IsMultiplierInterpolant.vanish_affineMultiplier' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.IsMultiplierInterpolant.vanish_affineMultiplier

/-- info: 'ReedSolomon.multiplierEval_eq_aeval_affineShift' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.multiplierEval_eq_aeval_affineShift

/-- info: 'ReedSolomon.natDegree_multiplierEval_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.natDegree_multiplierEval_le

/-- info: 'ReedSolomon.eval_multiplierEval' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.eval_multiplierEval

/-- info: 'ReedSolomon.natDegree_affineMultiplier_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.natDegree_affineMultiplier_le

/-- info: 'ReedSolomon.map_multiplierEval' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.map_multiplierEval

-- The `m`-th power factor holds over `ℤ`, outside polynomial targets:
-- with `Z ↦ 2` and `X ↦ 6`, the monomial `Z X` evaluates to a multiple of `2²`.
example : (2 : ℤ) ^ 2 ∣ MvPolynomial.aeval (fun w : AffineVar ↦ w.elim (2 : ℤ) ![6, 1])
    (MvPolynomial.monomial (Finsupp.single none 1 + Finsupp.single (some 0) 1) (1 : ℤ)) :=
  pow_dvd_aeval_of_affineWeight_le (by simp) (by simp) fun e he ↦ by
    simp only [MvPolynomial.support_monomial, one_ne_zero, ite_false, Finset.mem_singleton] at he
    subst he
    simp

-- The bound `A ≤ n` is needed: an empty domain meets the surplus condition at `M = 0`,
-- while `M = 0` caps the `Z`-degree at zero.
open Polynomial.SymbolicInterpolation in
example {F : Type*} [Field F] [DecidableEq F] (domain : Empty ↪ F) (f g : Empty → F) :
    Fintype.card Empty * (constraintSupport 1 (0 + 1)).card <
      (monomialSupport 0 (1 * 1 - 0) (0 + 1) (0 + 1)).card ∧
    ¬ ∃ Q, IsMultiplierInterpolant domain f g 1 0 1 1 0 0 Q ∧ 0 < Q.degreeOf none := by
  refine ⟨by norm_num [card_monomialSupport], fun ⟨Q, hQ, hpos⟩ ↦ ?_⟩
  have := hQ.rootDegree_le
  omega

/-- info: 'ReedSolomon.exists_isMultiplierInterpolant_degreeOf_none_pos' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.exists_isMultiplierInterpolant_degreeOf_none_pos

/-- info: 'ReedSolomon.pow_dvd_aeval_of_affineWeight_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.pow_dvd_aeval_of_affineWeight_le
