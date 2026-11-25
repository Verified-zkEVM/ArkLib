/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.TaylorChart
import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.PersistenceDescent
import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.FrobeniusFactor
import Mathlib.Algebra.CharP.Two
import Mathlib.Basic.Complex.Basic

/-! # Acceptance cases for coefficient descent and regular Taylor reconstruction -/

open ReedSolomon Polynomial
open scoped Finset

/-- The equation `Z² - X²`, singular at the origin. -/
private noncomputable def singularR : MvPolynomial AffineVar ℚ :=
  MvPolynomial.X none ^ 2 - MvPolynomial.X (some 0) ^ 2

-- Initial value and challenge do not determine a root at a singular center.
example : multiplierEval (affineMultiplier 0 0) (X : ℚ[X]) singularR = 0 := by simp [singularR]
example : multiplierEval (affineMultiplier 0 0) (-X : ℚ[X]) singularR = 0 := by
  simp [singularR]
example : (X : ℚ[X]).eval 0 = (-X : ℚ[X]).eval 0 := by simp
example : (X : ℚ[X]) ≠ -X := by
  intro h
  have h1 := congrArg (fun p : ℚ[X] ↦ p.coeff 1) h
  norm_num at h1

-- Complex coefficient data descend to a rational witness; X/1 is one such witness.
example : ∃ H₀ L₀ : ℚ[X], L₀ ≠ 0 ∧ L₀.degree ≤ 1 ∧ H₀.degree ≤ 1 ∧
    ∀ k : Fin 2, H₀.eval (k : ℚ) = L₀.eval (k : ℚ) * (k : ℚ) := by
  apply exists_lineRatioWitness_of_map (algebraMap ℚ ℂ)
    (fun k : Fin 2 ↦ (k : ℚ)) (fun k : Fin 2 ↦ (k : ℚ)) 1
    (H := C Complex.I * X) (L := C Complex.I)
  · exact C_ne_zero.mpr Complex.I_ne_zero
  · simp
  · compute_degree; norm_num
  · intro k
    simp

/-- info: 'ReedSolomon.exists_lineRatioWitness_of_map' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.exists_lineRatioWitness_of_map
/-- info: 'Matrix.exists_mulVec_eq_zero_apply_ne_zero_of_map' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.exists_mulVec_eq_zero_apply_ne_zero_of_map

/-- A regular line equation `Z - Y`. -/
private noncomputable def regularR : MvPolynomial AffineVar ℚ :=
  MvPolynomial.X none - MvPolynomial.X (some 1)

-- The chart reconstruction API has an actual linear root at every challenge and center.
example (a b c : ℚ) :
    chartPolynomial c affineFamily regularR 1 1 (chartPoint c 1 ![a, b] (C a + C b * X)) =
      C a + C b * X := by
  refine chartPolynomial_point c affineFamily regularR (p := 1) (r := 0) (by simp) ?_ ?_ ?_
  · simpa [add_comm] using (degree_linear_le (a := b) (b := a))
  · simp [regularR, affineMultiplier]
  · simp [regularR]

-- A nondegenerate discriminant and the simple-root API.
private theorem regular_discriminant : affineDiscriminant regularR = 1 := by
  simp [affineDiscriminant, regularR]

example (a b : ℚ) : multiplierEval (affineMultiplier a b) (C a + C b * X)
    (MvPolynomial.pderiv none regularR) ≠ 0 := by
  apply multiplierEval_pderiv_ne_zero
    (MvPolynomial.degreeOf_pos_of_pderiv_ne_zero none (by simp [regularR]))
    (by simp [regularR, affineMultiplier])
  simp [regular_discriminant]

/-- A polynomial free of Z, for which the positive-Z-degree guard is necessary. -/
private noncomputable def freeR : MvPolynomial AffineVar ℚ :=
  MvPolynomial.X (some 1) - MvPolynomial.X (some 0)

example : freeR.degreeOf none = 0 := by
  rw [← natDegree_affineNested]
  simp [freeR]

example : affineDiscriminant freeR = 1 := by
  have hdeg : (affineNested freeR).natDegree = 0 := by simp [freeR]
  simp [affineDiscriminant, hdeg, resultant, Matrix.det_isEmpty]

example (P : ℚ[X]) :
    multiplierEval (affineMultiplier 0 1) P freeR = 0 ∧ MvPolynomial.pderiv none freeR = 0 := by
  simp [freeR, affineMultiplier]

-- Finset-filter statements retain the caller's equality instance.
-- The Reed–Solomon lines `α + β X` of injectively embedded challenges form an injective family.
example {E F : Type*} [Field E] [DecidableEq E] {G : MvPolynomial AffineVar E}
    (hG : G ≠ 0) (hZ : G.degreeOf none = 0) (S : Finset (F × F))
    (φ : F × F → E × E) (hφ : φ.Injective) :
    (S.filter fun c ↦ multiplierEval (affineMultiplier (φ c).1 (φ c).2) 0 G = 0).card ≤
      G.degreeOf (some 1) :=
  card_filter_multiplierEval_eq_zero_le hG hZ S _ (affineMultiplier_injective.comp hφ).injOn

example {E F : Type*} [Field E] [DecidableEq E] {R : MvPolynomial AffineVar E}
    {h : ℕ} (hR0 : affineDiscriminant R ≠ 0)
    (hR : R.weightedTotalDegree affineYZWeight ≤ h) (S : Finset (F × F))
    (φ : F × F → E × E) (hφ : φ.Injective) :
    (S.filter fun c ↦
      (affineDiscriminant R).eval (affineMultiplier (φ c).1 (φ c).2) = 0).card ≤ h * (h - 1) :=
  card_filter_affineDiscriminant_eq_zero_le hR0 hR S _ (affineMultiplier_injective.comp hφ).injOn

/-- The quadratic multipliers `X² + c` are pairwise distinct. -/
private theorem injective_X_sq_add_C {E : Type*} [Field E] :
    Function.Injective fun c : E ↦ (X ^ 2 + C c : E[X]) :=
  fun _ _ h ↦ C_injective (add_left_cancel h)

-- A nonzero `G` free of `Z` vanishes along at most `deg_Y G` quadratic multipliers `X² + c`.
example {E : Type*} [Field E] [Fintype E] [DecidableEq E] {G : MvPolynomial AffineVar E}
    (hG : G ≠ 0) (hZ : G.degreeOf none = 0) :
    #(Finset.univ.filter fun c : E ↦ multiplierEval (X ^ 2 + C c) 0 G = 0) ≤
      G.degreeOf (some 1) :=
  card_filter_multiplierEval_eq_zero_le hG hZ _ _ injective_X_sq_add_C.injOn

-- The `Z`-free polynomial `Y - X²` vanishes along the quadratic multiplier `X²`.
example {E : Type*} [Field E] (P : E[X]) :
    multiplierEval (X ^ 2) P (MvPolynomial.X (some 1) - MvPolynomial.X (some 0) ^ 2) = 0 := by
  simp

-- A nonzero discriminant vanishes at most at `h (h - 1)` quadratic multipliers.
example {E : Type*} [Field E] [Fintype E] [DecidableEq E] {R : MvPolynomial AffineVar E}
    {h : ℕ} (hR0 : affineDiscriminant R ≠ 0) (hR : R.weightedTotalDegree affineYZWeight ≤ h) :
    #(Finset.univ.filter fun c : E ↦ (affineDiscriminant R).eval (X ^ 2 + C c) = 0) ≤
      h * (h - 1) :=
  card_filter_affineDiscriminant_eq_zero_le hR0 hR _ _ injective_X_sq_add_C.injOn

-- For a line, the multiplier with `s`-th-rooted coefficients is the line with `s`-th-rooted
-- coefficients.
example {E : Type*} [Field E] (p r : ℕ) [ExpChar E p] [PerfectRing E p] (α β : E) :
    (affineMultiplier α β).map ((iterateFrobeniusEquiv E p r).symm : E →+* E) =
      affineMultiplier ((iterateFrobeniusEquiv E p r).symm α)
        ((iterateFrobeniusEquiv E p r).symm β) := by
  simp

-- In characteristic two, Z² - Y normalizes to Z - Y after squaring X and Y.
open MvPolynomial in
example {K : Type*} [Field K] [CharP K 2] :
    (X none - X (some 1) : MvPolynomial AffineVar K) ^ 2 =
      variablePowerSubstitution (fun v : AffineVar ↦ v.elim 1 fun _ ↦ 2)
        (X none ^ 2 - X (some 1)) := by
  simp only [map_sub, map_pow, variablePowerSubstitution_X, Option.elim_none, Option.elim_some,
    pow_one]
  exact sub_pow_char _ _

/-- The polynomial `Y - Z²` over `ZMod 2`, with zero `Z`-derivative. -/
private noncomputable def inseparableQ : MvPolynomial AffineVar (ZMod 2) :=
  MvPolynomial.X (some 1) - MvPolynomial.X none ^ 2

private theorem irreducible_inseparableQ : Irreducible inseparableQ := by
  let φ := (MvPolynomial.renameEquiv (ZMod 2) (Equiv.swap (none : AffineVar) (some 1))).trans
    (MvPolynomial.optionEquivLeft (ZMod 2) (Fin 2))
  apply (MulEquiv.irreducible_iff φ).mp
  simp only [φ, AlgEquiv.trans_apply, inseparableQ, map_sub, map_pow,
    MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X, Equiv.swap_apply_left,
    Equiv.swap_apply_right, MvPolynomial.optionEquivLeft_X_none,
    MvPolynomial.optionEquivLeft_X_some]
  rw [← Polynomial.C_pow]
  exact Polynomial.irreducible_X_sub_C _

private theorem degreeOf_inseparableQ_none : inseparableQ.degreeOf none = 2 := by
  rw [← natDegree_affineNested]
  simp only [inseparableQ, map_sub, map_pow, affineNested_X_y, affineNested_X_none]
  rw [Polynomial.natDegree_sub_eq_right_of_natDegree_lt (by simp)]
  simp

private theorem pderiv_inseparableQ : MvPolynomial.pderiv none inseparableQ = 0 := by
  simp [inseparableQ, smul_eq_mul, CharTwo.two_eq_zero]

-- The factorization API must use a positive characteristic-two exponent here.
example : ∃ r, ∃ R : MvPolynomial AffineVar (ZMod 2),
    0 < r ∧ MvPolynomial.pderiv none R ≠ 0 ∧
      R ^ (2 ^ r) = MvPolynomial.variablePowerSubstitution
        (fun v : AffineVar ↦ v.elim 1 fun _ ↦ 2 ^ r) inseparableQ := by
  obtain ⟨r, R, -, hder, -, -, hidentity, -⟩ := exists_frobeniusFactor 2
    irreducible_inseparableQ (by rw [degreeOf_inseparableQ_none]; norm_num)
  have hr : 0 < r := by
    by_contra h
    have hr0 : r = 0 := Nat.eq_zero_of_not_pos h
    have hRQ : R = inseparableQ := by simpa [hr0, inseparableQ] using hidentity
    apply hder
    rw [hRQ]
    exact pderiv_inseparableQ
  exact ⟨r, R, hr, hder, hidentity⟩

-- Frobenius transport along the quadratic multiplier `X²`: the root `X` of `Y - Z²` along `X²`
-- gives the root `X^(2^r)` of the normalized factor along `X²`.
example : ∃ r, ∃ R : MvPolynomial AffineVar (ZMod 2), Irreducible R ∧
    multiplierEval (X ^ 2) (expand (ZMod 2) (2 ^ r) X) R = 0 := by
  obtain ⟨r, R, hirr, -, -, -, -, hroot⟩ := exists_frobeniusFactor 2
    irreducible_inseparableQ (by rw [degreeOf_inseparableQ_none]; norm_num)
  have h := hroot (X ^ 2) X (by simp [inseparableQ])
  exact ⟨r, R, hirr, by simpa using h⟩

/-- info: 'ReedSolomon.multiplierEval_eq_nested' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.multiplierEval_eq_nested

/-- info: 'ReedSolomon.card_filter_multiplierEval_eq_zero_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.card_filter_multiplierEval_eq_zero_le

/-- info: 'ReedSolomon.card_filter_affineDiscriminant_eq_zero_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.card_filter_affineDiscriminant_eq_zero_le

/-- info: 'ReedSolomon.multiplierEval_pderiv_ne_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.multiplierEval_pderiv_ne_zero

/-- info: 'ReedSolomon.multiplierEval_eq_of_degreeOf_none_eq_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.multiplierEval_eq_of_degreeOf_none_eq_zero

/-- info: 'ReedSolomon.exists_frobeniusFactor' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.exists_frobeniusFactor

/-- info: 'ReedSolomon.map_affineMultiplier' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.map_affineMultiplier
