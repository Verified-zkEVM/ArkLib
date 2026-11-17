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

/-- The equation `Z² - X²`, singular at the origin. -/
private noncomputable def singularR : MvPolynomial AffineVar ℚ :=
  MvPolynomial.X none ^ 2 - MvPolynomial.X (some 0) ^ 2

-- Initial value and challenge do not determine a root at a singular center.
example : affineLineEval 0 0 (X : ℚ[X]) singularR = 0 := by simp [singularR]
example : affineLineEval 0 0 (-X : ℚ[X]) singularR = 0 := by simp [singularR]
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

#print axioms ReedSolomon.totalDegree_affineChartNumerator_le
#print axioms ReedSolomon.exists_lineRatioWitness_of_map
#print axioms Matrix.exists_mulVec_eq_zero_apply_ne_zero_of_map

/-- A regular line equation `Z - Y`. -/
private noncomputable def regularR : MvPolynomial AffineVar ℚ :=
  MvPolynomial.X none - MvPolynomial.X (some 1)

-- The chart reconstruction API has an actual linear root at every challenge and center.
example (a b c : ℚ) :
    affineChartPolynomial c regularR 1 1 (affineChartPoint c 1 a b (C a + C b * X)) =
      C a + C b * X := by
  refine affineChartPolynomial_point c regularR (p := 1) (e := 0) (by simp) ?_ ?_ ?_
  · simpa [add_comm] using (degree_linear_le (a := b) (b := a))
  · simp [regularR, affineMultiplier]
  · simp [regularR]

-- A nondegenerate discriminant and the simple-root API.
private theorem regular_discriminant : affineDiscriminant regularR = 1 := by
  simp [affineDiscriminant, regularR]

example (a b : ℚ) : affineLineEval a b (C a + C b * X)
    (MvPolynomial.pderiv none regularR) ≠ 0 := by
  apply affineLineEval_pderiv_ne_zero
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

example (P : ℚ[X]) : affineLineEval 0 1 P freeR = 0 ∧ MvPolynomial.pderiv none freeR = 0 := by
  simp [freeR, affineMultiplier]

-- The normalized-factor theorem exports its defining polynomial identity.
example : ∃ e, ∃ R : MvPolynomial AffineVar ℚ,
    R ^ (1 ^ e) = MvPolynomial.variablePowerSubstitution
      (fun v : AffineVar ↦ v.elim 1 fun _ ↦ 1 ^ e) regularR := by
  have hirr : Irreducible regularR := by
    apply (MulEquiv.irreducible_iff (MvPolynomial.optionEquivLeft ℚ (Fin 2))).mp
    simpa [regularR] using
      Polynomial.irreducible_X_sub_C (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) ℚ)
  obtain ⟨e, R, -, -, -, -, hidentity, -⟩ := exists_affineFrobeniusFactor 1 hirr
    (MvPolynomial.degreeOf_pos_of_pderiv_ne_zero none (by simp [regularR]))
  exact ⟨e, R, hidentity⟩

-- Finset-filter statements retain the caller's equality instance.
example {E F : Type*} [Field E] [DecidableEq E] {G : MvPolynomial AffineVar E}
    (hG : G ≠ 0) (hZ : G.degreeOf none = 0) (S : Finset (F × F))
    (φ : F × F → E × E) (hφ : φ.Injective) :
    (S.filter fun c ↦ affineLineEval (φ c).1 (φ c).2 0 G = 0).card ≤ G.degreeOf (some 1) :=
  card_filter_affineLine_eq_zero_le hG hZ S φ hφ

example {E F : Type*} [Field E] [DecidableEq E] {R : MvPolynomial AffineVar E}
    {h : ℕ} (hR0 : affineDiscriminant R ≠ 0)
    (hR : R.weightedTotalDegree affineYZWeight ≤ h) (S : Finset (F × F))
    (φ : F × F → E × E) (hφ : φ.Injective) :
    (S.filter fun c ↦
      (affineDiscriminant R).eval (affineMultiplier (φ c).1 (φ c).2) = 0).card ≤ h * (h - 1) :=
  card_filter_affineDiscriminant_eq_zero_le hR0 hR S φ hφ

-- In characteristic two, Z² - Y normalizes to Z - Y after squaring X and Y.
open MvPolynomial in
example {K : Type*} [Field K] [CharP K 2] :
    (X none - X (some 1) : MvPolynomial AffineVar K) ^ 2 =
      variablePowerSubstitution (fun v : AffineVar ↦ v.elim 1 fun _ ↦ 2)
        (X none ^ 2 - X (some 1)) := by
  simp only [map_sub, map_pow, variablePowerSubstitution_X, Option.elim_none, Option.elim_some,
    pow_one]
  exact sub_pow_char _ _

-- The factorization API must use a positive characteristic-two exponent here.
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
example : ∃ e, ∃ R : MvPolynomial AffineVar (ZMod 2),
    0 < e ∧ MvPolynomial.pderiv none R ≠ 0 ∧
      R ^ (2 ^ e) = MvPolynomial.variablePowerSubstitution
        (fun v : AffineVar ↦ v.elim 1 fun _ ↦ 2 ^ e) inseparableQ := by
  obtain ⟨e, R, -, hder, -, -, hidentity, -⟩ := exists_affineFrobeniusFactor 2
    irreducible_inseparableQ (by rw [degreeOf_inseparableQ_none]; norm_num)
  have he : 0 < e := by
    by_contra h
    have he0 : e = 0 := Nat.eq_zero_of_not_pos h
    have hRQ : R = inseparableQ := by simpa [he0, inseparableQ] using hidentity
    apply hder
    rw [hRQ]
    exact pderiv_inseparableQ
  exact ⟨e, R, he, hder, hidentity⟩
