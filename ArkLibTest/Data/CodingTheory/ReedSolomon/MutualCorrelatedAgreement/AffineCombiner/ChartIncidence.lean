/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.ChartIncidence
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Acceptance cases for the nonpersistent count in the Taylor chart

A quadratic family `(1, X, X²)` over the algebraic closure of `𝔽₇` checks a chart of three
coefficients.
Its incidence bound carries the exponent `|κ| = 3`.

The main case counts a nonempty set: the root `0` along the challenge `0`, with six positions.
The targets `∑ⱼ aⱼ xⱼ ^ (j + 3)` lie outside the reconstruction degree, so no other challenge
shares all six agreements.

## References

* [Chiesa, A., Weissenberg, G., Yogev, E., and Zheng, K. Z.,
    *Affine combiners for Reed–Solomon proximity gaps*][CWYZ26]
-/

open ReedSolomon Polynomial

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- The algebraic closure of `𝔽₇`. -/
private abbrev K := AlgebraicClosure (ZMod 7)

/-- The quadratic family `(1, X, X²)`. -/
private noncomputable def quadraticFamily : Fin 3 → K[X] := ![1, X, X ^ 2]

/-- The regular equation `Z - Y`, of `(Y, Z)`-degree `1`. -/
private noncomputable def regularR : MvPolynomial AffineVar K :=
  MvPolynomial.X none - MvPolynomial.X (some 1)

/-- The positions `0, 1, …, m - 1`. -/
private noncomputable def positions {m : ℕ} (i : Fin m) : K := (i.val : K)

/-- The positions are distinct in characteristic `7` when there are at most seven. -/
private theorem positions_injective {m : ℕ} (hm : m ≤ 7) :
    Function.Injective (positions (m := m)) := by
  intro i j h
  have h' := (CharP.natCast_eq_natCast K 7).mp h
  rw [Nat.ModEq, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h'
  exact Fin.ext h'

/-- The equation `Z - Y` has `(Y, Z)`-degree at most `1`. -/
private theorem weightedTotalDegree_regularR :
    regularR.weightedTotalDegree affineYZWeight ≤ 1 := by
  rw [regularR, ← MvPolynomial.mem_restrictWeightedDegree_iff_weightedTotalDegree_le]
  exact Submodule.sub_mem _ (MvPolynomial.X_mem_restrictWeightedDegree _ 1 _ (by simp))
    (MvPolynomial.X_mem_restrictWeightedDegree _ 1 _ (by simp))

/-- The target `∑ⱼ aⱼ xᵢ ^ (j + 3)` at the position `xᵢ`, of degree one. -/
private noncomputable def highTarget (i : Fin 6) : MvPolynomial (Fin 3) K :=
  ∑ j : Fin 3, MvPolynomial.X j * MvPolynomial.C (positions i ^ (j.val + 3))

/-- The target `∑ⱼ aⱼ xᵢ ^ (j + 3)` has degree at most one. -/
private theorem totalDegree_highTarget_le (i : Fin 6) : (highTarget i).totalDegree ≤ 1 := by
  unfold highTarget
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ ↦ ?_)
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]

/-- The chart point of the root `0` along the challenge `0`, at the center `0`. -/
private noncomputable def zeroPoint : ChartVar (Fin 3) → K := chartPoint 0 1 0 0

/-- The reconstruction at the zero point is the root `0`. -/
private theorem chartPolynomial_zeroPoint :
    chartPolynomial 0 quadraticFamily regularR 1 2 zeroPoint = 0 := by
  refine chartPolynomial_point (p := 7) (e := 0) 0 quadraticFamily regularR (by simp)
    (by simp) ?_ ?_
  · simp [regularR, multiplierEval, familyMultiplier_apply]
  · simp [regularR, multiplierEval, familyMultiplier_apply]

/-- No regular point on another challenge shares the six agreements of the zero point. -/
private theorem zeroPoint_not_mem_chartExcluded :
    zeroPoint ∉ chartExcluded 0 quadraticFamily regularR 1 2 5 1 []
      (fun i ↦ leval (positions i)) highTarget := by
  classical
  rintro ⟨U, hU, -, pt', -, -, hagree, hne⟩
  have hUu : U = Finset.univ := Finset.eq_univ_of_card U (le_antisymm (Finset.card_le_univ U)
    (by simpa using hU))
  subst hUu
  set H := chartPolynomial 0 quadraticFamily regularR 1 2 pt'
  set a := pt' ∘ Sum.inr
  -- The reconstruction `H` has degree at most `2` and meets `∑ⱼ aⱼ X ^ (j + 3)` six times.
  set G : K[X] := C (a 0) * X ^ 3 + C (a 1) * X ^ 4 + C (a 2) * X ^ 5 - H
  have hH := degree_chartPolynomial_le 0 quadraticFamily regularR 1 2 pt'
  have hG : G = 0 := by
    refine Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero
      ((Finset.univ : Finset (Fin 6)).image positions) ?_ ?_
    · rw [Finset.card_image_of_injective _ (positions_injective (by norm_num)),
        Finset.card_univ, Fintype.card_fin]
      refine lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt ?_ (hH.trans_lt (by decide)))
      compute_degree
      decide
    · intro y hy
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
      have := hagree i (Finset.mem_univ _)
      simp only [leval_apply, highTarget, Fin.sum_univ_three] at this
      simp only [G, eval_sub, eval_add, eval_mul, eval_C, eval_pow, eval_X, this]
      simp [a]
  have hcoef (k : ℕ) (hk : 3 ≤ k) : H.coeff k = 0 :=
    Polynomial.coeff_eq_zero_of_degree_lt (hH.trans_lt (by exact_mod_cast (by omega : 2 < k)))
  have h3 := congrArg (Polynomial.coeff · 3) hG
  have h4 := congrArg (Polynomial.coeff · 4) hG
  have h5 := congrArg (Polynomial.coeff · 5) hG
  simp only [Fin.isValue, coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, ↓reduceIte, mul_one,
    Nat.reduceEqDiff, mul_zero, add_zero, Std.le_refl, hcoef, sub_zero, coeff_zero,
    Nat.succ_ne_self, zero_add, Nat.reduceLeDiff, G] at h3 h4 h5
  apply hne
  funext j
  fin_cases j
  · exact h3
  · exact h4
  · exact h5

-- The counted set `{0}` is nonempty, and the bound is `(6 · 2 · 1 · 2 · 1 / 1)³ = 13824`.
example : ({zeroPoint} : Finset (ChartVar (Fin 3) → K)).Nonempty ∧
    (({zeroPoint} : Finset (ChartVar (Fin 3) → K)).card : ℚ) ≤ 13824 := by
  refine ⟨Finset.singleton_nonempty _, ?_⟩
  have h := card_le_of_regular_chartPoints 0 quadraticFamily regularR (d := 2) (s := 1) (h := 1)
    (A := 6) (B := 5) (e := 1) (by norm_num) le_rfl (by norm_num) le_rfl (by simp)
    weightedTotalDegree_regularR [] (fun i ↦ leval (positions i)) highTarget
    totalDegree_highTarget_le (separatesDegree_leval (positions_injective (by norm_num))
      (by norm_num)) {zeroPoint}
    (by
      intro pt hpt
      rw [Finset.mem_singleton] at hpt
      subst hpt
      refine ⟨?_, ?_, by simp, zeroPoint_not_mem_chartExcluded⟩
      · rw [zeroPoint, aeval_chartEquation_point]
        simp [regularR, multiplierEval, familyMultiplier_apply]
      · rw [zeroPoint, aeval_chartSeparant_point]
        simp [regularR, multiplierEval])
    (by
      intro pt hpt
      rw [Finset.mem_singleton] at hpt
      subst hpt
      rw [chartPolynomial_zeroPoint]
      have : (zeroPoint ∘ Sum.inr : Fin 3 → K) = 0 := rfl
      simp [this, highTarget, Set.ncard_univ])
  norm_num at h ⊢

/-- The target `a₀` of every position, of degree `1`. -/
private noncomputable def firstCoordinate (_ : Fin 3) : MvPolynomial (Fin 3) K :=
  MvPolynomial.X 0

-- A degenerate case: with `d = 1` every regular point is excluded, so `S` is always empty.
-- The bound still shows the exponent: `(3 · 2 / 1)³ = 216`.
example (c : K) (S : Finset (ChartVar (Fin 3) → K))
    (hS : ∀ pt ∈ S, MvPolynomial.aeval pt (chartEquation c quadraticFamily regularR) = 0 ∧
      MvPolynomial.aeval pt (chartSeparant c quadraticFamily regularR) ≠ 0 ∧
      (∀ Λ' ∈ ([] : List (K[X] →ₗ[K] K)),
        Λ' (chartPolynomial c quadraticFamily regularR 1 1 pt) = 0) ∧
      pt ∉ chartExcluded c quadraticFamily regularR 1 1 1 1 []
        (fun i : Fin 3 ↦ leval (positions i)) firstCoordinate)
    (hA : ∀ pt ∈ S, 2 ≤ {i : Fin 3 | leval (positions i)
      (chartPolynomial c quadraticFamily regularR 1 1 pt) =
        MvPolynomial.aeval (pt ∘ Sum.inr) (firstCoordinate i)}.ncard) :
    (S.card : ℚ) ≤ 216 := by
  have h := card_le_of_regular_chartPoints c quadraticFamily regularR (h := 1) (A := 2) le_rfl
    le_rfl (by norm_num) le_rfl (by simp) weightedTotalDegree_regularR []
    (fun i : Fin 3 ↦ leval (positions i)) firstCoordinate (fun _ ↦ by simp [firstCoordinate])
    (separatesDegree_leval (positions_injective (by norm_num)) (by norm_num)) S hS hA
  norm_num at h
  exact_mod_cast h

-- Evaluations at three positions determine polynomials of degree `1` from two of them.
example : SeparatesDegree [] (fun i : Fin 3 ↦ leval (positions i)) 1 2 :=
  separatesDegree_leval (positions_injective (by norm_num)) (by norm_num)

-- Two of the evaluations do not determine polynomials of degree `2`: `X (X - 1)` is a witness.
example : ¬ SeparatesDegree [] (fun i : Fin 3 ↦ leval (positions i)) 2 2 := by
  intro h
  have := h {0, 1} (by decide) (X * (X - 1)) (by compute_degree!) (by simp) (by
    intro i hi
    fin_cases hi <;> simp [positions])
  exact mul_ne_zero X_ne_zero (by simpa using X_sub_C_ne_zero (1 : K)) this

/-- info: 'ReedSolomon.mem_chartExcluded' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.mem_chartExcluded

/-- info: 'ReedSolomon.separatesDegree_leval' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.separatesDegree_leval

/-- info: 'ReedSolomon.eq_of_separatesDegree' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.eq_of_separatesDegree

/-- info: 'ReedSolomon.regularLocus_subset_chartExcluded' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.regularLocus_subset_chartExcluded

/-- info: 'ReedSolomon.card_le_of_regular_chartPoints' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.card_le_of_regular_chartPoints

/-- info: 'ReedSolomon.exists_chartExcluded_finset_card_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.exists_chartExcluded_finset_card_le

/-- info: 'ReedSolomon.totalDegree_affineChartTarget_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.totalDegree_affineChartTarget_le

/-- info: 'ReedSolomon.eval_map_eq_aeval_affineChartTarget_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.eval_map_eq_aeval_affineChartTarget_iff

/-- info: 'ReedSolomon.isAffinePersistent_of_mem_chartExcluded' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.isAffinePersistent_of_mem_chartExcluded
