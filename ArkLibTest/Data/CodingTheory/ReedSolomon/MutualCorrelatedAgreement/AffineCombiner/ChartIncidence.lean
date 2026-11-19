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

A quadratic family `(1, X, X²)` over the algebraic closure of `𝔽₅` checks a chart of three
coefficients.
Its incidence bound carries the exponent `|κ| = 3`.

## References

* [Chiesa, A., Weissenberg, G., Yogev, E., and Zheng, K. Z.,
    *Affine combiners for Reed–Solomon proximity gaps*][CWYZ26]
-/

open ReedSolomon Polynomial

instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- The algebraic closure of `𝔽₅`. -/
private abbrev K := AlgebraicClosure (ZMod 5)

/-- The quadratic family `(1, X, X²)`. -/
private noncomputable def quadraticFamily : Fin 3 → K[X] := ![1, X, X ^ 2]

/-- The regular equation `Z - Y`, of `(Y, Z)`-degree `1`. -/
private noncomputable def regularR : MvPolynomial AffineVar K :=
  MvPolynomial.X none - MvPolynomial.X (some 1)

/-- The three positions `0, 1, 2`. -/
private noncomputable def positions (i : Fin 3) : K := (i.val : K)

/-- The target `a₀` of every position, of degree `1`. -/
private noncomputable def firstCoordinate (_ : Fin 3) : MvPolynomial (Fin 3) K :=
  MvPolynomial.X 0

/-- The positions `0, 1, 2` are distinct in characteristic `5`. -/
private theorem positions_injective : Function.Injective positions := by
  intro i j h
  have h' := (CharP.natCast_eq_natCast K 5).mp h
  rw [Nat.ModEq, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h'
  exact Fin.ext h'

/-- The equation `Z - Y` has `(Y, Z)`-degree at most `1`. -/
private theorem weightedTotalDegree_regularR :
    regularR.weightedTotalDegree affineYZWeight ≤ 1 := by
  rw [regularR, ← MvPolynomial.mem_restrictWeightedDegree_iff_weightedTotalDegree_le]
  exact Submodule.sub_mem _ (MvPolynomial.X_mem_restrictWeightedDegree _ 1 _ (by simp))
    (MvPolynomial.X_mem_restrictWeightedDegree _ 1 _ (by simp))

-- Three positions, `d = s = e = 1`, `B = 1`, `A = 2` and `h = 1` give `(3 · 2 / 1)³ = 216`.
example (c : K) (S : Finset (ChartVar (Fin 3) → K))
    (hS : ∀ pt ∈ S, MvPolynomial.aeval pt (chartEquation c quadraticFamily regularR) = 0 ∧
      MvPolynomial.aeval pt (chartSeparant c quadraticFamily regularR) ≠ 0 ∧
      (∀ Λ' ∈ ([] : List (K[X] →ₗ[K] K)),
        Λ' (chartPolynomial c quadraticFamily regularR 1 1 pt) = 0) ∧
      pt ∉ chartExcluded c quadraticFamily regularR 1 1 1 1 []
        (fun i ↦ leval (positions i)) firstCoordinate)
    (hA : ∀ pt ∈ S, 2 ≤ {i | leval (positions i) (chartPolynomial c quadraticFamily regularR 1 1 pt)
      = MvPolynomial.aeval (pt ∘ Sum.inr) (firstCoordinate i)}.ncard) :
    (S.card : ℚ) ≤ 216 := by
  have h := card_le_of_regular_chartPoints c quadraticFamily regularR (h := 1) (A := 2) le_rfl
    le_rfl le_rfl le_rfl (by simp) weightedTotalDegree_regularR []
    (fun i ↦ leval (positions i)) firstCoordinate (fun _ ↦ by simp [firstCoordinate])
    (separatesDegree_leval positions_injective (by norm_num)) S hS hA
  norm_num at h
  exact_mod_cast h

-- Evaluations at the three positions determine polynomials of degree `1` from two of them.
example : SeparatesDegree [] (fun i ↦ leval (positions i)) 1 2 :=
  separatesDegree_leval positions_injective (by norm_num)

-- Two of the evaluations do not determine polynomials of degree `2`: `X (X - 1)` is a witness.
example : ¬ SeparatesDegree [] (fun i ↦ leval (positions i)) 2 2 := by
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

/-- info: 'ReedSolomon.exists_affineNonpersistent_finset_card_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.exists_affineNonpersistent_finset_card_le
