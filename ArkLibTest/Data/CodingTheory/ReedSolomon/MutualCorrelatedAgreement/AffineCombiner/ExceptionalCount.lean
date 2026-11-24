/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.ExceptionalCount
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Acceptance cases for the exceptional count through the factors of the interpolant

The generic count runs on a family of three coefficients over the algebraic closure of `𝔽₇`.
The challenges are the quadratic multipliers `γ₀ + γ₁ X + γ₂ X²` with coefficients in `𝔽₇`.
A root counts as good when some factor gives it an excluded chart point.

The generic count at `|κ| = 2` and `e = 1` gives the Reed–Solomon term.
That term is `4 d² M² D³ (n / (A - B))²`.

## References

* [Chiesa, A., Weissenberg, G., Yogev, E., and Zheng, K. Z.,
    *Affine combiners for Reed–Solomon proximity gaps*][CWYZ26]
-/

open ReedSolomon Polynomial
open scoped Finset

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- The algebraic closure of `𝔽₇`. -/
private abbrev K := AlgebraicClosure (ZMod 7)

/-- The quadratic family `(1, X, X²)`. -/
private noncomputable def quadraticFamily : Fin 3 → K[X] := ![1, X, X ^ 2]

/-- The interpolant `Z - Y`. -/
private noncomputable def regularQ : MvPolynomial AffineVar K :=
  MvPolynomial.X none - MvPolynomial.X (some 1)

/-- The positions `0, 1, …, 5`. -/
private noncomputable def positions (i : Fin 6) : K := (i.val : K)

/-- The multiplier `γ₀ + γ₁ X + γ₂ X²` of a challenge with coefficients in `𝔽₇`. -/
private noncomputable def quadraticMultiplier (γ : Fin 3 → ZMod 7) : K[X] :=
  familyMultiplier quadraticFamily fun j ↦ algebraMap (ZMod 7) K (γ j)

/-- The chart coordinates `γⱼ ^ (1 / 7 ^ r)` of a challenge. -/
private noncomputable def frobeniusCoordinates (r : ℕ) (γ : Fin 3 → ZMod 7) : Fin 3 → K :=
  fun j ↦ (iterateFrobeniusEquiv K 7 r).symm (algebraMap (ZMod 7) K (γ j))

/-- The target `uᵢ + (∑ⱼ aⱼ ^ (7 ^ r) xᵢ ^ j) vᵢ` at the position `xᵢ`. -/
private noncomputable def quadraticTarget (u v : Fin 6 → K) (r : ℕ) (i : Fin 6) :
    MvPolynomial (Fin 3) K :=
  MvPolynomial.C (u i) + (∑ j : Fin 3, MvPolynomial.X j ^ (7 ^ r) *
    MvPolynomial.C (positions i ^ (j : ℕ))) * MvPolynomial.C (v i)

/-- The positions are distinct in characteristic `7`. -/
private theorem positions_injective : Function.Injective positions := by
  intro i j h
  have h' := (CharP.natCast_eq_natCast K 7).mp h
  rw [Nat.ModEq, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h'
  exact Fin.ext h'

/-- The multiplier of the quadratic family is `a₀ + a₁ X + a₂ X²`. -/
private theorem familyMultiplier_quadraticFamily (a : Fin 3 → K) :
    familyMultiplier quadraticFamily a = C (a 0) + C (a 1) * X + C (a 2) * X ^ 2 := by
  simp [familyMultiplier_apply, quadraticFamily, Fin.sum_univ_three]

/-- Distinct challenges give distinct multipliers. -/
private theorem quadraticMultiplier_injective : Function.Injective quadraticMultiplier := by
  intro γ γ' h
  simp only [quadraticMultiplier, familyMultiplier_quadraticFamily] at h
  funext j
  apply (algebraMap (ZMod 7) K).injective
  fin_cases j
  · simpa using congrArg (·.coeff 0) h
  · simpa using congrArg (·.coeff 1) h
  · simpa using congrArg (·.coeff 2) h

/-- Distinct challenges give distinct chart coordinates. -/
private theorem frobeniusCoordinates_injective (r : ℕ) :
    Function.Injective (frobeniusCoordinates r) := by
  intro γ γ' h
  funext j
  exact (algebraMap (ZMod 7) K).injective
    ((iterateFrobeniusEquiv K 7 r).symm.injective (congrFun h j))

/-- The Frobenius root of a challenge multiplier is the multiplier at its chart coordinates. -/
private theorem map_quadraticMultiplier (r : ℕ) (γ : Fin 3 → ZMod 7) :
    (quadraticMultiplier γ).map ((iterateFrobeniusEquiv K 7 r).symm : K →+* K) =
      familyMultiplier quadraticFamily (frobeniusCoordinates r γ) := by
  simp [quadraticMultiplier, familyMultiplier_quadraticFamily, frobeniusCoordinates]

/-- The target has degree at most `7 ^ r`. -/
private theorem totalDegree_quadraticTarget_le (u v : Fin 6 → K) (r : ℕ) (i : Fin 6) :
    (quadraticTarget u v r i).totalDegree ≤ 7 ^ r := by
  refine (MvPolynomial.totalDegree_add _ _).trans (max_le (by simp) ?_)
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, Nat.add_zero]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ ↦ ?_)
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, Nat.add_zero]
  exact (MvPolynomial.totalDegree_pow _ _).trans (by simp [MvPolynomial.totalDegree_X])

/-- At the chart coordinates, the target reads the agreement condition. -/
private theorem aeval_quadraticTarget (u v : Fin 6 → K) (r : ℕ) (γ : Fin 3 → ZMod 7)
    (i : Fin 6) : MvPolynomial.aeval (frobeniusCoordinates r γ) (quadraticTarget u v r i) =
      u i + leval (positions i) (quadraticMultiplier γ) * v i := by
  have hfr (x : K) : (iterateFrobeniusEquiv K 7 r).symm x ^ 7 ^ r = x := by
    rw [← iterateFrobeniusEquiv_def, RingEquiv.apply_symm_apply]
  simp [quadraticTarget, frobeniusCoordinates, hfr, quadraticMultiplier,
    familyMultiplier_quadraticFamily, Fin.sum_univ_three]

/-- The interpolant `Z - Y` is nonzero. -/
private theorem regularQ_ne_zero : regularQ ≠ 0 :=
  sub_ne_zero.mpr ((MvPolynomial.X_injective (σ := AffineVar) (R := K)).ne (by simp))

/-- The interpolant `Z - Y` has `(Y, Z)`-degree at most `1`. -/
private theorem weightedTotalDegree_regularQ :
    regularQ.weightedTotalDegree affineYZWeight ≤ 1 := by
  rw [regularQ, ← MvPolynomial.mem_restrictWeightedDegree_iff_weightedTotalDegree_le]
  exact Submodule.sub_mem _ (MvPolynomial.X_mem_restrictWeightedDegree _ 1 _ (by simp))
    (MvPolynomial.X_mem_restrictWeightedDegree _ 1 _ (by simp))

-- Six positions, `d = 2`, `B = 2`, `e = 1`, `A = 6` and `D = M = 1` give `1 + 6³ = 217`.
-- That is fewer than the `7³ = 343` challenges.
-- Outside those challenges, every root with six agreements has an excluded chart point.
example (u v : Fin 6 → K) : ∃ Ex : Finset (Fin 3 → ZMod 7), (#Ex : ℝ) ≤ 217 ∧
    ∀ γ ∉ Ex, ∀ P : K[X], multiplierEval (quadraticMultiplier γ) P regularQ = 0 →
      P.degree ≤ 2 →
      6 ≤ {i | leval (positions i) P =
        u i + leval (positions i) (quadraticMultiplier γ) * v i}.ncard →
      ∃ (r : ℕ) (R : MvPolynomial AffineVar K) (c : K),
        chartPoint c (7 ^ r) (frobeniusCoordinates r γ) P ∈ chartExcluded c quadraticFamily R
          (7 ^ r) 2 2 1 [] (fun i ↦ leval (positions i)) (quadraticTarget u v r) := by
  obtain ⟨Ex, hEx, hgood⟩ := exists_interpolantRoots_finset_card_le (κ := Fin 3) 7
    regularQ_ne_zero (d := 2) (A := 6) (B := 2) (e := 1) (D := 1) (M := 1) (by norm_num)
    (by norm_num) (by norm_num) (by simp) weightedTotalDegree_regularQ
    ((MvPolynomial.degreeOf_le_weightedTotalDegree affineYZWeight none (by simp) _).trans
      weightedTotalDegree_regularQ)
    quadraticMultiplier quadraticMultiplier_injective (fun _ ↦ quadraticFamily)
    frobeniusCoordinates frobeniusCoordinates_injective map_quadraticMultiplier []
    (fun i ↦ leval (positions i)) u v (quadraticTarget u v) (totalDegree_quadraticTarget_le u v)
    (aeval_quadraticTarget u v) (separatesDegree_leval positions_injective (by norm_num))
    (fun γ P ↦ ∃ (r : ℕ) (R : MvPolynomial AffineVar K) (c : K),
      chartPoint c (7 ^ r) (frobeniusCoordinates r γ) P ∈ chartExcluded c quadraticFamily R
        (7 ^ r) 2 2 1 [] (fun i ↦ leval (positions i)) (quadraticTarget u v r))
    (fun r R c _ _ _ _ _ hex ↦ ⟨r, R, c, hex⟩)
  refine ⟨Ex, ?_, fun γ hγ P hroot hP hA ↦ hgood γ hγ P hroot hP (by simp) hA⟩
  norm_num at hEx
  exact_mod_cast hEx

-- At `|κ| = 2` and `e = 1`, the generic term is the Reed–Solomon incidence term.
example (d M D n A B : ℕ) (hBA : B < A) :
    (2 * d * M * ((n : ℝ) / (A - B - 1 + 1 : ℕ))) ^ 2 * D ^ (2 + 1) =
      4 * d ^ 2 * M ^ 2 * D ^ 3 * ((n : ℝ) / (A - B : ℕ)) ^ 2 := by
  rw [show A - B - 1 + 1 = A - B by omega]
  ring

/-- info: 'ReedSolomon.exists_factorRoots_finset_card_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.exists_factorRoots_finset_card_le

/-- info: 'ReedSolomon.exists_interpolantRoots_finset_card_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.exists_interpolantRoots_finset_card_le

/-- info: 'ReedSolomon.exists_affineExceptional_finset_card_le_of_interpolant' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.exists_affineExceptional_finset_card_le_of_interpolant
