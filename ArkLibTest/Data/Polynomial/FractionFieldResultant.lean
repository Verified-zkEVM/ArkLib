/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.FractionFieldResultant
import ArkLib.Data.Polynomial.ResultantSpecialization
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.SpecificDegree

/-! The padded resultant includes the derivative-degree drop in small characteristic,
the degree-one boundary, fraction-field separability without ring separability, and the
irreducibility criterion with counterexamples for each of its hypotheses. -/

open Polynomial

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

private noncomputable def artinSchreier : (ZMod 3)[X] := X ^ 3 - X

private theorem artinSchreier_derivative : artinSchreier.derivative = -1 := by
  have hthree : ((3 : ℕ) : ZMod 3) = 0 := CharP.cast_eq_zero _ 3
  simp only [artinSchreier, derivative_sub, derivative_pow, derivative_X]
  rw [hthree]
  simp

private theorem artinSchreier_separable : artinSchreier.Separable := by
  rw [separable_def, artinSchreier_derivative]
  exact ⟨0, -1, by simp⟩

example : artinSchreier.derivative.natDegree < artinSchreier.natDegree - 1 := by
  rw [artinSchreier_derivative]
  norm_num [artinSchreier, natDegree_sub_eq_left_of_natDegree_lt]

example : resultant artinSchreier artinSchreier.derivative 3 2 ≠ 0 := by
  have h := resultant_derivative_ne_zero_of_separable_map_fractionField
    (K := ZMod 3) artinSchreier (by simpa using artinSchreier_separable)
  simpa [artinSchreier, natDegree_sub_eq_left_of_natDegree_lt] using h

example : resultant (X : ℚ[X]) (X : ℚ[X]).derivative 1 0 ≠ 0 := by
  have hsep : ((X : ℚ[X]).map (algebraMap ℚ ℚ)).Separable := by
    simpa using (separable_X : (X : ℚ[X]).Separable)
  convert resultant_derivative_ne_zero_of_separable_map_fractionField (X : ℚ[X]) hsep
    using 1
  simp

example : resultant (C 2 : ℚ[X]) (C 2 : ℚ[X]).derivative 0 0 ≠ 0 := by
  have hsep : ((C 2 : ℚ[X]).map (algebraMap ℚ ℚ)).Separable := by
    simp [separable_C]
  convert resultant_derivative_ne_zero_of_separable_map_fractionField (C 2 : ℚ[X]) hsep
    using 1
  simp

-- 2Y has no Bezout identity with its derivative over Z, but is separable over Q.
example : resultant (C 2 * X : ℤ[X]) (C 2 * X : ℤ[X]).derivative 1 0 ≠ 0 := by
  have hsep : ((C 2 * X : ℤ[X]).map (algebraMap ℤ ℚ)).Separable := by
    rw [separable_def]
    refine ⟨0, C (1 / 2), ?_⟩
    norm_num
    rw [← C_ofNat, ← C_mul]
    norm_num
  have h := resultant_derivative_ne_zero_of_separable_map_fractionField (K := ℚ)
    (C 2 * X : ℤ[X]) hsep
  convert h using 1
  simp

-- The actual-degree certificate also covers derivative degree drop in characteristic two.
example : resultant (X ^ 2 + X : Polynomial (ZMod 2))
    (X ^ 2 + X : Polynomial (ZMod 2)).derivative ≠ 0 := by
  apply resultant_derivative_ne_zero_of_fractionField_separable (K := ZMod 2)
  have htwo : (2 : ZMod 2) = 0 := by decide
  simpa [separable_def, one_add_one_eq_two, htwo] using
    (isCoprime_one_right : IsCoprime (X ^ 2 + X : Polynomial (ZMod 2)) 1)

-- The specialization criterion needs positive combined degree: two zero constants fail it.
example : resultant (0 : Polynomial (ZMod 2)) 0 = 1 ∧
    ¬ IsCoprime (0 : Polynomial (ZMod 2)) 0 := by
  exact ⟨by simp, not_isCoprime_zero_zero⟩

/-! ### Irreducibility -/

-- `Y ^ 2 - t` is irreducible over `F[t]` for every field `F`: it is monic of degree two and
-- `t` is not a square in `F[t]`.
private theorem irreducible_sq_sub_C_X (F : Type*) [Field F] :
    Irreducible (X ^ 2 - C X : F[X][X]) := by
  have hmonic : (X ^ 2 - C X : F[X][X]).Monic := by monicity!
  have hdeg : (X ^ 2 - C X : F[X][X]).natDegree = 2 := by compute_degree!
  rw [Monic.irreducible_iff_roots_eq_zero_of_degree_le_three hmonic (by omega) (by omega)]
  refine Multiset.eq_zero_of_forall_notMem fun r hr ↦ ?_
  rw [mem_roots hmonic.ne_zero, IsRoot, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hr
  have h := congrArg natDegree hr
  rw [natDegree_pow, natDegree_X] at h
  omega

-- The source instance: over `F[t]`, an irreducible `A` with exact outer degree `b` and nonzero
-- derivative has `separableResultant A b = resultant A.derivative A (b - 1) b ≠ 0`.
-- The source's `0 < b` is not needed.
example {F : Type*} [Field F] (A : F[X][X]) {b : ℕ} (hdegree : A.natDegree = b)
    (hirreducible : Irreducible A) (hderivative : A.derivative ≠ 0) :
    resultant A.derivative A (b - 1) b ≠ 0 := by
  rw [resultant_comm_sub_one, ← hdegree]
  exact resultant_derivative_ne_zero_of_irreducible A hirreducible hderivative

-- A concrete bivariate instance: `Y ^ 2 - t` over `ℚ[t]`.
example : resultant (X ^ 2 - C X : ℚ[X][X]) (X ^ 2 - C X : ℚ[X][X]).derivative 2 1 ≠ 0 := by
  have h := resultant_derivative_ne_zero_of_irreducible _ (irreducible_sq_sub_C_X ℚ)
    (by simp [derivative_sub])
  have hdeg : (X ^ 2 - C X : ℚ[X][X]).natDegree = 2 := by compute_degree!
  rwa [hdeg] at h

-- The nonzero-derivative hypothesis is needed: `Y ^ 2 - t` over `𝔽₂[t]` is irreducible,
-- its derivative is `2 * Y = 0`, and the padded derivative resultant vanishes.
example : Irreducible (X ^ 2 - C X : (ZMod 2)[X][X]) ∧
    (X ^ 2 - C X : (ZMod 2)[X][X]).derivative = 0 ∧
    resultant (X ^ 2 - C X : (ZMod 2)[X][X]) (X ^ 2 - C X : (ZMod 2)[X][X]).derivative 2 1 = 0 := by
  have hder : (X ^ 2 - C X : (ZMod 2)[X][X]).derivative = 0 := by
    simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero]
    rw [show ((2 : ℕ) : (ZMod 2)[X]) = 0 from CharP.cast_eq_zero _ 2, C_0, zero_mul]
  refine ⟨irreducible_sq_sub_C_X (ZMod 2), hder, ?_⟩
  rw [hder, resultant_zero_right]
  simp

-- Irreducibility is needed: `Y ^ 2` over `ℚ[t]` has derivative `2 * Y ≠ 0`, but the two share
-- the root `0`, so the padded derivative resultant vanishes.
example : (X ^ 2 : ℚ[X][X]).derivative ≠ 0 ∧
    resultant (X ^ 2 : ℚ[X][X]) (X ^ 2 : ℚ[X][X]).derivative 2 1 = 0 := by
  refine ⟨by simp, ?_⟩
  have h := map_resultant_eq_zero_of_common_root (RingHom.id ℚ[X]) (X ^ 2 : ℚ[X][X])
    (X ^ 2 : ℚ[X][X]).derivative (m := 2) (n := 1) (by compute_degree!)
    (by rw [derivative_X_pow]; compute_degree!) (by omega) 0 (by simp) (by simp)
  simpa using h
