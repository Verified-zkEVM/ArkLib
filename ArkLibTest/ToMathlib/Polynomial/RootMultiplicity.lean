/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.Polynomial.RootMultiplicity
import Mathlib.Algebra.Field.ZMod

/-!
# Acceptance tests for vanishing from roots of uniform multiplicity

* A polynomial over `ℚ` of degree below `4` with double roots at `0` and `1` is zero, and the
  same holds over `ℤ`, which is a domain but not a field.
* Every hypothesis is needed:
  - domain: over `ZMod 4`, `2 * X` has degree `1 < 1 * 2` and is divisible by `X` and `X - 2`;
  - distinct points: `X` is divisible by `X - 0` at two indices that both map to `0`;
  - strict degree: `X * (X - 1)` has degree `2 = 1 * 2`.
* The degree form allows `multiplicity = 0`; the source statement over a field is an instance.
-/

open Polynomial

/-- Double roots at `0` and `1` and degree below `4` force the zero polynomial. -/
example (W : ℚ[X]) (h0 : (X - C 0) ^ 2 ∣ W) (h1 : (X - C 1) ^ 2 ∣ W) (hW : W.natDegree < 4) :
    W = 0 :=
  eq_zero_of_natDegree_lt_mul_of_pow_X_sub_C_dvd_at_injOn id {0, 1} 2 2 (Set.injOn_id _)
    (by rw [Finset.card_pair zero_ne_one]) (fun i hi ↦ by
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact h0
      · rw [Finset.mem_singleton.mp hi]; exact h1) hW

/-- The theorem holds over the domain `ℤ`. -/
example (W : ℤ[X]) (h0 : X - C 0 ∣ W) (h1 : X - C 1 ∣ W) (h2 : X - C 2 ∣ W)
    (hW : W.natDegree < 3) : W = 0 :=
  eq_zero_of_natDegree_lt_mul_of_pow_X_sub_C_dvd_at_injOn id {0, 1, 2} 1 3 (Set.injOn_id _)
    (by decide) (fun i hi ↦ by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl
      exacts [by simpa using h0, by simpa using h1, by simpa using h2]) hW

/-- The domain hypothesis is needed: over `ZMod 4`, the nonzero polynomial `2 * X` of degree
`1 < 1 * 2` is divisible by `X - 0` and `X - 2`. -/
example :
    let W : (ZMod 4)[X] := C 2 * X
    W ≠ 0 ∧ W.natDegree < 1 * 2 ∧ (X - C 0) ^ 1 ∣ W ∧ (X - C 2) ^ 1 ∣ W := by
  have hdeg : (C 2 * X : (ZMod 4)[X]).natDegree = 1 := natDegree_C_mul_X 2 (by decide)
  refine ⟨fun h ↦ by simp [h] at hdeg, by rw [hdeg]; decide,
    ⟨C 2, by rw [C_0, sub_zero, pow_one, mul_comm]⟩, ⟨C 2, ?_⟩⟩
  rw [pow_one, sub_mul, ← C_mul, show (2 * 2 : ZMod 4) = 0 by decide, C_0, sub_zero, mul_comm]

/-- Distinct points are needed: `X` is divisible by `X - 0` at both indices of the constant map
to `0`, and its degree `1` is below `1 * 2`. -/
example : (X : ℚ[X]) ≠ 0 ∧ (X : ℚ[X]).natDegree < 1 * 2 ∧
    ∀ i ∈ (Finset.univ : Finset (Fin 2)), (X - C ((fun _ ↦ 0 : Fin 2 → ℚ) i)) ^ 1 ∣ X :=
  ⟨X_ne_zero, by simp, fun _ _ ↦ by simp⟩

/-- The strict degree bound is needed: `X * (X - 1)` has simple roots at `0` and `1` and degree
exactly `1 * 2`. -/
example : (X * (X - C 1) : ℚ[X]) ≠ 0 ∧ (X * (X - C 1) : ℚ[X]).natDegree = 1 * 2 := by
  refine ⟨mul_ne_zero X_ne_zero (X_sub_C_ne_zero 1), ?_⟩
  rw [natDegree_mul X_ne_zero (X_sub_C_ne_zero 1), natDegree_X, natDegree_X_sub_C]

/-- The degree form allows `multiplicity = 0`: then `W.degree < 0` already forces `W = 0`. -/
example (W : ℚ[X]) (hW : W.degree < ((0 * 5 : ℕ) : WithBot ℕ)) : W = 0 :=
  eq_zero_of_degree_lt_mul_of_pow_X_sub_C_dvd_at_injOn (fun _ : Fin 0 ↦ (0 : ℚ)) ∅ 0 0
    (by simp) le_rfl (by simp) (by simpa using hW)

/-- Source shape: `eq_zero_of_natDegree_lt_mul_of_pow_X_sub_C_dvd_at_injOn` over a field. -/
example {ι F : Type*} [Field F] {W : F[X]} (points : ι → F) (indices : Finset ι)
    (multiplicity requiredPoints : ℕ) (hpoints : Set.InjOn points (indices : Set ι))
    (hcard : requiredPoints ≤ indices.card)
    (hdiv : ∀ i ∈ indices, (X - C (points i)) ^ multiplicity ∣ W)
    (hdegree : W.natDegree < multiplicity * requiredPoints) : W = 0 :=
  eq_zero_of_natDegree_lt_mul_of_pow_X_sub_C_dvd_at_injOn points indices multiplicity
    requiredPoints hpoints hcard hdiv hdegree
