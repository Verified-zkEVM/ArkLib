/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.FractionFieldRoots
import Mathlib.Algebra.Field.ZMod

/-! Acceptance checks for rational linear roots, including characteristic two and two coefficient
axes as used by the function-field argument. -/

open Polynomial

-- A nonconstant denominator need not give a polynomial root: `X * Y + 1` over `ℚ[X]`.
example : ¬ ∃ c : Polynomial ℚ,
    (C (X : Polynomial ℚ) * X + C 1).eval₂
      (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)))
      (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)) c) = 0 := by
  rw [exists_eval₂_linear_algebraMap_eq_zero_iff]
  rw [X_dvd_iff]
  simp

-- The same domain-root criterion works over `F₂[Z][X]`, with no characteristic bound.
example (a b : Polynomial (Polynomial (ZMod 2))) :
    (∃ c : Polynomial (Polynomial (ZMod 2)),
      (C a * X + C b).eval₂
        (algebraMap _ (FractionRing (Polynomial (Polynomial (ZMod 2)))))
        (algebraMap _ (FractionRing (Polynomial (Polynomial (ZMod 2)))) c) = 0) ↔
      a ∣ b :=
  exists_eval₂_linear_algebraMap_eq_zero_iff
    (K := FractionRing (Polynomial (Polynomial (ZMod 2)))) a b

#print axioms Polynomial.separable_map_fractionField_iff
#print axioms Polynomial.IsPrimitive.separable_map_fractionField_iff
#print axioms Polynomial.eval₂_linear_eq_zero_iff
#print axioms Polynomial.eval₂_linear_algebraMap_eq_zero_iff
#print axioms Polynomial.exists_eval₂_linear_algebraMap_eq_zero_iff
