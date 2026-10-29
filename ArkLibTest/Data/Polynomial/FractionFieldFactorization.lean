/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.FractionFieldFactorization
import Mathlib.Algebra.Field.ZMod

/-! The content-aware decomposition applies over `F₂[Z][X]` in arbitrary outer degree. -/

open Polynomial

example (f : Polynomial (Polynomial (Polynomial (ZMod 2)))) (hf : f ≠ 0) :
    ∃ (c : Polynomial (Polynomial (ZMod 2)))
      (s : List (Polynomial (Polynomial (Polynomial (ZMod 2))) × ℕ)), c ≠ 0 ∧
      (∀ t ∈ s, 0 < t.1.natDegree ∧ Irreducible t.1 ∧
        Irreducible (t.1.map
          (algebraMap _ (FractionRing (Polynomial (Polynomial (ZMod 2)))))) ∧
        (t.1.map (algebraMap _ (FractionRing (Polynomial (Polynomial (ZMod 2)))))).Separable) ∧
      f = C c * (s.map (fun t ↦ expand _ (2 ^ t.2) t.1)).prod ∧
      f.natDegree = (s.map (fun t ↦ t.1.natDegree * 2 ^ t.2)).sum := by
  exact exists_content_mul_fractionField_separable_factors
    (K := FractionRing (Polynomial (Polynomial (ZMod 2)))) 2 (by decide) f hf

#print axioms Polynomial.exists_content_mul_fractionField_separable_factors
