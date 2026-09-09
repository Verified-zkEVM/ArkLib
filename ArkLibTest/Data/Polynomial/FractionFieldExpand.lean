/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.FractionFieldExpand
import Mathlib.Algebra.Field.ZMod

/-! Characteristic-two acceptance for Frobenius descent over two polynomial coefficient axes. -/

open Polynomial

example {f : Polynomial (Polynomial (Polynomial (ZMod 2)))}
    (hf : Irreducible (f.map
      (algebraMap _ (FractionRing (Polynomial (Polynomial (ZMod 2))))))) :
    ∃ (n : ℕ) (g : Polynomial (Polynomial (Polynomial (ZMod 2)))),
      Irreducible (g.map (algebraMap _ (FractionRing (Polynomial (Polynomial (ZMod 2)))))) ∧
      (g.map (algebraMap _ (FractionRing (Polynomial (Polynomial (ZMod 2)))))).Separable ∧
      expand _ (2 ^ n) g = f ∧ g.natDegree * 2 ^ n = f.natDegree := by
  exact exists_fractionField_separable_expand
    (K := FractionRing (Polynomial (Polynomial (ZMod 2)))) 2 (by decide) hf

#print axioms Polynomial.exists_fractionField_separable_expand
