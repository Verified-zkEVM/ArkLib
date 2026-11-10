/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/

import ArkLib.Data.Polynomial.SubspacePolynomial
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finite.GaloisField

/-! # Subspace polynomial acceptance tests -/

open Polynomial

-- The subspace polynomial of `𝔽₂` is monic of degree two.
example : (subspacePolynomial (⊤ : AddSubgroup (ZMod 2))).Monic ∧
    (subspacePolynomial (⊤ : AddSubgroup (ZMod 2))).natDegree = 2 := by
  refine ⟨monic_subspacePolynomial _, ?_⟩
  rw [natDegree_subspacePolynomial]
  simp [Nat.card_eq_fintype_card, ZMod.card]

-- `GaloisField 2 2` has at least `2 ^ (1 * (2 - 1)) = 2` additive subgroups of size `2`.
example : 2 ≤ Nat.card {V : AddSubgroup (GaloisField 2 2) // Nat.card V = 2} := by
  have : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  exact FiniteField.two_pow_le_card_addSubgroup (F := GaloisField 2 2) (m := 2) (v := 1)
    (by rw [← Nat.card_eq_fintype_card]; exact GaloisField.card 2 2 (by norm_num)) (by norm_num)
