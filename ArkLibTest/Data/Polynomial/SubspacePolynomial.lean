/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/

import ArkLib.Data.Polynomial.SubspacePolynomial
import Mathlib.Algebra.Field.ZMod

/-! # Subspace polynomial acceptance tests -/

open Polynomial

-- The subspace polynomial of `𝔽₂` is monic of degree two.
example : (subspacePolynomial (⊤ : AddSubgroup (ZMod 2))).Monic ∧
    (subspacePolynomial (⊤ : AddSubgroup (ZMod 2))).natDegree = 2 := by
  refine ⟨monic_subspacePolynomial _, ?_⟩
  rw [natDegree_subspacePolynomial]
  simp [Nat.card_eq_fintype_card, ZMod.card]
