/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

import ArkLib.ToMathlib.FieldTheory.Finite.Packing
import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.Complex.Basic

/-! # Acceptance cases for packing polynomial tuples -/

open Polynomial

-- Along the basis `1, i` of `ℂ` over `ℝ`, the pair `(X, 1)` packs to `X + i`.
-- At `x = 2` the packed polynomial is `2 + i`, packed from the values `(2, 1)`.
example : (pack Complex.basisOneI ![(X : ℝ[X]), 1]).eval (algebraMap ℝ ℂ 2) = 2 + Complex.I := by
  rw [eval_pack]
  simp [Fin.sum_univ_two]

-- Packing reflects degrees: `(X², X)` packs to a polynomial of degree at most `2`, not `1`.
example : (pack Complex.basisOneI ![(X : ℝ[X]) ^ 2, X]).degree ≤ 2 ∧
    ¬ (pack Complex.basisOneI ![(X : ℝ[X]) ^ 2, X]).degree ≤ 1 := by
  rw [degree_pack_le_iff Complex.basisOneI.linearIndependent,
    degree_pack_le_iff Complex.basisOneI.linearIndependent]
  refine ⟨fun r ↦ ?_, fun h ↦ ?_⟩
  · fin_cases r <;> simp
  · have := h 0
    simp at this

-- Packing a tuple into one polynomial loses no information.
example (P Q : Fin 2 → ℝ[X]) (h : pack Complex.basisOneI P = pack Complex.basisOneI Q) :
    P = Q :=
  pack_injective Complex.basisOneI.linearIndependent h

-- A polynomial with a non-real coefficient unpacks into two real polynomials.
example : ∃ P : Fin 2 → ℝ[X], pack Complex.basisOneI P = X + C Complex.I :=
  exists_pack_eq Complex.basisOneI _

-- The prime field `𝔽₂` has an extension with a basis of size `3`.
example : ∃ (E : Type) (_ : Field E) (_ : Finite E) (_ : Algebra (ZMod 2) E),
    Nonempty (Module.Basis (Fin 3) (ZMod 2) E) :=
  FiniteField.exists_basis_fin (ZMod 2) (by norm_num)

/-- info: 'Polynomial.pack_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Polynomial.pack_injective

/-- info: 'Polynomial.exists_pack_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Polynomial.exists_pack_eq

/-- info: 'FiniteField.exists_basis_fin' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FiniteField.exists_basis_fin
