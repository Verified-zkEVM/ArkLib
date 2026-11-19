/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

import ArkLib.ToMathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Acceptance cases for extensions of finite fields inside an algebraic closure -/

open FiniteField

-- A quadratic extension of `𝔽₂` embeds into the algebraic closure of `𝔽₂`.
example : ∃ (L : Type) (_ : Field L) (_ : Algebra (ZMod 2) L) (_ : Finite L),
    Module.finrank (ZMod 2) L = 2 ∧ Nonempty (L →ₐ[ZMod 2] AlgebraicClosure (ZMod 2)) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exists_algHom_of_finrank_eq _ _ two_ne_zero

-- A quadratic extension of `𝔽₃` embeds into the algebraic closure of a field over `𝔽₃`.
-- Here the closure is that of `𝔽₉`, an algebra over `𝔽₃` through `𝔽₉`.
example : ∃ (L : Type) (_ : Field L) (_ : Algebra (ZMod 3) L) (_ : Finite L),
    Module.finrank (ZMod 3) L = 2 ∧
      Nonempty (L →ₐ[ZMod 3] AlgebraicClosure (GaloisField 3 2)) :=
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exists_algHom_of_finrank_eq _ _ two_ne_zero

-- The degree `k = 0` is excluded: no finite field has degree `0` over `𝔽₂`.
example (L : Type) [Field L] [Algebra (ZMod 2) L] [Module.Finite (ZMod 2) L] :
    Module.finrank (ZMod 2) L ≠ 0 :=
  Module.finrank_pos.ne'

/-- info: 'FiniteField.exists_algHom_of_finrank_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FiniteField.exists_algHom_of_finrank_eq
