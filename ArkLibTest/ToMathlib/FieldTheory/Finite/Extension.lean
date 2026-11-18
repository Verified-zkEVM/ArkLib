/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

import ArkLib.ToMathlib.FieldTheory.Finite.Extension
import Mathlib.Algebra.Field.ZMod

/-! # Acceptance cases for finite extensions with a basis of any size -/

-- The prime field `𝔽₂` has an extension with a basis of size `3`.
example : ∃ (E : Type) (_ : Field E) (_ : Finite E) (_ : Algebra (ZMod 2) E),
    Nonempty (Module.Basis (Fin 3) (ZMod 2) E) :=
  FiniteField.exists_basis_fin (ZMod 2) (by norm_num)

/-- info: 'FiniteField.exists_basis_fin' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FiniteField.exists_basis_fin
