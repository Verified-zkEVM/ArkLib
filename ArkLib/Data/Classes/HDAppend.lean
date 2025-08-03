/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

/-!
# Heterogeneous Dependent Append
-/

universe u v w

/-- The notation typeclass for heterogeneous dependent append. This enables the notation
`a ++ᵈ b : γ` where `a : α` and `b : β`. -/
class HDAppend (α : Sort u) (β : Sort v) (γ : outParam (Sort w)) where
  /-- `a ++ᵈ b` is the result of concatenating `a` and `b`, usually read "dependent append".
  The meaning of this notation is type-dependent. -/
  hDAppend : α → β → γ

@[inherit_doc HDAppend.hDAppend] infixl:65 " ++ᵈ " => HDAppend.hDAppend
macro_rules | `($x ++ᵈ $y)  => `(binop% HDAppend.hDAppend $x $y)
