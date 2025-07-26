/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Logic.Equiv.Defs

/-!
# FunEquiv

This file defines the `(D)FunEquiv` type class, which expresses that a given type `F` has an
equivalence to a dependent function type.

This is stronger than `(D)FunLike` since we get an equivalence and not just an injection into the
dependent function type.
-/

/-- Type class to express that a given type `F` has an equivalence to a dependent function type.

This is stronger than `DFunLike` since we get an equivalence and not just an injection into the
dependent function type. -/
class DFunEquiv (F : Sort*) (α : outParam (Sort*)) (β : outParam <| α → Sort*) where
  equiv : F ≃ ∀ a : α, β a

/-- Type class to express that a given type `F` has an equivalence to a function type.

This is stronger than `FunLike` since we get an equivalence and not just an injection into the
function type. -/
abbrev FunEquiv F α β := DFunEquiv F α fun _ => β

instance {F : Sort*} {α : Sort*} {β : α → Sort*} [DFunEquiv F α β] : DFunLike F α β where
  coe := DFunEquiv.equiv.toFun
  coe_injective' := DFunEquiv.equiv.injective

/-- Coercion from the dependent function type `∀ a : α, β a` to another type `F` that has a
`DFunEquiv` instance.

TODO: is `Coe` the right thing to use here? What about other variants of coercion? -/
instance {F : Sort*} {α : Sort*} {β : α → Sort*} [DFunEquiv F α β] : Coe (∀ a : α, β a) F where
  coe := DFunEquiv.equiv.invFun

-- @[simp]
-- lemma coe_equiv {F : Sort*} {α : Sort*} {β : α → Sort*} [DFunEquiv F α β] (f : F) (a : α) :
--   DFunEquiv.equiv.toFun f a = f a := rfl
