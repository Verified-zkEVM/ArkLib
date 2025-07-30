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

namespace DFunEquiv

variable {F : Sort*} {α : Sort*} {β : α → Sort*} [inst : DFunEquiv F α β]

/-- Default instance: `∀ a : α, β a` itself satisfies `DFunEquiv`. -/
instance : DFunEquiv (∀ a : α, β a) α β where
  equiv := Equiv.refl _

/-- The forward direction of the equivalence is a `DFunLike`. -/
instance : DFunLike F α β where
  coe := DFunEquiv.equiv.toFun
  coe_injective' := DFunEquiv.equiv.injective

/-- Coercion from the dependent function type `∀ a : α, β a` to another type `F` that has a
`DFunEquiv` instance.

TODO: is `Coe` the right thing to use here? What about other variants of coercion? -/
instance : Coe (∀ a : α, β a) F where
  coe := DFunEquiv.equiv.invFun

@[simp]
lemma toFun_invFun (f : ∀ a, β a) : inst.equiv.toFun (equiv.invFun f : F) = f :=
  inst.equiv.right_inv _

@[simp]
lemma invFun_toFun (f : F) : inst.equiv.invFun (inst.equiv.toFun f) = f :=
  inst.equiv.left_inv _

@[simp]
lemma coe_toFun_of_coe_apply (f : ∀ a, β a) (a : α) : (f : F) a = f a := by
  simp [instDFunLike]

@[simp]
lemma coe_fn_of_coe (f : ∀ a, β a) : (f : F) = inst.equiv.invFun f := rfl

@[simp]
lemma coe_of_coe_fn (f : F) : (f : ∀ a, β a) = inst.equiv.toFun f := rfl

end DFunEquiv
