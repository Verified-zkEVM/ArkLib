/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Logic.Equiv.Defs

/-!
  # Helper Functions and Lemmas

  TODO: split these files into different files based on each namespace
-/

/-- Equivalence between `α` and the sum of `{a // p a}` and `{a // ¬ p a}` -/
@[simps]
def subtypeSumComplEquiv {α : Type*} {p : α → Prop} [DecidablePred p] :
    {a // p a} ⊕ {a // ¬ p a} ≃ α where
  toFun := fun x => match x with
    | Sum.inl a => a.1
    | Sum.inr a => a.1
  invFun := fun x =>
    if h : p x then Sum.inl ⟨x, h⟩ else Sum.inr ⟨x, h⟩
  left_inv := fun x => match x with
    | Sum.inl a => by simp [a.2]
    | Sum.inr a => by simp [a.2]
  right_inv := fun x => by simp; split_ifs <;> simp
