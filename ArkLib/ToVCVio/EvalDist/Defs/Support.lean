/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VCVio.EvalDist.Monad.Basic

/-!
# Additions to VCV-io's `EvalDist.Defs.Support`
-/

lemma support_bind_exists {m : Type → Type} [Monad m] [LawfulMonad m]
    [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
    {α β : Type} (x : m α) (f : α → m β) {y : β}
    (hy : y ∈ support (x >>= f)) : ∃ a, a ∈ support x ∧ y ∈ support (f a) := by
  simpa [mem_support_bind_iff] using hy

lemma eq_of_mem_support_pure {m : Type → Type} [Monad m] [LawfulMonad m]
    [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
    {α : Type} {x y : α} (h : y ∈ support (pure x : m α)) : y = x := by
  simpa [mem_support_pure_iff] using h
