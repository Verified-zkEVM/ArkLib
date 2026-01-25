/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import VCVio.OracleComp.OracleComp

/-!
# StateT Helper Lemmas

This file contains simple helper lemmas for `StateT` operations that simplify
reasoning about `run`, `run'`, and monadic operations in the probability monad.

These lemmas are used throughout the execution semantics to unfold stateful
computations into their underlying probability distributions.
-/

universe u v w

namespace StateT

variable {m : Type u → Type v} {σ α β : Type u}

/-- Unfolding lemma for `run'` on `pure`. -/
@[simp]
theorem run'_pure_lib [Monad m] [LawfulMonad m] (x : α) (s : σ) :
    (pure x : StateT σ m α).run' s = (pure x : m α) := by
  simp only [run', pure, StateT.pure, map_pure]

/-- Unfolding lemma for `run'` on `bind`. -/
@[simp]
theorem run'_bind_lib [Monad m] [LawfulMonad m] (ma : StateT σ m α) (f : α → StateT σ m β) (s : σ) :
    (ma >>= f).run' s = ((ma.run s) >>= fun (a, s') => (f a).run' s') := by
  simp only [run', bind, StateT.bind, map_bind, run]

/-- Unfolding lemma for `run` on `liftM`. -/
@[simp]
theorem run_liftM_lib [Monad m] [LawfulMonad m] (ma : m α) (s : σ) :
    (liftM ma : StateT σ m α).run s = (ma >>= fun a => pure (a, s)) := by
  simp only [run, liftM, bind_pure_comp]
  rw [map_eq_pure_bind]; rfl

end StateT
