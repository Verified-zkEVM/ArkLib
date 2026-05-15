/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ToMathlib.Control.StateT

/-!
# Additions to VCV-io's `ToMathlib.Control.StateT`
-/

/-- `StateT.run'` commutes with `Functor.map`. -/
lemma StateT.run'_map_comm {m : Type → Type} {σ α β : Type}
    [Monad m] [LawfulMonad m]
    (f : α → β) (mx : StateT σ m α) (s : σ) :
    (f <$> mx).run' s = f <$> mx.run' s := by
  change (fun x : β × σ => x.1) <$> (StateT.map f mx) s =
    f <$> ((fun x : α × σ => x.1) <$> mx s)
  simp [StateT.map, Functor.map_map]
