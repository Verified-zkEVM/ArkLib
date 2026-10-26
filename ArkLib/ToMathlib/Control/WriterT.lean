/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import Mathlib.Control.Monad.Writer

/-!
# Lawful lifting into an append-based writer

Lifting a base computation writes the empty log. The lift therefore needs only that appending
empty to empty remains empty; full associativity or identity laws for other logs are unnecessary.
This named law can be installed locally without changing global writer instance priorities.
-/

@[expose] public section

universe u v

namespace WriterT

/-- The append-based writer lift preserves pure and bind when two empty logs append to empty. -/
theorem lawfulMonadLiftAppend {m : Type u → Type v} [Monad m] [LawfulMonad m]
    {ω : Type u} [EmptyCollection ω] [Append ω] (hempty : (∅ : ω) ++ ∅ = ∅) :
    LawfulMonadLift m (WriterT ω m) where
  monadLift_pure x := map_pure (·, ∅) x
  monadLift_bind x f := by
    ext
    simp [MonadLift.monadLift, hempty]

end WriterT
