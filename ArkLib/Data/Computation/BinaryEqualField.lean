/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.BinaryEqualSemantics
public import Mathlib.Data.ZMod.Basic

/-!
# Actual equality guards for reduced scalars

Reduced words have equal natural values exactly when their residue-ring scalars are equal. This
links the Boolean produced by the same five-tape run to scalar equality without normalization.
-/

@[expose] public section

namespace Computation.BinaryEqualMachine

open BinaryWordMachine (Word value)

/-- Reduced scalar equality is precisely equality of the words' decoded natural values. -/
theorem reduced_equal_iff (q xs ys : Word) (hx : value xs < value q) (hy : value ys < value q) :
    value xs = value ys ↔ (value xs : ZMod (value q)) = (value ys : ZMod (value q)) := by
  constructor
  · intro h
    exact congrArg (fun n : ℕ ↦ (n : ZMod (value q))) h
  · intro h
    have hv := congrArg ZMod.val h
    simpa only [ZMod.val_natCast_of_lt hx, ZMod.val_natCast_of_lt hy] using hv

/-- The actual width-bounded Boolean guard decides scalar equality and retains its modulus. -/
theorem equality_zmod (q xs ys : Word) (hx : value xs < value q) (hy : value ys < value q) :
    Trace (max xs.length ys.length + 3) (.compare q (.startCompare xs ys))
      (.done q (decide ((value xs : ZMod (value q)) = (value ys : ZMod (value q))))) ∧
    runFuel (max xs.length ys.length + 3) (.compare q (.startCompare xs ys)) =
      .done q (decide ((value xs : ZMod (value q)) = (value ys : ZMod (value q)))) := by
  have he := reduced_equal_iff q xs ys hx hy
  have hb : decide (value xs = value ys) =
      decide ((value xs : ZMod (value q)) = (value ys : ZMod (value q))) := by
    by_cases h : value xs = value ys
    · simp [h]
    · have hn := mt he.mpr h
      simp [h, hn]
  simpa only [hb] using equality_correct q xs ys

end Computation.BinaryEqualMachine
