/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.BinaryRetainedNegateSemantics
public import Mathlib.Data.ZMod.Basic

/-!
# Scalar negation retaining the modulus

The same six-tape execution refines residue-ring negation and retains its exact input modulus.
The arithmetic modulus copy is supplied by the literal copy/restore preparation, not by the caller.
-/

@[expose] public section

namespace Computation.BinaryRetainedNegateMachine

open BinaryWordMachine (Word value Canonical)

/-- The actual retained-modulus trace computes scalar negation, including padded zero. -/
theorem negate_zmod (q x : Word) (hx : value x < value q) :
    ∃ n ≤ 6 * max q.length x.length + 11, ∃ out : Word,
      Trace n (.start q x) (.done q out) ∧ runFuel n (.start q x) = .done q out ∧
      (value out : ZMod (value q)) = -(value x : ZMod (value q)) ∧
      value out < value q ∧ Canonical out ∧ out.length ≤ q.length := by
  obtain ⟨n, hn, out, ht, hr, hv, hb, hc, hw⟩ := negate_correct q x hx
  refine ⟨n, hn, out, ht, hr, ?_, hb, hc, hw⟩
  rw [hv, ZMod.natCast_mod, Nat.cast_sub hx.le, ZMod.natCast_self, zero_sub]

end Computation.BinaryRetainedNegateMachine
