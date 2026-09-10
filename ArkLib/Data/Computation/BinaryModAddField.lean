/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.BinaryModAddSemantics
public import Mathlib.Data.ZMod.Basic

/-!
# Modular addition refines scalar addition

The literal seven-tape run computes addition in the input modulus's residue ring, including
prime-field scalar addition. The modulus word is retained exactly by that same execution.
-/

@[expose] public section

namespace Computation.BinaryModAddMachine

open BinaryWordMachine (Word value Canonical)

/-- The actual local-bit execution computes scalar addition and retains its original modulus. -/
theorem add_zmod (q xs ys : Word) (hx : value xs < value q) (hy : value ys < value q) :
    ∃ n ≤ 10 * max q.length (max xs.length ys.length) + 25, ∃ out : Word,
      Trace n (.start q xs ys) (.done q out) ∧ runFuel n (.start q xs ys) = .done q out ∧
      (value out : ZMod (value q)) =
        (value xs : ZMod (value q)) + (value ys : ZMod (value q)) ∧
      value out < value q ∧ Canonical out ∧
      out.length ≤ max q.length (max xs.length ys.length) + 1 := by
  obtain ⟨n, hn, out, ht, hr, hv, hb, hc, hw⟩ := add_correct q xs ys hx hy
  refine ⟨n, hn, out, ht, hr, ?_, hb, hc, hw⟩
  rw [hv, ZMod.natCast_mod, Nat.cast_add]

end Computation.BinaryModAddMachine
