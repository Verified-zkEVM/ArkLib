/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.BinaryMulSemantics
public import Mathlib.Data.ZMod.Basic

/-!
# Literal multiplication refines scalar multiplication

The repeated-addition trace implements multiplication in the input modulus's residue ring,
including prime-field multiplication. Its countdown input is canonical; the multiplicand and
modulus may carry padding, which is included in the physical-width bound and retained exactly.
-/

@[expose] public section

namespace Computation.BinaryMulMachine

open BinaryWordMachine (Word value Canonical)

/-- The same eleven-tape execution computes the residue-ring product. -/
theorem multiply_zmod (q xs ys : Word) (hc : Canonical xs)
    (hx : value xs < value q) (hy : value ys < value q) :
    ∃ n ≤ value q * (24 * max q.length ys.length + 48) + 2, ∃ out : Word,
      Trace n (.start q xs ys) (.done q ys out) ∧
      runFuel n (.start q xs ys) = .done q ys out ∧
      (value out : ZMod (value q)) =
        (value xs : ZMod (value q)) * (value ys : ZMod (value q)) ∧
      value out < value q ∧ Canonical out ∧ out.length ≤ q.length := by
  obtain ⟨n, hn, out, ht, hr, hv, hb, hco, hw⟩ := multiply_correct q xs ys hc hx hy
  refine ⟨n, hn, out, ht, hr, ?_, hb, hco, hw⟩
  rw [hv, ZMod.natCast_mod, Nat.cast_mul]

end Computation.BinaryMulMachine
