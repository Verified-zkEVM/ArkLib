/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.BinaryNegateSemantics
public import Mathlib.Data.ZMod.Basic

/-!
# Modular negation refines scalar negation

The word machine computes the same additive inverse as `ZMod`. This applies to every positive
modulus and hence, in particular, to prime-field scalars. The theorem uses the actual literal
execution witness; no algebraic operation is added to the machine's runtime instruction set.
-/

@[expose] public section

namespace Computation.BinaryNegateMachine

open BinaryWordMachine (Word value Canonical)

/-- The exact local-bit run implements negation in the residue ring of its input modulus. -/
theorem negate_zmod (q xs : Word) (hx : value xs < value q) :
    ∃ n ≤ 4 * max q.length xs.length + 7, ∃ out : Word,
      Trace n (.start q xs) (.subtract (.normalize (.word out))) ∧
      runFuel n (.start q xs) = .subtract (.normalize (.word out)) ∧
      (value out : ZMod (value q)) = -(value xs : ZMod (value q)) ∧
      value out < value q ∧ Canonical out ∧ out.length ≤ max q.length xs.length := by
  obtain ⟨n, hn, out, ht, hr, hv, hb, hc, hw⟩ := negate_correct q xs hx
  refine ⟨n, hn, out, ht, hr, ?_, hb, hc, hw⟩
  rw [hv, ZMod.natCast_mod, Nat.cast_sub hx.le, ZMod.natCast_self, zero_sub]

end Computation.BinaryNegateMachine
