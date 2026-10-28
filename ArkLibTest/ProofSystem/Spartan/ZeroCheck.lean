/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ProofSystem.Spartan.ZeroCheck
import Mathlib.Algebra.Field.ZMod

/-! # Zero-check examples over a small prime field -/

namespace Spartan.ZeroCheckTest

open MvPolynomial OracleComp
open scoped ENNReal

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

noncomputable local instance : SampleableType (ZMod 5) := SampleableType.ofFintype _

/-- A false identity can pass at the zero challenge. -/
example : _root_.ZeroCheck.badEvent (X (0 : Fin 1) : MvPolynomial (Fin 1) (ZMod 5))
    (fun _ => (0 : ZMod 5)) := by
  simp [_root_.ZeroCheck.badEvent]

/-- The same false identity fails at a nonzero challenge. -/
example : ¬ _root_.ZeroCheck.badEvent (X (0 : Fin 1) : MvPolynomial (Fin 1) (ZMod 5))
    (fun _ => (1 : ZMod 5)) := by
  simp [_root_.ZeroCheck.badEvent]

/-- The zero-check error for this nonzero linear polynomial is at most one fifth. -/
example :
    Pr{let τ ← $ᵗ (Fin 1 → ZMod 5)}[
      _root_.ZeroCheck.badEvent (X (0 : Fin 1) : MvPolynomial (Fin 1) (ZMod 5)) τ] ≤
      (1 : ℝ≥0∞) / 5 := by
  simpa only [ZMod.card, Nat.cast_one, Nat.cast_ofNat] using
    _root_.ZeroCheck.badEvent_bound (X (0 : Fin 1) : MvPolynomial (Fin 1) (ZMod 5))
      (fun i => degreeOf_X_le (R := ZMod 5) i (0 : Fin 1))

/-- With no variables, a false constant identity never passes. -/
example :
    Pr{let τ ← $ᵗ (Fin 0 → ZMod 5)}[
      _root_.ZeroCheck.badEvent (C 1 : MvPolynomial (Fin 0) (ZMod 5)) τ] = 0 := by
  apply le_antisymm _ zero_le
  simpa using _root_.ZeroCheck.badEvent_bound (C 1 : MvPolynomial (Fin 0) (ZMod 5))
    (fun i => Fin.elim0 i)

/-- The specialized first challenge preserves satisfaction over the small prime field. -/
example (pp : PublicParams) (x : R1CS.Statement (ZMod 5) pp.toSizeR1CS)
    (oracles : ∀ i, Realization.OracleStatement (R := ZMod 5) pp i)
    (h : Spartan.ZeroCheck.inputRelation pp x oracles) (τ : Fin pp.ℓ_m → ZMod 5) :
    Spartan.ZeroCheck.outputRelation pp (τ, x) oracles := by
  change eval τ (Spartan.ZeroCheck.polynomial pp x oracles) = 0
  rw [(Spartan.ZeroCheck.polynomial_zero_iff pp x oracles).2 h, map_zero]

end Spartan.ZeroCheckTest
