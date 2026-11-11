/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Message.Basic
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.Tactic.Ring

/-!
# Compressed quadratic messages on the Boolean domain

The constant and quadratic coefficients determine the linear coefficient using the running
claim. Decoding enforces the Boolean sum, so acceptance is unconditional. No division or
restriction on the characteristic is needed.
-/

@[expose] public section

namespace Sumcheck

open Polynomial

variable {R : Type} [CommRing R]

/-- Reconstruct the missing linear coefficient from the running claim. -/
noncomputable def quadratic (c : R) (m : R × R) : R⦃≤ 2⦄[X] :=
  ⟨Polynomial.C m.1 + Polynomial.C (c - 2 * m.1 - m.2) * Polynomial.X +
    Polynomial.C m.2 * Polynomial.X ^ 2, by
      apply Polynomial.mem_degreeLE.mpr
      apply Polynomial.natDegree_le_iff_degree_le.mp
      compute_degree⟩

/-- Evaluate the compressed message directly in the ring; decoding enforces acceptance. -/
def quadraticOps : MessageOps R (R × R) where
  evaluate c m r := m.1 + (c - 2 * m.1 - m.2) * r + m.2 * r ^ 2
  accept _ _ := true

/-- The decoded quadratic has Boolean sum equal to the running claim. -/
noncomputable def quadraticModel [DecidableEq R] [Nontrivial R] :
    MessageModel ({0, 1} : Finset R) (quadraticOps (R := R)) 2 where
  interpret := quadratic
  evaluate_eq _ _ _ := by simp [quadraticOps, quadratic]
  accept_iff c m := by simp [quadraticOps, quadratic]; ring

end Sumcheck
