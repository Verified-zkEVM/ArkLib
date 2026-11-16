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

Here a quadratic is a polynomial of degree at most 2.

Its message is its value at zero and its coefficient of `X ^ 2`.

The running claim determines the linear coefficient.

Decoding is a bijection onto the quadratics whose Boolean sum is the claim.

## Scope

Decoding enforces the Boolean sum, so acceptance is unconditional.

No division or restriction on the characteristic is needed.

Only degree 2 is compressed: there is no encoder for a general degree bound.
-/

@[expose] public section

namespace Sumcheck

open Polynomial

variable {R : Type} [CommRing R]

/-- Reconstruct the missing linear coefficient from the running claim.

The result has degree at most 2. -/
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

variable (c : R) (m : R × R)

/-- The decoded quadratic takes the first message entry at zero. -/
@[simp] theorem eval_zero_quadratic : (quadratic c m).val.eval 0 = m.1 := by
  simp [quadratic]

/-- The second message entry is the coefficient of `X ^ 2` of the decoded quadratic. -/
@[simp] theorem coeff_two_quadratic : (quadratic c m).val.coeff 2 = m.2 := by
  simp [quadratic]

/-- The decoded quadratic has Boolean sum equal to the running claim. -/
theorem eval_zero_add_eval_one_quadratic :
    (quadratic c m).val.eval 0 + (quadratic c m).val.eval 1 = c := by
  simp [quadratic]
  ring

/-- The message of a polynomial: its value at zero and its coefficient of `X ^ 2`.

On quadratics with Boolean sum equal to the claim it inverts decoding. -/
def quadraticEncode (p : R[X]) : R × R := (p.eval 0, p.coeff 2)

/-- Encoding a decoded message gives the message back. -/
@[simp] theorem quadraticEncode_quadratic : quadraticEncode (quadratic c m).val = m := by
  simp [quadraticEncode]

variable {c} in
/-- A quadratic with Boolean sum `c` is the decoding of its own message under the claim `c`. -/
theorem quadratic_quadraticEncode {p : R[X]} (hp : p.natDegree ≤ 2)
    (hc : p.eval 0 + p.eval 1 = c) : (quadratic c (quadraticEncode p)).val = p := by
  have h1 : p.eval 1 = p.coeff 0 + p.coeff 1 + p.coeff 2 := by
    simp [eval_eq_sum_range' (show p.natDegree < 3 by omega), Finset.sum_range_succ]
  subst hc
  rw [quadraticEncode, h1, ← coeff_zero_eq_eval_zero]
  ext (_ | _ | _ | n)
  · simp [quadratic, coeff_C]
  · simp [quadratic, coeff_C]
    ring
  · simp [quadratic]
  · simp [quadratic, coeff_eq_zero_of_natDegree_lt (show p.natDegree < n + 3 by omega)]

/-- Messages are in bijection with the quadratics whose Boolean sum is the claim. -/
noncomputable def quadraticEquiv :
    R × R ≃ {p : R[X] // p.natDegree ≤ 2 ∧ p.eval 0 + p.eval 1 = c} where
  toFun m := ⟨(quadratic c m).val,
    natDegree_le_iff_degree_le.mpr (mem_degreeLE.mp (quadratic c m).property),
    eval_zero_add_eval_one_quadratic c m⟩
  invFun p := quadraticEncode p.val
  left_inv m := quadraticEncode_quadratic c m
  right_inv p := Subtype.ext (quadratic_quadraticEncode p.property.1 p.property.2)

end Sumcheck
