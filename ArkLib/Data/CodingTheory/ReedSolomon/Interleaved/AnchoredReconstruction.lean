/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.DivisorReconstruction

/-!
# Reconstructing a message from a cubic anchored quotient

An anchored Reed–Solomon check fixes the values of a message polynomial at two early anchors
`s₁, s₂` and one later evaluation point `z`, and works with the quotient of the message minus an
interpolant of those three values by the cubic divisor `(X - s₁) (X - s₂) (X - z)`. This file
reverses that step, one column at a time. Multiplying a quotient of degree below `k` by the cubic
divisor and adding an interpolant of degree below `3` gives a message of degree below `k + 3`
that takes the interpolant's values at the three anchors, and that agrees with a received value
wherever the quotient equation holds. The three points need not be distinct: distinctness is used
only to construct the interpolant, while reconstruction uses only its degree and values.

The file also records the two facts about reduction modulo `X ^ T - c` that the anchored list
bound uses for a trace domain `{x | x ^ T = c}`: the remainder has degree below `T`, and it has the
same values as the message on the trace domain.

## Main definitions

* `ReedSolomon.cubicAnchorDivisor`, `ReedSolomon.cubicAnchorReconstruct`.

## Main statements

* `ReedSolomon.cubicAnchorDivisor_eq_nodal`: the cubic divisor is `Lagrange.nodal` of the three
  anchors, so the general statements of `ArkLib.Data.Polynomial.DivisorReconstruction` apply.
* `ReedSolomon.cubicAnchorReconstruct_degree_lt`, `ReedSolomon.cubicAnchorReconstruct_eval_anchors`,
  `ReedSolomon.cubicAnchorReconstruct_eval_of_quotient`.
* `ReedSolomon.traceRemainder_degree_lt`, `ReedSolomon.traceRemainder_eval_eq`.
-/

@[expose] public section

namespace ReedSolomon

open Polynomial

variable {F : Type*} [CommRing F]

/-- The monic cubic divisor `(X - s₁) (X - s₂) (X - z)` for two early anchors `s₁, s₂` and a
later evaluation point `z`. The three points may coincide. -/
noncomputable def cubicAnchorDivisor (s₁ s₂ z : F) : F[X] :=
  (X - C s₁) * (X - C s₂) * (X - C z)

/-- The cubic divisor is the nodal polynomial of the anchor tuple `![s₁, s₂, z]`. -/
theorem cubicAnchorDivisor_eq_nodal (s₁ s₂ z : F) :
    cubicAnchorDivisor s₁ s₂ z = Lagrange.nodal Finset.univ ![s₁, s₂, z] := by
  simp [cubicAnchorDivisor, Lagrange.nodal, Fin.prod_univ_three]

/-- Undo the cubic quotient: `cubicAnchorDivisor s₁ s₂ z * quotient + interpolant`. -/
noncomputable def cubicAnchorReconstruct (s₁ s₂ z : F) (quotient interpolant : F[X]) : F[X] :=
  cubicAnchorDivisor s₁ s₂ z * quotient + interpolant

/-- **Cubic reconstruction raises the strict degree bound by three.** A quotient of degree below
`k` and an interpolant of degree below `3` give a message of degree below `k + 3`. For `k = 0` the
quotient is `0` and the message is the interpolant. -/
theorem cubicAnchorReconstruct_degree_lt [Nontrivial F] {k : ℕ} (s₁ s₂ z : F)
    {quotient interpolant : F[X]} (hq : quotient.degree < k) (hI : interpolant.degree < 3) :
    (cubicAnchorReconstruct s₁ s₂ z quotient interpolant).degree < (k + 3 : ℕ) := by
  have h := degree_nodal_mul_add_lt Finset.univ ![s₁, s₂, z] hq
    (I := interpolant) (by simpa using hI)
  simpa [cubicAnchorReconstruct, cubicAnchorDivisor_eq_nodal] using h

/-- **The reconstruction keeps the interpolant's anchor values.** At each of `s₁`, `s₂` and `z`,
the reconstructed message takes the value of the interpolant, whatever the quotient. -/
theorem cubicAnchorReconstruct_eval_anchors (s₁ s₂ z : F) (quotient interpolant : F[X]) :
    (cubicAnchorReconstruct s₁ s₂ z quotient interpolant).eval s₁ = interpolant.eval s₁ ∧
    (cubicAnchorReconstruct s₁ s₂ z quotient interpolant).eval s₂ = interpolant.eval s₂ ∧
    (cubicAnchorReconstruct s₁ s₂ z quotient interpolant).eval z = interpolant.eval z := by
  refine ⟨?_, ?_, ?_⟩ <;>
    exact eval_mul_add_of_eval_eq_zero (by simp [cubicAnchorDivisor])

/-- **The quotient equation restores agreement.** If at a domain point `x` the received value
`received` satisfies `divisor(x) * quotient(x) = received - interpolant(x)`, the reconstructed
message takes the value `received` at `x`. No division by `divisor(x)` is used, so `x` may be an
anchor. -/
theorem cubicAnchorReconstruct_eval_of_quotient (s₁ s₂ z x received : F)
    (quotient interpolant : F[X])
    (h : (cubicAnchorDivisor s₁ s₂ z).eval x * quotient.eval x =
      received - interpolant.eval x) :
    (cubicAnchorReconstruct s₁ s₂ z quotient interpolant).eval x = received :=
  eval_mul_add_of_eval_mul_eq_sub h

/-- **The trace remainder has degree below `T`.** Reducing a message modulo the monic divisor
`X ^ T - c` gives degree below `T`. The hypothesis `0 < T` is needed: for `T = 0` and `c = 1` the
divisor is `0`, reduction does nothing, and a nonzero constant message has degree `0`. -/
theorem traceRemainder_degree_lt [Nontrivial F] (T : ℕ) (hT : 0 < T) (c : F) (message : F[X]) :
    (message %ₘ (X ^ T - C c)).degree < T := by
  simpa only [degree_X_pow_sub_C hT] using
    degree_modByMonic_lt message (monic_X_pow_sub_C c hT.ne')

/-- **Reduction preserves trace-domain values.** At every `x` with `x ^ T = c`, the remainder of
the message modulo `X ^ T - c` has the same value as the message. Any quantity computed from the
values on the trace domain, such as a lookup contribution, is therefore unchanged. -/
theorem traceRemainder_eval_eq (T : ℕ) (c : F) (message : F[X]) {x : F} (hx : x ^ T = c) :
    (message %ₘ (X ^ T - C c)).eval x = message.eval x := by
  have hroot : (X ^ T - C c).eval₂ (RingHom.id F) x = 0 := by simp [hx]
  simpa using eval₂_modByMonic_eq_self_of_root (p := message) hroot

end ReedSolomon
