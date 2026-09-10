/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.Div

/-!
# Reconstructing a message from a cubic anchored quotient

Two early evaluations and one later evaluation determine an interpolation polynomial of
degree below three. Multiplying the extracted quotient by the three linear factors and adding
that interpolant restores all three values. A quotient of degree below `k` produces a message
of degree below `k + 3`. This is the degree shift needed by the anchored LambdaVM list bound.

The lemmas apply to each column separately. They do not assume that the three points are distinct:
distinctness is needed to construct the interpolant, while reconstruction only uses its degree
and values. The agreement lemma connects a received quotient equation to the recovered message
at any evaluation position without dividing by a possibly zero field element.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial

variable {F : Type*} [Field F]

/-- The monic divisor for two early anchors and a later evaluation. -/
def cubicAnchorDivisor (s₁ s₂ z : F) : F[X] :=
  (X - C s₁) * (X - C s₂) * (X - C z)

/-- Undo the cubic quotient using its interpolation polynomial. -/
def cubicAnchorReconstruct (s₁ s₂ z : F) (quotient interpolant : F[X]) : F[X] :=
  cubicAnchorDivisor s₁ s₂ z * quotient + interpolant

/-- Cubic reconstruction increases the strict degree bound by three. -/
theorem cubicAnchorReconstruct_degree_lt {k : ℕ} (hk : 0 < k)
    (s₁ s₂ z : F) (quotient interpolant : F[X])
    (hq : quotient.degree < k) (hI : interpolant.degree < 3) :
    (cubicAnchorReconstruct s₁ s₂ z quotient interpolant).degree < (k + 3 : ℕ) := by
  have hqn : quotient.natDegree < k := by
    by_cases hzero : quotient = 0
    · simp [hzero, hk]
    · exact (natDegree_lt_iff_degree_lt hzero).mpr hq
  have hIn : interpolant.natDegree < 3 := by
    by_cases hzero : interpolant = 0
    · simp [hzero]
    · exact (natDegree_lt_iff_degree_lt hzero).mpr hI
  have hdiv : (cubicAnchorDivisor s₁ s₂ z).natDegree ≤ 3 := by
    exact natDegree_mul_le_of_le
      (natDegree_mul_le_of_le (natDegree_X_sub_C_le s₁) (natDegree_X_sub_C_le s₂))
      (natDegree_X_sub_C_le z)
  have hprod := (natDegree_mul_le (p := cubicAnchorDivisor s₁ s₂ z)
    (q := quotient))
  have hsum := natDegree_add_le (cubicAnchorDivisor s₁ s₂ z * quotient) interpolant
  have hnat : (cubicAnchorReconstruct s₁ s₂ z quotient interpolant).natDegree < k + 3 := by
    unfold cubicAnchorReconstruct
    exact hsum.trans_lt (max_lt (by omega) (by omega))
  exact degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr hnat)

/-- The reconstructed polynomial retains the interpolant's values at all three anchors. -/
theorem cubicAnchorReconstruct_eval_anchors (s₁ s₂ z : F) (quotient interpolant : F[X]) :
    (cubicAnchorReconstruct s₁ s₂ z quotient interpolant).eval s₁ = interpolant.eval s₁ ∧
    (cubicAnchorReconstruct s₁ s₂ z quotient interpolant).eval s₂ = interpolant.eval s₂ ∧
    (cubicAnchorReconstruct s₁ s₂ z quotient interpolant).eval z = interpolant.eval z := by
  simp [cubicAnchorReconstruct, cubicAnchorDivisor]

/-- A quotient equation at a domain point restores agreement with the received message. -/
theorem cubicAnchorReconstruct_eval_of_quotient (s₁ s₂ z x received : F)
    (quotient interpolant : F[X])
    (h : (cubicAnchorDivisor s₁ s₂ z).eval x * quotient.eval x =
      received - interpolant.eval x) :
    (cubicAnchorReconstruct s₁ s₂ z quotient interpolant).eval x = received := by
  simp [cubicAnchorReconstruct, h]

/-- Reducing a reconstructed message modulo the trace zerofier gives degree below `T`. -/
theorem traceRemainder_degree_lt (T : ℕ) (hT : 0 < T) (message : F[X]) :
    (message %ₘ (X ^ T - C (1 : F))).degree < T := by
  simpa only [degree_X_pow_sub_C hT] using
    degree_modByMonic_lt message (monic_X_pow_sub_C (1 : F) (by omega : T ≠ 0))

/-- Reduction modulo the trace zerofier preserves every trace-domain value. Thus any lookup
contribution depending on these values is unchanged. -/
theorem traceRemainder_eval_eq (T : ℕ) (message : F[X]) (x : F) (hx : x ^ T = 1) :
    (message %ₘ (X ^ T - C (1 : F))).eval x = message.eval x := by
  have hroot : (X ^ T - C (1 : F)).eval₂ (RingHom.id F) x = 0 := by simp [hx]
  simpa using eval₂_modByMonic_eq_self_of_root (p := message) hroot

end ReedSolomon
