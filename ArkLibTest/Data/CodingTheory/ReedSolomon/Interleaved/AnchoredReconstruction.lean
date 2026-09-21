/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.AnchoredReconstruction
import Mathlib.Tactic.NormNum

/-!
# Cubic anchored reconstruction clients

These clients reconstruct a concrete message over `ℚ` from a constant quotient and a quadratic
interpolant, check its anchor values and its degree, use coincident anchors and a zero degree
bound, recover the source-shaped degree statement with its hypothesis `0 < k`, reduce modulo
`X ^ 2 - 1` on the trace domain `{1, -1}`, and show that `0 < T` is needed for the remainder
bound.
-/

namespace AnchoredReconstructionTest

open Polynomial ReedSolomon

noncomputable section

-- Anchors `0, 1` and later point `2`, quotient `1`, interpolant `X ^ 2`: the message is
-- `(X - 0) (X - 1) (X - 2) * 1 + X ^ 2`.
example :
    cubicAnchorReconstruct (0 : ℚ) 1 2 1 (X ^ 2) =
      (X - C 0) * (X - C 1) * (X - C 2) * 1 + X ^ 2 :=
  rfl

-- Its values at the anchors are those of `X ^ 2`, and its value at `3` is `6 + 9`.
example : (cubicAnchorReconstruct (0 : ℚ) 1 2 1 (X ^ 2)).eval 2 = 4 := by
  rw [(cubicAnchorReconstruct_eval_anchors (0 : ℚ) 1 2 1 (X ^ 2)).2.2]
  norm_num

example : (cubicAnchorReconstruct (0 : ℚ) 1 2 1 (X ^ 2)).eval 3 = 15 :=
  cubicAnchorReconstruct_eval_of_quotient 0 1 2 3 15 1 (X ^ 2)
    (by simp [cubicAnchorDivisor]; norm_num)

-- The degree is below `1 + 3`.
example : (cubicAnchorReconstruct (0 : ℚ) 1 2 1 (X ^ 2)).degree < (1 + 3 : ℕ) :=
  cubicAnchorReconstruct_degree_lt 0 1 2 (by simp) (by rw [degree_X_pow]; decide)

-- Coincident anchors and degree bound `0`: the quotient is `0` and the message is the interpolant.
example {I : ℚ[X]} (hI : I.degree < 3) :
    (cubicAnchorReconstruct (5 : ℚ) 5 5 0 I).degree < (0 + 3 : ℕ) :=
  cubicAnchorReconstruct_degree_lt 5 5 5 (by simp) hI

-- Source shape: the degree statement over a field with the hypothesis `0 < k`, now unused.
example {F : Type} [Field F] {k : ℕ} (_hk : 0 < k) (s₁ s₂ z : F) (quotient interpolant : F[X])
    (hq : quotient.degree < k) (hI : interpolant.degree < 3) :
    (cubicAnchorReconstruct s₁ s₂ z quotient interpolant).degree < (k + 3 : ℕ) :=
  cubicAnchorReconstruct_degree_lt s₁ s₂ z hq hI

-- The cubic divisor is the nodal polynomial of its three anchors.
example (s₁ s₂ z : ℚ) :
    cubicAnchorDivisor s₁ s₂ z = Lagrange.nodal Finset.univ ![s₁, s₂, z] :=
  cubicAnchorDivisor_eq_nodal s₁ s₂ z

-- Reducing `X ^ 3` modulo `X ^ 2 - 1` keeps its values on `{1, -1}`.
example : ((X ^ 3 : ℚ[X]) %ₘ (X ^ 2 - C 1)).eval (-1) = -1 := by
  rw [traceRemainder_eval_eq 2 1 (X ^ 3) (by norm_num)]
  norm_num

example : ((X ^ 3 : ℚ[X]) %ₘ (X ^ 2 - C 1)).degree < (2 : ℕ) :=
  traceRemainder_degree_lt 2 (by decide) 1 _

-- The hypothesis `0 < T` is needed: modulo `X ^ 0 - 1 = 0` nothing is reduced.
example : ¬ ((1 : ℚ[X]) %ₘ (X ^ 0 - C 1)).degree < (0 : ℕ) := by
  simp

end

end AnchoredReconstructionTest
