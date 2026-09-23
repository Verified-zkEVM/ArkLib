/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.AgreementBounds
import ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.AnchoredAgreement
import ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.AnchoredReconstruction
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum

/-!
# Interleaved Reed–Solomon acceptance tests

Concrete instances exercise agreement bounds, anchored evaluation, cubic reconstruction, trace
remainders, scalar-to-interleaved power agreement, and the height-three tensor-fold count.
-/

open Polynomial Code ReedSolomon ReedSolomon.AnchoredAgreement
open scoped ProbabilityTheory

namespace InterleavedAcceptance

example : tupleRatFunc ![(1 : ZMod 2), 0] ≠ tupleRatFunc ![0, 1] := by
  intro h
  have := congrFun (tupleRatFunc_injective h) 0
  simp at this

/-- The single evaluation point `0` of `ZMod 2`. -/
private def point : Fin 1 ↪ ZMod 2 :=
  ⟨fun _ ↦ 0, fun a b _ ↦ Subsingleton.elim a b⟩

-- Packing into `F(Z)` bounds the list size of a concrete two-fold interleaving.
example :
    Lambda (interleavedCodeSet (κ := Fin 2) (code point 1 : Set (Fin 1 → ZMod 2))) 1 ≤
      Lambda (code (point.trans ⟨algebraMap (ZMod 2) (RatFunc (ZMod 2)),
        (algebraMap (ZMod 2) (RatFunc (ZMod 2))).injective⟩) 1 :
          Set (Fin 1 → RatFunc (ZMod 2))) 1 :=
  Lambda_interleaved_le_ratFunc point 1 2 1

private def domain3 : Fin 3 ↪ ℚ :=
  ⟨fun i ↦ (i : ℚ), fun a b h ↦ Fin.ext (by simpa using h)⟩

example : Set.InjOn (evalTuple (domain3 : Fin 3 → ℚ))
    {Q : Fin 1 → ℚ[X] | ∀ j, (Q j).degree < 2} :=
  injOn_evalTuple_of_degree_lt domain3 (by decide)

example : cubicAnchorDivisor (0 : ℚ) 1 2 = Lagrange.nodal Finset.univ ![0, 1, 2] :=
  cubicAnchorDivisor_eq_nodal 0 1 2

example : (cubicAnchorReconstruct (0 : ℚ) 1 2 1 (X ^ 2)).eval 2 = 4 := by
  rw [(cubicAnchorReconstruct_eval_anchors (0 : ℚ) 1 2 1 (X ^ 2)).2.2]
  norm_num

example : (cubicAnchorReconstruct (0 : ℚ) 1 2 1 (X ^ 2)).eval 3 = 15 :=
  cubicAnchorReconstruct_eval_of_quotient 0 1 2 3 15 1 (X ^ 2)
    (by simp [cubicAnchorDivisor]; norm_num)

example : (cubicAnchorReconstruct (0 : ℚ) 1 2 1 (X ^ 2)).degree < (1 + 3 : ℕ) :=
  cubicAnchorReconstruct_degree_lt 0 1 2 (by simp) (by rw [degree_X_pow]; decide)

example : ((X ^ 3 : ℚ[X]) %ₘ (X ^ 2 - C 1)).eval (-1) = -1 := by
  rw [traceRemainder_eval_eq 2 1 (X ^ 3) (by norm_num)]
  norm_num

example : ((X ^ 3 : ℚ[X]) %ₘ (X ^ 2 - C 1)).degree < (2 : ℕ) :=
  traceRemainder_degree_lt 2 (by decide) 1 _

end InterleavedAcceptance
