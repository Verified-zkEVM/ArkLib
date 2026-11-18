/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/

import ArkLib.Data.MvPolynomial.SchwartzZippelCounting
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Schwartz–Zippel probability over distinct points: acceptance test

VCVio samples `Fin 2 ↪ ZMod 3` uniformly once `Nonempty (Fin 2 ↪ ZMod 3)` is supplied. For
`X 0 - X 1 - 1`, of total degree one, `prob_eval_zero_embedding_le_div` gives the bound
`1 / (3 - 2 + 1) = 1 / 2`.
-/

open MvPolynomial
open scoped ProbabilityTheory ENNReal

instance : Nonempty (Fin 2 ↪ ZMod 3) := ⟨⟨![0, 1], by decide⟩⟩

/-- A uniformly random pair of distinct elements of `ZMod 3` is a zero of `X 0 - X 1 - 1` with
probability at most `1 / 2`. -/
example :
    Pr{let x ← $ᵗ (Fin 2 ↪ ZMod 3)}[eval x (X 0 - X 1 - 1 : MvPolynomial (Fin 2) (ZMod 3)) = 0] ≤
      1 / 2 := by
  have hne : (X 0 - X 1 - 1 : MvPolynomial (Fin 2) (ZMod 3)) ≠ 0 := fun h ↦ by
    simpa using congrArg (eval ![0, 0]) h
  have hle : (X 0 - X 1 - 1 : MvPolynomial (Fin 2) (ZMod 3)).totalDegree ≤ 1 :=
    (totalDegree_sub _ _).trans <| max_le ((totalDegree_sub _ _).trans (by simp)) (by simp)
  refine (prob_eval_zero_embedding_le_div _ hne hle).trans_eq ?_
  rw [ZMod.card]
  norm_num
