/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.Separation
import Mathlib.Algebra.Field.ZMod

/-! # Acceptance cases for the combiner lower bounds -/

open ReedSolomon

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The whole field `F₅` as the evaluation domain. -/
private def fullDomain : ZMod 5 ↪ ZMod 5 := Function.Embedding.refl _

/-- Without loss, the affine error at `d = 1`, `A = 3` on `F₅` is at least `12 / 25`. -/
example : (12 : ENNReal) / 25 ≤ affineMcaError fullDomain 1 3 0 := by
  have h := affineMcaError_zero_loss_ge fullDomain (d := 1) (A := 3) (by norm_num)
    (by simp [ZMod.card])
  norm_num [ZMod.card, ENNReal.ofReal_div_of_pos] at h
  exact h

/-- With loss `1`, the scalar error at `d = 0`, `A = 3` on `F₅` is at least `2 / 5`. -/
example : (2 : ENNReal) / 5 ≤ scalarMcaError fullDomain 0 3 1 := by
  have h := scalarMcaError_ge fullDomain (d := 0) (A := 3) (s := 1) (by norm_num)
    (by simp [ZMod.card])
  norm_num [ZMod.card, ENNReal.ofReal_div_of_pos] at h
  exact h
