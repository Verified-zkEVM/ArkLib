/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.EqualDegree
import Mathlib.Algebra.Field.ZMod

/-! # Acceptance cases for the equal-degree combiner -/

open ReedSolomon

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The whole field `F₅` as the evaluation domain. -/
private def fullDomain : ZMod 5 ↪ ZMod 5 := Function.Embedding.refl _

/-- At `d = 1`, `A = 4` on `F₅`, the Johnson list size is `5 / 2`, so the loss is `1 / 2`. -/
example :
    equalDegreeMCAError fullDomain 1 4 1 ≤ affineMCAError fullDomain 1 4 1 + 1 / 2 := by
  have h := equalDegreeMCAError_le fullDomain (d := 1) (A := 4) (by norm_num)
    (by simp [ZMod.card])
  norm_num [ZMod.card] at h
  exact h
