/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.InterleavedCode.Projection

/-!
# Semiring row-projection client

This ordinary import checks that row-combination preservation is available for module codes
over `ℕ`, without a field or a generator.
-/

open Code LinearCode

example {ι κ : Type} [Fintype κ] (C : ModuleCode ι ℕ ℕ) (w : ι → κ → ℕ)
    (T : Finset ι) (l : κ → ℕ)
    (h : projectedWord w T ∈ projectedCodeSubmod (C^⋈κ) T) :
    projectedWord (fun i ↦ ∑ r, l r • w i r) T ∈ projectedCodeSubmod C T :=
  projectedWord_rowCombination_mem C w T l h
