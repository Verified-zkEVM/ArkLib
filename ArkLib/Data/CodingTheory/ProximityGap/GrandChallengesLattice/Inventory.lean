/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.GrandChallengeCollapse
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallengeLDThresholdElias
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallengeLattice
import ArkLib.Data.CodingTheory.InterleavedCode
import ArkLib.Data.CodingTheory.ProximityGap.MCABadCount
import ArkLib.Data.CodingTheory.ProximityGap.MCABadCountRatio
import ArkLib.Data.CodingTheory.ProximityGap.MCAEndpointLower
import ArkLib.Data.CodingTheory.ProximityGap.MCASecondMoment
import ArkLib.Data.CodingTheory.ProximityGap.SubsetSumErdosHeilbronn

/-!
# GrandChallengesLattice — Inventory

Small finite-set inventory lemmas for lattice threshold proofs.

Split from `GrandChallengesLattice.lean` for longFile hygiene (#110).
-/

set_option linter.style.longFile 2000

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false


namespace ProximityGap

open scoped NNReal ProbabilityTheory BigOperators
open Code

namespace GrandChallengesLattice

/-! ## Small finite-set inventory lemmas -/

/-- A subset of a finite type with at most one missing point is either the whole type or the
complement of a single point.

This is the purely combinatorial first step in the radius-`1/n` MCA/J1 analysis: once an
`mcaEvent` witness set is known to have cardinality at least `n - 1`, its shape is rigid. -/
theorem exists_eq_univ_or_eq_univ_erase_of_card_pred_le
    {α : Type} [Fintype α] [DecidableEq α] (S : Finset α)
    (hS : Fintype.card α - 1 ≤ S.card) :
    S = Finset.univ ∨ ∃ i : α, S = Finset.univ.erase i := by
  by_cases hfull : S = Finset.univ
  · exact Or.inl hfull
  · right
    have hmissing : ∃ i : α, i ∉ S := by
      by_contra hmissing
      apply hfull
      ext i
      simp only [Finset.mem_univ, iff_true]
      by_contra hi
      exact hmissing ⟨i, hi⟩
    rcases hmissing with ⟨i, hiS⟩
    refine ⟨i, ?_⟩
    have hsubset : S ⊆ Finset.univ.erase i := by
      intro x hx
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      exact fun hxi => hiS (hxi ▸ hx)
    refine Finset.eq_of_subset_of_card_le hsubset ?_
    simpa using hS

end GrandChallengesLattice

end ProximityGap

