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
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallengesLattice.Inventory

/-!
# GrandChallengesLattice — Radii

Lattice radii `mcaLatticePoint` and supporting lemmas.

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

/-! ## Lattice radii -/

/-- The lattice radius `j/n : ℝ≥0` for `j : Fin (n+1)`. Relative Hamming distances take
values in `{0, 1/n, …, n/n = 1}`, so these are the only meaningful proximity radii. -/
noncomputable def mcaLatticePoint (n : ℕ) (j : Fin (n + 1)) : ℝ≥0 :=
  (j.val : ℝ≥0) / (n : ℝ≥0)

/-- Each lattice radius lies in `[0, 1]`. -/
theorem mcaLatticePoint_le_one (n : ℕ) (j : Fin (n + 1)) :
    mcaLatticePoint n j ≤ 1 := by
  unfold mcaLatticePoint
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp
  · rw [div_le_one (by exact_mod_cast hn)]
    exact_mod_cast Nat.lt_succ_iff.mp j.isLt

@[simp] theorem mcaLatticePoint_top (ι : Type) [Fintype ι] [Nonempty ι] :
    mcaLatticePoint (Fintype.card ι)
      ⟨Fintype.card ι, Nat.lt_succ_self _⟩ = 1 := by
  unfold mcaLatticePoint
  have hn : (Fintype.card ι : ℝ≥0) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  exact div_self hn

/-- Lattice radii are monotone in the index. -/
theorem mcaLatticePoint_mono (n : ℕ) {i j : Fin (n + 1)} (h : i ≤ j) :
    mcaLatticePoint n i ≤ mcaLatticePoint n j := by
  unfold mcaLatticePoint
  gcongr
  exact_mod_cast h

/-- The floor index of a lattice radius is the index itself: `⌊(j/n)·n⌋ = j` (for `0 < n`). -/
theorem floor_mcaLatticePoint (n : ℕ) (hn : 0 < n) (j : Fin (n + 1)) :
    Nat.floor (mcaLatticePoint n j * (n : ℝ≥0)) = j.val := by
  unfold mcaLatticePoint
  have hnne : (n : ℝ≥0) ≠ 0 := by exact_mod_cast hn.ne'
  rw [div_mul_cancel₀ _ hnne]
  exact Nat.floor_natCast _

/-- At the first nonzero MCA lattice radius `1/n`, the `mcaEvent` size lower bound forces
the witness set to contain at least `n - 1` coordinates. -/
theorem mcaEventWitness_card_pred_le_j1
    {ι : Type} [Fintype ι] [Nonempty ι] (S : Finset ι)
    (hS : (S.card : ℝ≥0) ≥
      (1 - mcaLatticePoint (Fintype.card ι)
        (⟨1, by
          have hn : 0 < Fintype.card ι := Fintype.card_pos
          omega⟩ : Fin (Fintype.card ι + 1))) *
        (Fintype.card ι : ℝ≥0)) :
    Fintype.card ι - 1 ≤ S.card := by
  let n := Fintype.card ι
  have hn : 0 < n := by simp [n, Fintype.card_pos (α := ι)]
  have hdiv_le : (1 : ℝ≥0) / (n : ℝ≥0) ≤ 1 := by
    rw [div_le_one (by exact_mod_cast hn)]
    exact_mod_cast Nat.succ_le_of_lt hn
  have hmul :
      (1 - mcaLatticePoint n
        (⟨1, by omega⟩ : Fin (n + 1))) * (n : ℝ≥0) =
        (((n - 1) : ℕ) : ℝ≥0) := by
    have hn0 : (n : ℝ≥0) ≠ 0 := by exact_mod_cast hn.ne'
    have h1n : (1 : ℕ) ≤ n := Nat.one_le_iff_ne_zero.mpr hn.ne'
    unfold mcaLatticePoint
    simp only [Nat.cast_one]
    -- `(1 - 1/n) * n = 1*n - (1/n)*n = n - 1` in `ℝ≥0` (truncated sub, `n ≥ 1`).
    rw [tsub_mul, one_mul, one_div, inv_mul_cancel₀ hn0]
    -- `↑n - 1 = ↑(n-1)` in `ℝ≥0` (no `Nat.cast_sub` for monus); via `↑(n-1) + 1 = ↑n`.
    have hadd : (((n - 1) : ℕ) : ℝ≥0) + 1 = (n : ℝ≥0) := by
      exact_mod_cast (Nat.sub_add_cancel h1n)
    exact (eq_tsub_of_add_eq hadd).symm
  have hnn : (((n - 1) : ℕ) : ℝ≥0) ≤ (S.card : ℝ≥0) := hmul.symm.trans_le hS
  exact_mod_cast hnn

end GrandChallengesLattice

end ProximityGap

