/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ProximityGap.CapacityBounds
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenges

/-!
# Capacity-bound witnesses for the Grand MCA Challenge

This extension connects the citation-heavy bounds catalogue to the prize carriers in
`GrandChallenges.lean`. Keeping the import in this direction leaves the core grid and witness API
independent of the catalogue's external admits.
-/

namespace ProximityGap.GrandChallenges

open scoped NNReal
open CoreDefinitions
open CodingTheory

variable {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- The source-native BCHKS25 Johnson-range bound supplies a safe one-sided MCA witness whenever
its explicit numerical upper bound is at most the requested threshold. -/
noncomputable def McaLowerWitness.ofJohnsonBCHKS25
    (domain : ι ↪ F) (k : ℕ) (δ ε_star : ℝ≥0)
    (hk : 1 < k) (hδ_pos : 0 < δ)
    (hδ_johnson :
      (δ : ℝ) < 1 - ((((k - 1 : ℕ) : ℝ) / Fintype.card ι) ^ ((1 : ℝ) / 2)))
    (hδ_le_one : δ ≤ 1)
    (hle :
      ENNReal.ofReal
        (let n : ℝ := Fintype.card ι
         let ρ : ℝ := (k - 1 : ℕ) / n
         let m : ℝ := max ⌈(ρ ^ ((1 : ℝ) / 2)) /
           (1 - ρ ^ ((1 : ℝ) / 2) - δ)⌉ 3
         ((2 * (m + 1/2) ^ 5 + 3 * (m + 1/2) * δ * ρ)
            / (3 * ρ ^ ((3 : ℝ) / 2)) * n
          + (m + 1/2) / ρ ^ ((1 : ℝ) / 2))
            / (Fintype.card F : ℝ)) ≤ (ε_star : ENNReal)) :
    McaLowerWitness (ReedSolomon.code domain k) ε_star :=
  McaLowerWitness.ofLe hδ_le_one
    (le_trans
      (rs_epsMCA_johnson_range_bchks25 domain k δ hk hδ_pos hδ_johnson)
      hle)

end ProximityGap.GrandChallenges
