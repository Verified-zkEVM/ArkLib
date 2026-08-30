/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ProximityGap.CapacityBounds
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenges

/-!
# Capacity-bound witnesses for the Grand MCA Challenge

This extension turns capacity bounds into one-sided witnesses for the Grand MCA Challenge while
keeping the core grid and witness API independent of external admits.

## References

- [BCHKS25] Theorem 4.6.
-/

namespace ProximityGap.GrandChallenges

open scoped NNReal
open CoreDefinitions
open CodingTheory

variable {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- Builds a one-sided MCA witness from the Reed--Solomon Johnson-range bound whenever its
explicit numerical upper bound is at most the requested threshold. -/
noncomputable def McaLowerWitness.ofJohnsonRangeBound
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
      (rs_mcaError_le_in_johnson_range domain k δ hk hδ_pos hδ_johnson)
      hle)

end ProximityGap.GrandChallenges
