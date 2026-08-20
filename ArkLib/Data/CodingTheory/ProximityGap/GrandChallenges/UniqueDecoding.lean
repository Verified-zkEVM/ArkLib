/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nishimwe Prince
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.EpsCa
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenges

/-!
# Unique-decoding witnesses for the Grand MCA Challenge

`GrandChallenges/CapacityBounds.lean` builds `McaLowerWitness`es from the capacity-regime
catalogue, every entry of which is an external admit. This module builds one from [BCIKS20]'s
unique-decoding-regime bound instead, which is proved in-tree.

## Main definition

- `McaLowerWitness.ofUniqueDecodingRange` — a one-sided Grand MCA Challenge witness for a
  Reed-Solomon code at any positive radius up to the relative unique-decoding radius, valid
  whenever `n / |F|` clears the requested threshold.

## Why this one is different

It is the first `McaLowerWitness` constructor in the tree whose numeric input is proved rather
than admitted: `McaLowerWitness.ofJohnsonRangeBound` rests on `rs_mcaError_le_in_johnson_range`,
an external [BCHKS25] admit, whereas this rests on `rs_mcaError_le_of_le_relUDR`, which is
axiom-clean.

The trade is radius for provenance. [BCIKS20] only reaches half the minimum distance, well short
of the Johnson radius the challenge cares about, and its `n / |F|` is a factor `n` weaker than
[BCHKS25] Theorem 1.3 in the overlapping range. So this constructor is not a route to the prize
thresholds — at `ε* = 2^-128` it demands `|F| ≥ n · 2^128`. It is the honest floor: what the
challenge API can currently certify with no admit anywhere beneath it.

## References

- [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf. *Proximity Gaps for Reed-Solomon Codes*.
-/

namespace ProximityGap.GrandChallenges

open scoped NNReal
open Code CoreDefinitions

variable {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- Builds a one-sided MCA witness from [BCIKS20]'s unique-decoding-regime bound: at any positive
radius `δ` up to the relative unique-decoding radius of the Reed-Solomon code, the affine-line MCA
error is at most `n / |F|`, so any threshold `ε_star` that `n / |F|` clears is witnessed.

Unlike `McaLowerWitness.ofJohnsonRangeBound`, nothing below this constructor is admitted. -/
noncomputable def McaLowerWitness.ofUniqueDecodingRange
    (domain : ι ↪ F) (deg : ℕ) (δ ε_star : ℝ≥0)
    (hδ_pos : 0 < δ)
    (hδ_le_one : δ ≤ 1)
    (hδ : δ ≤ relativeUniqueDecodingRadius
            (ι := ι) (F := F) (C := ReedSolomon.code domain deg))
    (hle : ((Fintype.card ι / Fintype.card F : ℝ≥0) : ENNReal) ≤ (ε_star : ENNReal)) :
    McaLowerWitness (ReedSolomon.code domain deg) ε_star :=
  McaLowerWitness.ofLe hδ_le_one
    (le_trans (rs_mcaError_le_of_le_relUDR hδ_pos hδ) hle)

end ProximityGap.GrandChallenges
