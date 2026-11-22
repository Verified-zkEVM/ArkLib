/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nishimwe Prince
-/
module

public import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.EpsCa
public import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenges

/-!
# Unique-decoding witnesses for the Grand MCA Challenge

`GrandChallenges/CapacityBounds.lean` builds `McaLowerWitness`es from the Johnson-range
bound proved via [DKT26], with the printed constant from [BCHKS25] Theorem 4.6. This module
builds one from [BCIKS20]'s unique-decoding-regime bound, also proved in-tree.

## Main definition

- `McaLowerWitness.ofUniqueDecodingRange` — a one-sided Grand MCA Challenge witness for a
  Reed-Solomon code at any positive radius up to the relative unique-decoding radius, valid
  whenever `n / |F|` clears the requested threshold.

## Radius and constant

This constructor rests on the axiom-clean `rs_mcaError_le_of_le_relUDR`. The Johnson-range
constructor `McaLowerWitness.ofJohnsonRangeBound` also has a proved numeric input,
`rs_mcaError_le_in_johnson_range`.

[BCIKS20] only reaches half the minimum distance, well short
of the Johnson radius the challenge cares about, and its `n / |F|` is a factor `n` weaker than
[BCHKS25] Theorem 1.3 in the overlapping range. So this constructor is not a route to the prize
thresholds: at `ε* = 2^-128` it demands `|F| ≥ n · 2^128`. It provides a simple proved
baseline for the challenge API.

## References

- [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf. *Proximity Gaps for Reed-Solomon Codes*.
- [BCHKS25] Theorem 4.6 (Johnson-range printed constant).
- [DKT26] (proof of the Johnson-range MCA bound).
-/

@[expose] public section

namespace ProximityGap.GrandChallenges

open scoped NNReal
open Code CoreDefinitions

variable {F ι : Type} [Field F] [Fintype F] [SampleableType F] [DecidableEq F]
    [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- Builds a one-sided MCA witness from [BCIKS20]'s unique-decoding-regime bound: at any positive
radius `δ` up to the relative unique-decoding radius of the Reed-Solomon code, the affine-line MCA
error is at most `n / |F|`, so any threshold `ε_star` that `n / |F|` clears is witnessed.

The numeric input is proved in-tree. -/
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
