# Issue 141: Grand Challenge 1 open prize surfaces (proximity)

Status: tracking issue; genuinely open mathematics retained as named hypotheses, with the
surrounding provable mathematics formalized and the open prize sharpened.

## Scope

Two ABF26 Grand Challenge 1 conjecture surfaces are tracked here. They are the research prize
(the beyond-UDR Guruswami–Sudan list-decoder mass bound), **open mathematics**, not closeable
formalization debt:

- `ProximityGap.GrandChallenges.mcaConjecture`
  ([GrandChallenges.lean](../../../../../ArkLib/Data/CodingTheory/ProximityGap/GrandChallenges.lean)) —
  abstract `ε_mca` uniform bound, ABF26 §4.5 (`conj:mca-conjecture`); constants quantified
  *before* the `∀` over codes (the genuine uniform form).
- `ProximityGap.MCAGS.epsMCAgs_prizeBound_conjecture`
  ([MCAGS.lean](../../../../../ArkLib/Data/CodingTheory/ProximityGap/MCAGS.lean)) — GS-exposed form,
  stated against the real GS-exposed definitions (`epsMCAgs`, `gsListBound`).

## What was proved (Issue #141 math)

New module
[GrandChallenge141PrizeMath.lean](../../../../../ArkLib/Data/CodingTheory/ProximityGap/GrandChallenge141PrizeMath.lean),
all declarations axiom-clean `[propext, Classical.choice, Quot.sound]`, sorry-free:

- `epsMCAgs_le_one`, `epsMCA_le_one` — both prize errors are suprema of probabilities, hence `≤ 1`.
- **`epsMCAgs_prizeBound_conjecture_holds`** — the GS-exposed prize `def`
  `epsMCAgs_prizeBound_conjecture` packages its constants *inside* the per-input `Prop`, so for a
  single instance the bound can be inflated past `1` (the gap `η < 1` in the prize regime, so
  `η^{c₃} → 0`) while `epsMCAgs ≤ 1`. Hence the **per-input** GS form is a *theorem*. This is not
  a proof of the prize: it pinpoints that the open content lives entirely in the *uniformity* of
  the constants, exactly as `mcaConjecture` (constants before the `∀`) already captures.
- `epsMCAgsPrizeUniformConjecture` — the honest **uniform** GS-exposed open prize (one constant
  triple for every rate/gap/radius/domain/list family), the genuine #141 surface, a named `Prop`
  left deliberately unproved.
- `epsMCAgs_prizeBound_of_listSize_clears` — explicit-constant conditional reduction deriving the
  per-input conjecture from the proved pivot-covering bound `epsMCAgs ≤ ℓ/q`
  (`MCAGSWitness.epsMCAgs_le_listSize_div_of_pivotCovering`) plus one numeric clearance, with the
  open content isolated into named list-size/covering hypotheses.

## Decision

- Keep both surfaces as named `Prop`s, not theorems. The genuine open prize is the **uniform**
  form (`mcaConjecture`, `epsMCAgsPrizeUniformConjecture`); it is not proved and must not be
  laundered into a theorem via an equivalent packaged form.
- Every consumer takes a surface as an *explicit hypothesis* (conditional reduction). These are
  the permitted partial progress and are linked to #141:
  - `mcaConjecture`: `nonempty_mcaLowerWitness_of_mcaConjecture`,
    `exists_mcaLowerWitness_of_mcaConjecture`, the `ignoredSource` adapters, and the
    lattice-threshold links in `GrandChallengesLattice.lean`.
  - `epsMCAgs_prizeBound_conjecture`: `MCAGSWitness.epsMCAgs_prizeBound_of_massBound` and the new
    `GrandChallenge141PrizeMath.epsMCAgs_prizeBound_of_listSize_clears`.
- Leave #141 **open**: the uniform prize remains genuinely unproved. Closing would require either
  laundering or upstreaming classical GS list decoding (absent from mathlib).

## Relationship to neighbouring tickets

`mcaConjecture` API status (compatibility vs. `ignoredSource` adapters) is #78 (resolved). The
GS reduction plumbing (mass bound, pivot covering, faithful family) is #52/#66. #141 sits above
both, tracking the *open mathematics* of the prize surfaces themselves and now their
genuinely-provable surrounding mathematics.

## Regression search

```sh
rg -n 'mcaConjecture|epsMCAgs_prizeBound_conjecture|epsMCAgsPrizeUniformConjecture|#141' \
  ArkLib/Data/CodingTheory/ProximityGap/GrandChallenges.lean \
  ArkLib/Data/CodingTheory/ProximityGap/GrandChallengesLattice.lean \
  ArkLib/Data/CodingTheory/ProximityGap/MCAGS.lean \
  ArkLib/Data/CodingTheory/ProximityGap/MCAGSWitness.lean \
  ArkLib/Data/CodingTheory/ProximityGap/GrandChallenge141PrizeMath.lean \
  docs/kb/audits/proximity-prize
```

Expected: both surfaces remain `def : Prop`; the uniform prize stays unproved; the
per-input/uniform distinction is recorded; new declarations are axiom-clean.
