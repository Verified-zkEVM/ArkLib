---
kind: paper
bibkey: GMW25
title: "A Simplified Round-by-round Soundness Proof of FRI"
year: 2025
bib_source: blueprint/src/references.bib
canonical_url: https://eprint.iacr.org/2025/1993
source_metadata: ../sources/GMW25/metadata.yml
status: mapped
related_modules:
  - ArkLib/ProofSystem/Fri/FoldingSoundness.lean
  - ArkLib/ProofSystem/Fri/ErrorBounds.lean
  - ArkLib/ProofSystem/Fri/QuerySoundness.lean
  - ArkLib/ProofSystem/Fri/RoundConsistency.lean
  - ArkLib/ProofSystem/Fri/Spec/Soundness.lean
---

# GMW25

## At A Glance

Garreta, Mohnblatt, and Wagner analyze FRI by preserving agreement on the actual accepting
query positions. ArkLib follows the March 27, 2026 revision of ePrint 2025/1993.

## What ArkLib Uses From This Paper

- The reduction of a folding agreement failure to mutual correlated agreement (Lemma 5.1).
- The query bound `(1 - min θ δ)^t`, with the tradeoff parameter `θ` independent of input
  distance `δ` (Theorem 5.2).
- Agreement on accepting positions, uniqueness above the rate threshold, interpolation,
  and detection of disagreement queries (Corollary 5.6).

## Main ArkLib Touchpoints

`Fri.foldingAgreementFailure_prob_le_powers` uses `CoreDefinitions.mcaError` and the existing
`univariatePowersGenerator`. `Fri.FoldTrace.query_soundness_distance` states the conditional
query error at `Code.relDistFromCode`. The trace is an algebraic view of a commitment
transcript; the executable protocol remains in `Fri/Spec`. `Fri.Spec.soundness` and
`Fri.Spec.rbrSoundness` establish its end-to-end adaptive security with the existing
input/output relations. `Fri.Spec.soundness_proximity` gives the stronger rejection bound
for every input at distance at least `δ`.

## Version Notes

The earlier [simple-rbr-fri](https://github.com/zksecurity/simple-rbr-fri) formalization was
consulted at commit `5d99bc7bcabc7b640e063f4d75f17d8262e00a8a`. Credit belongs to Yoichi Hirai,
Pietro Monticone, and Harmonic's Aristotle. ArkLib reuses its own codes, distances, folding,
probabilities, and MCA rather than importing the reference repository's parallel foundations.

The revised paper separates `θ` from `δ`, uses a non-strict large-set threshold, gives an
explicit powers-MCA bound, and includes the additional binding and extraction consequences.
The MCA value interface permits established ArkLib bounds to be substituted without baking
one particular numerical estimate into the protocol proof. `Fri/ErrorBounds.lean` provides
the generalized-Johnson specialization using ArkLib's existing powers-MCA theorem.

## Known Divergences From ArkLib

ArkLib's existing domains support folding factors that are powers of two. The paper allows
more general multiplicative subgroups. Algebraic interpolation is formalized without claiming
an extraction running-time bound. Zero query repetitions are allowed, yielding the vacuous
error bound one; the paper's probability-to-binding deduction assumes a positive repetition count.

## Open Formalization Gaps

Ordinary and round-by-round soundness of the specified interactive oracle reduction are
proved. Fiat–Shamir compilation, concrete oracle commitments, and efficient extraction are
outside this result. See the [proof and specification audit](../audits/fri-soundness.md).

## Source Access

- [Paper](https://eprint.iacr.org/2025/1993)
- [Source provenance](../sources/GMW25/metadata.yml)
- [Reference formalization](https://github.com/zksecurity/simple-rbr-fri)
