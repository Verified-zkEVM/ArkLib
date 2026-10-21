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
  - ArkLib/ProofSystem/Fri/Spec/KnowledgeSoundness.lean
  - ArkLib/ProofSystem/Fri/Spec/Extraction/Program.lean
  - ArkLib/ProofSystem/Fri/Spec/Extraction/FullCost.lean
  - ArkLib/ProofSystem/Fri/Spec/Extraction/ClosedCost.lean
---

# GMW25

## At A Glance

Garreta, Mohnblatt, and Wagner analyze FRI by preserving agreement on the actual accepting
query positions. ArkLib follows the March 27, 2026 revision of ePrint 2025/1993.

## What ArkLib Uses From This Paper

- The reduction of a folding agreement failure to mutual correlated agreement (Lemma 5.1).
- The query bound `(1 - min θ δ)^t`, with the tradeoff parameter `θ` independent of input
  distance `δ` (Theorem 5.2).
- Proximity, unique agreement on accepting positions, deterministic extraction by
  interpolating any `d` accepting positions, and detection of disagreement queries:
  Corollary 5.6, with separate `δ ≤ θ` and `δ ≤ 1 - ρ` hypotheses.

## Main ArkLib Touchpoints

`Fri.foldingAgreementFailure_prob_le_powers` uses `CoreDefinitions.mcaError` and the existing
`univariatePowersGenerator`. `Fri.FoldTrace.query_soundness_distance` states the conditional
query error at `Code.relDistFromCode`. The trace is an algebraic view of a commitment
transcript; the executable protocol remains in `Fri/Spec`. `Fri.Spec.soundness` and
`Fri.Spec.rbr_soundness` establish its end-to-end adaptive security with the existing
input/output relations. `Fri.Spec.soundness_proximity` gives the stronger rejection bound
for every input at distance at least `δ`.

`Fri.FoldTrace.exists_codeword_of_query_probability` packages proximity, binding,
interpolation, and erasure detection for a safe trace with positive degree bound and query
count. The rate constraint is on `δ`, not `θ`. Positive acceptance supplies the final
code-membership premise; it need not be assumed separately.

`Fri.Spec.Extractor.extract` implements the corollary's interpolation construction on the
actual retained history before query sampling. It scans the accepting positions and
interpolates the first `D` samples, where `D` is ArkLib's initial degree dimension (the
paper's `d`). `Fri.Spec.knowledge_soundness_with` lifts deterministic recovery to the
logged knowledge game for every input and malicious prover, using the existing relations
and `soundnessError`. This game-level result also handles extraction failure explicitly.

The named extractor is the result projection of its measured instruction program.
`Extraction/FullCost.lean` bounds all thirteen instruction coordinates, including retained-word
reads and inversions; `Extraction/ClosedCost.lean` gives closed field-operation bounds.
These bounds cover arbitrary histories and early rejection. They count unit-cost field
operations and immutable accesses, not machine runtime, field bit complexity, or total
workspace. See the [proof and specification audit](../audits/fri-soundness.md) for the
formulas and exact cost model.

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
more general multiplicative subgroups. ArkLib certifies the extractor's query and algebraic
instruction bounds without a machine-level polynomial-time adequacy theorem. Zero query
repetitions are allowed, making the query-error term one and the total bound vacuous; the
paper's probability-to-binding deduction assumes a positive repetition count.

## Open Formalization Gaps

Ordinary, round-by-round, and straightline knowledge soundness of the specified interactive
oracle reduction are proved, together with deterministic extraction and explicit query and
field-operation bounds. Fiat–Shamir compilation, concrete commitment security, and a
machine/bit-runtime or total-workspace theorem remain separate obligations.

## Source Access

- [Paper](https://eprint.iacr.org/2025/1993)
- [Source provenance](../sources/GMW25/metadata.yml)
- [Reference formalization](https://github.com/zksecurity/simple-rbr-fri)
