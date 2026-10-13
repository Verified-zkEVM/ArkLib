---
kind: paper
bibkey: RSG
title: "Ring switching, generalized"
bib_source: blueprint/src/references.bib
canonical_url: https://github.com/leanEthereum/leanVM-b/blob/main/misc/ring-switching-generalized.pdf
status: seeded
related_concepts:
  - ring-switching
related_modules:
  - ArkLib/ProofSystem/RingSwitching/Packing/Coordinates.lean
  - ArkLib/ProofSystem/RingSwitching/Packing/Relations.lean
  - ArkLib/ProofSystem/RingSwitching/Packing/Batching.lean
---

# RSG

## At A Glance

*Ring switching, generalized* is a three-page note, with no printed author or date, that separates
the packing extension `P` and the evaluation extension `E` over a common base `B`. Its credits
read "The idea comes from Lev Soukhanov, `[[alloc]init]`."

## What ArkLib Uses From This Paper

- **Independent bases.** Bases of `E` and `P` over `B` identify a family of evaluations over `E`
  with a `B`-coordinate matrix; transposing and packing it gives the slice targets. No embedding
  between `E` and `P` is needed. This is `PackingData` and `PackingData.transpose`.
- **Slices and batching.** The verifier batches the slices with a random challenge and runs a
  sumcheck. `Relations.lean` states the opening, slice and batched-sumcheck relations and proves
  that correct slices give a correct batched claim.
- **Batching loss.** The note batches with exponents `1, …, e` and loss `e/|C|`. ArkLib's
  `gammaPowers` uses exponents `0, …, e − 1` and proves the bound `(e − 1)/|P|`.

## Main ArkLib Touchpoints

- [`Coordinates.lean`](../../../ArkLib/ProofSystem/RingSwitching/Packing/Coordinates.lean) — independent bases and the coordinate transpose.
- [`Relations.lean`](../../../ArkLib/ProofSystem/RingSwitching/Packing/Relations.lean) — slice and batched-sumcheck relations.
- [`Batching.lean`](../../../ArkLib/ProofSystem/RingSwitching/Packing/Batching.lean) — batching strategies with proved collision bounds.
- [Ring-switching concept](../concepts/ring-switching.md).

## Source Access

- [Public note](https://github.com/leanEthereum/leanVM-b/blob/main/misc/ring-switching-generalized.pdf).
- [Bibliography](../../../blueprint/src/references.bib), key `RSG`.
