---
kind: paper
bibkey: ChiesaYogev2024
title: "Building Cryptographic Proofs from Hash Functions"
year: 2024
bib_source: blueprint/src/references.bib
source_metadata: ../sources/ChiesaYogev2024/metadata.yml
status: investigated
canonical_url: https://snargsbook.org/
related_concepts:
  - interactive-oracle-proofs
related_modules:
  - ArkLib/Interaction/Protocol.lean
  - ArkLib/Interaction/Security/CompositionSoundness.lean
  - ArkLib/OracleReduction/Security/RoundByRound.lean
  - ArkLib/ProofSystem/Sumcheck/Soundness.lean
---

# ChiesaYogev2024

## At A Glance

Alessandro Chiesa and Eylon Yogev's *Building Cryptographic Proofs from Hash Functions* is a
required long-term coverage target for ArkLib's interaction framework. The ambition is to
formalize the book in ArkLib's language, including its more general reductions and dependent
interfaces. It is not enough to reuse the book's terminology for a different security experiment.

The repository bibliography retains its 2024 key. The comparison below uses version 1.2 of
March 25, 2026, at the pinned source revision in the metadata.

## What ArkLib Uses From This Paper

The book provides concrete security experiments and a modular route from oracle proofs to
hash-based arguments: round-by-round and state-restoration security, interactive compilation
using commitments, hash-chain Fiat-Shamir, and knowledge extraction with explicit losses.
It also covers material outside this route, including zero knowledge, preprocessing and witness
indistinguishability. Whole-book coverage remains an ambition, not a completed theorem inventory.

The [detailed comparison and research notes](../audits/chiesa-yogev-interaction.md) distinguish
source definitions, implemented results, proposed bridges and unanswered design questions.

## Main ArkLib Touchpoints

- [Native interaction protocols](../../../ArkLib/Interaction/Protocol.lean) and the runtime
  results of [composition soundness](../../../ArkLib/Interaction/Security/CompositionSoundness.lean)
  supply execution and reduction semantics, including persistent oracle state.
- [Sumcheck soundness](../../../ArkLib/ProofSystem/Sumcheck/Soundness.lean) is an
  ordinary-security client, not yet a formalization of the book's whole security pipeline.
- [Legacy round-by-round security](../../../ArkLib/OracleReduction/Security/RoundByRound.lean)
  has one fixed-prefix notion; #1413 and #1421 removed the execution-averaged and one-shot
  variants. Its knowledge variant needs separate access and timing comparisons.
- [Legacy transcript-tree extraction](../../../ArkLib/OracleReduction/Security/TranscriptTree/Composition.lean)
  contains reusable mathematical composition results, distinct from an efficient tree-finding
  algorithm with black-box prover access.
- The [state-restoration module](../../../ArkLib/Interaction/Security/StateRestoration.lean)
  cites Definitions 23.2.1 and 23.2.3 and Theorem 31.3.1 for fixed-round protocols; see the
  [correspondence note](../audits/interaction-state-restoration-correspondence.md).
- The [design roadmap](../../design/05-roadmap.md) lists the remaining interaction-layer work.

## Known Divergences From ArkLib

ArkLib has dependent interaction trees, output claims and virtual oracle interfaces, refined
message types, and explicit shared-state execution. The book's relevant IOP experiments use
fixed-round strings and precisely specified randomness and extractor observations. Some
differences are useful generalizations; others are missing specialization or compiler proofs.
The detailed comparison records which is which rather than assuming equivalence.

## Source Access

- [Official book site](https://snargsbook.org/).
- [Pinned official TeX source](https://github.com/hash-based-snargs-book/hash-based-snargs-book/blob/305fa3d9d19ee6dba135de64b3156d1760df8426/snargs-book.tex).
- [Source metadata](../sources/ChiesaYogev2024/metadata.yml). No book artifact is vendored here.
