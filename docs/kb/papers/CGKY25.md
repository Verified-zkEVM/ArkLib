---
kind: paper
bibkey: CGKY25
title: "On the Fiat-Shamir Security of Succinct Arguments from Functional Commitments"
year: 2025
bib_source: blueprint/src/references.bib
canonical_url: https://eprint.iacr.org/2025/902
source_metadata: ../sources/CGKY25/metadata.yml
status: investigated
related_modules:
  - ArkLib/Commitments/Functional/Basic.lean
  - ArkLib/Commitments/Functional/KZG/FunctionBinding/Reduction.lean
  - ArkLib/Commitments/Functional/KZG/Security.lean
---

# CGKY25

## At A Glance

`CGKY25` defines and analyzes the Funky protocol, compiling functional IOPs and functional
commitments into succinct interactive arguments secure under state restoration. It is also
the reference used by ArkLib's KZG function-binding reduction. The general compiler theorem
is an active coverage target, not an already proved consequence of that KZG client.

## What ArkLib Uses From This Paper

- Function binding (Definition 3.17), which `KZG.functionBindingExperiment` states for KZG: every
  opening is accepted and no message fits all of them.
- The ARSDH assumption (Definition 9.6), which VCVio states as `ARSDH.experiment`.
- The reduction from KZG function binding to ARSDH. ArkLib's version,
  `KZG.FunctionBinding.functionBindingReduction`, treats three cases: two conflicting openings,
  the trapdoor among the queries, and interpolation through `n + 1` distinct openings.
- The broader compiler target: functional query classes, state-restoration function binding,
  query solving and tail bounds. See the
  [interaction literature map](../audits/interaction-literature-map.md#fiops-iors-and-funky-separate-two-independent-axes).

## Main ArkLib Touchpoints

- [`ArkLib/Commitments/Functional/KZG/FunctionBinding/Reduction.lean`](../../../ArkLib/Commitments/Functional/KZG/FunctionBinding/Reduction.lean)
  cites `CGKY25` directly.
- [`ArkLib/Commitments/Functional/Basic.lean`](../../../ArkLib/Commitments/Functional/Basic.lean)
  cites the paper as a reference for the general interface.
- [`ArkLib/Commitments/Functional/KZG/Security.lean`](../../../ArkLib/Commitments/Functional/KZG/Security.lean)
  states `KZG.functionBindingExperiment` and the ARSDH bounds, and cites `CGKY25`.

## Version Notes

- Inspected the June 2, 2026 revision, 90 pages; retain the original 2025 bibliography key.
- Exact PDF hash is recorded in source metadata. Definition and theorem numbers in the
  broader audit refer to this revision.

## Open Formalization Gaps

- A paper-to-Lean audit of the KZG reduction remains separate from this framework audit. It should
  record which steps of the paper reduction correspond to each major lemma in
  `FunctionBinding/Wins.lean`.
- ArkLib proves the pointwise statement `KZG.FunctionBinding.functionBindingReduction_wins` and the
  game-level bound `KZG.functionBinding_le_arsdh` against VCVio's `ARSDH.experiment`. The
  corollary `KZG.functionBinding_le_of_arsdh` assumes the ARSDH bound only over an explicit
  adversary class.
- The general Funky theorem needs its actual SR experiments, query solver/tail obligations,
  resource substitutions and extractor access. Full-message extractability is not a universal
  prerequisite of this route.
- Funky has an accept/reject endpoint. An extension to arbitrary native output-oracle reductions
  requires a separate theorem.

## Source Access

- Source metadata: [`../sources/CGKY25/metadata.yml`](../sources/CGKY25/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
