---
kind: paper
bibkey: BCPZZ26
title: "Algorithmic List Decoding of Reed--Solomon Codes up to Capacity in the Low-Rate Regime"
year: "2026"
bib_source: blueprint/src/references.bib
canonical_url: https://eccc.weizmann.ac.il/report/2026/164/
source_metadata: ../sources/BCPZZ26/metadata.yml
status: active
---

# BCPZZ26

## At A Glance

BCPZZ introduce the hidden-derivative interpolation framework used by the all-rate formalization.
Their published theorem specializes the method to the low-rate regime.

## What ArkLib Uses From This Paper

- hidden-derivative local substitutions and local contact constraints;
- factorization through an enlarged local map and its exhibited kernel;
- interpolation-to-differential-equation reduction;
- the differential root-finding interface attributed there to Kopparty.

## Main ArkLib Touchpoints

- `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/`
- `ArkLib/Data/CodingTheory/ReedSolomon/ListDecodability/Capacity/`
- `ArkLib/Data/CodingTheory/ReedSolomon/ListDecodability/Capacity.lean`
- `ArkLib/Data/CodingTheory/ReedSolomon/ListDecoding/CapacityDecoder.lean`
- `ArkLib/Data/CodingTheory/ReedSolomon/PaperGuide.lean` for the later all-rate theorem map
- `ArkLib/Data/CodingTheory/ReedSolomon/ListDecoding/PaperAlgorithms.lean` for decoder boundaries

## Known Divergences From ArkLib

ArkLib separates the free derivative order from BCPZZ's low-rate parameter specialization and uses
ambient padding or a finite rate cover to obtain one derivative order depending only on the additive
capacity gap.

## Open Formalization Gaps

`ListDecodability/Capacity.lean` gives the later all-rate mathematical exact-list theorem.
`CapacityDecoder.lean` connects the retained coordinate decoder's output to that specification and
records an observed primitive-work ledger; it is a correctness reference, not the integrated norm
and square-system decoder. The current component and backend boundaries are maintained in
`ListDecoding/PaperAlgorithms.lean`. Historical restricted-machine work is recorded in the
[algebraic-machine plan](../../design/rs-algebraic-machine-plan.md). None of these narrower results
is a whole-decoder bit-time theorem.

## Source Access

- Source metadata: [`../sources/BCPZZ26/metadata.yml`](../sources/BCPZZ26/metadata.yml)
- Public paper: <https://eccc.weizmann.ac.il/report/2026/164/>
