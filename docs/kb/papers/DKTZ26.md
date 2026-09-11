---
kind: paper
bibkey: DKTZ26
title: "Quantitative Reed--Solomon List Decoding and Mutual Correlated Agreement: From Johnson to Capacity"
year: "2026"
bib_source: blueprint/src/references.bib
canonical_url: null
source_metadata: ../sources/DKTZ26/metadata.yml
status: active-private-manuscript
---

# DKTZ26

## At A Glance

Dao, Kominers, and Thaler give quantitative list and mutual-correlated-agreement bounds from
the Johnson regime through every fixed positive capacity gap. The mathematical statements apply to
arbitrary fields under explicit characteristic guards; the fast decoding claims use supplied prime
fields. The paper also sharpens the parameter choices, root bounds, endpoint analysis, and
characteristic limitations.

## What ArkLib Uses From This Paper

- the no-band weighted-support construction, with the finite-cover alternative retained separately;
- the order-zero proof for gaps at least one quarter;
- the revised small-gap order `ceil(exp(1.5 / delta))` and 300-based mathematical multiplicity;
- primitive, separant, resonance, and exact local-rank refinements;
- exact-capacity and inverse-gap lower bounds;
- the linearly-growing-characteristic extension and Frobenius-plane obstruction.

## Main ArkLib Touchpoints

- Reader map: `ArkLib/Data/CodingTheory/ReedSolomon/PaperGuide.lean`
- Decoder-status map: `ArkLib/Data/CodingTheory/ReedSolomon/ListDecoding/PaperAlgorithms.lean`
- Weighted Johnson list and MCA:
  `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Johnson/WeightedCertificate.lean`
- First-derivative headline bounds:
  `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/Branchwise.lean`
- Fixed-order `Gamma > 1` list and MCA:
  `ArkLib/Data/CodingTheory/ReedSolomon/{ListDecodability,MutualCorrelatedAgreement}/Capacity/RatePartition.lean`
- Revised 300-based small-gap list and MCA:
  `ArkLib/Data/CodingTheory/ReedSolomon/{ListDecodability,MutualCorrelatedAgreement}/Capacity/MathematicalUniformRate.lean`
- All-rate facades: `ArkLib/Data/CodingTheory/ReedSolomon/ListDecodability/Capacity.lean` and
  `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Capacity.lean`
- Represented-family recovery:
  `ArkLib/Data/CodingTheory/ReedSolomon/ListDecoding/AgreementRecovery/RepresentedExact.lean`

## Version Notes

The current Lean correspondence target is private manuscript commit
`980d875a04f6472339e3b4147f3d90ae09dff57b` from September 11, 2026, matching the source metadata.
The original source record pinned `9e4d6488ead94be47cca69e5be915b5667143b66` from September 6.
The newer revision replaces that snapshot's asymmetric-band route and updates the title, authors,
quantitative bounds, decoder presentation, and application claims.

## Scope

The mathematical owners expose complete lists and exact line, affine-space, and polynomial-curve
MCA. The sharp paper-aligned MCA entrypoints are `sharpCapacity_lineAgreement`,
`sharpCapacity_affineAgreement_and_mcaError`, and `sharpCapacity_powerBatchingAgreement`; the
older `exists_capacity_*` family retains the 1000-based compatibility route and its
`n <= ringChar F` premise. `ListDecoding/CapacityDecoder.lean` is a retained coordinate correctness
reference with an
observed primitive-work ledger; it is not the paper's integrated fast decoder. Agreement recovery
from supplied finite representations is proved, and square-system recovery is conditional on a
torus-backend coverage contract. The first-order norm components do not yet form a top-level
constructor with coverage and `ExactOutput`, and no whole-decoder bit/RAM bound is formalized.
Historical decoder development is recorded in the
[algebraic-machine plan](../../design/rs-algebraic-machine-plan.md).

Concrete Johnson-table, BN254 curve, ProveKit, ZisK, and LambdaVM instantiations are indexed outside
the reusable library graph in `ArkLibExamples/ReedSolomon/PaperGuide.lean`.

## Source Access

- Source metadata: [`../sources/DKTZ26/metadata.yml`](../sources/DKTZ26/metadata.yml)
- The source repository is private; the pinned commit is recorded above for authorized collaborators.
