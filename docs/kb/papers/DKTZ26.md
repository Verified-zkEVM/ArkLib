---
kind: paper
bibkey: DKTZ26
title: "Reed--Solomon List Decoding up to Capacity at Every Rate"
year: "2026"
bib_source: blueprint/src/references.bib
canonical_url: null
source_metadata: ../sources/DKTZ26/metadata.yml
status: active-private-manuscript
---

# DKTZ26

## At A Glance

Dao, Kominers, Thaler, and Zheng strengthen the hidden-derivative method to every fixed rate and
every fixed positive capacity gap over prime fields. The paper also sharpens the quantitative
parameters, root bounds, endpoint analysis, and characteristic limitations.

## What ArkLib Uses From This Paper

- the no-band weighted-support construction, with the finite-cover alternative retained separately;
- the order-zero proof for gaps at least one quarter;
- derivative order `ceil(exp(2.7 / delta))`, surplus greater than `543/500`, and height below `12 nu`;
- primitive, separant, resonance, and exact local-rank refinements;
- exact-capacity and inverse-gap lower bounds;
- the linearly-growing-characteristic extension and Frobenius-plane obstruction.

## Main ArkLib Touchpoints

- `ArkLib/Data/CodingTheory/ReedSolomon/ListDecodability/Capacity/Basic.lean`
- `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/`
- `ArkLib/Data/CodingTheory/ReedSolomon/ListDecodability/Capacity.lean`
- `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Capacity.lean`
- `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Capacity/PrescribedLine.lean`

## Version Notes

The original source record pins private manuscript commit
`9e4d6488ead94be47cca69e5be915b5667143b66`. The current no-band revision follows the audited
September 6, 2026 revision plan beside the manuscript. The older asymmetric-band route and
its constants have been replaced; source metadata preserves the original provenance.

## Scope

The mathematical owners expose exact lists and line, affine-space, and polynomial-curve MCA.
The executable endpoint uses the same weighted-support parameters and bounds its existing
primitive-work model. Whole-protocol soundness and a whole-decoder bit/RAM bound are outside
this revision. Historical decoder development is recorded in the
[algebraic-machine plan](../../design/rs-algebraic-machine-plan.md).

## Source Access

- Source metadata: [`../sources/DKTZ26/metadata.yml`](../sources/DKTZ26/metadata.yml)
- The source repository is private; the pinned commit is recorded above for authorized collaborators.
