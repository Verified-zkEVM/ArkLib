---
kind: paper
bibkey: Mic07
title: "Generalized compact knapsacks, cyclic lattices, and efficient one-way functions"
year: "2007"
bib_source: blueprint/src/references.bib
source_metadata: ../sources/Mic07/metadata.yml
status: seeded
related_modules:
  - ArkLib/Data/Lattices/CyclotomicRing/NormBounds/MicciancioYoung.lean
---

# Mic07

## At A Glance

`Mic07` is Micciancio's paper on cyclic/ideal lattices and compact one-way functions. ArkLib
cites it for the ring product norm inequality `‖f·g‖ ≤ ‖f‖₁ · ‖g‖` over the cyclic convolution,
the analytic core of the norm-growth bound in the weak-binding argument.

## What ArkLib Uses From This Paper

- The convolution product norm inequality used to bound `‖(c·d)·v‖₂²` from `‖d‖₁` and `‖c·v‖₂²`.

## Main ArkLib Touchpoints

- [`ArkLib/Data/Lattices/CyclotomicRing/NormBounds/MicciancioYoung.lean`](../../../ArkLib/Data/Lattices/CyclotomicRing/NormBounds/MicciancioYoung.lean)
  — the product norm-growth bound `scalarVecMul_mul_l2NormSq_le`.

## Open Formalization Gaps

- `scalarVecMul_mul_l2NormSq_le` is currently deferred (`sorry`): the discrete Cauchy–Schwarz
  bound over the cyclic convolution is not yet formalized.

## Source Access

- Source metadata: [`../sources/Mic07/metadata.yml`](../sources/Mic07/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
