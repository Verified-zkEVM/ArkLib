---
kind: paper
bibkey: BSS08
title: "Short PCPs with polylog query complexity"
year: 2008
bib_source: blueprint/src/references.bib
canonical_url: https://people.csail.mit.edu/madhu/papers/2005/rspcpp-full.pdf
source_metadata: ../sources/BSS08/metadata.yml
status: seeded
related_modules:
---

# BSS08

## At A Glance

`BSS08` is a historical folding/division reference used in ArkLib's STIR folding development.
It appears as supporting background rather than as the main protocol paper.

## What ArkLib Uses From This Paper

- A source for the proposition-level polynomial identities that STIR reuses.

## Main ArkLib Touchpoints


## Version Notes

- Although this is not the main STIR paper, it is part of the proof lineage for the folding layer
  currently being formalized.

## Known Divergences From ArkLib

- ArkLib reaches the relevant constructions through Mathlib's multivariate polynomial and Groebner
  tooling instead of mirroring the original exposition directly.

## Open Formalization Gaps

- The STIR folding file still contains substantial proof gaps, so this paper currently supports
  partial formalization rather than a finished verified layer.

## Source Access

- Source metadata: [`../sources/BSS08/metadata.yml`](../sources/BSS08/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
