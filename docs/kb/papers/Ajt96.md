---
kind: paper
bibkey: Ajt96
title: "Generating hard instances of lattice problems (extended abstract)"
year: "1996"
bib_source: blueprint/src/references.bib
source_metadata: ../sources/Ajt96/metadata.yml
status: seeded
related_modules:
  - ArkLib/Data/Lattices/ModuleSIS.lean
  - ArkLib/CommitmentScheme/Ajtai/Simple/Scheme.lean
  - ArkLib/CommitmentScheme/Ajtai/Simple/Security.lean
---

# Ajt96

## At A Glance

`Ajt96` is Ajtai's STOC paper introducing the Short Integer Solution (SIS) problem and the
worst-case-to-average-case connection that underpins the SIS-based commitment used by ArkLib's
Ajtai commitments.

## What ArkLib Uses From This Paper

- The SIS hardness assumption, specialized to the module setting over the cyclotomic ring as
  `ModuleSIS` (find a nonzero short `z` with `A *ᵥ z = 0`).
- The Ajtai commitment idea (`commit A s = A *ᵥ s`) whose binding reduces to SIS.

## Main ArkLib Touchpoints

- [`ArkLib/Data/Lattices/ModuleSIS.lean`](../../../ArkLib/Data/Lattices/ModuleSIS.lean) — the
  Module-SIS search game.
- [`ArkLib/CommitmentScheme/Ajtai/Simple/Security.lean`](../../../ArkLib/CommitmentScheme/Ajtai/Simple/Security.lean)
  — binding reduces to Module-SIS.

## Open Formalization Gaps

- This is a lightweight landing page; the worst-case-to-average-case reduction itself is not
  formalized (ArkLib targets the average-case Module-SIS assumption directly).

## Source Access

- Source metadata: [`../sources/Ajt96/metadata.yml`](../sources/Ajt96/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
