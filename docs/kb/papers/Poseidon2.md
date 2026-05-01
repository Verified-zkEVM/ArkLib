---
kind: paper
bibkey: Poseidon2
title: "Poseidon2: A Faster Version of the Poseidon Hash Function"
year: 2023
bib_source: blueprint/src/references.bib
canonical_url: https://eprint.iacr.org/2023/323
source_metadata: ../sources/Poseidon2/metadata.yml
status: seeded
related_modules:
  - ArkLib/Data/Hash/Poseidon2.lean
---

# Poseidon2

## At A Glance

`Poseidon2` is ArkLib's reference for the Poseidon2 hash function.
The current repository usage is implementation-oriented: a Lean translation of a reference
implementation over the `KoalaBear` field.

## What ArkLib Uses From This Paper

- The hash-function specification context for
  [`ArkLib/Data/Hash/Poseidon2.lean`](../../../ArkLib/Data/Hash/Poseidon2.lean).
- Parameter and implementation background for the translated reference constants and round
  structure.

## Main ArkLib Touchpoints

- [`ArkLib/Data/Hash/Poseidon2.lean`](../../../ArkLib/Data/Hash/Poseidon2.lean) is the current
  landing module and cites `Poseidon2` directly.

## Version Notes

- The module docstring says the current Lean code is a translation of the reference Python
  implementation from `leanEthereum/leanSpec`, not a fresh derivation from the paper alone.
- Reviewers should therefore consider both the paper and the upstream implementation lineage.

## Known Divergences From ArkLib

- The current file is a reference implementation translation, not yet a proof-oriented theory file.
- ArkLib presently uses a concrete base field and hard-coded constants rather than a maximally
  abstract hash-function interface.

## Open Formalization Gaps

- If Poseidon2 becomes security-critical for later protocol work, add an audit page separating
  paper-level claims from implementation-level translation choices.

## Source Access

- Source metadata: [`../sources/Poseidon2/metadata.yml`](../sources/Poseidon2/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
