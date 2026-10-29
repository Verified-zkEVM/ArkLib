---
kind: paper
bibkey: Spi95
title: "Computationally efficient error-correcting codes and holographic proofs"
year: 1995
bib_source: blueprint/src/references.bib
source_metadata: ../sources/Spi95/metadata.yml
status: seeded
related_modules:
  - ArkLib/Data/CodingTheory/PolishchukSpielman/PolishchukSpielman.lean
  - ArkLib/Data/CodingTheory/PolishchukSpielman
---

# Spi95

## At A Glance

`Spi95` is the second historical source cited by ArkLib for the Polishchuk-Spielman lemma lineage.
Like `PS94`, it matters in the repository mostly as provenance and as part of the explanation for
why the corrected statement is used instead of the original formulation.

## What ArkLib Uses From This Paper

- Historical source lineage for the Polishchuk-Spielman divisibility criterion.
- Context for the flaw noted in the original statement lineage and the need for the corrected
  version used in ArkLib.

## Main ArkLib Touchpoints

- [`ArkLib/Data/CodingTheory/PolishchukSpielman/PolishchukSpielman.lean`](../../../ArkLib/Data/CodingTheory/PolishchukSpielman/PolishchukSpielman.lean)
  cites `Spi95` directly and explicitly notes the flaw in the original statement.
- The auxiliary files in
  [`ArkLib/Data/CodingTheory/PolishchukSpielman`](../../../ArkLib/Data/CodingTheory/PolishchukSpielman)
  are the main code-level context for this reference.

## Version Notes

- ArkLib records `Spi95` together with `PS94` as part of the original statement lineage.
- The repo docstring explicitly points readers to `BCIKS20` for the corrected version of the lemma.

## Known Divergences From ArkLib

- ArkLib intentionally does not formalize the original flawed statement as-is.
- The current proof organization is shaped by the corrected version and by reusable algebraic helper
  lemmas.

## Open Formalization Gaps

- This landing page should be read together with [`PS94.md`](PS94.md) and
  [`BCIKS20.md`](BCIKS20.md).
- Add a dedicated audit page if later work needs a more explicit provenance map from the original
  sources to the corrected theorem now formalized.

## Source Access

- Source metadata: [`../sources/Spi95/metadata.yml`](../sources/Spi95/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
