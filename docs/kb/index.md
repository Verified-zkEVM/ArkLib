# Knowledge Base Index

This is the main catalog for ArkLib's knowledge base.

## Generated Registries

- [`_generated/references.json`](_generated/references.json) - normalized export of
  `blueprint/src/references.bib`.
- [`_generated/lean-citations.json`](_generated/lean-citations.json) - generated map from
  `ArkLib/**/*.lean` to cited BibTeX keys.

## Paper Pages

- [`papers/ACFY24.md`](papers/ACFY24.md) - WHIR ePrint paper and its ArkLib touchpoints in
  `ReedSolomon` and `ProofSystem/Whir`.
- [`papers/ACFY24stir.md`](papers/ACFY24stir.md) - STIR paper page for the active
  `ProofSystem/Stir` development.
- [`papers/BCIKS20.md`](papers/BCIKS20.md) - proximity gaps for Reed-Solomon codes and the main
  coding-theory formalization it drives in ArkLib.
- [`papers/BCS16.md`](papers/BCS16.md) - original IOP reference used by the core oracle-reduction
  layer.
- [`papers/BBS24.md`](papers/BBS24.md) - formal verification reference for sum-check.
- [`papers/DP24.md`](papers/DP24.md) - binary-tower multilinear proof reference for the Binius
  development.

The paper index now also includes scaffolded landing pages for all other citation keys currently
used in `ArkLib/**/*.lean`, including:

- `AHIV22`, `BSS08`, `FRI1216`, `GWZC19`, `JM24`, `LFKN92`, `LPS24`, `PS94`, `Poseidon2`,
  `STIR2005`, `Spi95`, `codingtheory`, and `listdecoding`.

## Concept Pages

- [`concepts/interactive-oracle-proofs.md`](concepts/interactive-oracle-proofs.md) - how ArkLib's
  oracle-reduction abstractions relate to IOP terminology and references.
- [`concepts/polishchuk-spielman-lineage.md`](concepts/polishchuk-spielman-lineage.md) - corrected
  versus original source lineage for the Polishchuk-Spielman lemma in ArkLib.
- [`concepts/reed-solomon-proximity.md`](concepts/reed-solomon-proximity.md) - proximity gaps,
  WHIR/STIR context, and the main ArkLib coding-theory entry points.

## Audit Pages

- [`audits/README.md`](audits/README.md) - audit conventions and migration notes for paper-to-code
  comparison pages.
- [`audits/open-problems-list-decoding-and-correlated-agreement.md`](audits/open-problems-list-decoding-and-correlated-agreement.md)
  - detailed paper-to-ArkLib matrix for *Open Problems in List Decoding and Correlated Agreement*
    (dated April 8, 2026).

## Query Pages

- [`queries/README.md`](queries/README.md) - purpose and filing rules for persistent query outputs.

## Source Metadata

- [`sources/README.md`](sources/README.md) - source artifact policy and metadata layout.
