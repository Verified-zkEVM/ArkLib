# Polishchuk-Spielman Lineage

This page is the KB hub for the Polishchuk-Spielman lemma and its source lineage in ArkLib.

## Scope

Use this page when a task is about:

- the Polishchuk-Spielman lemma itself;
- the difference between the original and corrected statement;
- the Reed-Solomon decoding context that motivates the lemma;
- finding the right ArkLib files for the supporting algebra.

## Core References

- [`../papers/PS94.md`](../papers/PS94.md) - original historical source lineage.
- [`../papers/Spi95.md`](../papers/Spi95.md) - thesis/book source in the same original lineage.
- [`../papers/BCIKS20.md`](../papers/BCIKS20.md) - corrected statement lineage used by ArkLib.

## Main ArkLib Touchpoints

- [`../../../ArkLib/Data/CodingTheory/PolishchukSpielman/PolishchukSpielman.lean`](../../../ArkLib/Data/CodingTheory/PolishchukSpielman/PolishchukSpielman.lean)
  - final theorem statement and provenance note.
- [`../../../ArkLib/Data/CodingTheory/PolishchukSpielman/Degrees.lean`](../../../ArkLib/Data/CodingTheory/PolishchukSpielman/Degrees.lean)
  - degree and evaluation lemmas.
- [`../../../ArkLib/Data/CodingTheory/PolishchukSpielman/Resultant.lean`](../../../ArkLib/Data/CodingTheory/PolishchukSpielman/Resultant.lean)
  - resultant and Sylvester-matrix support.
- [`../../../ArkLib/Data/CodingTheory/PolishchukSpielman/Existence.lean`](../../../ArkLib/Data/CodingTheory/PolishchukSpielman/Existence.lean)
  - existence and cancellation lemmas.

## Notes

- ArkLib follows the corrected statement path rather than the original flawed version.
- This is a good review entry point when a PR touches the `PolishchukSpielman` subtree.
