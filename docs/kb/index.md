# Knowledge Base Index

This is the main catalog for ArkLib's knowledge base.

## Generated Registries

- [`_generated/references.json`](_generated/references.json) - normalized export of
  `blueprint/src/references.bib`.
- [`_generated/lean-citations.json`](_generated/lean-citations.json) - generated map from
  `ArkLib/**/*.lean` to cited BibTeX keys.

## Paper Pages

- [`papers/ABF26.md`](papers/ABF26.md) - *Open Problems in List Decoding and Correlated Agreement*,
  the primary source for the coding-theory foundations: §2 preliminaries, the §2.4 code families,
  the §3.1 Johnson family, subspace designs, and extension codes.
- [`papers/ACFY24.md`](papers/ACFY24.md) - WHIR ePrint paper and its ArkLib touchpoints in
  `ReedSolomon`, `ListDecodability`, and `ProximityGap`.
- [`papers/ACFY24stir.md`](papers/ACFY24stir.md) - STIR paper page for the active
  `ProofSystem/Stir` development.
- [`papers/BCFW25.md`](papers/BCFW25.md) - cited only for Lemma D.3 (extension-code list size);
  none of the accumulation machinery is used.
- [`papers/BCIKS20.md`](papers/BCIKS20.md) - proximity gaps for Reed-Solomon codes and the main
  coding-theory formalization it drives in ArkLib.
- [`papers/BCGM25.md`](papers/BCGM25.md) - polynomial-generator MCA and related ArkLib
  proximity-generator infrastructure.
- [`papers/BCS16.md`](papers/BCS16.md) - original IOP reference used by the core oracle-reduction
  layer.
- [`papers/BBS24.md`](papers/BBS24.md) - formal verification reference for sum-check.
- [`papers/DG25.md`](papers/DG25.md) - interleaved-code proximity gaps and the DG25 formalization
  subtree.
- [`papers/DP24.md`](papers/DP24.md) - binary-tower multilinear proof reference for the Binius
  development.
- [`papers/DP25.md`](papers/DP25.md) - Theorem 3.2, the minimum-distance equality between a base
  code and its extension code.
- [`papers/GG25.md`](papers/GG25.md) - Lemma 2.16 (= `ABF26` Lemma 2.17), the distance lower bound
  for subspace-design codes.
- [`papers/GK16.md`](papers/GK16.md) - explicit subspace designs; Definition 11 and Lemma 12 supply
  the folded-Wronskian criterion behind `ABF26` Theorem 2.18.
- [`papers/GR08.md`](papers/GR08.md) - Definition 2.1, the definitional source for folded
  Reed-Solomon codes.
- [`papers/GW13.md`](papers/GW13.md) - linear-algebraic list decoding; origin of the univariate
  multiplicity codes (ordinary derivative, large characteristic).
- [`papers/GX13.md`](papers/GX13.md) - definitional lineage for the `τ`-subspace-design property.
- [`papers/HMZ25.md`](papers/HMZ25.md) - sublinear proofs over polynomial rings and the generic
  `Lift` quotient-evaluation switch.
- [`papers/Jo26.md`](papers/Jo26.md) - interleaving stability for generator MCA and curve
  decodability.
- [`papers/Joh62.md`](papers/Joh62.md) - the original Johnson bound underlying the `JohnsonBound`
  development.
- [`papers/KSY14.md`](papers/KSY14.md) - high-rate codes with sublinear-time decoding; the
  multiplicity-code analysis, whose Hasse-derivative variant differs from `ABF26` Definition A.6.

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
- [`audits/noz26-subfield-lemmas5-6.md`](audits/noz26-subfield-lemmas5-6.md)
  - Hachi §3 Lemmas 5–6 paper-to-Lean audit, including the remaining Lemma 5 factor-swap gap
    and the completed Lemma 6 norm proof.
- [`audits/noz26-zero-check-lemma10.md`](audits/noz26-zero-check-lemma10.md)
  - Hachi Figure 5 / Lemma 10 paper-to-Lean audit; the nested-tree repair and the weak-binding
    seam as integrated into the escape-threaded opening chain.
- [`audits/bciks20-appendix-a-rational-functions.md`](audits/bciks20-appendix-a-rational-functions.md)
  - status matrix for the rational-function and Hensel-lifting layer used by `BCIKS20`.
- [`audits/open-problems-list-decoding-and-correlated-agreement.md`](audits/open-problems-list-decoding-and-correlated-agreement.md)
  - detailed paper-to-ArkLib matrix for *Open Problems in List Decoding and Correlated Agreement*
    (dated April 8, 2026).

## Query Pages

- [`queries/README.md`](queries/README.md) - purpose and filing rules for persistent query outputs.
- [`queries/abf26-split-pr1-review-2026-08-07/README.md`](queries/abf26-split-pr1-review-2026-08-07/README.md)
  - adversarial review record for the `ABF26` coding-theory foundations, including the per-area
    `R*` reports, the remediation log, and the declaration provenance snapshot.
- [`queries/abf26-split-pr1-deep-review-2026-08-11/README.md`](queries/abf26-split-pr1-deep-review-2026-08-11/README.md)
  - later, broader pre-merge review of the same PR at its final head: gate results, findings, the
    remediation applied, and the source-side defects found along the way.

## Source Metadata

- [`sources/README.md`](sources/README.md) - source artifact policy and metadata layout.
