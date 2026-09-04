# Knowledge Base Index

This is the main catalog for ArkLib's knowledge base. Every BibTeX key cited from `ArkLib/` has a
page under [`papers/`](papers/README.md); that directory, not this list, is the authoritative set.

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
- [`papers/BCPZZ26.md`](papers/BCPZZ26.md) - low-rate capacity-achieving Reed–Solomon list
  decoding, its hidden-derivative interpolation method, and the central formalization target.
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
- [`papers/Kop15.md`](papers/Kop15.md) - polynomial differential-equation root finding and the
  exact candidate bound used by the low-rate Reed–Solomon decoder.

- [`papers/AHIV22.md`](papers/AHIV22.md) - Ligero-family interleaved-code and affine-line proximity
  statements, secondary to the `BCIKS20` development.
- [`papers/Ajt96.md`](papers/Ajt96.md) - the Short Integer Solution problem underpinning ArkLib's
  Ajtai commitments.
- [`papers/BSS08.md`](papers/BSS08.md) - the Reed-Solomon PCP-of-proximity paper; its bivariate
  division property backed the old STIR folding route, and is currently uncited.
- [`papers/CGKY25.md`](papers/CGKY25.md) - the ARSDH-style extraction argument behind the KZG
  function-binding reduction.
- [`papers/codingtheory.md`](papers/codingtheory.md) - *Essential Coding Theory*; classical
  background for the Johnson-bound layer, and the authority for the list-`ℓ` Johnson radius.
- [`papers/FMN24.md`](papers/FMN24.md) - the origin of coordinate-wise special soundness, the
  security notion of the Hachi development.
- [`papers/FRI1216.md`](papers/FRI1216.md) - the generalized FRI low-degree test, for the abstract
  protocol layer in `ProofSystem/Fri`.
- [`papers/GWZC19.md`](papers/GWZC19.md) - Plonk, for the Plonk entry-point module.
- [`papers/JM24.md`](papers/JM24.md) - AGM/GGM transfer context for the algebraic-group-model
  development.
- [`papers/KZG10.md`](papers/KZG10.md) - the KZG polynomial commitment construction.
- [`papers/KZG10TR.md`](papers/KZG10TR.md) - the extended KZG report, cited for the
  evaluation-binding proof the conference version omits.
- [`papers/LFKN92.md`](papers/LFKN92.md) - the classical sum-check reference for
  `ProofSystem/Sumcheck`.
- [`papers/listdecoding.md`](papers/listdecoding.md) - list-decoding background for the
  alphabet-free framing of the Johnson-bound layer.
- [`papers/LNP22.md`](papers/LNP22.md) - the lattice zero-knowledge framework whose
  power-of-two cyclotomic ring setting `Data/Lattices/CyclotomicRing/` constructs.
- [`papers/LPS24.md`](papers/LPS24.md) - AGM reasoning connected back to Plonk knowledge
  soundness.
- [`papers/LS18.md`](papers/LS18.md) - invertibility of short nonzero elements of
  `Z_q[X]/(X^d+1)`, which is what makes the lattice relaxation factors work.
- [`papers/Mic07.md`](papers/Mic07.md) - the ring product norm inequality behind the
  norm-growth bound in the weak-binding argument.
- [`papers/NOZ26.md`](papers/NOZ26.md) - Hachi, the lattice multilinear polynomial commitment
  formalized under `Commitments/Functional/Hachi/`.
- [`papers/NS24.md`](papers/NS24.md) - Greyhound, the inner/outer Ajtai commitment composition
  and its weak-binding reduction to Module-SIS.
- [`papers/Poseidon2.md`](papers/Poseidon2.md) - the Poseidon2 hash, translated over `KoalaBear`.
- [`papers/PS94.md`](papers/PS94.md) - historical provenance for the Polishchuk-Spielman lemma.
- [`papers/Spi95.md`](papers/Spi95.md) - the second Polishchuk-Spielman source, and why ArkLib
  uses the corrected statement.

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
- [`audits/bcgm25-mca-generators.md`](audits/bcgm25-mca-generators.md)
  - `BCGM25` generator layer: definition and result correspondence, the two forms Lemma 4.4 is
    proved in and why, and a gap in the paper's Theorem 9.2 citation.
- [`audits/open-problems-list-decoding-and-correlated-agreement.md`](audits/open-problems-list-decoding-and-correlated-agreement.md)
  - detailed paper-to-ArkLib matrix for *Open Problems in List Decoding and Correlated Agreement*
    (dated April 8, 2026).
- [`audits/bcpzz26-main-theorem.md`](audits/bcpzz26-main-theorem.md) - clause-by-clause audit of
  the published corollary, parametric contract architecture, and confirmed source repairs.

## Source Metadata

- [`sources/README.md`](sources/README.md) - source artifact policy and metadata layout.
