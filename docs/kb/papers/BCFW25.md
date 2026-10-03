---
kind: paper
bibkey: BCFW25
title: "Linear time accumulation schemes"
year: "2025"
bib_source: blueprint/src/references.bib
canonical_url: https://eprint.iacr.org/2025/753
source_metadata: ../sources/BCFW25/metadata.yml
status: investigated
related_concepts:
  - reed-solomon-proximity
related_modules:
  - ArkLib/Data/CodingTheory/ExtensionCodes.lean
  - ArkLib/OracleReduction/Security/RoundByRound.lean
  - ArkLib/Interaction/Oracle/Claim.lean
---

# BCFW25

## At A Glance

`BCFW25` is Bünz–Chiesa–Fenzi–Wang, *Linear-Time Accumulation Schemes*, ePrint 2025/753.
Its subject is accumulation (proof-carrying data) with a linear-time accumulation prover.

The directly formalized result is `BCFW25` **Lemma D.3**, the statement that an extension code
has the same list size as the interleaved base code, which `ABF26` restates as Lemma 2.21.
The paper's WARP knowledge framework also provides a close structural precedent for ArkLib's
witness-indexed states and backward extraction. This does not mean that the accumulation
scheme or its compiler theorem has been formalized.

## What ArkLib Uses From This Paper

- **Definitions 4.1-4.2 and Appendix B.** These guide the proposed native relational RBR
  package. The [source crosswalk](../audits/interaction-literature-map.md#arc-warp-and-the-librarys-actual-knowledge-notion)
  records the fixed-prefix bad event, endpoint laws, extractor observations and computational
  requirements. The code explicitly cites ABF26 A.5; a structural match to WARP does not by
  itself establish historical authorship of a code change. Appendix C's comparison carries
  an extractor-consistency premise and is not an unconditional equivalence.
- **Lemma D.3 (extension-code list size).** Formalized as
  `CodingTheory.lambda_extensionCode_eq_lambda_interleaved`:
  `Λ(C_F, δ) = Λ(C_B^{⋈e}, δ)`, both sides being `ListDecodability.Lambda` (the sup over centers),
  both normalized by the block length `n` — never by `n·e`. The proof is a genuine blockwise
  isometry: `Equiv.piCongrRight (fun _ ↦ φ)` combined with Mathlib's `hammingDist_comp`.
- **§D.2's extension-field presentation setup**, which `ABF26` Definition 2.19 packages and ArkLib
  implements as `CodingTheory.ExtensionFieldPresentation` (`ψ = algebraMap`, `φ = basis.equivFun`,
  `e = Module.finrank B F`), together with the notion of a *systematic* presentation
  (`IsSystematic`).

## Main ArkLib Touchpoints

- [Legacy security](../../../ArkLib/OracleReduction/Security/RoundByRound.lean): `WitMid`,
  `extractMid`, `KnowledgeStateFunction`, and fixed-prefix versus averaged games.
- [Native claims](../../../ArkLib/Interaction/Oracle/Claim.lean) and
  [prefixes](../../../ArkLib/Interaction/Oracle/Prefix.lean): target carriers for the
  [proposed backward-extraction experiment](../../design/05-roadmap.md#bounded-interaction-theory-investigation).
- [`ArkLib/Data/CodingTheory/ExtensionCodes.lean`](../../../ArkLib/Data/CodingTheory/ExtensionCodes.lean)
  — `ExtensionFieldPresentation`, `IsSystematic`, `extensionEncode`, its `F`-linear-map packaging,
  systematic identity and range bridge, `extensionCode` / `extensionCodeSubmodule`, presentation
  independence, DP25 distance preservation, and `lambda_extensionCode_eq_lambda_interleaved`.

## Version Notes

- **Key normalization.** The coding-theory key is `BCFW25`; `WARP` is an existing bibliography
  alias for the same paper, with this page as its shared landing page. Do not use `BuenzCFW25`.
  A citation key with
  no `references.bib` entry makes `scripts/kb/extract_lean_citations.py` drop the entire citing
  file from the citation map, so a single bad spelling silently loses a file's whole citation
  record. The same applies to the Diamond–Posen result cited alongside it, which is `DP25`.
- Tracked as ePrint 2025/753. Two reference copies exist locally:
  `~/abf26-refs/bcfw25.pdf` (build date 2025-05-28) and `~/abf26-refs/BuenzCFW25.pdf` (build date
  2026-06-18). Appendix numbering (`D.2`, `D.3`) was checked against the later copy. Note the
  PDF title is *Linear-Time Accumulation Schemes*; the BibTeX `title` field is unhyphenated.
- The October 3, 2026 interaction audit inspected the 76-page revision with a June 17, 2026
  cover date and June 18, 2026 ePrint metadata. Its exact PDF hash is in the source metadata.

## Known Divergences From ArkLib

- **The `δ ∈ (0,1)` window is not enforced, and need not be.** Lemma D.3 is true at `δ = 0` and
  `δ ≥ 1` as well; the isometry argument never uses the window. Accordingly
  `lambda_extensionCode_eq_lambda_interleaved` carries no hypothesis on `δ`.
- **Both the encoder and image formulations are present.** `extensionEncode` states D2.20 at
  encoder level and `extensionEncodeLinearMap` proves that it is the asserted `F`-linear code map;
  `extensionEncode_comp_algebraMap` proves the §D.2 identity `C_F(ψ ∘ v) = ψ ∘ C_B(v)`, and
  `range_extensionEncode` connects its image to `extensionCode`. The image-level form
  `mem_extensionCode_comp_algebraMap_iff` is retained as a reusable consequence.
- **The §D.2 identity does not need a systematic presentation.** Both statements above are
  proved for an *arbitrary* presentation, where the printed remark (and ABF26's remark after
  D2.20) assumes systematicity. The mechanism: `φ_j(ψ x) = x · φ_j(1)` for every `j`, so the
  `j`-th coordinate row of an embedded message is the rescaling `φ_j(1) • v`, and `B`-linearity
  of the base encoder moves that scalar through `encode`; the reverse direction rescales by
  `φ_j(1)⁻¹` at any `j` with `φ_j(1) ≠ 0`, and one exists because `1 ≠ 0` in `F`.
  Systematicity only specialises the scalars to `(1, 0, …, 0)`. `IsSystematic` is kept for
  fidelity to the source, with no consumer.
- **The extension code provably does not depend on the presentation.**
  `extensionCodeSubmodule P C_B = Submodule.span F ((fun c i ↦ algebraMap B F (c i)) '' C_B)`
  (compiled), from which `extensionCode P C_B = extensionCode P' C_B` for any two presentations
  `P`, `P'`. So the `ExtensionFieldPresentation` apparatus is optional for Definition 2.20, and
  the long hand proof of `F`-scalar closure (`extensionCode_smul_mem`) is a one-liner from
  `Submodule.span`. These facts are exposed as `extensionCode_eq_span` and
  `extensionCode_presentation_independent`.
- **Mathlib overlaps, resolved.** `ExtensionFieldPresentation.coord` is a `noncomputable abbrev`
  for `Module.Basis.coord`, with `coord_eq_basis_coord` as the `rfl` witness, so the "no parallel
  implementation" claim now holds for `coord` as well as for `ψ` (`algebraMap`, injective by
  `FaithfulSMul.algebraMap_injective`) and `φ` (`Basis.equivFun`). Additivity and `B`-linearity
  of the coordinate maps are Mathlib's `map_add`/`map_smul` on the underlying `LinearMap`; no
  ArkLib restatements exist or are needed.
- The statement uses `Code.interleavedCodeSet` raw rather than the equivalent `C ^⋈ κ` notation;
  the underlying object is the right one, so this is cosmetic.

## Open Formalization Gaps

- **The accumulation scheme itself remains unformalized.** The linear-time accumulation
  prover and its security have no completed ArkLib counterpart. The Appendix D coding result
  and the structural knowledge-state precedent should be distinguished from such a theorem.
  Accumulation would require development at the `ProofSystem`/`Commitments` layer.
- **A native WARP specialization remains proposed.** ArkLib permits witness transformations
  and has a weaker one-way terminal clause; its legacy API also omits the source's extraction
  time accounting. These differences require explicit bridge theorems.

## Source Access

- Source metadata: [`../sources/BCFW25/metadata.yml`](../sources/BCFW25/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
