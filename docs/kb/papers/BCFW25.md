---
kind: paper
bibkey: BCFW25
title: "Linear time accumulation schemes"
year: "2025"
bib_source: blueprint/src/references.bib
canonical_url: https://eprint.iacr.org/2025/753
source_metadata: ../sources/BCFW25/metadata.yml
status: seeded
related_concepts:
  - reed-solomon-proximity
related_modules:
  - ArkLib/Data/CodingTheory/ExtensionCodes.lean
---

# BCFW25

## At A Glance

`BCFW25` is Bünz–Chiesa–Fenzi–Wang, *Linear-Time Accumulation Schemes*, ePrint 2025/753.
Its subject is accumulation (proof-carrying data) with a linear-time accumulation prover.

ArkLib uses **none of the accumulation machinery**. What it uses is a single coding-theory
ingredient from the appendix: `BCFW25` **Lemma D.3**, the statement that an extension code has the
same list size as the interleaved base code, which `ABF26` restates as its Lemma 2.21.

## What ArkLib Uses From This Paper

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

- [`ArkLib/Data/CodingTheory/ExtensionCodes.lean`](../../../ArkLib/Data/CodingTheory/ExtensionCodes.lean)
  — `ExtensionFieldPresentation`, `IsSystematic`, `extensionCode`, `extensionCodeSubmodule`,
  `lambda_extensionCode_eq_lambda_interleaved`.

## Version Notes

- **Key normalization.** PR #701 originally cited this paper in Lean as `BuenzCFW25`, a key with no
  BibTeX entry. Since the same file's other keys (`ABF26`, and a `DiamondP23` spelling) were also
  unknown at the time, `scripts/kb/extract_lean_citations.py` dropped
  `ExtensionCodes.lean` from the citation map entirely. The key is now **`BCFW25`**, which is also
  the spelling used by the ABF26 faithfulness audit. Use `BCFW25`; `BuenzCFW25` should not
  reappear.
- **Related key hygiene in the same file.** The docstring's `[DiamondP23, Theorem 3.2]` was a third
  spelling of Diamond–Posen, *Succinct Arguments over Towers of Binary Fields*, which the
  repository already keys twice (`DP23` for the 2023 ePrint, `DP25` for the EUROCRYPT '25 version)
  and which both `ABF26` and `BCFW25` cite as `DP25`. It now reads `DP25`.
- Tracked as ePrint 2025/753. Two reference copies exist locally:
  `~/abf26-refs/bcfw25.pdf` (build date 2025-05-28) and `~/abf26-refs/BuenzCFW25.pdf` (build date
  2026-06-18). Appendix numbering (`D.2`, `D.3`) was checked against the later copy. Note the
  PDF title is *Linear-Time Accumulation Schemes*; the BibTeX `title` field is unhyphenated.

## Known Divergences From ArkLib

- **The `δ ∈ (0,1)` window is not enforced, and need not be.** The statement is true at
  `δ = 0` and `δ ≥ 1` too (verified by re-proving it verbatim without the window). The 2026-08-07
  review found the headline theorem carrying `_hδ_pos`/`_hδ_lt` as unused hypotheses plus six
  unused instance binders behind two file-scope linter suppressions; all were removed in the
  same review's fix sweep — the current theorem carries no window hypotheses and no
  suppressions.
- **The systematic-presentation consequence is not expressible.** `BCFW25` §D.2 (and `ABF26`
  Definition 2.20) rely on `C_F(ψ(v)) = ψ(C_B(v))` for a systematic presentation — a statement
  about the **encoder** `F^k → F^n`. ArkLib models only the code *image* (`Set (ι → F)`), so this
  cannot be written down, and `IsSystematic` is defined but has zero consumers anywhere in the
  repository. The membership form ("`ψ ∘ c ∈ extensionCode` for `c ∈ C_B`") is *not* a faithful
  stand-in, because it holds without systematicity.
- **The extension code provably does not depend on the presentation.**
  `extensionCodeSubmodule P C_B = Submodule.span F ((fun c i ↦ algebraMap B F (c i)) '' C_B)`
  (compiled), from which `extensionCode P C_B = extensionCode P' C_B` for any two presentations
  `P`, `P'`. So the `ExtensionFieldPresentation` apparatus is optional for Definition 2.20, and
  the long hand proof of `F`-scalar closure (`extensionCode_smul_mem`) is a one-liner from
  `Submodule.span`. This is the mathematically informative fact about the construction and it is
  currently invisible in the tree.
- **Mathlib overlaps.** `ExtensionFieldPresentation.coord` re-derives `Module.Basis.coord`;
  `φ` is `Basis.equivFun` (`rfl`); `ψ_injective` is `FaithfulSMul.algebraMap_injective`;
  `coord_add`/`coord_psi_smul` are `map_add`/`map_smul`. The module docstring's "no parallel
  implementation" claim is accurate for `ψ` and `φ` but not for `coord`.
- **Docstring shape mismatch.** The module and Definition-2.20 docstrings describe `extensionCode`
  as "the extension code `C_F : F^k → F^n`"; it is a `Set (ι → F)`, and `k` never appears in the
  module. Same encoder-versus-image gap as above.
- The statement uses `Code.interleavedCodeSet` raw rather than the equivalent `C ^⋈ κ` notation;
  the underlying object is the right one, so this is cosmetic.

## Open Formalization Gaps

- **The accumulation scheme itself is entirely unformalized.** BCFW25's actual results — the
  linear-time accumulation prover, its security — have no ArkLib counterpart. Only the Appendix D
  coding-theory lemma is used, and adding accumulation would be a new development at the
  `ProofSystem`/`Commitments` layer, not an extension of this module.
- An **encoder-level extension code** (`extensionEncode : (Fin k → F) → (ι → F)` built from a base
  encoder) plus the systematic consequence
  `IsSystematic → extensionEncode (ψ ∘ v) = ψ ∘ baseEncode v`.
  Without it `IsSystematic` should arguably be dropped.
- The presentation-independence bridge (`extensionCode_eq_span`) and the resulting simplification
  of `extensionCodeSubmodule`'s closure proofs.
- `δ_min(C_F) = δ_min(C_B)`, which `ABF26` §2.6 attributes to Diamond–Posen (`DP25`), is not
  formalized and the tree does not claim it.
- `ExtensionCodes.lean` has no in-repo consumers other than the generated import in `ArkLib.lean`.

## Source Access

- Source metadata: [`../sources/BCFW25/metadata.yml`](../sources/BCFW25/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
