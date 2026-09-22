---
kind: paper
bibkey: KSY14
title: "High-rate codes with sublinear-time decoding"
year: "2014"
bib_source: blueprint/src/references.bib
source_metadata: ../sources/KSY14/metadata.yml
status: seeded
related_concepts:
  - reed-solomon-proximity
related_modules:
  - ArkLib/Data/CodingTheory/ReedSolomon/Multiplicity.lean
---

# KSY14

## At A Glance

`KSY14` is Kopparty–Saraf–Yekhanin, *High-rate codes with sublinear-time decoding*, Journal of
the ACM **61**(5) (2014), article 28 (preliminary version in STOC '11).
It introduced **multiplicity codes** and gave the first high-rate locally decodable codes, and it
is the standard detailed reference for their parameters.

For ArkLib it is the second attribution key on **univariate multiplicity codes**: `ABF26`
Definition A.7 is tagged `[GW13, KSY14]`, with `KSY14` supplying the detailed analysis and
[`GW13.md`](GW13.md) the list-decoding variant framing. `ReedSolomon.Multiplicity.umCode` is the
Lean transcription.

## What ArkLib Uses From This Paper

- Only the **univariate multiplicity code definition** as restated in `ABF26` Definitions A.6 and
  A.7: encode `f̂ ∈ F[X]_{<k}` at each evaluation point by the tuple of its first `s` iterated
  derivatives. Formalized as `ReedSolomon.Multiplicity.umEvalOnPoints` / `umCode`.
- No KSY14 theorem is formalized. In particular the paper's own subject — local decodability and
  sublinear-time decoding — has no ArkLib counterpart, and the multivariate multiplicity codes it
  is really about are not modelled at all (ArkLib has only the univariate case).

## Main ArkLib Touchpoints

- [`ArkLib/Data/CodingTheory/ReedSolomon/Multiplicity.lean`](../../../ArkLib/Data/CodingTheory/ReedSolomon/Multiplicity.lean)
  — `umEvalOnPoints`, `umCode`, `mem_umCode_one_iff_mem_rsCode`.

## Version Notes

- The BibTeX entry is the journal version (JACM 61(5), 2014); the `note` field records that a
  preliminary version appeared in STOC '11. The reference copy in
  `~/abf26-refs/KoppartySY14.pdf` is the **2010 preprint**, so its statement numbering matches
  neither the STOC nor the JACM version.
- Because ArkLib cites `GW13` and `KSY14` jointly for a *definition* — as `ABF26` Definition A.7
  itself does — no ArkLib statement pins a KSY14 theorem number, and the version discrepancy is
  harmless. If a future ArkLib result cites a specific KSY14 parameter bound, pin the JACM
  numbering.

## Known Divergences From ArkLib

- **Ordinary derivatives, not Hasse derivatives, and only because the source says so.** `ABF26`
  Definition A.6 specifies the *ordinary* iterated formal derivative under the global side
  condition `char F ≥ k`, and ArkLib transcribes exactly that (`Polynomial.derivative^[j]`). This
  is deliberate and correct for the source being formalized: it is not a small-characteristic bug,
  and it does not duplicate Mathlib's `Polynomial.hasseDeriv`.
  Treatments of multiplicity codes that must work in small characteristic use Hasse derivatives
  (or divide by `j!`); ArkLib's transcription is licensed *only* by `char F ≥ k`, which is recorded
  in the module docstring rather than baked into the definition. Any development that drops that
  condition has to switch derivative notions and re-prove the degree/multiplicity facts.
- **Univariate only.** KSY14's multiplicity codes are multivariate; ArkLib's `umCode` is the
  univariate specialisation that `ABF26` §A.2 uses.
- ArkLib models the code as an image submodule over an abstract `domain : ι ↪ F` rather than over
  KSY14's concrete point sets, and carries no locality or query-complexity data.

## Open Formalization Gaps

- **Minimum distance of `umCode` is unproved.** Its exact saturated dimension is
  `dim_umCode_eq_min`, and `CodingTheory.isSubspaceDesign_umCode` is now a substantive
  in-repo consumer proving the univariate-multiplicity half of ABF26 Theorem 2.18 via GK16's
  classical Wronskian argument.
- KSY14's actual results — local decodability, sublinear-time decoding, the high-rate LDC
  parameters — are entirely out of scope, and there is no ArkLib abstraction for local decoding to
  hang them on.

## Source Access

- Source metadata: [`../sources/KSY14/metadata.yml`](../sources/KSY14/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
