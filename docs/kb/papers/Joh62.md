---
kind: paper
bibkey: Joh62
title: "A new upper bound for error-correcting codes"
year: "1962"
bib_source: blueprint/src/references.bib
source_metadata: ../sources/Joh62/metadata.yml
status: seeded
related_concepts:
  - reed-solomon-proximity
related_modules:
  - ArkLib/Data/CodingTheory/JohnsonBound/Family.lean
---

# Joh62

## At A Glance

`Joh62` is Selmer M. Johnson, *A new upper bound for error-correcting codes*, IRE Transactions on
Information Theory **8**(3) (1962) 203–207 — the origin of the **Johnson bound**, the
double-counting argument that limits how many codewords of a distance-`d` code can lie inside a
single Hamming ball.

In ArkLib it is the attribution key for the paper-shaped, list-size-parameterised Johnson layer:
`ABF26` Definition 3.1's radius family and Theorem 3.2 are tagged `[Joh62]`, and both live in
`ArkLib/Data/CodingTheory/JohnsonBound/Family.lean`.

## What ArkLib Uses From This Paper

- The **Johnson bound itself**, in its list-size form: for any `C ⊆ Σ^n` with `|Σ| = q`,
  `|Λ(C, J_{q,ℓ}(δ_min(C)))| ≤ ℓ`. Formalized as
  `CodingTheory.johnson_bound_lambda_le_ell` (= `ABF26` Theorem 3.2).
- The **radius family** it induces: `CodingTheory.Jqℓ` (the `ℓ`-parameterised `q`-ary Johnson
  radius) and `JohnsonBound.Jcap` (`1 − √(1−δ)`), both from `ABF26` Definition 3.1.
- The **MDS corollary** `CodingTheory.mds_johnson_lambda_le` (= `ABF26` Corollary 3.3,
  `Λ(C, 1 − √ρ − η) ≤ 1/(2ηρ)`), and the complementary Plotkin regime
  `CodingTheory.plotkin_card_le_ell`.
- ArkLib does **not** follow Johnson's own derivation. The numeric core is
  `CodingTheory.johnson_card_le_ell`, the standard average-distance double counting, built on the
  pre-existing `JohnsonBound/Basic.lean` development.

## Main ArkLib Touchpoints

- [`ArkLib/Data/CodingTheory/JohnsonBound/Family.lean`](../../../ArkLib/Data/CodingTheory/JohnsonBound/Family.lean)
  — `Jqℓ`, `Jcap`, `johnson_bound_lambda_le_ell`, `mds_johnson_lambda_le`,
  `plotkin_card_le_ell`, `johnson_card_le_ell`.
- [`ArkLib/Data/CodingTheory/JohnsonBound/Basic.lean`](../../../ArkLib/Data/CodingTheory/JohnsonBound/Basic.lean)
  — the pre-existing `JohnsonBound.J`, `sqrt_le_J`, `johnson_bound`, `johnson_bound_lemma`, which
  `Family.lean` consumes rather than re-proves. That file cites `codingtheory` and `listdecoding`,
  not `Joh62`.

## Version Notes

**Which of the three Johnson-related keys to use.** `Joh62`, `codingtheory`, and `listdecoding`
all cover overlapping material, and the split is deliberate:

- **`Joh62`** — use for *attribution of the original bound*, i.e. on the paper-shaped statements
  in `JohnsonBound/Family.lean` that follow `ABF26` §3's packaging (`Jqℓ`,
  `johnson_bound_lambda_le_ell`, `mds_johnson_lambda_le`).
- **[`codingtheory`](codingtheory.md)** (Guruswami–Rudra–Sudan, *Essential Coding Theory*) — use
  for the *derivation you are actually transcribing*, and for classical background. It is also the
  authority for the `ℓ`-parameterised radius: **GRS12 Exercise 7.8 states `J_{q,ℓ}` with the
  `(ℓ−1)/ℓ` factor**, which is what settles `ABF26` Definition 3.1's printed `ℓ/(ℓ−1)` as a typo
  (see [`ABF26.md`](ABF26.md) Version Notes). This is the key `JohnsonBound/Basic.lean` uses.
- **[`listdecoding`](listdecoding.md)** — use for the alphabet-free / list-decodability framing in
  `JohnsonBound/Basic.lean`.

Do not add a fourth key for the same fact. `Joh62` has no `url`/DOI in the bibliography and no
local artifact in `~/abf26-refs/`; it is a 1962 IRE Transactions article, reachable through IEEE
Xplore.

## Validated ArkLib Status

- `Jqℓ` is defined through the pre-existing `J`, and `Jcap` lives beside `J`; the exported
  bridges recover the paper forms without a parallel radius hierarchy.
- `johnson_bound_lambda_le_ell` matches ABF26 Theorem 3.2 without a public radicand guard. Its
  proof splits internally between the Johnson and Plotkin regimes.
- The `ℓ = 0` false corner is excluded by the theorem's `2 ≤ ℓ` hypothesis, and the
  list-size-two specialization is documented as distinct from the binary Johnson radius.
- **The MDS corollary does not cover the paper's motivating class.** `ABF26` Corollary 3.3's
  preamble singles out interleaved Reed–Solomon codes; `mds_johnson_lambda_le` is stated for
  `LinearCode ι F` (field alphabet) only, and interleaved RS lives over the module alphabet `F^m`.
- `Lambda` uses `Set.encard`, so infinite lists contribute `⊤` rather than silently collapsing
  to zero. Finiteness assumptions remain exactly on bridges to the pre-existing
  `Set.ncard`-based `listDecodable` API and on finite numeric bounds.

## Open Formalization Gaps

- ~~Export `Jqℓ_eq_J` and `Jcap_le_J`, and reduce the three in-tree copies of the Johnson
  radius to one.~~ **Done.** `Jqℓ` is now *defined* as `J q (((ℓ-1)/ℓ) * δ)` with `Jqℓ_eq_J`
  as the (`rfl`) bridge and `Jqℓ_paper_form` recovering ABF26 Definition 3.1's printed shape;
  `Jcap` moved next to `J` in `JohnsonBound/Basic.lean`, and the pre-existing `sqrt_le_J` is
  now stated as `Jcap δ ≤ J q δ` — i.e. it *is* the `Jcap` bridge, so no separate
  `Jcap_le_J` is needed.
- ~~State `ABF26` Theorem 3.2 without the radicand guard.~~ **Done.**
  `johnson_bound_lambda_le_ell` now carries only `2 ≤ ℓ`, matching the paper exactly; the
  guarded form survives as the private `johnson_lambda_le_ell_of_radicand`, and the
  low-rate branch where the radicand guard fails is `plotkin_card_le_ell`.
- A module-alphabet version of the MDS corollary, so interleaved Reed–Solomon is covered.
- ~~**Wire the bounds to a consumer.**~~ **Done.** `rs_lambda_le_johnson_mds`
  (`mds_johnson_lambda_le` + the proven `ReedSolomon.isMDS_code`) is ArkLib's first Reed–Solomon
  list-size bound, and `johnson_listDecodable` / `johnson_listDecodable_of_le` deliver
  `johnson_bound_lambda_le_ell` in the real-valued `listDecodable` shape.
- ~~`Lambda_le_iff_listDecodable` is stated only at `ℓ : ℕ`, while in-tree `listDecodable`
  consumers use `ℓ : ℝ≥0`.~~ **Done.** `ListDecodability.lean` now also ships
  `Lambda_le_floor_iff_listDecodable` (`ℓ : ℝ`), its `ℝ≥0` variant, and the
  `(Lambda C δ : ENNReal) ≤ ENNReal.ofReal ℓ` forms that the Johnson family actually produces,
  so the transfer goes through. **Still open:** no `ArkLib/ProofSystem/Stir` proof has yet been
  rewritten to *discharge* its `listDecodable` hypothesis from these — that is a separate change
  to the STIR development, not to this layer.
- The Elias and volume-based *lower* bounds (`ABF26` Lemma 3.7 / Corollary 3.8), which pair with
  the Johnson upper bound, are not proved; only their support layer
  (`hammingBallVolume`, `qEntropy`) exists.

## Source Access

- Source metadata: [`../sources/Joh62/metadata.yml`](../sources/Joh62/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
