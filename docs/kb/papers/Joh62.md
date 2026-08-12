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
- The **radius family** it induces: `JohnsonBound.Jqℓ` (the `ℓ`-parameterised `q`-ary Johnson
  radius) and `JohnsonBound.Jcap` (`1 − √(1−δ)`), both from `ABF26` Definition 3.1.
- The **MDS corollary** `CodingTheory.mds_johnson_lambda_le_of_rate_distance` (= `ABF26`
  Corollary 3.3, `Λ(C, 1 − √ρ − η) ≤ 1/(2ηρ)`) for an arbitrary finite alphabet, its
  field-linear wrapper `mds_johnson_lambda_le`, and the complementary Plotkin regime
  `CodingTheory.plotkin_card_le_ell`.
- ArkLib does **not** follow Johnson's own derivation. The numeric core is
  `CodingTheory.johnson_card_le_ell`, the standard average-distance double counting, built on the
  pre-existing `JohnsonBound/Basic.lean` development.

## Main ArkLib Touchpoints

- [`ArkLib/Data/CodingTheory/JohnsonBound/Family.lean`](../../../ArkLib/Data/CodingTheory/JohnsonBound/Family.lean)
  — `Jqℓ`, `Jcap`, `johnson_bound_lambda_le_ell`, the alphabet-generic
  `mds_johnson_lambda_le_of_rate_distance`, field/RS wrappers, `plotkin_card_le_ell`, and
  `johnson_card_le_ell`.
- [`ArkLib/Data/CodingTheory/JohnsonBound/Basic.lean`](../../../ArkLib/Data/CodingTheory/JohnsonBound/Basic.lean)
  — `Jcap` and the pre-existing `sqrt_le_J`, `johnson_bound`, `johnson_bound_alphabet_free`, which
  `Family.lean` consumes rather than re-proves. That file cites `codingtheory` and `listdecoding`,
  not `Joh62`.
- [`ArkLib/Data/CodingTheory/JohnsonBound/Lemmas.lean`](../../../ArkLib/Data/CodingTheory/JohnsonBound/Lemmas.lean)
  — the single `JohnsonBound.J` (the paper's `J_q`) and `johnson_bound_lemma`. This is the
  *upstream* definition: `Basic.lean` imports this file, and the de-duplication described below
  kept the copy here.

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

- `Jqℓ` is defined through the pre-existing `J` (which lives in `Lemmas.lean`), and `Jcap`
  lives beside the `sqrt_le_J` bridge that consumes it (in `Basic.lean`); the exported bridges
  recover the paper forms without a parallel radius hierarchy.
- `johnson_bound_lambda_le_ell` matches ABF26 Theorem 3.2 without a public radicand guard. Its
  proof splits internally between the Johnson and Plotkin regimes.
- The `ℓ = 0` false corner is excluded by the theorem's `1 ≤ ℓ` hypothesis; the elementary
  `ℓ = 1` radius-zero boundary is proved separately inside the theorem, and the list-size-two
  specialization is documented as distinct from the binary Johnson radius.
- **The MDS corollary's metric core is alphabet-generic.**
  `mds_johnson_lambda_le_of_rate_distance` accepts an arbitrary finite-alphabet code, its
  alphabet-normalized rate `ρ`, and the exact MDS rate-distance equation. The field-linear
  `mds_johnson_lambda_le` is only a convenience wrapper. Module/interleaved consumers are covered
  by the generic theorem, but must still supply their appropriate rate definition and
  rate-distance bridge.
- `Lambda` uses `Set.encard`, so infinite lists contribute `⊤` rather than silently collapsing
  to zero. The real-valued `listDecodable` API explicitly records point-list finiteness beside
  its `Set.ncard` bound, making every finite-bound bridge instance-free.

## Open Formalization Gaps

- ~~Export `Jqℓ_eq_J` and `Jcap_le_J`, and reduce the three in-tree copies of the Johnson
  radius to one.~~ **Done.** `Jqℓ` is now *defined* as `J q (((ℓ-1)/ℓ) * δ)` with `Jqℓ_eq_J`
  as the (`rfl`) bridge and `Jqℓ_eq_mul_one_sub_sqrt` recovering ABF26 Definition 3.1's printed shape;
  the two identical `q`-ary definitions collapsed to the single upstream
  `JohnsonBound.J` in `JohnsonBound/Lemmas.lean` (the downstream copy in
  `JohnsonBound/Basic.lean` is gone), `Jcap` lives beside the `sqrt_le_J` bridge in
  `JohnsonBound/Basic.lean`, and that pre-existing lemma is now stated as
  `Jcap δ ≤ J q δ` — i.e. it *is* the `Jcap` bridge, so no separate `Jcap_le_J` is needed.
- ~~State `ABF26` Theorem 3.2 without the radicand guard.~~ **Done.**
  `johnson_bound_lambda_le_ell` now covers the paper's full `1 ≤ ℓ` range; the `ℓ = 1`
  radius-zero case is elementary, the guarded `ℓ ≥ 2` form survives as the private
  `johnson_lambda_le_ell_of_radicand`, and the low-rate branch where the radicand guard fails
  is `plotkin_card_le_ell`.
- ~~Add an alphabet-generic MDS corollary.~~ **Done.**
  `mds_johnson_lambda_le_of_rate_distance` is metric and works over any finite alphabet; module
  and interleaved consumers instantiate it by supplying their alphabet-normalized rate and MDS
  rate-distance equation.
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
