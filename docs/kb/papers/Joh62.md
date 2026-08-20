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

In ArkLib it is the attribution key for the list-size-parameterised Johnson layer: the radius
family of `ABF26` Definition 3.1 and its Theorem 3.2, both in
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
  — `JohnsonBound.J` (the paper's `J_q`) and `johnson_bound_lemma`. This is where `J` is defined;
  `Basic.lean` and `Family.lean` both import it, and there is no second copy of the radius.

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

## ArkLib Notes

- `Jqℓ` is *defined* through `J`, as `J q (((ℓ-1)/ℓ) * δ)`, with `Jqℓ_eq_J` the `rfl` bridge and
  `Jqℓ_eq_mul_one_sub_sqrt` recovering the expanded form. `Jcap` sits beside `sqrt_le_J`, which
  states `Jcap δ ≤ J q δ` and so is itself the `Jcap`-to-`J` bridge. There is one radius
  hierarchy, not a parallel paper-shaped one.
- `johnson_bound_lambda_le_ell` carries no public radicand guard: it holds over the full `1 ≤ ℓ`
  range, splitting internally between the Johnson regime (`johnson_lambda_le_ell_of_radicand`,
  private) and the low-rate Plotkin regime (`plotkin_card_le_ell`). The `ℓ = 0` corner is
  genuinely false as encoded and is excluded by the `1 ≤ ℓ` hypothesis.
- The MDS corollary's metric core is alphabet-generic:
  `mds_johnson_lambda_le_of_rate_distance` takes an arbitrary finite-alphabet code, a rate `ρ`,
  and the MDS rate-distance equation. `mds_johnson_lambda_le` is the field-linear convenience
  wrapper; module and interleaved codes instantiate the generic form with
  `LinearCode.alphabetRate` and their own rate-distance equation.
- `Lambda` is built from `Set.encard`, so an infinite point list contributes `⊤` rather than
  collapsing to zero, and a finite bound therefore implies point-list finiteness. `IsListDecodable`
  is a `def` whose body *is* `Lambda C r ≤ ⌊ℓ⌋₊`, so the Johnson bounds land on the predicate
  directly and no transfer lemma is involved.

## Open Formalization Gaps

- No `ArkLib/ProofSystem/Stir` proof yet discharges its `IsListDecodable` hypothesis from the
  Johnson bounds. The suppliers exist (`johnson_isListDecodable`, `johnson_isListDecodable_of_le`);
  wiring them up is a change to the STIR development, not to this layer.
- The Elias and volume-based *lower* bounds (`ABF26` Lemma 3.7 / Corollary 3.8), which pair with
  the Johnson upper bound, are not proved. Only their support layer exists
  (`hammingBallVolume`, `qEntropy`).

## Source Access

- Source metadata: [`../sources/Joh62/metadata.yml`](../sources/Joh62/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
