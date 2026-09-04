---
kind: paper
bibkey: BCPZZ26
title: "Algorithmic List Decoding of Reed–Solomon Codes up to Capacity in the Low-Rate Regime"
year: "2026"
bib_source: blueprint/src/references.bib
canonical_url: https://eccc.weizmann.ac.il/report/2026/164/
source_metadata: ../sources/BCPZZ26/metadata.yml
status: active
related_concepts:
  - reed-solomon-proximity
related_modules:
  - ArkLib/Data/CodingTheory/ReedSolomon/ListDecoding/Specification.lean
  - ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters.lean
  - ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Contracts.lean
  - ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Variables.lean
  - ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Substitution.lean
  - ArkLib/Data/CodingTheory/ReedSolomon/LowRateListDecoding/Main.lean
---

# BCPZZ26

## At A Glance

`BCPZZ26` is Brakensiek–Chen–Putterman–Zhang–Zheng, *Algorithmic List Decoding of
Reed–Solomon Codes up to Capacity in the Low-Rate Regime*. It gives a deterministic
polynomial-time list decoder over prime fields for every evaluation set when the rate is at most
`(1 - θ)ε`, approaching the list-decoding capacity in the low-rate regime.

The new ingredient is a multivariate interpolation argument using hidden Hasse derivatives. A
local-rank bound supplies a nonzero interpolant; Kopparty's differential-equation root finder then
enumerates a bounded candidate list.

## What ArkLib Uses From This Paper

- Theorem 4.1 supplies the public parameter regime and decoder guarantee.
- Theorem 2.1, restating `Kop15` Theorem 4.3, supplies the exact `q^(4d+6)` candidate bound.
- Section 3 supplies the hidden-derivative interpolation construction, its weighted lattice count,
  and the local-kernel/rank argument.
- Algorithm 1 supplies the intended executable pipeline: interpolate, solve the differential
  equation, then filter by actual agreement.

## Main ArkLib Touchpoints

- [`Specification.lean`](../../../ArkLib/Data/CodingTheory/ReedSolomon/ListDecoding/Specification.lean)
  defines a decoder contract whose degree bound is enforced by the output type and whose membership
  equivalence includes both soundness and completeness. Its ambient-candidate layer keeps the
  message and design dimensions separate.
- [`Parameters.lean`](../../../ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters.lean)
  keeps the natural interpolation parameters free.
- [`Contracts.lean`](../../../ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Contracts.lean)
  freezes the parametric interpolation/root-solver join and arbitrary list bound.
- [`Main.lean`](../../../ArkLib/Data/CodingTheory/ReedSolomon/LowRateListDecoding/Main.lean) states
  the source-shaped headline theorem and records the intentional `sorry` that coordinates the
  project.
- [`low_rate_rs_list_decoding.tex`](../../../blueprint/src/coding_theory/low_rate_rs_list_decoding.tex)
  records the theorem, trust boundary, source blockers, and proof decomposition.
- [`bcpzz26-main-theorem.md`](../audits/bcpzz26-main-theorem.md) is the clause-by-clause source
  audit.

## Version Notes

- The formalization is pinned initially to the ECCC report published on 2026-09-04.
- The audited PDF has SHA-256
  `b749151a7b5961e34760c735cf64067f0c3dea632030f2e69737b6caef7a3e70`.
- Source changes must be compared against the theorem audit before changing the Lean statement.

## Known Divergences From ArkLib

- The Lean theorem exposes the exact list bound `q^(4d+6)` from the paper's Theorem 2.1 rather than
  only the asymptotic `q^O(ε^(-3/θ))` presentation in Theorem 4.1.
- The paper's runtime claim is not represented. ArkLib has no machine-cost model for the required
  interpolation and root-finding algorithms; a decoder certificate proves only extensional
  correctness and output cardinality.
- Generic decoder contracts live in `ReedSolomon.ListDecoding`; the exact-parameter engine lives in
  `ReedSolomon.HiddenDerivative`; only the published corollary uses
  `ReedSolomon.LowRateListDecoding`.

## Open Formalization Gaps

- Proposition 3.13 is stated for every `k/n ≤ (1 - θ)ε`, but its proof uses equality with
  `floor ((1 - θ)εn)`. The expected repair is to decode in that ambient dimension and filter to
  degree `< k`.
- The lattice-growth proof's hidden term should be replaced by
  `2/(2+θ) * log d + 5/4`, followed by an explicit parameter-discharge inequality.
- Lemma 3.2 uses the false inequality `ceil x ≤ x`; the repaired support-cap estimate is recorded
  in the statement audit and blueprint.
- ArkLib has no Kopparty differential-equation root finder.
- The Hasse–Taylor toolkit and generic multivariate weighted-support API are under review. The
  paper-specific named variables and the two-stage local substitution are implemented on top of
  them. The weighted-simplex, local-rank, executable interpolation, and parameter-arithmetic layers
  remain to be built.

## Source Access

- Source metadata: [`../sources/BCPZZ26/metadata.yml`](../sources/BCPZZ26/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
