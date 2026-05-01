# Repo Map

This repo is easiest to navigate by subtree, not by individual file name.
Many developments are paper-scoped and spread across several modules.

## Main Surfaces

```text
ArkLib/
  Data/               foundational math, coding theory, polynomials, probability, etc.
  OracleReduction/    core IOR abstractions and security theory
  CommitmentScheme/   commitments and opening arguments
  ProofSystem/        protocol families and higher-level proofs
  ToMathlib/          local additions not upstreamed to Mathlib
blueprint/src/        blueprint sources and references.bib
scripts/              repo utilities
home_page/            site assets and assembled website root
```

## Conceptual Layering

- `ArkLib/OracleReduction/` is the conceptual center of the library.
- `ArkLib/Data/` and `ArkLib/ToMathlib/` support the core with reusable definitions and lemmas.
- `ArkLib/CommitmentScheme/` and `ArkLib/ProofSystem/` build on top of those foundations.
- When changing a protocol subtree, read the local subtree plus one layer of imports toward
  `Data/` or `OracleReduction/` before making architectural edits.

## Where To Start By Task

- Extending foundational math or coding theory: start in `ArkLib/Data/`.
- Changing core reduction or security abstractions: start in `ArkLib/OracleReduction/`.
- Working on protocol statements or proofs: start in `ArkLib/ProofSystem/`.
- Updating commitment interfaces or concrete schemes: start in `ArkLib/CommitmentScheme/`.
- Moving reusable helper lemmas that ideally belong upstream: start in `ArkLib/ToMathlib/`.
- Updating theory docs, references, or long-form exposition: start in `blueprint/src/`.

## Navigation Notes

- `ArkLib.lean` is a generated umbrella import file, not a hand-maintained module index.
- The Merkle tree implementations now live upstream in `VCVio`, so use
  `VCVio.CryptoFoundations.MerkleTree` or `VCVio.CryptoFoundations.InductiveMerkleTree`
  instead of the old ArkLib-local modules.
- Reed-Solomon code definitions live under the `ReedSolomon` namespace in
  `ArkLib/Data/CodingTheory/ReedSolomon.lean`. The older `ReedSolomonCode` namespace has been
  merged into `ReedSolomon`; use the consolidated name at new call sites.
- Vandermonde matrix utilities shared across Reed-Solomon and proximity-gap developments live in
  `ArkLib/Data/Matrix/Vandermonde.lean`, not in the Reed-Solomon file.
- Trivariate polynomial utilities used by the BCIKS20 proximity-gap proofs
  (`eval_on_Z`, `toRatFuncPoly`, `D_Y`, `D_YZ`, and related notation) live in
  `ArkLib/Data/Polynomial/Trivariate.lean`, not in `ProximityGap/Basic.lean` or
  `ProximityGap/BCIKS20/ListDecoding/Guruswami.lean`.
- Active areas are often grouped by paper or protocol family, for example
  `Data/CodingTheory/ProximityGap/BCIKS20/...` or `ProofSystem/Binius/...`.
- Before assuming a file is authoritative, check whether it is source or derived output. See
  [`generated-files.md`](generated-files.md).
