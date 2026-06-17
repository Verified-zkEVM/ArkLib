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
  ToCompPoly/         local additions not upstreamed to CompPoly
  ToVCVio/            local additions not upstreamed to VCV-io
blueprint/src/        blueprint sources and references.bib
docs/kb/             persistent paper, concept, audit, and query knowledge base
scripts/              repo utilities
home_page/            site assets and assembled website root
```

## Conceptual Layering

- `ArkLib/OracleReduction/` is the conceptual center of the library.
- `ArkLib/Data/`, `ArkLib/ToMathlib/`, `ArkLib/ToCompPoly/`, and `ArkLib/ToVCVio/` support the
  core with reusable definitions and lemmas.
- `ArkLib/CommitmentScheme/` and `ArkLib/ProofSystem/` build on top of those foundations.
- When changing a protocol subtree, read the local subtree plus one layer of imports toward
  `Data/` or `OracleReduction/` before making architectural edits.

## Where To Start By Task

- Extending foundational math or coding theory: start in `ArkLib/Data/`.
- Changing core reduction or security abstractions: start in `ArkLib/OracleReduction/`.
- Working on protocol statements or proofs: start in `ArkLib/ProofSystem/`.
- Updating commitment interfaces or concrete schemes: start in `ArkLib/CommitmentScheme/`.
- Moving reusable helper lemmas that ideally belong upstream: start in `ArkLib/ToMathlib/`,
  `ArkLib/ToCompPoly/`, or `ArkLib/ToVCVio/`, depending on the upstream project.
- Updating theory docs, references, or long-form exposition: start in `blueprint/src/`.
- Updating repository-local paper summaries, audits, or reference context: start in `docs/kb/`.

## Navigation Notes

- `ArkLib.lean` is a generated umbrella import file, not a hand-maintained module index.
- `ArkLib/ToVCVio/` mirrors VCV-io module structure under the importable Lean prefix
  `ArkLib.ToVCVio`; use it for reusable `VCVio` helper lemmas before they are upstreamed.
- KZG commitment-scheme modules live under `ArkLib/CommitmentScheme/KZG/`: `Basic` for the
  construction and scheme instance, `Correctness` for correctness proofs, `FunctionBinding` for
  the function-binding reduction, and `Binding` for evaluation binding. Shared
  CPolynomial/Polynomial division bridge lemmas live under `ArkLib/ToCompPoly/`.
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
- `ArkLib/OracleReduction/Security/` uses the umbrella-file + folder convention: each notion is a
  thin umbrella module (`KnowledgeSoundness.lean`, `SpecialSoundness.lean`,
  `CoordinateWiseSpecialSoundness.lean`, `Implications.lean`, `Rewinding.lean`) re-exporting a
  same-named folder. `Basic.lean` holds the straightline notions; soundness ⇒ knowledge-soundness
  implications live under `Implications/` (one file per implication).
- The rewinding-extraction infrastructure is a peer subpackage `Security/Rewinding/`, not nested
  under one notion: `Basic` (abstract rewinding-KS notions — `Extractor.Rewinding`,
  `QueryImpl.ReplayConsistent`, `knowledgeSoundnessRewinding(WithError)`), `Coupling` (run-coupling
  / execution-semantics lemmas — `Prover.Realizes`, `runToRound_couple`, `run_pin` — plus the
  `QueryImpl.IsDeterministic` predicate), `ReplayFork` (the protocol-generic round-indexed replay
  fork — `replayChallenge`, `replayForkImpl`, structural guarantees, `.replay` determinism), and
  `SeededReplay` (the `oSpec`-randomness-as-tape abstraction). `Rewinding/*` never imports CWSS.
  The design rationale is `docs/general-replay-fork-design.md`.
- Coordinate-wise special soundness ([FMN24]/[NOZ26]) is its own peer subpackage
  `Security/CoordinateWiseSpecialSoundness/`: `Basic` (the notion + combinatorics),
  `CoordinateOracle` (per-coordinate challenge oracle + Bridge 1), and `ForkOracle` (the
  CWSS-specific client of `Rewinding.ReplayFork` — query datatype, collector, coordinate edit). The
  CWSS ⇒ rewinding-knowledge-soundness implication and its extraction bound live in
  `Security/Implications/CoordinateWiseSpecialSoundnessRewinding.lean`.
- Active areas are often grouped by paper or protocol family, for example
  `Data/CodingTheory/ProximityGap/BCIKS20/...` or `ProofSystem/Binius/...`.
- Before assuming a file is authoritative, check whether it is source or derived output. See
  [`generated-files.md`](generated-files.md).
