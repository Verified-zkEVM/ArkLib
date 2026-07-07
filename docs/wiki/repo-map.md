# Repo Map

This repo is easiest to navigate by subtree, not by individual file name.
Many developments are paper-scoped and spread across several modules.

## Main Surfaces

```text
ArkLib/
  Data/               foundational math, coding theory, polynomials, probability, etc.
  OracleReduction/    core IOR abstractions and security theory
  Commitments/        commitments and opening arguments
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
- `ArkLib/Commitments/` and `ArkLib/ProofSystem/` build on top of those foundations.
- When changing a protocol subtree, read the local subtree plus one layer of imports toward
  `Data/` or `OracleReduction/` before making architectural edits.

## Where To Start By Task

- Extending foundational math or coding theory: start in `ArkLib/Data/`.
- Changing core reduction or security abstractions: start in `ArkLib/OracleReduction/`.
- Working on protocol statements or proofs: start in `ArkLib/ProofSystem/`.
- Updating commitment interfaces or concrete schemes: start in `ArkLib/Commitments/`
  (`Ordinary/` for plain commit-and-open schemes whose definition comes from the VCV-io
  `CommitmentScheme`, `Functional/` for commit-plus-oracle-evaluation schemes defined by
  ArkLib's own `Commitment.Scheme` in `ArkLib/Commitments/Functional/Basic.lean`).
- Moving reusable helper lemmas that ideally belong upstream: start in `ArkLib/ToMathlib/`,
  `ArkLib/ToCompPoly/`, or `ArkLib/ToVCVio/`, depending on the upstream project.
- Updating theory docs, references, or long-form exposition: start in `blueprint/src/`.
- Updating repository-local paper summaries, audits, or reference context: start in `docs/kb/`.

## Navigation Notes

- `ArkLib.lean` is a generated umbrella import file, not a hand-maintained module index.
- `ArkLib/ToVCVio/` mirrors VCV-io module structure under the importable Lean prefix
  `ArkLib.ToVCVio`; use it for reusable `VCVio` helper lemmas before they are upstreamed.
- `ArkLib/Commitments/` splits into two families by *what an opening proves*:
  - `Ordinary/` — standard commitments that only **commit and open** (reveal the committed
    message). These reuse the VCV-io `CommitmentScheme` definition rather than redefining it;
    the concrete schemes are `SimpleRO` (a random-oracle commitment, `Ordinary/SimpleRO.lean`)
    and the simple Ajtai lattice commitment (`Ordinary/Ajtai/Simple/`, with `Scheme`,
    `Correctness`, and `Security` modules).
  - `Functional/` — *functional* commitments that **commit and then prove oracle evaluations**
    of the committed data (an opening proves `oracle data query = response`, not the data
    itself). These have their own, unrelated definition in
    `ArkLib/Commitments/Functional/Basic.lean` (`Commitment.Scheme`, plus correctness,
    evaluation/function binding, and extractability games). KZG and Hachi are the concrete
    functional schemes.
- KZG commitment-scheme modules live under `ArkLib/Commitments/Functional/KZG/`: `Basic` for the
  construction and scheme instance, `Correctness` for correctness proofs, `FunctionBinding` for
  the function-binding reduction, and `Binding` for evaluation binding. Shared
  CPolynomial/Polynomial division bridge lemmas live under `ArkLib/ToCompPoly/`.
- Hachi commitment-scheme modules live under `ArkLib/Commitments/Functional/Hachi/` and formalize
  the Greyhound [NS24] / Hachi [NOZ26] *inner-outer* Ajtai lattice commitment over a cyclotomic
  ring `Rq Φ`. **This development is in progress.** Layout:
  - `Gadget.lean` / `GadgetNorms.lean` — the base-`b` gadget matrix `G`, its norm-reducing digit
    decomposition `G⁻¹`, and the centered `ℓ₂²`/`ℓ∞` shortness bounds the honest case needs.
  - `InnerOuter/` — the scheme itself: `Scheme` (the inner/outer commit composition and its
    *weak opening*, following [NOZ26, §4.1]), `Correctness` (perfect correctness for lawful
    gadget decompositions), `Security` (the weak-binding reduction to Module-SIS via
    `verify_weak`), and `Arithmetic` (pins the modulus to the power-of-two cyclotomic
    `X^{2^α}+1`, which the security proofs genuinely require).
  - `InnerOuter.lean` — top-level re-export of the scheme, its correctness, and its
    weak-binding reduction.
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
- Transcript-tree infrastructure for special-soundness-style notions lives in
  `Security/TranscriptTree/`: `Basic` defines `ChallengeTree`, `LeafPath`,
  `ChallengeTreeShape`, `ChallengeTree.IsStructured`, `ChallengeTree.IsAccepting`,
  `Extractor.TreeBased`, and the shape-generic soundness core `Verifier.treeSpecialSound` (a
  tree-based extractor recovering a witness from every `S`-structured accepting tree); `Composition`
  defines shape append, `appendSplit`, and the generic structure-preservation/recombination lemmas
  for sequential protocol append. The umbrella `Security/TranscriptTree.lean` re-exports both files.
  Both plain and coordinate-wise special soundness are instances of `Verifier.treeSpecialSound` for
  different shapes; neither special-soundness file imports the other.
- Plain `(k)`-special soundness lives in `Security/SpecialSoundness.lean`. It is the instance of
  `Verifier.treeSpecialSound` for the pairwise-distinct shape `distinctShape k` (arity `kᵢ`, node
  predicate `Function.Injective`), with input/output relations like CWSS; it is the `ℓᵢ = 1`
  specialization of coordinate-wise special soundness. The bridge
  `coordinateWiseSpecialSound (ofSpecialSound k) ↔ specialSound k` lives in
  `Security/Implications.lean`.
- Coordinate-wise special soundness ([FMN24]/[NOZ26]) lives in
  `Security/CoordinateWiseSpecialSoundness/`: `Basic` defines the `SS(S, ℓ, k)` combinatorics
  (`CoordEq`, `IsSpecialSoundFamily`), `CWSSStructure`, `CWSSStructure.toShape`, and
  `Verifier.coordinateWiseSpecialSound`; `Composition` transports CWSS structures across
  sequential composition and proves binary append preservation via the generic transcript-tree
  split. The umbrella `CoordinateWiseSpecialSoundness.lean` re-exports both files.
- Active areas are often grouped by paper or protocol family, for example
  `Data/CodingTheory/ProximityGap/BCIKS20/...` or `ProofSystem/Binius/...`.
- Ring switching is a **generic, instantiable compiler** under `ProofSystem/RingSwitching/`, not a
  Binius-only protocol: `Profile.lean` holds the `RingSwitchingProfile` abstraction (packing data +
  reconstruction laws), `Prelude.lean` the shared defs + the Binius instance `binaryTowerProfile`,
  and `General.lean` the full reduction and generic security theorems. Binius instantiates it in
  `ProofSystem/Binius/FRIBinius/` (`biniusProfile`); Hachi (`NOZ26`) is the intended next instance.
  Background: KB concept page `docs/kb/concepts/ring-switching.md`; blueprint section
  `proof_systems/ring_switching.tex`. Structured sum-check support lives in
  `ProofSystem/Sumcheck/Structured*` and `ProofSystem/Sumcheck/Domain.lean`.
- Before assuming a file is authoritative, check whether it is source or derived output. See
  [`generated-files.md`](generated-files.md).
