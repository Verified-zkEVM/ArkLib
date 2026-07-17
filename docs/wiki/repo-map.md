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
  ring `Rq Φ`. **This development is in progress.** The folder is organized by paper section, each
  subfolder carrying an umbrella `.lean` re-export next to it (the `Ajtai/Simple.lean + Simple/`
  convention); `ArkLib/Commitments/Functional/Hachi.lean` is the folder-level landing page, with
  the full folder map in its module docstring. Layout:
  - `Gadget/` (§2.1) — `Gadget/Basic` is the base-`b` gadget matrix `G` and its norm-reducing digit
    decomposition `G⁻¹`; `Gadget/Norms` is the centered `ℓ₂²`/`ℓ∞` shortness bounds for both
    directions the honest case and Lemma 8 need. `Gadget.lean` re-exports both.
  - `EvalSplit.lean` (§4, Eq. (12)) — the matrix split underlying the evaluation argument:
    multilinear evaluation `eval p (xl ++ xh)` factors as the vector–matrix–vector product
    `mb(xl) ⬝ᵥ (toMatrix p *ᵥ mb(xh))` (`evalSplit_eq_eval`), with the inverse reshape
    `toPolynomial` and the bridge lemma `splitForm_monomialBasis_eq_eval` consumed by
    `QuadEval/Bridge`. Kept top-level because the future §3 packing head reuses it over the subfield.
  - `InnerOuter/` (§4.1) — the scheme itself: `Scheme` (the inner/outer commit composition and its
    *weak opening*, following [NOZ26, §4.1]), `Correctness` (perfect correctness for lawful
    gadget decompositions), `Security` (the weak-binding reduction to Module-SIS via
    `verify_weak`), and `Arithmetic` (pins the modulus to the power-of-two cyclotomic
    `X^{2^α}+1`, which the security proofs genuinely require). `InnerOuter.lean` re-exports the
    scheme, its correctness, and its weak-binding reduction.
  - `QuadEval/` (§4.2, "Polynomial Evaluation as Quadratic Equation", Figure 3) — Hachi's
    polynomial-evaluation reduction, which proves `f(x) = y` by expressing the evaluation as the
    quadratic form `bᵀ M a` and folding the `2ʳ` carrier blocks under the challenge vector (hence
    the name `QuadEval`); it is Hachi's multilinear/inner-outer lift of Greyhound's [NS24, §3.1]
    folding protocol. `QuadEval/Gadgets` holds the gadget algebra (`PublicParamsD`, the
    honest-prover carrier/short commitment `v = D ŵ`, the `J`-decomposition of `z`, and the
    `tensorG`/`tensorG1` challenge combinations). `QuadEval/Reduction` is the 2-round protocol with
    its types, `relOut` (Eq. (20) + range balls), and `relIn` (weak opening ∨ MSIS(B) ∨ MSIS(D)).
    `QuadEval/Soundness` is the subtract-and-divide extractor `buildWitness`, **Lemma 8**
    (coordinate-wise special soundness) as `quadEval_coordinateWiseSpecialSound` (`sorryAx`-free),
    the composable `quadEvalPackage`, and the reduction's derived norm constants
    `quadEvalZL2SqBound` = `B_z` / `quadEvalBetaSq` = `4·B_z` (the generic tree plumbing lives in
    `Security/CoordinateWiseSpecialSoundness/SingleRound`; the supporting norm growth is in
    `Data/Lattices/CyclotomicRing/NormBounds/Basic` and `Gadget/Norms`). `QuadEval/Bridge` is the
    **polynomial-level bridge**: a zero-round `ReduceClaim` head (`bridgeVerifier`) reinterpreting a
    `CMlPolynomial`-level `PolyEvalStatement` as a `QuadEvalStatement` via the monomial tensor bases
    (`toQuadEvalStatement`), the pulled-back input relation `relPolyEval`, and its CWSS
    `bridge_coordinateWiseSpecialSound`. `QuadEval.lean` re-exports the reduction, its soundness,
    and the bridge.
  - §4.3 (Hachi's sumcheck-based opening, Figures 4–7) is a **skeleton** split into one flat
    folder per paper subprotocol figure (peers of `QuadEval/`), each file exporting a
    `CWSSPackage`/`GCWSSPackage` with a sorried CWSS theorem, plus the front-threading file
    `Escape.lean` at the Hachi root:
  - `Escape.lean` — the escape-threaded front `evalChainE` (design G1): widens the finished
    `QuadEval` front relations with an abstract weak-binding escape budget so every §4.3 seam has a
    home for the `w̃`-commitment's binding break. Front glue, not a §4.3 subprotocol; sits at the
    Hachi root beside `EvalSplit`/`Composition`.
  - `RingSwitch/` (§4.3 entry, Figure 4 / Lemma 9) — the HMZ25 **ring-switching lift** reducing
    `R^lin` to a claim about the committed lifted witness evaluated at a random `α`.
    `RingSwitch/Rlin` is the zero-round Eq. (20) → `R^lin` adapter (F2); `RingSwitch/Reduction`
    is the **cyclotomic instance** of the generic quotient-evaluation switch
    (`ProofSystem/RingSwitching/Lift/`): `cyclotomicPresentation` + `IsPresentation`
    laws (discharged from `Data/Lattices/CyclotomicRing/QuotientLift.lean`), the generic
    `checkAt`, and the generic interpolation/descent engine, assembled through the
    committed-scalar shell (`k = 2d`, abstract `w̃`-commitment `LiftCom`; **proven** Lemma 9
    CWSS). `RingSwitch.lean` re-exports the folder. (The §3 packing reduction is a distinct
    algebraic construction — `ProofSystem/RingSwitching/Packing/` — which does not use
    the committed-scalar seam; the two constructions share the ring-switching folder's
    top-level verifier skeletons and transport algebra.)
  - `ZeroCheck/` (§4.3, Figure 5 / **corrected** Lemma 10) — reduces the batched identities
    `H₀ ≡ 0 ∧ H_α ≡ 0` to random-point evaluations. `ZeroCheck/Constraints` is the **shared**
    encoding (Eqs. (21)–(23): the table `w̃`, `H₀`/`H_α`, the sumcheck polynomials, degree pins,
    the Kronecker curve `kroneckerPoint`, per-round seam `roundRel`), consumed by both this
    zero-check and `Sumcheck/`; `ZeroCheck/Batch` is the per-row/range ⇄ `H₀/H_α ≡ 0` batching
    bridge; `ZeroCheck/Reduction` is the corrected Lemma 10 (Kronecker seed pair, `(ℓ, k) = (2, D)`;
    see `HACHI_LEMMA10_GAP.md`). `ZeroCheck.lean` re-exports the folder.
  - `Sumcheck/` (§4.3, Figure 6 / Lemma 11 + Figure 7 tail) — the sumcheck loop finishing the
    opening. `Sumcheck/Bridge` reshapes the zero-check's point claims into the initial hypercube
    sums; `Sumcheck/Rounds` is the `m₀`-round guarded paired sumcheck (loop by recursion over
    `▷ᵍ`); `Sumcheck/FinalEval` is the guarded reveal of `w̃(a)` (Figure 7 tail) landing on the
    recursion's evaluation claim. `Sumcheck.lean` re-exports the folder.
  - `Recursion/` (§4.5) — the recursion adapters: `PartialEval` (Eq. (24) peeling, pure
    derive-`y₀`), `ZBatchBridge` (Eqs. (25)–(26) `Z`-packing — ⚠ carries the open
    partial-evaluation soundness gap, `HACHI_RECURSION_GAP.md`), `TraceHandoff` (Eqs. (27)–(28)
    — guarded trace check, lands on the next iteration's `QuadEval` seam over `Φ'`).
  - `Composition.lean` — the **CWSS composition home**: `evalChain` is the `bridgePackage ▷
    quadEvalPackage` chain and `eval_coordinateWiseSpecialSound` is its composed CWSS certificate
    (`sorryAx`-free). `openCore` chains the escape-threaded front with the pure §4.3 links (rows
    1–7 of the header's seam table), and `openingChain` /
    `hachi_iteration_coordinateWiseSpecialSound` compose the guarded tail (sumcheck loop, final
    eval, recursion adapters) into the full one-iteration certificate — a skeleton whose sorry
    provenance is inventoried in the module header.
  - `Commitment.lean` — **Hachi as a `Commitment.Scheme`**: the eval `OracleInterface`, honest
    `keygen`/`commit` (canonical base-`b` gadget decomposition at width `δ = ⌈log_b q⌉`), and the
    `hachi` scheme value (its opening `Proof` is a documented `sorry` pending the remaining §4.3+
    subprotocols and the completeness layer).
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
  split; `NoChallenge` and `SeqCompose` supply the empty-challenge base case and the n-ary
  sequential wrappers. `NoChallenge` also provides `CWSSStructure.ofIsEmpty`, the concrete
  challenge-free structure used as the left factor when appending a zero-round `ReduceClaim` head
  (e.g. Hachi's `bridgeVerifier`). `SingleRound` is the generic single-challenge-round navigation
  layer (tree shape recovery `tree_shape`, the star-center machinery, the tree extractor
  `E`, and the assembly `coordinateWiseSpecialSound_of_mkWitness`) used by Hachi's polynomial-
  evaluation reduction `QuadEval` (Lemma 8). `ScalarRound` is its **proven** `(ℓ = 1, k)`
  scalar-challenge twin (`pSpecScalar`, `scalarStructure`, the arity-`k` tree kit, and the
  assembly `coordinateWiseSpecialSound_of_mkWitness_scalar`) for Hachi's Lemmas 9/11-shaped
  rounds and the DP24 batching wire format. `CommittedScalar` is the **proven** commit-then-
  scalar-challenge shell on top of `ScalarRound`: `BindingCommitment` (binding restricted to
  `Short` openings, escape budget for weak binding), the anchored relation/verifier/prover, the
  three-way extractor `buildWitness` (escape pass-through / collision escape / common-opening
  recovery), and its generic CWSS theorem + `CWSSPackage`; instantiated by Hachi's HMZ
  quotient-evaluation ring switch. `Escape` provides `Set.withEscape`, the escape-threading of
  relations (`W ⊕ E` witnesses) used by composed extraction chains that can emit binding-break
  escapes mid-chain. `Guarded` is the **B4 skeleton**: `Verifier.IsGuardedWith`/`IsGuarded`
  (runtime-rejecting verifiers), the guarded package `GCWSSPackage` with its append `▷ᵍ`, and
  the (sorried) guarded binary CWSS append theorem. The umbrella
  `CoordinateWiseSpecialSoundness.lean` re-exports the core files.
- Active areas are often grouped by paper or protocol family, for example
  `Data/CodingTheory/ProximityGap/BCIKS20/...` or `ProofSystem/Binius/...`.
- Ring switching is a **family of constructions, not one protocol** — the umbrella
  `ProofSystem/RingSwitching/Basic.lean` carries the taxonomy over two construction folders.
  `Packing/` is the small→large packing family: `Profile.lean` holds the shared
  packing data layer `RingSwitchingProfile` (packing data + reconstruction laws) and the
  remaining files are the DP24/Binius construction (`Prelude` with `packMLE` + the Binius
  instance `binaryTowerProfile`, `Spec`, `BatchingPhase`, `SumcheckPhase`, `General`; RBR
  soundness, `[IsDomain L]`); Binius instantiates it in `ProofSystem/Binius/FRIBinius/`
  (`biniusProfile`), and Hachi's §3 packing head is the intended next `Profile` instance.
  `Lift/` is the **generic HMZ lift** (large quotient ring →
  field, CWSS at `k = 2d`): `Presentation.lean` is its data layer (proof-free
  `Presentation R S` + `IsPresentation` laws over any monic modulus — not cyclotomic-specific
  — with the full lift algebra and interpolation engine proven over the laws), and
  `Reduction.lean` is the protocol layer over the committed-scalar shell
  (`OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean`), with the
  recovery obligation proven generically. Hachi's `Commitments/Functional/Hachi/RingSwitch/`
  is its cyclotomic instance, with law-discharge lemmas in
  `Data/Lattices/CyclotomicRing/QuotientLift.lean`. What the two families share lives at the
  folder top level — the check-then-update round-shape verifiers (`RoundVerifiers.lean`,
  over the `pSpecScalar` wire shape and the one-message `pSpecMessage` wire) and the
  embed-and-evaluate transport algebra (`Transport/Eval.lean`, `Transport/Coeffs.lean`) — plus the
  committed-scalar seam under `OracleReduction/`.
  Background: KB concept page `docs/kb/concepts/ring-switching.md`; design note
  `HACHI_RING_SWITCHING_COMPARISON.md`; blueprint section
  `proof_systems/ring_switching.tex`. Structured sum-check support lives in
  `ProofSystem/Sumcheck/Structured*` and `ProofSystem/Sumcheck/Domain.lean`.
- Before assuming a file is authoritative, check whether it is source or derived output. See
  [`generated-files.md`](generated-files.md).
