# Repo Map

This repo is easiest to navigate by subtree, not by individual file name.
Many developments are paper-scoped and spread across several modules.

## Main Surfaces

```text
ArkLib/
  Data/               foundational math, coding theory, polynomials, probability, etc.
  Interaction/        typed prover, verifier, and reduction foundations
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

- `ArkLib/Interaction/` is the new typed-interaction foundation. Its plain reduction layer is
  intentionally independent of oracle, probability, and legacy protocol semantics.
- `ArkLib/OracleReduction/` remains the conceptual center of the legacy reduction and security
  layer while protocol clients migrate.
- `ArkLib/Data/`, `ArkLib/ToMathlib/`, `ArkLib/ToCompPoly/`, and `ArkLib/ToVCVio/` support the
  core with reusable definitions and lemmas.
- `ArkLib/Commitments/` and `ArkLib/ProofSystem/` build on top of those foundations.
- When changing a protocol subtree, read the local subtree plus one layer of imports toward
  `Data/` or `OracleReduction/` before making architectural edits.

## Where To Start By Task

- Extending foundational math or coding theory: start in `ArkLib/Data/`.
- Changing typed interaction or dependent reduction foundations: start in `ArkLib/Interaction/`.
- Changing legacy reduction or security abstractions: start in `ArkLib/OracleReduction/`.
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
  **Nothing there may import ArkLib outside `ToVCVio` itself** — that invariant is what makes a file
  movable to VCVio unchanged. Content that is generic in spirit but depends on an ArkLib layer
  belongs beside its consumers in core instead; generalise first, then move. Files whose contents
  have gone upstream are kept as import-only compatibility shells rather than deleted. See
  [`ArkLib/ToVCVio/README.md`](../../ArkLib/ToVCVio/README.md) for the upstream-then-delete rule.
- Across the PolyFun/VCVio boundary, import generic polynomial-functor and handler structure from
  PolyFun and oracle/probability specializations from VCVio. Dependency internals are not an ArkLib
  proof surface: if an ordinary import is missing a usable law, stage that law in `ToVCVio` or
  upstream it rather than reaching through the module boundary.
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
  ring `Rq Φ`. **This development is in progress.** The folder is organized by paper section;
  every subfolder carries its umbrella as `Basic.lean` inside that subfolder.
  `ArkLib/Commitments/Functional/Hachi/Basic.lean` is the folder-level landing page, with the full
  folder map in its module docstring. Layout:
  - `Gadget/` (§2.1) — `Gadget/Core` is the base-`b` gadget matrix `G` and its norm-reducing digit
    decomposition `G⁻¹`; `Gadget/Norms` is the centered `ℓ₂²`/`ℓ∞` shortness bounds for both
    directions the honest case and Lemma 8 need. `Gadget/Basic.lean` re-exports both.
  - `EvalSplit.lean` (§4, Eq. (12)) — the matrix split underlying the evaluation argument:
    multilinear evaluation `eval p (xl ++ xh)` factors as the vector–matrix–vector product
    `mb(xl) ⬝ᵥ (toMatrix p *ᵥ mb(xh))` (`evalSplit_eq_eval`), with the inverse reshape
    `toPolynomial` and the bridge lemma `splitForm_monomialBasis_eq_eval` consumed by
    `QuadEval/Bridge`. Kept top-level because the future §3 packing head reuses it over the subfield.
  - `InnerOuter/` (§4.1) — the scheme itself: `Scheme` (the inner/outer commit composition and its
    *weak opening*, following [NOZ26, §4.1]), `Correctness` (perfect correctness for lawful
    gadget decompositions), `Security` (the weak-binding reduction to Module-SIS via
    `verify_weak`), and `Arithmetic` (pins the modulus to the power-of-two cyclotomic
    `X^{2^α}+1`, which the security proofs genuinely require). `InnerOuter/Basic.lean`
    re-exports the scheme, its correctness, and its weak-binding reduction.
  - `QuadEval/` (§4.2, "Polynomial Evaluation as Quadratic Equation", Figure 3) — Hachi's
    polynomial-evaluation reduction, which proves `f(x) = y` by expressing the evaluation as the
    quadratic form `bᵀ M a` and folding the `2ʳ` carrier blocks under the challenge vector (hence
    the name `QuadEval`); it is Hachi's multilinear/inner-outer lift of Greyhound's [NS24, §3.1]
    folding protocol. `QuadEval/Gadgets` holds the gadget algebra (`PublicParamsD`, the
    honest-prover carrier/short commitment `v = D ŵ`, the `J`-decomposition of `z`, and the
    `tensorG`/`tensorG1` challenge combinations). `QuadEval/Reduction` is the 2-round protocol with
    its types, plain `relOut` (Eq. (20) + range balls), plain `relIn` (eval-consistent weak
    opening), and the `QuadEvalSISBreak`/`quadEvalSISSet` **break vocabulary** for MSIS(B/D)
    outcomes — key-tied: breaks are validated against the fixed key parameter `pp`, which (like
    the relations' key) is never statement data.
    `QuadEval/Soundness` is the subtract-and-divide extraction `buildWitness`, split into the plain
    assembler `quadEvalMkWitness` and the **escape event** `quadEvalEscLocal`, and **Lemma 8**
    (coordinate-wise special soundness) as the single
    `quadEval_coordinateWiseSpecialSoundWithEscape` (named-extractor, *plain* input and output
    relations, escape as a disjunct of the conclusion; `sorryAx`-free) feeding the package,
    the composable `quadEvalPackage`, and the reduction's derived norm constants
    `quadEvalZL2SqBound` = `B_z` / `quadEvalBetaSq` = `4·B_z` (the generic tree plumbing lives in
    `Security/CoordinateWiseSpecialSoundness/SingleRound`; the supporting norm growth is in
    `Data/Lattices/CyclotomicRing/NormBounds/Basic` and `Gadget/Norms`; the executable division
    the extraction divides by is `Data/Lattices/CyclotomicRing/Inverse`). `QuadEval/Bridge` is the
    **polynomial-level bridge**: a zero-round `ReduceClaim` head (`bridgeVerifier`) reinterpreting a
    `CMlPolynomial`-level `PolyEvalStatement` as a `QuadEvalStatement` via the monomial tensor bases
    (`toQuadEvalStatement`), the pulled-back input relation `relPolyEval`, and its CWSS
    `bridge_coordinateWiseSpecialSoundWith`. That link is proved in **both** directions too: the
    computable protocol object `bridgeReduction` (verifier `= bridgeVerifier` by
    `bridgeReduction_verifier`), the converse relation step `mem_relIn_of_relPolyEval` — which makes
    `relPolyEval` exactly the pull-back of `relIn` — and `bridgeReduction_perfectCompleteness`
    (error `0`, straight from the generic `ReduceClaim.reduction_completeness`: a zero-round
    `ReduceClaim` head draws no challenge and performs no check, so all of its content is that
    relation equivalence). `QuadEval/Completeness` is the **honest direction**, in
    two readings that must not be conflated. *Ball-relaxed*
    (`quadEvalReduction_perfectCompleteness`, `…_zmodDigits` at the unsigned base-`b` digits)
    reaches ArkLib's `relOut`, whose c6 is the symmetric ball, **not** Eq. (20)'s box `S_b` — the
    containment
    `paperRelOut ⊆ relOut` transports *soundness* to the paper's verifier and is useless in the
    honest direction. *Paper-exact* (`…_paperRelOut`, `…_balancedDigits`) reaches `paperRelOut`
    itself, using the balanced digits `balancedZmodDigitDecomposition` whose range *is* `S_b`
    (`balancedZmodDigit_valMinAbs_mem`), from the box-carrying input relation `relInBox`;
    `…_relOut_of_balancedDigits` then derives the relaxed conclusion, making the containment's
    direction explicit. Shared linear content: `honestRows_of_relIn` (rows c1–c5 at every challenge
    vector — hence error `0`). The certificate is tied to the same verifier by
    `quadEvalPackage_verifier_eq_quadEvalReduction_verifier`.
    `QuadEval/Basic.lean` re-exports the reduction, its soundness, its completeness,
    and the bridge.
  - §4.3 (Hachi's sumcheck-based opening, Figures 4–7) is split into one flat folder per paper
    subprotocol figure (peers of `QuadEval/`), each file exporting a CWSS package
    in the weakest kind it honestly lives in: plain `CWSSPackage`/`GCWSSPackage` for the reshaping
    and guarded-check links, `EscapeCWSSPackage`/`EscapeGCWSSPackage` (plain relations plus an
    escape *event*) for the links whose extraction can break an assumption. The nine-link
    iteration's soundness side is **complete and axiom-clean**, with a **computable**
    composed extractor — as is the closing `EndPiece/` — so the remaining work is the
    honest-prover/completeness layer.
  - `RingSwitch/` (§4.3 entry, Figure 4 / Lemma 9) — the HMZ25 **ring-switching lift** reducing
    `R^lin` to a claim about the committed lifted witness evaluated at a random `α`.
    `RingSwitch/Rlin` is the zero-round Eq. (20) → `R^lin` adapter (a plain `CWSSPackage`, pure
    statement reshaping, **proven**); `RingSwitch/Reduction` is the **cyclotomic instance** of the
    generic `Lift` switch (`ProofSystem/RingSwitching/Lift/`): `cyclotomicPresentation` +
    `IsPresentation` laws (discharged from `Data/Lattices/CyclotomicRing/QuotientLift.lean`), the
    generic `checkAt`, and the generic interpolation/descent engine, assembled through the
    committed-scalar shell (`k = 2d`, abstract `w̃`-commitment `LiftCom` with its short-collision
    set `LiftCom.Collision`; the weak-binding escape event is `CommittedScalar.escEvent`, so this
    link is an `EscapeCWSSPackage`; **proven** Lemma 9 CWSS). `RingSwitch/Completeness` is the
    honest direction of **both** links, proven and axiom-clean and now **unconditional**:
    `rlinReduction_perfectCompleteness_image` lands in the *image* seam `relRlinImage` (the pairs
    that came from the adapter: `p = (rlinStmt X, stack w)` with `(X, w) ∈ relOut`), and
    `liftReduction_perfectCompleteness_image` consumes exactly that, discharging **both** halves of
    `liftShort`: the `z`-bound from seam membership, the quotient bound from the digit encoding
    (`rhoDigitsShort_of_digitBaseOk`), which needs no hypothesis on the witness. Nothing is
    assumed. Why the honest side uses a different relation
    than soundness: `relRlin` forgets the matrix provenance, the value of `s.bound`, and hence the
    protocol-level `z`-bound — and `∀ s, bound ≤ s.bound` is *false* for positive `bound`
    (`s.bound = 0` is a legal statement), so the condition must be carried by the seam. The seam
    refines `relRlin` (`mem_relRlin_of_mem_relRlinImage`), so no relation is weakened.
    `RingSwitch/RhoDigits` is [NOZ26] §4.3's **hidden gadget decomposition** of the quotient:
    `rhoDigits` splits each quotient row into `δ = clog_b q` balanced base-`b` digits, with the
    reconstruction identity `rhoDigits_reconstruct` / `rhoDigits_evalAt` and the unconditional
    per-digit bound `rhoDigits_valMinAbs_natAbs_le` (`⌊b/2⌋`, for *any* quotient). This is what
    `liftMessage` commits — a vector of width `μ + n·δ`, not `μ + n` — and what makes
    `LiftCom.Collision` a genuine Module-SIS instance: `moduleSIS_relation_of_mem_Collision`
    proves a short collision satisfies `ModuleSIS.relation` for the Ajtai key at radius `2·bound`,
    its nonzero conjunct coming from `liftMessage_injective` (the digits reconstruct the
    quotient, so the committed vector determines the opening).
    `RingSwitch/QuotientNorms` is the bound on the **raw** quotient: for `φ = X^d + 1` division
    *selects* coefficients (`Polynomial.coeff_divByMonic_X_pow_add_one`, in
    `ToMathlib/Polynomial/DivByXPowAddOne`), so it inherits any coefficient bound on the row sum —
    `μ · 2d · βM · βz`, with **no wraparound hypothesis**. For the Hachi chain the only honest `βM`
    is `q/2` (the `R^lin` matrix carries the Ajtai key and gadget powers), so an *undecomposed*
    quotient can only be bounded by `q/2` (`rhoShort_half`); that is precisely why the digit
    encoding is necessary rather than decorative, and `HonestChain.lean` records the parameter
    collapse it removes.
    `RingSwitch/Basic.lean` re-exports the folder. (The §3 packing reduction is a distinct
    algebraic construction —
    `ProofSystem/RingSwitching/Packing/` — which does not use the committed-scalar seam; the two
    constructions share the ring-switching folder's top-level verifier skeletons and transport
    algebra.)
  - `ZeroCheck/` (§4.3, Figure 5 / **corrected** Lemma 10) — reduces the batched identities
    `H₀ ≡ 0 ∧ H_α ≡ 0` to random-point evaluations. `ZeroCheck/Constraints` is the **shared**
    encoding (Eqs. (21)–(23): the table `w̃`, `H₀`/`H_α`, the sumcheck polynomials, degree pins,
    per-round seam `nestedRoundRel`), consumed by both this zero-check and `Sumcheck/`;
    `ZeroCheck/Batch` is the per-row/range ⇄ `H₀/H_α ≡ 0` batching bridge (proven **both ways** —
    `mem_relLift_of_relBatched` and `mem_relBatched_of_relLift` — and the place
    `liftShort` is *derived* from `H₀ ≡ 0` rather than assumed); `ZeroCheck/Reduction` is the
    corrected Lemma 10 (`m₀ + m₁` scalar challenge rounds with `k = 2` each, extracted through the
    nested evaluation tree of `ArkLib/Data/MvPolynomial/NestedEvaluationTree.lean` — Mathlib-level,
    `k`-ary, individual degree `< k` — with the computable view in
    `ArkLib/ToCompPoly/Multilinear/NestedEvaluationTree.lean`; its named
    `nestedZeroCheckExtractor` is an executable all-left lookup into
    `ChallengeTree.LeafWitnesses`, with no runtime relation search; the weak-binding failure mode
    is the escape event `nestedZeroCheckEsc`, whose hardness target is `LiftCom.Collision`). Its
    module docstring carries the counterexample and the repair; the full analysis is
    `docs/kb/audits/noz26-zero-check-lemma10.md`. `ZeroCheck/Completeness` is the honest direction
    (`nestedZeroCheckReduction_perfectCompleteness`, proven and axiom-clean, with error exactly
    zero — `relBatched` asserts the identities, so nothing about the challenge distribution is
    used). It also carries `batchReduction_perfectCompleteness`, the batching bridge's honest
    direction, so both links of this folder are certified in both directions.
    `ZeroCheck/Basic.lean` re-exports the folder.
  - `Sumcheck/` (§4.3, Figure 6 / Lemma 11 + Figure 7 tail) — the sumcheck loop finishing the
    opening, **proven and axiom-clean throughout** (rows 7–9). `Sumcheck/Bridge` reshapes the
    zero-check's point claims into the initial hypercube sums; `Sumcheck/RoundPoly` is the
    round-polynomial layer (cube split, the partial sum as a univariate with its evaluation and
    degree lemmas — proof-side in Mathlib's `Polynomial`, plus the computable `computableRoundPoly`
    the prover sends and the transfer lemma tying the two together); `Sumcheck/Rounds` is the
    `m₀`-round guarded paired sumcheck (Lemma 11, loop by recursion over `▷ᵍ`) with a computable
    extractor that reads the supplied branch openings; `Sumcheck/FinalEval` is the guarded reveal
    of `w̃(a)` (Figure 7 tail) landing on the short-opening evaluation claim `relWEvalClaim`,
    whose computable extractor reads the unique leaf opening; `Sumcheck/Completeness` is the
    honest side — `honestComputeG`, one round's perfect completeness (axiom-clean), the `m₀`-fold
    honest chain sharing its verifier with `roundsChain`, and
    `bridge ▷ rounds ▷ final evaluation`. `Sumcheck/Basic.lean`
    re-exports the folder and records why this round layer is *not* built on the generic
    `ProofSystem/Sumcheck/` modes (their rejection convention is incompatible with tree-based
    extraction, and neither carries a soundness certificate to inherit). Caveat on the honest
    side: every *folded* completeness statement inherits `sorryAx` from the generic
    `Reduction.append_completeness`, which is still `sorry`.
  - `EndPiece/` (§4.3, closing) — the **terminal link** of the opening: the prover sends the
    reduced witness `w̃` and the guarded verifier checks `relWEvalClaim` against it directly
    (recompute the commitment, evaluate the table MLE at the sumcheck point), leaving nothing to
    reduce. Escape-free — it re-reads data just sent, so no hardness assumption is consulted — and
    **`sorry`-free and axiom-clean**: extraction is the identity on the transcript message
    (`endPieceWitness`), and CWSS closes through the challenge-free bridge plus guarded
    acceptance. Certified in both directions about the same verifier: `endPieceReduction` /
    `endPieceReduction_perfectCompleteness` is the honest side, and the full reflection lemma
    `endPieceCheck_eq_true_iff` is shared with the nonrecursive scheme's terminal verdict
    (`Correctness.lean`), so the closing link has one decision procedure.
    `EndPiece/Basic.lean` re-exports `EndPiece/Reduction.lean`.
  - `Recursion/` (§4.5) — the recursion adapters, **formalized but not composed into
    `Composition.lean`'s chain** (future recursion work): `PartialEval` (Eq. (24) peeling, pure
    derive-`y₀`), `ZBatchBridge` (Eqs. (25)–(26) `Z`-packing — ⚠ carries the open
    partial-evaluation soundness gap, analyzed in its module docstring), `TraceHandoff`
    (Eqs. (27)–(28)
    — guarded trace check, lands on the next iteration's `QuadEval` seam over `Φ'`).
    `Recursion/Basic.lean` re-exports the folder, and the top-level `Hachi.lean` umbrella imports
    it so the umbrella reaches every folder it documents.
  - `Composition.lean` — the **CWSS composition home**: `iteration` chains all nine subprotocol
    links (rows 1–9 of the header's seam table) into one evaluation iteration, and
    `hachi_iteration_coordinateWiseSpecialSoundWithEscape` states its composed named-extractor CWSS
    certificate (`sorry`-free and axiom-clean). `eval_coordinateWiseSpecialSoundWithEscape` states
    the same for the rows 1–2 front alone — the paper's Figure 3 reduction. `roundsChain` re-pins
    the sumcheck loop's relation seams definitionally, so the guarded tail composes with the
    universal `▷` rather than with explicit appends at named seam lemmas. `endPiece` (imported
    from `EndPiece/`, `sorry`-free and axiom-clean) closes a run of iterations, and `evaluation`
    is `iteration ▷ endPiece` — the complete opening argument, with no sorried factor left.
    Escape events compose along the chain by `ChallengeTree.EscapeEvent.append`, so only relation
    seams have to match.
  - `Commitment.lean` — **Hachi as a `Commitment.Scheme`**: the eval `OracleInterface`, honest
    `keygen`/`commit` (canonical base-`b` gadget decomposition at width `δ = ⌈log_b q⌉`), and the
    `hachi` scheme value (its opening `Proof` is a documented `sorry` pending the end-piece, the §4.5
    recursion tail, and the recursive honest-prover layer). It also carries the **honest-committer facts**
    the honest chain needs: `verifiedOpening_honestOpening` (the committer's own output is a
    `WeakBinding.VerifiedOpening` — it lives here, not in `InnerOuter/Correctness`, because
    `InnerOuter/Security` imports that file), `vecInSb_honestInnerDecomp_balanced`, and
    `mem_relInBox_of_honestBalanced` / `mem_relInBox_of_commitBalanced`: with
    `balancedZmodDigitDecomposition` the honest opening satisfies paper-exact `QuadEval`'s input
    relation `relInBox`, given Eq. (15) evaluation consistency — the second one at the actual
    output of `commitBalanced`. **The packaged `hachi.commit` uses unsigned digits**, so the
    paper-exact link does not apply to it (only the ball-relaxed reading does); switching the
    scheme's committer is part of the opening work. Weak-opening validity, evaluation consistency
    and box membership stay separate, and establishing that input relation is **not** a claim about
    `Commitment.perfectCorrectness` (`hachi.opening` is still `sorry`, and the declared `pSpec`
    covers only the bridge ▷ QuadEval prefix, not the full opening protocol). The **nonrecursive**
    scheme `hachiNonrecursive` in `Correctness.lean` is where the balanced committer is packaged
    with a complete opening and perfect correctness is actually proved.
  - `HonestChain.lean` — the honest side's **parameter interface** and prefix composition:
    `HonestRangeParams` (digit base `b`, Eq. (20) ball radius `γ`, zero-check range base `bZero` —
    which is also the base of the quotient's hidden gadget decomposition — with the box→ball
    condition, the batching bridge's *honest-direction* inequality, and the digit-base
    admissibility triple `DigitBaseOk q γ bZero`, plus two witnesses that are **not**
    interchangeable: `HonestRangeParams.ofDigitBase` at `γ = ⌊b/2⌋`, `bZero = b`, which is
    honest-direction-only, and `ofPinnedDigitBase` at `γ = b − 1`, which also meets the pull-back
    orientation and so realizes the two-sided regime), one named corollary per seam,
    and `completePrefixReduction` — the appended bridge ▷ QuadEval ▷ `R^lin` ▷ lift ▷ batching ▷
    zero-check protocol, whose completeness is proved **modulo the sorried generic
    `Reduction.append_completeness` / `liftContext_completeness`** (so it is `sorryAx`-tainted, by
    design and recorded in the baseline; the per-link theorems it composes are not). What the
    non-short honest lift quotient *used to* cost was a zero-check range base of at least
    `q/2 + 1`, and — with the pull-back orientations — the collapse `γ = q/2 = bZero − 1`. Since
    `ZeroCheck/Constraints`'s `w̃` carries the quotient's base-`bZero` **digits** (NOZ26 §4.3's
    hidden gadget decomposition, `rhoDigits`), which are `⌊bZero/2⌋`-bounded for every quotient,
    that cost is gone: honest completeness of the batching bridge needs only
    `bound ≤ bZero − 1` (it goes through `ReduceClaim.reduction_completeness_of_imp`), so
    `γ` stays free. Adding the pull-back's reverse orientation pins the parameters, and
    `HonestRangeParams.pinned_of_soundness_orientations` now lands at the **healthy** point
    `γ = bZero − 1 < q/2`.
  - `Correctness.lean` — **the complete nonrecursive opening and its perfect correctness**. The
    chain is closed without the §4.5 recursion adapters by a `SendWitness`-style **terminal
    reveal-and-check**: the prover sends the final `LiftedWitness`, the verifier decides the whole
    `relWEvalClaim` predicate on it by returning `endPieceCheck` — the very check the guarded
    `EndPiece/` verifier guards on, with reflection lemma `endPieceCheck_eq_true_iff`, both
    axiom-clean — as its Boolean verdict (`terminalVerifier_verify_eq_endPieceCheck`). A zero-round
    **input adapter** (`commitInputReduction`, honest lemma `mem_relPolyEval_of_relCommitInput`)
    converts the commitment API's claim into `relPolyEval` for the balanced committer. Adapter ▷
    chain-through-sumcheck ▷ terminal compose into `hachiNonrecursiveOpening`, packaged with
    `commitBalanced` as the scheme `hachiNonrecursive`, and
    `hachiNonrecursive_perfectCorrectness` proves `Commitment.perfectCorrectness` via the generic
    bridge `Commitment.perfectCorrectness_of_opening_perfectCompleteness`
    (`Commitments/Functional/Basic.lean`, axiom-clean, on the new
    `OptionT.probEvent_eq_one_bind`). The three composed theorems inherit `sorryAx` from the
    admitted generic `Reduction.append_completeness` only (recorded in the baseline); every link,
    the adapter, the terminal step, and the bridge are individually axiom-clean. Recursion
    (`PartialEval`/`ZBatchBridge`/`TraceHandoff`) is deliberately not involved.
- Merkle trees live upstream in VCV-io under `VCVio/CryptoFoundations/MerkleTree/`: the vector
  commitment in `Vector/` (namespace `MerkleTree`) and the inductive tree in `Inductive/`
  (namespace `InductiveMerkleTree`).
- Reed-Solomon code definitions live under the `ReedSolomon` namespace: the base RS code in
  `ArkLib/Data/CodingTheory/ReedSolomon.lean`, and the folded/interleaved/multiplicity/multilinear
  variants under `ArkLib/Data/CodingTheory/ReedSolomon/` (see
  [coding-theory-conventions.md](coding-theory-conventions.md)).
- **Two different "folds" coexist and must not be confused.** GR08 *alphabet-enlarging* folding —
  a codeword symbol packs `(f̂(x), f̂(xω), …, f̂(xω^{s-1}))`, the degree bound is unchanged, and the
  code lives in `ι → Fin s → F` — is `ArkLib/Data/CodingTheory/ReedSolomon/Folded.lean`. The
  FRI/STIR-style *split-and-fold*, where a challenge contracts the polynomial and the evaluation
  domain shrinks, is `ProximityGap/Folding.lean`, `Data/Polynomial/SplitFold.lean`, and
  `Data/Polynomial/FoldingPolynomial.lean`; the "folded RS code" there is a plain RS code on a
  subdomain, not an FRS code.
- The ABF26 generic coding-theory layer sits in `ArkLib/Data/CodingTheory/` under the
  `CodingTheory` namespace: `SubspaceDesign.lean` (`IsSubspaceDesign` and the folded-RS
  subspace-design theorem), `ExtensionCodes.lean` (extension-field presentations and extension
  codes), `Erasure.lean` (erasure-consistency uniqueness below minimum distance),
  `HammingBallVolume.lean`,
  `Basic/Entropy.lean` (`qEntropy`). List-size bounds of Johnson type are in
  `JohnsonBound/Family.lean`, alongside the pre-existing `JohnsonBound/Basic.lean` machinery it
  consumes.
- List-size bounds that are *not* of Johnson type are under `ListDecodability/Bounds/`, with
  `ListDecodability/Bounds.lean` as the umbrella that imports them and carries the family overview,
  the quantification conventions and the shared reference list. The split is by scope, not by paper:
  `Bounds/Basic.lean` (the three counting identities everything rests on), `Bounds/Linear.lean`
  (bounds valid for every linear code — Elias volume and its entropy form, the rate–radius
  arithmetic, the generalized Singleton bound, random linear codes),
  `Bounds/LargeAlphabet.lean` (the exponential-alphabet barrier, over the four-file development in
  `Bounds/LargeAlphabet/`: statements and family counting, centres and incidence counting, the local
  neighbourhood bound and pigeonhole barrier, then sparse large-union families and the assembly),
  `Bounds/Interleaved.lean` ([GGR11]'s interleaved-code list-size bound),
  `Bounds/ReedSolomon.lean` (the Reed-Solomon separations and the random-evaluation-domain bound),
  `Bounds/SubspaceDesign.lean` ([CZ25]'s upper bound and the folded-RS and multiplicity-code
  corollaries) over `Bounds/AgreementHypergraph.lean` (the geometric agreement machinery that proof
  needs, which mentions no list size and is reusable), and `Bounds/KKH26.lean` plus
  `Bounds/KKH26Asymptotic.lean` (the concrete [KKH26] templates and ABF26 Theorem 3.15). The
  file/directory pair
  `ListDecodability.lean` + `ListDecodability/` follows the same shape as `ReedSolomon.lean` +
  `ReedSolomon/`: the file holds the definitions (`Lambda`, `listDecodable`), the directory holds
  results about them. Some deep bounds are externally sourced and carry tagged `sorry`
  annotations; use the paper KB pages and the axiom baseline to inspect their source and trusted
  impact. In-tree results include [CZ25]'s subspace-design theorem (and therefore the
  folded-Reed-Solomon and univariate-multiplicity capacity corollaries) and the [AGL23]
  large-alphabet barrier.
- ABF26's citation-heavy §4–§5 catalogue is separated from the core error definitions:
  `ProximityGap/CapacityBounds.lean` holds the numeric upper/lower bounds,
  `ProximityGap/LineDecoding.lean` holds the GG25-corrected interfaces corresponding to ABF26
  Definition 4.20 and Theorem 4.21, and
  `Connections/ListDecodingAndCA.lean` holds the four list-decoding/CA connections. Extensions
  that turn those admits into prize witnesses live below `ProximityGap/GrandChallenges/`, so the
  core `GrandChallenges.lean` grid and carrier API does not import the catalogue.
- The folded Wronskian (GK16 Definition 11) and its linear-independence criterion live in
  `ArkLib/Data/Polynomial/FoldedWronskian.lean`, not under `CodingTheory/`; its sibling
  `ArkLib/Data/Polynomial/ClassicalWronskian.lean` holds the ordinary Wronskian and the
  degree/derivative criterion behind the univariate-multiplicity half of ABF26 T2.18. Their
  generic determinant-divisibility and finite-field Kummer dependencies live in
  `ArkLib/ToMathlib/LinearAlgebra/Matrix/Determinant.lean` and
  `ArkLib/ToMathlib/FieldTheory/Kummer.lean`.
- **MDS lives in two shapes, and only one reaches module alphabets.** `LinearCode.IsMDS`
  (`Basic/LinearCode.lean`) is the `ℕ` Singleton-equality form and is stated only for
  `LinearCode ι F = Submodule F (ι → F)`; `LinearCode.IsMDS_iff_rate_distance` converts it to
  the `ℝ` rate-distance form `δ_min = 1 − ρ + 1/n` that ABF26 uses. Codes over a module
  alphabet `Fin s → F` (folded, interleaved, extension) **cannot** use the predicate and
  supply the rate-distance equation directly instead, at the alphabet-normalized rate
  `LinearCode.alphabetRate`: see `ReedSolomon.Interleaved.irs_rate_distance` (no divisibility
  needed) and `ReedSolomon.Folded.frs_rate_distance_of_dvd` (needs `s ∣ k`). Both feed the
  alphabet-generic `CodingTheory.mds_johnson_lambda_le_of_rate_distance`, whose module-alphabet
  consumers are `CodingTheory.irs_lambda_le_johnson_mds` and
  `CodingTheory.frs_lambda_le_johnson_mds` in `JohnsonBound/Family.lean`. Generalising the
  `IsMDS` *predicate* itself to `ModuleCode ι F A` is still open, and is **independent** of the
  module-alphabet `IsMCA` (which has landed): `IsMDSGenerator` constrains `C_G ⊆ F^|S|`, the
  generator's own code over the base field, so nothing on the MCA path needs it. Whoever does it
  should update this bullet and the corresponding row in
  [`../kb/audits/open-problems-list-decoding-and-correlated-agreement.md`](../kb/audits/open-problems-list-decoding-and-correlated-agreement.md).
- Finite-probability helpers live under the `Probability` namespace in
  `ArkLib/Data/Probability/Instances.lean` (see
  [probability-conventions.md](probability-conventions.md)); the collision bound for random
  functions is `ArkLib/Data/Probability/Combinatorial.lean`.
- Vandermonde matrix utilities shared across Reed-Solomon and proximity-gap developments live in
  `ArkLib/Data/Matrix/Vandermonde.lean`, not in the Reed-Solomon file.
- Trivariate polynomial utilities used by the BCIKS20 proximity-gap proofs
  (`evalAtX`, `evalAtY`, `evalAtZ`, the named degree projections, `D_Y`, `D_YZ`, and related
  notation) live in
  `ArkLib/Data/Polynomial/Trivariate.lean`, not in `ProximityGap/Basic.lean` or
  `ProximityGap/BCIKS20/ListDecoding/Guruswami.lean`. See
  [`polynomial-conventions.md`](polynomial-conventions.md) before applying generic bivariate
  operations to a trivariate value.
- **The reusable way into `perfectCompleteness` is `Reduction.perfectCompleteness_of_run_support`
  in `Security/Basic.lean`**, not the commented-out `perfectCompleteness_forall_challenge` sketch
  a few lines below it. It reduces perfect completeness to a support statement about the
  *unsimulated* `(Reduction.run …).run`: show every element of that support is a success whose
  output pair is in the output relation and whose two output statements agree, and the probability
  obligation is discharged (through VCVio's
  `OptionT.probEvent_eq_one_of_simulateQ_support_bind`, which handles the sampled initial state and
  the oracle implementation uniformly). It applies to any reduction, of any length, over any
  `oSpec` — no determinism or single-round hypotheses. The worked example is Hachi's zero-check
  (`Commitments/Functional/Hachi/ZeroCheck/Completeness.lean`), where the per-link work reduces to
  a prover-state induction, an output lemma, a run-support lemma, and the relation lemma. Before
  hand-peeling `OptionT`/`liftM`/`simulateQ` layers for a new protocol, check whether this covers
  it. (`Commitments/Functional/KZG/Correctness.lean` predates the lemma and still peels by hand.)
  The second worked example is `QuadEval` (`.../Hachi/QuadEval/Completeness.lean`), which adds the
  message-round case: there the run-support half is a closed-form computation of `Prover.run`
  (`prover_runToRound_last` / `prover_run_eq`) rather than an induction.
- **For a zero-round `ReduceClaim` link, do not use `perfectCompleteness_of_run_support` at all.**
  `ReduceClaim.reduction_completeness` (`ProofSystem/Component/ReduceClaim.lean`, proven) discharges
  the whole execution layer; its `hRel` is an **iff**
  (`(stmtIn, witIn) ∈ relIn ↔ (mapStmt stmtIn, mapWit stmtIn witIn) ∈ relOut`), so the only real
  obligation is the converse of the pull-back the soundness side already needed. Three links are
  done this way — `bridgeReduction_perfectCompleteness` (`QuadEval/Bridge.lean`),
  `rlinReduction_perfectCompleteness` (`RingSwitch/Completeness.lean`) and
  `batchReduction_perfectCompleteness` (`ZeroCheck/Completeness.lean`) — each in a few lines once
  the relation converse exists. Budget zero-round heads in hours, not days.
- **The two-round commit-then-challenge execution is owned generically** by
  `CoordinateWise.CommittedScalar.reduction_perfectCompleteness`
  (`Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean`): supply `computeW` plus the two
  facts `rel K checkAt` asks for that are not definitional — the challenge-local check at *every*
  challenge, and admissibility of the computed opening — and the run/probability layer is free.
  Commitment consistency is definitional, because the prover shell derives its round-0 message from
  `computeW`. Consumers: the generic ring-switching lift and, through it, Hachi's Figure 4. Any new
  link of that shape (`pSpecScalar`) should go through it rather than repeating `QuadEval`'s
  hand-unfolding.
- **Unfolding a fixed-length `Prover.runToRound` by hand: ascribe the round indices, do not rewrite
  them.** `Prover.runToRound_succ` is stated at `i.succ` with the recursive call at `i.castSucc`,
  but a concrete run starts from `Fin.last n`, and `Fin.last 2`, `Fin.succ 1`, `Fin.castSucc 1` and
  `(1 : Fin 3)` are equal only after `Fin.val`/`Nat.mod` arithmetic. Consequences, all hit while
  proving `QuadEval` completeness:
  - `rw` on the index itself (`show Fin.last 2 = Fin.succ 1 from rfl`) fails with "motive is not
    type correct", and `rw [Prover.runToRound_succ 1]` fails to match `runToRound (Fin.last 2)`.
  - The working shape is to *state* each unfolding as a `have` at the index that literally occurs
    (`Fin.last 2`, then `(1 : Fin 2).castSucc`, then `(0 : Fin 2).castSucc`) and prove it by the
    framework lemma — the `have`'s type ascription is checked at full transparency, so the indices
    reconcile there instead of inside `rw`. Chain them with `Eq.trans` / `rw`.
  - At index `castSucc 0` the `Unique (Transcript 0 pSpec)` instance is not found; write the empty
    transcript as `fun i => Fin.elim0 i` instead of `default`.
  - Pass the direction proof (`pSpec.dir 1 = .V_to_P`) as a *named hypothesis*, not `rfl`:
    `⟨1, rfl⟩` makes the surrounding term ill-typed at `instances` transparency, which silently
    stops both `rw` matching and `simp` congruence.
  - Once the rounds are unfolded, `simp [monad_norm, liftM, monadLift, MonadLift.monadLift]`
    followed by `rfl` closes the monadic bookkeeping; `FullTranscript.mk2` and
    `FullTranscript.mk2_eq_snoc_snoc` are the bridge between the `Transcript.concat` chain the
    prover builds and the two transcript slots the verifier reads.
- Transcript-tree infrastructure for special-soundness-style notions lives in
  `Security/TranscriptTree/`: `Basic` defines `ChallengeTree`, `LeafPath`,
  `ChallengeTreeShape`, `ChallengeTree.IsStructured`, `ChallengeTree.IsAccepting`,
  `Extractor.TreeBased`, and the shape-generic soundness core `Verifier.treeSpecialSound`. The
  extractor is **witness-only**: it consumes the tree *and* one candidate output witness per leaf
  (`ChallengeTree.LeafWitnesses`, honest when each answer certifies in `relOut` some statement the
  verifier can actually output there — `LeafWitnesses.IsValid`), and returns `Option WitIn`. The
  notion says extraction succeeds on every `S`-structured accepting tree at every valid witnessing;
  the unconditioned reading follows by closing the extractor at `ChallengeTree.canonWitnesses`
  (`treeSpecialSoundWith.mem_relIn_of_isAccepting`). `Basic` also defines the **escape layer**:
  `ChallengeTree.EscapeEvent` (a statement-indexed predicate on full challenge trees, with the
  trusted-spec contract in its docstring) and
  `Verifier.treeSpecialSoundWithEscape`, whose conclusion is `esc stmt tree ∨ extraction succeeds`;
  the plain notion is the never-firing event (`treeSpecialSoundWithEscape_false_iff`) and every plain
  certificate lifts losslessly (`treeSpecialSoundWith.withEscape`). `Composition`
  defines shape append, `appendSplit`, the generic structure-preservation/recombination lemmas
  for sequential protocol append, and `ChallengeTree.EscapeEvent.append` (composition of escape
  events along that split). The umbrella `Security/TranscriptTree.lean` re-exports both files.
  Both plain and coordinate-wise special soundness are instances of `Verifier.treeSpecialSound` for
  different shapes; neither special-soundness file imports the other.
- Plain `(k)`-special soundness lives in `Security/SpecialSoundness.lean`. It is the instance of
  `Verifier.treeSpecialSound` for the pairwise-distinct shape `distinctShape k` (arity `kᵢ`, node
  predicate `Function.Injective`), with input/output relations like CWSS; it is the `ℓᵢ = 1`
  specialization of coordinate-wise special soundness. The bridge
  `coordinateWiseSpecialSound (ofSpecialSound k) ↔ specialSound k` lives in
  `Security/Implications.lean`.
- Round-by-round security lives in `Security/RoundByRound.lean` (state functions,
  `Extractor.RoundByRound`, the one-shot variants and their bridges, plus the **worst-case** layer
  `rbrSoundnessWorstCase` / `rbrKnowledgeSoundnessWorstCase` and the implications back to the
  averaged notions), on top of the probability glue in `Security/RbrGame.lean` (the challenge-first
  master bounds over `simulateQ`/`OptionT` that discharge those implications). This is a **separate
  axis** from the transcript-tree notions below: its extractor type is `Extractor.RoundByRound` on
  transcripts, not `Extractor.TreeBased`, and it carries no escape-event layer.
- Coordinate-wise special soundness ([FMN24]/[NOZ26]) lives in
  `Security/CoordinateWiseSpecialSoundness/`: `Basic` defines the `SS(S, ℓ, k)` combinatorics
  (`CoordEq`, `IsSpecialSoundFamily`), `CWSSStructure`, `CWSSStructure.toShape`, and both forms
  of the soundness notion — the **named-extractor form**
  `Verifier.coordinateWiseSpecialSoundWith` (the content-bearing statement; the extractor is an
  explicit parameter) and its existential closure `Verifier.coordinateWiseSpecialSound` (plumbing;
  it loses the algorithm, so advertised protocol statements use the named form) — plus their
  escape-threaded twins `…WithEscape` / `…Escape` and the lossless lift
  `coordinateWiseSpecialSoundWith.withEscape`; `Composition`
  transports CWSS structures across protocol append and proves binary append preservation
  via the generic transcript-tree split, in all forms (the composed extractor is the left
  factor's on the prefix tree, the composed event is `ChallengeTree.EscapeEvent.append`), and hosts
  the two directions of the pure-verifier acceptance bridge (`pure_accepting_of_mem` /
  `mem_of_pure_accepting`); `NoChallenge` supplies the empty-challenge base case. **Composition is
  binary only** — there is no n-ary CWSS `seqCompose`; chains are built by recursion over the binary
  append (`▷`), which keeps the composed extractor a nameable function. All CWSS packages
  (`CWSSPackage` and its guarded / escape-aware variants) carry their extraction algorithm as an
  explicit `extractor` field, with the `isCWSS` certificate stated at it — so a composed chain
  exposes an actual end-to-end extractor (`chain.extractor`). `NoChallenge` also provides
  `CWSSStructure.ofIsEmpty`, the concrete
  challenge-free structure used as the left factor when appending a zero-round `ReduceClaim` head
  (e.g. Hachi's `bridgeVerifier`). `SingleRound` is the generic single-challenge-round navigation
  layer (tree shape recovery `tree_shape`, the star-center machinery, the tree extractor
  `treeExtractor`, and the assemblies `coordinateWiseSpecialSoundWith_of_mkWitness` and its escape
  twin at the induced event `escEvent`) used by Hachi's polynomial-evaluation reduction `QuadEval`
  (Lemma 8). `ScalarRound` is its **proven** `(ℓ = 1, k)` scalar-challenge twin (`pSpecScalar`,
  `scalarStructure`, readers/shape recovery, the per-branch transcript kit,
  `treeExtractorScalar`, `escEventScalar(OfValid)`, and both assemblies
  `coordinateWiseSpecialSoundWith(Escape)_of_mkWitness_scalar`) for Hachi's Lemmas 9/11-shaped
  rounds and the DP24 batching wire format. `CommittedScalar` is the **proven** commit-then-
  scalar-challenge shell on top of `ScalarRound`: `BindingCommitment` (a commitment indexed by the
  shortness regime its binding is restricted to, with its short-collision set `Collision`), the
  anchored relation/verifier/prover, the plain assembler `mkWitness`, the binding-break escape
  event `escEvent`, the named `treeExtractor`, and its generic certificate + `EscapeCWSSPackage`;
  instantiated by the generic HMZ25 lift (`ProofSystem/RingSwitching/Lift/`) and through it by
  Hachi's ring switch. `Escape` is the **package lattice**: the escape-aware packages
  `EscapeCWSSPackage`/`EscapeGCWSSPackage` (ordinary relations and extractor, plus one `esc`
  **event** field), the lossless kind lifts `toEscape`/`toGuarded`, all mixed appends, and the
  universal `▷` elaborator dispatching over the 2×2 grid escape? × guarded?. Since escapes are
  events on `(statement, tree)`, composition matches only relation seams. `Guarded` is the
  **proven** runtime-rejection layer: `Verifier.IsGuardedWith`/`IsGuarded` and their data form
  `Verifier.GuardedForm` (check and verdict map as fields, which keeps composed extractors
  computable), the guarded package `GCWSSPackage` with its append `▷ᵍ`, the guarded seam
  lemmas, and both guarded binary CWSS append theorems (plain and escape-threaded). The umbrella
  `CoordinateWiseSpecialSoundness.lean` re-exports the core files.
- Active areas are often grouped by paper or protocol family, for example
  `Data/CodingTheory/ProximityGap/BCIKS20/...` or `ProofSystem/Binius/...`.
- The ABF26 Section 6 toy IOP lives under `ProofSystem/ToyProblem/`. `Spec/` contains the
  domain-generic protocol and extraction theorems, `Impl/IRS.lean` supplies the computable
  interleaved Reed--Solomon extractor, `Impl/FRS.lean` contains neutral KoalaBear folded-RS
  reference points, and `Codegen.lean` enforces compiler-IR availability. The simplified IOR
  (`SimplifiedIOR`) is an `OracleReduction` with a query-by-query virtual output oracle and
  exact named interleaved-RS straightline and RBR extractors. The compiled small-parameter
  checks run with
  `lake exe toyproblem-runtime`; the security theorems themselves are parametric in the code, the
  radius, and the repetition count, so they apply at production sizes without evaluation. Turning
  such a theorem into a *numeric* error value additionally requires the MCA/CA capacity bounds in
  `Data/CodingTheory/ProximityGap/CapacityBounds`, several proven and the rest external admits,
  deliberately outside the toy-problem import cone; no numeric error value is proven in-tree at
  any production shape.
- Batched FRI's batching round now emits the random-linear-combination codeword directly as a
  virtual output oracle. The former `BatchedFri.Spec.liftingLens` / `liftedFRI` repair layer was
  removed rather than renamed: downstream code should compose
  `BatchingRound.batchOracleReduction` directly with `Fri.Spec.reduction` as
  `BatchedFri.Spec.batchedFRIreduction` does.
- Virtual-output execution commutes through append, salt, cast, and executable lifting. This does
  not close the inherited generic append-security boundary: the unrestricted `StateT`
  completeness/soundness composition theorems in `Composition/Sequential/Append.lean` remain
  admitted and must not anchor a standalone security claim.
- Ring switching is a **family of constructions, not one protocol** — the umbrella
  `ProofSystem/RingSwitching/Basic.lean` carries the taxonomy over two construction folders.
  `Packing/` is the small→large packing family: `Profile.lean` holds the shared
  packing data layer `RingSwitchingProfile` (packing data + reconstruction laws) and the
  remaining files are the DP24/Binius construction (`Prelude` with `packMLE` + the Binius
  instance `binaryTowerProfile`, `Spec`, `BatchingPhase`, `SumcheckPhase`, `General`; RBR
  soundness, `[IsDomain L]`); Binius instantiates it in `ProofSystem/Binius/FRIBinius/`
  (`biniusProfile`), and Hachi's §3 packing head is the intended next `Profile` instance.
  `Lift/` is the **generic HMZ25 lift** (large quotient ring →
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
  Background: KB concept page `docs/kb/concepts/ring-switching.md`; blueprint section
  `proof_systems/ring_switching.tex`. Structured sum-check support lives in
  `ProofSystem/Sumcheck/Structured*` and `ProofSystem/Sumcheck/Domain.lean`.
- Before assuming a file is authoritative, check whether it is source or derived output. See
  [`generated-files.md`](generated-files.md).
