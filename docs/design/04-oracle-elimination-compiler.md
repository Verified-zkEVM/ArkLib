# 04 — Oracle Elimination: Compiler Passes, Backends, and Guarantee Transport

**Normative interfaces, fluid internals.** How ideal oracle reductions become real argument systems. Validated against Chiesa–Yogev's BCS chapters (whose modular proof factors exactly as this pipeline: `BCS = HashChainFS(iBCS)`); the CY coverage audit (archive) is this document's conformance suite.

## 1. The pipeline

```
ideal oracle reduction (Δ oracles, Γ = ∅ or small)
  ├─ RepresentOracles   oracle resources/messages ↦ commitment handles (in Γ-worlds)
  ├─ LowerAccesses      ideal reads ↦ responses + verified opening arguments
  ├─ TransportBoundary  inline | seal-and-link | derive (CommitAction)
  └─ FiatShamir         public coins ↦ challenges from the world (hash-chain or basic)
→ NARG = the Δ = ∅, one-message case of the same Reduction type, in world Γ
```

Passes are separate because their hypotheses differ; **but their security proofs cross pass boundaries through the global `WorldTrace`** (FS-event order controls Merkle-trace segmentation controls extraction controls SR moves). Therefore passes exchange **proof-relevant execution artifacts and trace transducers**, not just rewritten syntax + semantic equivalence. Each pass exposes: source/target game families, protocol-erasure theorem, relation transformer, schedule invariant, security-transfer theorem with V7-functional errors, and its transducers.

The target object is not a new framework: a compiled NARG *is* an oracle reduction with empty claim-oracle context, living entirely in Γ — CY's adaptive NARG games are the Δ=∅ instances of `03` §4.

## 2. GuaranteeTransport (D1 — the pass invariant)

Every type-level guarantee on an ideal oracle slot (degree bound, codeword membership, well-formedness) must be explicitly discharged by the compilation of that slot:

```
for each slot s with interface guarantee G_s:
  RepresentOracles(s) must name the backend obligation O_s  (commit-phase or open-phase)
  and the security transfer theorem consumes a capability record proving O_s enforces G_s
  (exactly: accepted openings of s are consistent with SOME object satisfying G_s,
   with error ε_{G_s} entering the additive/substitution budget).
```

Instances: bounded-degree slots → PCS degree enforcement or low-degree tests; codeword slots → proximity tests (FRI/STIR as *guarantee-restoring reductions* before/after transport); plain vector slots → trace coherence only. A slot whose guarantee no selected backend can discharge is a **compilation error**, surfaced at `BackendAssignment` time. This is the precise sense in which "proofs go off the wire" at compilation: the ideal promise becomes a cryptographic obligation, and the obligation's error appears in the final bound.

## 3. Modes at output boundaries

1. **Inline (fixed consumer):** compose first; lower the actual finite consumer through the virtual plan; each source query becomes an opening. Needs `FiniteConsumer`/staged plans (response-adaptive consumers need staged query programs, not just static bundles). No commitment for derived views. Ordinary soundness needs **trace coherence** (all accepted answers embed in one total behavior per handle); stronger binding only when the ideal relation promises representability or forks must agree.
2. **Seal-and-link (reusable boundary):** materialize, commit, change the relation to `Com_A[R]`, and prove a **malicious link** (consistency reduction / alias theorem). Honest `Materialization.correct` is never sufficient.
3. **Derive (`CommitAction`):** backend-specific public action on commitments for a certified plan fragment (Nova: linear/quadratic-in-challenge plans over Pedersen). Capability-indexed; no generic homomorphic action exists.

`Com_A[R]` is heterogeneous by construction (`BackendAssignment`: per-resource backend, setup, encoding, ownership); the homogeneous `Com_F[R]` is the special case. Witnesses are claim-dependent (`02` §6) precisely because committed claims put openings in the witness.

## 4. Backends as game-indexed capability records

A capability is a **complete game record**: experiment + phase structure + trace inputs + budget functional + extractor/simulator + error/time functionals + monotonicity/superadditivity facts. Never a bare `Prop`. The Merkle/ROM backend — the CY conformance target — needs at least:

```
Correctness, Binding, HonestTreeBinding,
SingleTraceExtractability,            -- two-phase; extractor eats commit-phase WorldTrace;
                                      -- partial-tree reconstruction; arbitrary completion;
                                      -- bad event = later-opening disagreement
StatefulMultiExtractability,          -- online transducer state; trace INCREMENTS;
                                      -- repeated-root coherence; non-union-bound error
MultiConfigurationExtractability,     -- per-configuration projection of one global trace
RootHiding, SelectiveOpeningPrivacy (local-view simulator), Equivocation
```

with explicit tree-shape/padding/encoding data (leaf-vs-internal query classification requires disjoint encodings — an *injectivity proof*, not a `domainSep` tag) and salt parameters. The current `Commitments/Functional/Basic.lean` placeholder (`extractability` ending in `False`, single-commitment binding) must never be cited by a compiler theorem.

`BCSPublicView` (commitments + challenges + clear messages) is distinct from the erased `SharedTranscript` skeleton; query functions read the former.

## 5. Fiat–Shamir

Consumes: public-coin replayable structure, exact serialization/absorption order, domain separation, and **state-restoration security of the interactive argument produced by the earlier passes** (CY's modular route). Hash-chain and basic variants both provided; hash-chain needs backtracking transducers. FS and RepresentOracles share a typed **public event log** substrate (`TranscriptTransform`) but remain separate passes (BCS applies without replayability; FS requires it).

## 6. Nova (the algebraic conformance case)

Kept as in the round-3 document (archive §6.10.6), now with D1 phrasing: the ideal relaxed-R1CS fold is an L3 reduction whose output slots are `linComb` plans; W/E slots carry no guarantee beyond shape (relaxed R1CS has no proximity promise — GuaranteeTransport is trivial there, which is *why* no consistency sampling appears); Pedersen's `commitWithOpening` linearity is the `CommitAction`; security = three-branch language-special-soundness tree + binding across forks → relational extraction for `Com[R_rel]`; the FRI contrast (Merkle roots admit no fold action → fresh word + sampled consistency + proximity guarantee restoration) is the two modes side by side.

## 7. Theorem matrix and schedule

The per-pass × per-property matrix from round 3 stands (correctness / soundness / knowledge / ZK per pass; batching as its own transform; recursion needs a well-founded measure). Additions from round 4: all errors/times in the matrix are V7 functionals (substitution mode for KS: `ε_NARG-KS = ε_IOP-SRKS(λ+s_FS, N, Q, δ_A + ε_MT + ε_chain) + …`); compilation fixes a topological schedule (key binding → absorption → challenges → queries → openings → decision) recorded in `ResourceMeta`; budget splits (`Q_MT + Q_FS ≤ Q`) are ledger constraints, and bounds like `ε_rbr + Q·ε_bind` are corollaries only when the conditional union bound is proved.
