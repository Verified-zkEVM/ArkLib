# 04 — Oracle Elimination: Compiler Passes, Backends, and Guarantee Transport

**Normative interfaces, fluid internals.** How ideal oracle reductions become real argument systems.
Validated against Chiesa–Yogev's BCS chapters (whose modular proof factors exactly as this pipeline:
`BCS = HashChainFS(iBCS)`); the preserved
[CY coverage audit](https://github.com/Verified-zkEVM/ArkLib/blob/archive/oracle-reduction-v2-pre-split/docs/design/archive/gpt-cy-coverage.md)
is this document's conformance suite.

## 1. The pipeline

```
ideal oracle reduction (Δ oracles, Γ = ∅ or small)
  ├─ RepresentOracles   oracle resources/messages ↦ commitment handles (in Γ-worlds)
  ├─ LowerAccesses      ideal reads ↦ responses + verified opening arguments
  ├─ TransportBoundary  inline | seal-and-link | derive (CommitAction)
  └─ FiatShamir         public coins ↦ challenges from the world (hash-chain or basic)
→ NARG = the Δ = ∅, one-message case of the same Reduction type, in world Γ
```

Passes are separate because their hypotheses differ; **but their security proofs cross pass boundaries through the runner-produced query trace** (FS-event order controls Merkle-trace segmentation controls extraction controls SR moves). Therefore passes exchange proof-relevant VCVio runtime artifacts and certified PolyFun/VCVio transducers, not just rewritten syntax + semantic equivalence. Each pass exposes source and target security games, a protocol-erasure theorem, a relation transformer, a schedule invariant, and concrete transducer adapters. Its security transfer pairs VCVio's existing `ReductionWithCost` with the explicit advantage-error transform required by that pass; the future generic package may bundle those two components once a client fixes the reusable interface.

The target object is not a new framework: a compiled NARG *is* an oracle reduction with empty claim-oracle context, living entirely in Γ — CY's adaptive NARG games are the Δ=∅ instances of `03` §4.

## 2. GuaranteeTransport (D1 — the pass invariant)

Every type-level guarantee on an ideal oracle slot (degree bound, codeword membership, well-formedness) must be explicitly discharged by the compilation of that slot. Crucially, the guarantee must be **reified** — an arbitrary refined Lean type does not expose its predicate to the compiler, so subtype inspection cannot be the API:

```lean
structure OracleGuarantee where
  Raw    : Type                 -- unrefined carrier
  good   : Raw → Prop           -- the reified promise
  oracle : OracleInterface Raw

abbrev OracleGuarantee.IdealObj (G) := {x : G.Raw // G.good x}
-- Ideal slots are typed as G.IdealObj; slot metadata carries G itself.

structure GuaranteeTransport (G : OracleGuarantee) (A : CommitBackend …) where
  -- accepted openings of this slot are consistent with SOME good raw object
  enforce       : AcceptedOpenings A → … (Σ x : G.Raw, G.good x ∧ OpeningsRealize A x)
  error         : ErrorFunctional      -- ε_{G} enters the additive/substitution budget
  enforce_bound : …
```

`ResourceMeta` (or the slot schema) carries the `OracleGuarantee` descriptor explicitly; `BackendAssignment` matches descriptors to backend capabilities, and a slot whose guarantee no selected backend can discharge is a **compilation error surfaced at assignment time**. Promise-free slots use `good := fun _ => True`.

Instances: bounded-degree slots → PCS degree enforcement or low-degree tests. **Proximity testing does not discharge an exact-codeword guarantee**: it establishes closeness, not consistency with an exact codeword behavior — an exact-codeword slot needs either an explicit guarantee-*relaxing* reduction whose output relation records proximity (FRI/STIR used as guarantee-restoring reductions, with the relaxation visible in the relation), followed by a decoding/query-agreement bridge, or a backend that extracts an exact codeword consistent with every accepted opening. Plain vector slots → trace coherence only. This is the precise sense in which "proofs go off the wire" at compilation: the ideal promise becomes a cryptographic obligation, and the obligation's error appears in the final bound.

## 3. Modes at output boundaries

1. **Inline (fixed consumer):** compose first; lower the actual finite consumer through the virtual plan; each source query becomes an opening. Needs `FiniteConsumer`/staged plans (response-adaptive consumers need staged query programs, not just static bundles). No commitment for derived views. Ordinary soundness needs **trace coherence** (all accepted answers embed in one total behavior per handle); stronger binding only when the ideal relation promises representability or forks must agree.
2. **Seal-and-link (reusable boundary):** materialize, commit, change the relation to `Com_A[R]`, and prove a **malicious link** (consistency reduction / alias theorem). Honest `Materialization.correct` is never sufficient.
3. **Derive (`CommitAction`):** backend-specific public action on commitments for a certified plan fragment (Nova: linear/quadratic-in-challenge plans over Pedersen). Capability-indexed; no generic homomorphic action exists.

`Com_A[R]` is heterogeneous by construction (`BackendAssignment`: per-resource backend, setup, encoding, ownership); the homogeneous `Com_F[R]` is the special case. The committed-schema transformer is normative — randomized commitment execution must never hide inside `Prop`:

```lean
def ComProblem (A : BackendAssignment) (P : Problem S) : Problem (ComSchema A S) where
  Witness ctx cc := Σ decoded : S.Claim ctx,
                    P.Witness ctx decoded × A.OpeningWitness cc decoded
  admissible ctx cc := …  -- WellFormedSetup ∧ EncodesPromise ∧ P.admissible on decoded
  rel ctx cc w := P.rel ctx w.1 w.2.1 ∧ A.RealizesHandles cc w.1 w.2.2
```

Commitment randomness and openings live in the **witness**; `RealizesHandles` is a deterministic relation (or the accepted outcome of a separately modeled commitment protocol). Witnesses are claim-dependent (`02` §6) precisely because of this transformer.

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

The pass × property matrix (normative; reproduced from round 3 so this document has no hidden archive dependency):

| Pass | Functional correctness | Ordinary soundness | Knowledge/extraction | Zero knowledge |
|---|---|---|---|---|
| `RepresentOracles` | honest commitment correctness; public-view projection | none by itself | none by itself | commitment leakage only |
| `LowerAccesses` | opening correctness + plan/trace erasure | trace coherence; stronger binding only when the ideal relation needs it | multi-extraction/WEE or backend tree extraction, with fork coherence | bounded-query ideal simulator + selective/adaptive hiding + opening simulation |
| fixed-consumer inline | composed evaluator equals lowered consumer | inherited after access lowering | inherited only with the preceding extraction theorem | leakage of the concrete consumer trace is charged |
| seal-and-link boundary | materialization + link correctness | sound link argument + target-handle coherence | extractable link or RBRTE-compatible witness relation | simulatable link argument |
| `CommitAction` boundary | representation commuting square | action correctness + required binding across forks | leaf openings/witnesses + relational tree bridge | action leakage + simulator compatibility |
| batching (own transform) | batch verifier equals individual obligations | native batch soundness or proved reduction | native multi-instance extraction | batch-proof simulation |
| `FiatShamir` | transcript/challenge agreement | state-restoration soundness in the chosen RO model | state-restoration function binding/extraction or RBRTE theorem | programmable-RO/QROM simulator as applicable |

Recursive compilation of opening protocols needs a well-founded measure (unrepresented oracle nodes, then depth). Errors and times remain explicit functions (substitution mode for KS: `ε_NARG-KS = ε_IOP-SRKS(λ+s_FS, N, Q, δ_A + ε_MT + ε_chain) + …`). Cost and resource transport reuse VCVio's existing carriers; advantage errors remain explicit until the first compiler client establishes the reusable error-bearing reduction package. Compilation fixes a topological schedule (key binding → absorption → challenges → queries → openings → decision) recorded in `ResourceMeta`; budget splits (`Q_MT + Q_FS ≤ Q`) are `ResourceProfile` feasibility constraints, and bounds like `ε_rbr + Q·ε_bind` are corollaries only when the conditional union bound is proved.
