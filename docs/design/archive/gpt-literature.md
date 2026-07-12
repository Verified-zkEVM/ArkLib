# Requirements Catalog for a Definitive Interactive Oracle Reduction Abstraction

**Survey date:** 12 July 2026  
**Scope:** Classical, finite interactive oracle protocols used in SNARKs, IOPs, PIOPs, IORs, folding, and accumulation. Quantum and genuinely nonterminating protocols are identified as explicit extensions rather than silently excluded.

## 1. Executive conclusion

The right foundational object is not “a verifier that eventually accepts or rejects,” nor even “a protocol returning a tuple of oracle values.” It is:

> A transcript-dependent interactive reduction from one typed oracle context to another, whose output oracles are typed query interpreters carrying explicit provenance into earlier context resources.

The protocol shape should be a dependent interaction tree rather than a flat list of rounds. Public moves may select later protocol structure; oracle-hidden moves may not. The output should distinguish:

- ordinary public claims;
- freshly sent oracle resources;
- virtual oracle handles whose queries are simulated from earlier resources;
- provenance and cost information for those simulations;
- the witness state forwarded by the honest prover.

Security notions should be predicates and games over this common executable semantics—not fields embedded in the protocol structure. Compilation to Merkle commitments, polynomial commitments, Fiat–Shamir, recursive verification, and accumulation should operate on typed interfaces and resource dependencies, not inspect protocol-specific definitions.

### Virtual-output verdict scale

- **Essential:** explicit output data is the wrong abstraction.
- **Preferred:** both work, but simulation-based outputs compose better.
- **Neutral:** the issue is orthogonal.
- **Explicit preferred:** the resource really is newly materialized; nevertheless it should receive a handle for subsequent composition.

---

# 2. Core reduction and claim requirements

## R1. Reductions between relations, not only accept/reject proofs

**Protocols and evidence.** Sumcheck reduces a sum claim in \(n\) variables to one in \(n-1\) variables; FRI and STIR recursively reduce proximity to a large Reed–Solomon code to proximity to a smaller code; Nova reduces two satisfiability instances to one folded instance. Nova explicitly characterizes folding as weaker than a proof of knowledge because it only reduces satisfiability of multiple instances to satisfiability of one instance. ARC and WARP likewise use IORs whose verifier outputs a new explicit/implicit instance rather than a Boolean. [Nova](https://eprint.iacr.org/2021/370.pdf), [FRI](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ICALP.2018.14), [STIR](https://eprint.iacr.org/2024/390.pdf), [ARC](https://eprint.iacr.org/2024/1731.pdf), [WARP](https://eprint.iacr.org/2025/753.pdf).

**Lean design pressure.** The foundational type must be parameterized by input and output statement/witness families:

\[
R_{\mathrm{in}}\subseteq \mathsf{StmtIn}\times\mathsf{WitIn},
\qquad
R_{\mathrm{out}}(tr)\subseteq
\mathsf{StmtOut}(tr)\times\mathsf{WitOut}(tr).
\]

The output family may depend on the realized public transcript. A proof system is only the specialization where the output relation is a decision relation or `Bool`.

**Virtual-output assessment:** **Preferred.** Some reductions output only scalar claims, but treating every output uniformly as a context makes composition much simpler.

---

## R2. Relation-changing and representation-changing reductions

**Protocols and evidence.** Nova changes R1CS into relaxed committed R1CS; ProtoStar compiles special-sound protocols into accumulation relations; ProtoGalaxy folds multiple base instances into a separate accumulator relation. ARC moves between rationally constrained RS proximity relations, and WARP reduces polynomial-equation satisfiability to code proximity relations. [Nova](https://eprint.iacr.org/2021/370.pdf), [ProtoStar](https://eprint.iacr.org/2023/620.pdf), [ProtoGalaxy](https://eprint.iacr.org/2023/1106.pdf), [ARC](https://eprint.iacr.org/2024/1731.pdf), [WARP](https://eprint.iacr.org/2025/753.pdf).

**Lean design pressure.** Do not require `StmtOut = StmtIn`, `WitOut = WitIn`, or even the same oracle schema. Relations should be indexed by public parameters such as a field, code, domain, degree bound, circuit shape, or preprocessing key. The reduction must be able to change those indices.

**Virtual-output assessment:** **Preferred.** Representation changes often preserve the underlying data only through a new query interpretation.

---

## R3. Multiple input and output claims

**Protocols and evidence.** Batching combines many polynomial evaluation or proximity constraints; WHIR batches multiple constrained-RS claims by random linear combination; ProtoGalaxy folds many instances in one step; accumulation schemes accept both new instances and old accumulators. [WHIR](https://eprint.iacr.org/2024/1586.pdf), [ProtoGalaxy](https://eprint.iacr.org/2023/1106.pdf), [WARP](https://eprint.iacr.org/2025/753.pdf).

**Lean design pressure.** A context should be a heterogeneous indexed family, not a single statement plus a single oracle. It should support dependent finite maps or telescopes of claims, with structural operations for insertion, projection, permutation, batching, and splitting.

**Virtual-output assessment:** **Essential** for efficient batching: the combined claim often references a random linear combination without materializing an additional full codeword.

---

## R4. Honest-prover witness forwarding

**Protocols and evidence.** Folding and accumulation require the verifier to output an accumulator instance while the honest prover privately outputs its corresponding accumulator witness. WARP explicitly uses split accumulators with short instance and long witness parts; Nova folds both public committed instances and private witnesses. [Nova](https://eprint.iacr.org/2021/370.pdf), [WARP](https://eprint.iacr.org/2025/753.pdf).

**Lean design pressure.** The honest prover and verifier have related but different outputs. Execution should produce:

\[
(\mathsf{public\ output},\ \mathsf{honest\ witness\ output}),
\]

while malicious-verifier security games and malicious-prover games may expose different projections. Do not identify “prover output” with transcript data.

**Virtual-output assessment:** **Neutral.** Witness forwarding is private state, although virtual output handles may refer to witness-derived resources.

---

# 3. Oracle and query requirements

## R5. Heterogeneous oracle interfaces

**Protocols and evidence.**

- Classical IOPs use point-query access to proof strings. [Interactive Oracle Proofs](https://eprint.iacr.org/2016/116.pdf).
- FRI, STIR, ARC, and WHIR use functions or RS codewords queried at domain positions.
- Marlin’s AHP uses polynomial oracles queried by evaluation at arbitrary field points.
- Multilinear protocols query evaluations at vectors of field elements.
- Ligero treats an oracle as a matrix or interleaved family of codewords.
- The 2026 query-optimal IOPP result is built around tensor-code rows and columns. [Marlin](https://eprint.iacr.org/2019/1047.pdf), [Ligero](https://eprint.iacr.org/2022/1608.pdf), [Query-Optimal IOPPs](https://doi.org/10.1007/978-3-032-25336-1_4).

**Lean design pressure.** Each resource needs an associated query family and response family:

```lean
interface OracleInterface (A : Type) where
  Query    : Type
  Response : Query → Type
  answer   : A → (q : Query) → Response q
```

The response may depend on the query. Interfaces must be first-class data, not globally inferred type classes only, because the same underlying data can legitimately support several interfaces.

**Virtual-output assessment:** **Essential.** A virtual oracle is fundamentally a query interpreter for one of these interfaces.

---

## R6. Structured and batched queries

**Protocols and evidence.** Ligero samples a random row combination and checks selected columns; WHIR combines multiple polynomial oracles into a virtual linear combination; tensor IOPPs issue row/column claims and lossy batches; polynomial commitments batch evaluation openings at multiple points or for multiple polynomials. [Ligero](https://eprint.iacr.org/2022/1608.pdf), [WHIR](https://eprint.iacr.org/2024/1586.pdf), [Query-Optimal IOPPs](https://doi.org/10.1007/978-3-032-25336-1_4).

**Lean design pressure.** A query cannot be assumed to be a scalar index. It may describe:

- a point;
- a vector of points;
- a row, column, affine line, or tensor slice;
- a linear functional;
- a batch of heterogeneous subqueries;
- a query whose response is itself structured.

The interface should expose lawful batching or product constructions separately from atomic access.

**Virtual-output assessment:** **Essential.** Structured queries are often answered by composing queries to several source oracles.

---

## R7. Adaptive query schedules and query phases

**Protocols and evidence.** In an IOP the verifier may defer queries until after all oracle messages and challenges; STIR and WHIR have interaction phases followed by consistency/proximity queries; compilation opens only the queried positions. The original IOP definition allows the verifier’s queries to depend on the transcript. [Interactive Oracle Proofs](https://eprint.iacr.org/2016/116.pdf), [STIR](https://eprint.iacr.org/2024/390.pdf), [WHIR](https://eprint.iacr.org/2024/1586.pdf).

**Lean design pressure.** Do not execute a query merely because an oracle message is sent. Oracle publication and oracle access are separate events. Query computations need effects, logs, and transcript-indexed access permissions. The semantics must distinguish adaptive from nonadaptive queries where security or batching theorems require it.

**Virtual-output assessment:** **Essential.** Simulation is invoked at query time, not when the virtual resource is declared.

---

## R8. Mixed public and oracle-hidden prover messages

**Protocols and evidence.** Classical IOPs consist mainly of oracle messages, but interactive PCPs have an initial oracle followed by ordinary messages; STIR includes long function messages and short scalar answers; PIOPs routinely mix polynomial oracles with field elements. The original IOP work explicitly observes that interactive PCPs are IOPs where only the initial prover message is oracle-accessed. [Interactive Oracle Proofs](https://eprint.iacr.org/2016/116.pdf), [STIR](https://eprint.iacr.org/2024/390.pdf).

**Lean design pressure.** Every sender node should specify visibility:

- public/plain;
- oracle-only;
- commitment-only after compilation;
- private to a subset of roles, if multiparty support is desired.

A crucial typing invariant is that later public protocol structure may depend on public messages but must not depend on the hidden value of an oracle-only message.

**Virtual-output assessment:** **Preferred.** Hidden resources should enter the context through opaque handles.

---

## R9. Holographic and preprocessed oracles

**Protocols and evidence.** Marlin defines an offline indexer producing polynomial oracles derived from the relation index, while the online verifier receives oracle access to them. Holographic IOPs and Fractal similarly preprocess circuit-dependent data. [Marlin](https://eprint.iacr.org/2019/1047.pdf).

**Lean design pressure.** Contexts need resource origins such as:

- public input;
- private witness;
- trusted or transparent setup;
- indexer output;
- prior transcript;
- shared global oracle.

Security games must quantify over the correct setup/index generation procedure. An index oracle is not an ordinary prover message and should not accidentally become adversarial.

**Virtual-output assessment:** **Preferred.** Preprocessed resources are best exposed through stable handles, although their backing data is explicitly generated by the indexer.

---

## R10. Non-field and algebraic oracle codomains

**Protocols and evidence.** Most current IOPs are field-valued, but code-based definitions work for general alphabets; WARP works with arbitrary linear codes over sufficiently large fields; 2026 work adapts BaseFold/WHIR-like proximity techniques to prime-order group-valued data. Quantum IOPs go further and use qubit messages and restricted quantum access. [WARP](https://eprint.iacr.org/2025/753.pdf), [Titan](https://kurate.org/paper/c861fec2-156e-45a5-886f-a9910d36069d), [Quantum IOPs](https://arxiv.org/abs/2601.12874).

**Lean design pressure.** The interaction core must not assume field values, decidable equality, or classical copyability. Algebraic structure belongs in protocol-specific interfaces. Quantum messages ultimately require a different linear/resource-sensitive semantics, so “all IOPs” must either include such a layer or explicitly declare a classical scope boundary.

**Virtual-output assessment:** **Preferred** classically; **insufficient by itself** quantumly, where query access is state-changing and no-cloning matters.

---

# 4. Interaction-shape requirements

## R11. Instance-dependent and transcript-dependent protocol trees

**Protocols and evidence.** FRI and STIR run \(O(\log d)\) recursive rounds; sumcheck runs one round per variable; the number and type of later claims depends on earlier challenges and parameters. New low-round IOPs emphasize that round complexity remains a first-class performance concern even after Fiat–Shamir. [FRI](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ICALP.2018.14), [STIR](https://eprint.iacr.org/2024/390.pdf), [Linear Prover IOPs in Log-Star Rounds](https://eccc.weizmann.ac.il/report/2025/090/download/).

**Lean design pressure.** A flat `Fin n → Type` signature is not maximally general. Use a well-founded W-type/free-monad interaction tree:

```lean
Spec := done | node (Move : Type) (Move → Spec)
```

indexed by the public instance. This supports public-message-dependent continuation types and varying path lengths without pervasive casts.

**Virtual-output assessment:** **Neutral**, but the output simulation type will normally depend on the chosen public path.

---

## R12. Hidden-oracle noninterference at the type level

**Protocols and evidence.** An IOP verifier does not see the full oracle message and therefore cannot branch its subsequent protocol shape on that hidden value. It may branch on public challenges and public scalar responses.

**Lean design pressure.** The best representation distinguishes:

```lean
public : (X : Type) → (X → Spec) → Spec
oracle : (X : Type) → Spec → Spec
```

or an equivalent polynomial-container encoding. The constant continuation of `oracle` makes noninterference definitional. This is preferable to proving after the fact that a general continuation ignores its argument.

**Virtual-output assessment:** **Essential.** The virtual handle is the verifier-visible representative of hidden data.

---

## R13. Arbitrary speaking order and multi-message phases

**Protocols and evidence.** Canonical papers often normalize public-coin protocols to alternating prover/verifier moves, but real descriptions contain multiple prover objects in one round, multiple verifier samples, query phases, and initial/final prover-only phases. Marlin sends several polynomial oracles per round; STIR has consecutive conceptual subphases for folding, out-of-domain sampling, and shift checks. [Marlin](https://eprint.iacr.org/2019/1047.pdf), [STIR](https://eprint.iacr.org/2024/390.pdf).

**Lean design pressure.** Direction must decorate individual nodes rather than be determined by parity. Adjacent same-role nodes should be legal. “Round” should be derived metadata or a grouping operation, not the primitive interaction constructor.

**Virtual-output assessment:** **Neutral.**

---

## R14. Public-coin and private-coin verifiers

**Protocols and evidence.** General IPs permit private verifier randomness; Arthur–Merlin games and most SNARK-oriented IOPs are public-coin. Fiat–Shamir applies only after establishing the stronger public-coin/replayable structure. [Interactive Oracle Proofs](https://eprint.iacr.org/2016/116.pdf), [Fiat–Shamir for Multi-Round Proofs](https://link.springer.com/article/10.1007/s00145-023-09478-y).

**Lean design pressure.** The executable verifier should permit private effects. Public-coin should be an additional structure exposing:

- the challenge sampler;
- the challenge-indexed continuation;
- deterministic replay under prescribed challenges.

Do not define every verifier to be public-coin merely because the first applications are.

**Virtual-output assessment:** **Neutral.**

---

## R15. Parallel repetition, parallel subprotocols, and shared prefixes

**Protocols and evidence.** IOP soundness is commonly amplified by repetitions; WHIR batches multiple constraints through a shared random combination; ProtoGalaxy folds multiple instances simultaneously. Special-soundness theory also studies transcript trees and parallel repetition rather than merely sequential runs. [WHIR](https://eprint.iacr.org/2024/1586.pdf), [ProtoGalaxy](https://eprint.iacr.org/2023/1106.pdf), [Straight-Line Knowledge Extraction for Multi-Round Protocols](https://eprint.iacr.org/2024/1724.pdf).

**Lean design pressure.** Provide distinct combinators for:

- independent product;
- shared-prefix product;
- lock-step parallel repetition;
- batched product with shared challenges;
- asynchronous/concurrent composition if eventually required.

A list of sequential invocations does not capture correlated challenges or shared oracles.

**Virtual-output assessment:** **Preferred.** Shared virtual resources prevent duplication of a common prefix oracle.

---

## R16. Abort, failure, and decision outcomes

**Protocols and evidence.** Verifiers may reject early because a scalar check fails, a denominator vanishes, a queried opening is invalid, or a decoding procedure returns no candidate.

**Lean design pressure.** Distinguish:

- protocol termination;
- verifier rejection;
- malformed input or impossible branch;
- probabilistic failure;
- reduction output.

Encoding every verifier output as `Option Bool` conflates these cases. The output family should choose its own result type, with acceptance supplied by a separate predicate or terminal observation.

**Virtual-output assessment:** **Neutral.**

---

# 5. Virtual outputs and provenance

## R17. Virtual oracle outputs defined by query simulation

**Protocols and evidence.**

- WHIR’s compiler answers a query to a virtual function \(g\) by querying prior polynomial oracles and returning their challenge-weighted linear combination.
- STIR checks a newly sent function against a folded virtual function and forms quotient-derived next claims.
- FRI compares a freshly sent smaller codeword against the virtual fold of the previous codeword.
- Ligero’s row-combination check defines \(r^\top U\) from the matrix oracle.
- ARC defines rational constraints and quotients pointwise from earlier words. [WHIR](https://eprint.iacr.org/2024/1586.pdf), [STIR](https://eprint.iacr.org/2024/390.pdf), [FRI](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ICALP.2018.14), [Ligero](https://eprint.iacr.org/2022/1608.pdf), [ARC](https://eprint.iacr.org/2024/1731.pdf).

**Lean design pressure.** An output oracle should be representable by:

```lean
structure VirtualOracle where
  interface  : OracleInterface Value
  simulate   : (q : interface.Query) →
                 OracleComp AvailableSources (interface.Response q)
  lawful     : ExtensionalCorrectness simulate
```

The verifier need not—and frequently cannot efficiently—construct `Value`. The honest prover may optionally carry a materialized witness value for completeness or implementation extraction.

**Virtual-output assessment:** **Essential.**

---

## R18. Freshly sent outputs and virtual views must coexist

**Protocols and evidence.** In FRI/STIR, the prover sends a new smaller function, but the verifier checks it against a virtual fold or quotient view of an earlier oracle. In folding schemes, new cross-term commitments may be freshly sent while the resulting folded witness is a challenge-dependent algebraic combination. [STIR](https://eprint.iacr.org/2024/390.pdf), [Nova](https://eprint.iacr.org/2021/370.pdf).

**Lean design pressure.** Do not force a binary choice between “explicit outputs” and “virtual outputs.” A context resource should have an origin:

```text
input | sent-at-node | preprocessed | derived-by-simulator
```

and may additionally expose several virtual interfaces.

**Virtual-output assessment:** **Explicit preferred** for the newly sent resource; **essential** for its derived views.

---

## R19. Provenance as a typed dependency DAG

**Protocols and evidence.** After several FRI folds or nested lifts, an output query may depend on an oracle sent several stages earlier through multiple virtual transformations. Accumulation repeatedly feeds the previous output accumulator into the next step. Shared batching can make one virtual output depend on several sources. ARC and WARP’s implicit instances illustrate the same distinction between explicit claim data and long oracle data. [ARC](https://eprint.iacr.org/2024/1731.pdf), [WARP](https://eprint.iacr.org/2025/753.pdf).

**Lean design pressure.** Provenance must not be only an extensional function with its source identity erased. Track:

- stable resource identifiers;
- the precise transcript node or input slot that created each resource;
- dependencies of each virtual resource;
- interface-preserving reindexing;
- ownership and visibility;
- optionally query and opening costs.

Composition should compose provenance DAGs and prove that no handle becomes dangling or captures the wrong same-typed oracle.

**Virtual-output assessment:** **Essential.** A subset embedding into “input oracle or message index” is too weak: it handles aliases but not linear combinations, quotients, folds, tensor slices, or multi-source dependencies.

---

## R20. Extensional equality without collapsing intensional provenance

**Protocols and evidence.** Two different simulation programs can answer every query identically but have very different compilation costs—for example, querying a precomputed combined codeword versus querying many source codewords and combining responses.

**Lean design pressure.** Maintain two notions:

1. extensional oracle equivalence, used in mathematical correctness;
2. intensional implementation/provenance equivalence, used for compilation and cost.

Quotienting virtual oracles immediately by extensional equality would destroy the information needed by BCS or PCS compilation.

**Virtual-output assessment:** **Essential.**

---

# 6. Composition requirements

## R21. Dependent sequential composition

**Protocols and evidence.** Sumcheck iterates claim reduction; FRI/STIR iterate code reductions; a PIOP compiler chains arithmetization, polynomial checks, proximity testing, commitments, and Fiat–Shamir. ArkLib’s stated objective is precisely to derive large protocols from composition of reusable reductions. [ArkLib](https://github.com/Verified-zkEVM/ArkLib), [STIR](https://eprint.iacr.org/2024/390.pdf).

**Lean design pressure.** The second reduction must be indexed by the realized first transcript and output context. Composition must substitute:

- public outputs;
- prover witness outputs;
- oracle handles;
- provenance;
- security-state and extractor interfaces.

The dependent form should be primitive; ordinary homogeneous composition is a specialization.

**Virtual-output assessment:** **Essential.** Otherwise every intermediate virtual claim must be materialized solely to compose.

---

## R22. Context lifting and lenses

**Protocols and evidence.** A zero-check or permutation-check subprotocol normally acts on a few claims inside a larger Plonkish context. ArkLib already identifies lifting through statement, witness, and oracle-context lenses as a principal construction mechanism. [ArkLib blueprint](https://verified-zkevm.github.io/ArkLib/blueprint/chap-oracle_reductions.html).

**Lean design pressure.** A lens needs more than projection and reinsertion of values. For oracle contexts it must provide:

- a typed map from inner handles to outer handles;
- query simulation;
- provenance preservation;
- relation-preservation theorems for completeness and soundness;
- witness extraction/reinsertion laws.

Lens composition should be associative up to a manageable definitional or propositional equality.

**Virtual-output assessment:** **Essential.**

---

## R23. Recursive composition, IVC, and unbounded accumulation depth

**Protocols and evidence.** Nova folds each new execution step into a running relaxed-R1CS instance; ARC and WARP support unbounded accumulation depth; proof-carrying data composes along computation graphs rather than only linear chains. [Nova](https://eprint.iacr.org/2021/370.pdf), [ARC](https://eprint.iacr.org/2024/1731.pdf), [WARP](https://eprint.iacr.org/2025/753.pdf).

**Lean design pressure.** Support iteration at the meta-level over any finite depth without placing the depth in the protocol’s semantic type unnecessarily. The recursive invariant should be a relation on accumulator contexts. For PCD, composition may eventually need a DAG/tree fold rather than a unary iterator.

The core interaction tree can remain finite: “unbounded accumulation” means any finite number of invocations, not a single infinite transcript. Truly reactive protocols should use a separate coinductive layer.

**Virtual-output assessment:** **Preferred.** Accumulator oracle state can remain handle-based, but many folding schemes explicitly update commitments.

---

## R24. Identity, reassociation, and provenance-safe algebraic laws

**Protocols and evidence.** Large formalizations will repeatedly reassociate nested compositions and insert no-op reductions. Without algebraic laws, dependent casts dominate proof terms.

**Lean design pressure.** Provide identity, append, product, replication, and lens laws early. Aim for definitional computation where possible and explicit equivalences otherwise. Provenance reindexing must participate in these laws.

**Virtual-output assessment:** **Essential** to keep nested virtual-resource composition tractable.

---

# 7. Security requirements

## R25. Completeness relative to transcript-dependent output relations

**Protocols and evidence.** Completeness for an IOR says that a valid input statement/witness produces an output statement/witness in the target relation—not merely that the verifier accepts. This is the form required by folding, ARC, and WARP. [Nova](https://eprint.iacr.org/2021/370.pdf), [WARP](https://eprint.iacr.org/2025/753.pdf).

**Lean design pressure.** Completeness should relate honest execution, the verifier’s public output, the prover’s forwarded witness, and the semantics of all output handles. Virtual-oracle lawfulness is part of completeness.

**Virtual-output assessment:** **Essential** whenever output relation membership is phrased through oracle access.

---

## R26. Standard soundness and knowledge soundness as separate games

**Protocols and evidence.** IOP soundness quantifies over malicious oracle provers; accumulation and folding normally require knowledge soundness so a valid output accumulator implies extractable valid inputs. WARP’s extractor propagates witnesses backward through an IOR. [Interactive Oracle Proofs](https://eprint.iacr.org/2016/116.pdf), [WARP](https://eprint.iacr.org/2025/753.pdf).

**Lean design pressure.** Parameterize games by:

- computational versus information-theoretic adversaries;
- oracle environment and query budgets;
- input/output relations;
- extractor access;
- setup and algebraic models;
- error functions rather than only constants.

Do not define oracle soundness merely by converting the protocol to an explicit-data verifier; that can erase query restrictions central to proximity soundness.

**Virtual-output assessment:** **Preferred.** Extractors may return witnesses plus virtual-resource consistency evidence.

---

## R27. Round-by-round soundness with transcript-indexed states

**Protocols and evidence.** WHIR proves round-by-round soundness by defining validity states for transcript prefixes. STIR was designed so its recursive reduction admits a relatively clean round-by-round analysis. This notion is central to Fiat–Shamir compilation. [WHIR](https://eprint.iacr.org/2024/1586.pdf), [STIR](https://eprint.iacr.org/2024/390.pdf), [On Soundness Notions for IOPs](https://eprint.iacr.org/2023/1256).

**Lean design pressure.** A state function must be indexed by arbitrary nodes or prefixes of the interaction tree, not by `Fin (n+1)` alone. For branching protocols, the intermediate witness type and error bound may depend on the concrete prefix.

**Virtual-output assessment:** **Preferred.** Intermediate states often describe proximity to a virtual folded/combined oracle.

---

## R28. Round-by-round knowledge and backward witness transport

**Protocols and evidence.** WARP introduces a variant of straight-line round-by-round knowledge soundness compatible with erasure-correction extraction and proves a route to state-restoration knowledge soundness. WHIR uses round-by-round knowledge soundness in its PIOP-to-IOP compilation. [WARP](https://eprint.iacr.org/2025/753.pdf), [WHIR](https://eprint.iacr.org/2024/1586.pdf).

**Lean design pressure.** An RBR extractor should transform an output/intermediate witness at a child state into a witness at its parent state. This is naturally a dependent family over transcript prefixes. ArkLib should not bake one historical RBR definition into the protocol type; competing definitions and implication theorems should coexist.

**Virtual-output assessment:** **Essential** when the child witness certifies a virtual output claim.

---

## R29. Special soundness and transcript-tree extraction

**Protocols and evidence.** ProtoStar and ProtoGalaxy build accumulation from multi-round special-sound protocols. Generalized special soundness extracts from a tree of accepting transcripts sharing prover prefixes and branching at verifier challenges. [ProtoStar](https://eprint.iacr.org/2023/620.pdf), [ProtoGalaxy](https://eprint.iacr.org/2023/1106.pdf), [Straight-Line Knowledge Extraction](https://eprint.iacr.org/2024/1724.pdf).

**Lean design pressure.** Transcripts require prefix, compatibility, grafting, and challenge-divergence operations. A transcript tree is not merely a list of full transcripts. Public-coin replayability must expose challenge-indexed continuations so tree extraction does not depend on axiomatized rewinding.

**Virtual-output assessment:** **Neutral** for the tree structure, but extracted witnesses may include virtual oracle claims.

---

## R30. State-restoration security and rewinding semantics

**Protocols and evidence.** Holmgren proves the equivalence of round-by-round soundness and resistance to state-restoration attacks in the relevant public-coin setting. State restoration permits returning to a prior verifier state and continuing with fresh randomness. [On Round-By-Round Soundness and State Restoration Attacks](https://eprint.iacr.org/2019/1261.pdf).

**Lean design pressure.** The semantics must support deterministic transcript replay and fresh resampling from an exposed verifier continuation. Oracle query logs and adversary-visible histories must be explicit. VCVio’s free-monad oracle syntax and handlers are directly useful: logging, caching, reprogramming, and replay become semantic operations rather than meta-level assumptions. [VCVio](https://eprint.iacr.org/2026/899).

**Virtual-output assessment:** **Preferred.** Restoration must replay the same resource graph and not silently create fresh identities for old oracles.

---

## R31. Zero knowledge and view-sensitive security

**Protocols and evidence.** Nova’s folding scheme is zero knowledge; Ligero is an interactive zero-knowledge protocol; holographic and blind-proof variants distinguish what the verifier learns from index, input, and proof oracles. [Nova](https://eprint.iacr.org/2021/370.pdf), [Ligero](https://eprint.iacr.org/2022/1608.pdf).

**Lean design pressure.** Define party views explicitly:

- public transcript;
- oracle queries and answers;
- private randomness;
- shared oracle logs;
- setup material.

Simulation should be parameterized by visibility and corruption assumptions. A full transcript containing hidden oracle data is not the verifier’s view.

**Virtual-output assessment:** **Essential.** Virtual handles expose only their query interface and should not leak an underlying materialization.

---

# 8. Compilation requirements

## R32. BCS/Merkle compilation from oracle interfaces

**Protocols and evidence.** The BCS transformation commits to IOP oracle messages and opens the positions queried by the verifier. ArkLib’s stated compilation plan generalizes this through functional commitments and batched opening arguments. [Interactive Oracle Proofs/BCS](https://eprint.iacr.org/2016/116.pdf), [ArkLib](https://github.com/Verified-zkEVM/ArkLib).

**Lean design pressure.** Compilation needs per-resource metadata:

- when the resource becomes binding;
- its oracle interface;
- commitment and opening scheme;
- query batching compatibility;
- encoding and domain separation;
- provenance-based opening plan.

A virtual oracle normally should not receive a new commitment: its answer should be compiled into openings of its source resources plus local computation.

**Virtual-output assessment:** **Essential.**

---

## R33. Polynomial-commitment compilation of PIOPs

**Protocols and evidence.** Marlin compiles polynomial oracle rounds using a PCS; modern PIOP frameworks batch claims and later discharge them through univariate or multilinear PCS backends. [Marlin](https://eprint.iacr.org/2019/1047.pdf), [ark-piop](https://docs.rs/ark-piop/latest/ark_piop/).

**Lean design pressure.** A polynomial oracle interface should carry degree/domain claims separately from raw evaluation semantics. PCS compilation must know which virtual polynomial operations—linear combinations, restrictions, quotients—are supported homomorphically or require additional proof obligations.

**Virtual-output assessment:** **Essential.** Most PCS batching is precisely commitment-preserving virtualization.

---

## R34. Fiat–Shamir and sponge transcript compilation

**Protocols and evidence.** Fiat–Shamir requires public-coin structure and security hypotheses stronger than ordinary soundness. Multi-round special soundness, RBR soundness, and state-restoration security yield different compilation results and security losses. [Fiat–Shamir for Multi-Round Proofs](https://link.springer.com/article/10.1007/s00145-023-09478-y), [On Soundness Notions for IOPs](https://eprint.iacr.org/2023/1256).

**Lean design pressure.** The protocol representation must expose:

- exact public serialization;
- statement and setup binding;
- absorb/squeeze ordering;
- domain separators;
- challenge sampling;
- replayable public-coin continuations;
- shared-prefix behavior under batching.

Fiat–Shamir should be a verified transformation on protocol syntax, not an alternative hand-written verifier.

**Virtual-output assessment:** **Preferred.** Provenance identifies which public commitments and claims must be absorbed before a dependent challenge.

---

## R35. Compilation-preserving cost semantics

**Protocols and evidence.** Round count matters on GPUs even after Fiat–Shamir; a virtual linear combination may require many Merkle openings but only one homomorphic PCS opening; WARP and ARC optimize precisely the costs of accumulated oracle claims. [Linear Prover IOPs in Log-Star Rounds](https://eccc.weizmann.ac.il/report/2025/090/download/), [ARC](https://eprint.iacr.org/2024/1731.pdf), [WARP](https://eprint.iacr.org/2025/753.pdf).

**Lean design pressure.** Track or derive:

- oracle lengths;
- query counts;
- adaptive rounds;
- source queries per virtual query;
- proof length;
- commitment/opening multiplicity.

Correctness should not depend on costs, but compiler theorems require them.

**Virtual-output assessment:** **Essential.** Extensional oracle semantics alone cannot predict compiled cost.

---

# 9. Formalization landscape and limitations

## ArkLib

ArkLib is the closest existing effort to a general mechanized IOR theory. Its published description supports heterogeneous oracle interfaces, relation-to-relation reductions, sequential composition, lifting, completeness, soundness, knowledge soundness, RBR notions, state restoration, and BCS/Fiat–Shamir plans. [ArkLib repository](https://github.com/Verified-zkEVM/ArkLib), [ArkLib blueprint](https://verified-zkevm.github.io/ArkLib/blueprint/chap-oracle_reductions.html).

The older `OracleReduction` layer has several important limitations:

1. `ProtocolSpec n` is a flat finite family indexed by `Fin n`.
2. The verifier is fundamentally public-coin.
3. Oracle prover messages are treated uniformly rather than allowing clean mixed visibility.
4. Output oracle statements are selected through an embedding into an input-or-message index. This supports aliases/subsets but not general folds, linear combinations, quotients, tensor views, or multi-source simulators.
5. Provenance is only the selected source index, not a compositional dependency graph.
6. RBR state families are indexed by round number rather than arbitrary nodes in a dependent interaction tree.

The current rebuild already moves in the right direction. `Interaction.Spec` is a W-type/free-monad interaction tree with transcript-dependent continuations; `Interaction.Oracle.Spec` separates public nodes from hidden oracle nodes and definitionally prevents branching on hidden values; `Reduction` has transcript-dependent statement and witness outputs. The missing centerpiece is a first-class output oracle context of simulation-based handles with provenance, together with security and compiler layers over that context.

## VCVio

VCVio represents oracle computations as free-monad syntax over an oracle specification and interprets oracle transformations through handlers. It supports explicit histories, caching, logging, reprogramming, and deterministic transcript replay, making it a strong semantic substrate for malicious-prover games, state restoration, Fiat–Shamir extraction, and compiler correctness. It does not by itself supply the IOR claim/context/provenance abstraction. [VCVio](https://eprint.iacr.org/2026/899).

## Other Lean work

Bailey and Miller formalize soundness for a class of linear-PCP SNARKs in Lean and automate algebraic soundness checking. This is valuable evidence that protocol-specific formalization catches proof errors, but its scope is a restricted noninteractive linear-PCP model rather than heterogeneous interactive oracle reductions. [Formalizing Soundness Proofs of Linear PCP SNARKs](https://www.usenix.org/conference/usenixsecurity24/presentation/bailey).

## Coq

Recent Coq work machine-checks 3-, 5-, and 9-round shuffle arguments and extracts a verifier. The authors report that a single round-parametric protocol definition became unwieldy, so they used separate definitions; they also leave machine-checked Fiat–Shamir reasoning open. This is a concrete warning against encoding dependent interaction through fixed-length tuples alone. It is not an IOP/IOR formalization. [Machine-checking Multi-Round Proofs of Shuffle](https://eprint.iacr.org/2025/461.pdf).

## Rust frameworks

Rust libraries generally expose protocol-specific trackers, transcripts, polynomial registries, and claim-batching pipelines. For example, `ark-piop` supports PIOP, sumcheck, lookup, PCS backends, and virtual symbolic polynomials. Such systems are useful implementation targets, but Rust trait APIs generally do not state or prove relation reduction, provenance preservation, extraction, or compiler security. [ark-piop](https://docs.rs/ark-piop/latest/ark_piop/).

**Overall finding:** no surveyed Lean, Coq, or Rust framework currently combines dependent interaction trees, arbitrary virtual oracle outputs, explicit provenance, all major extraction notions, and verified BCS/PCS/Fiat–Shamir compilation.

---

# 10. Recommended foundational architecture

## 10.1 Interaction syntax

Use the current dependent tree approach:

```text
done
public-node(role, Move, Move → continuation)
oracle-node(sender, ResourceType, interface, continuation)
```

The oracle-node continuation must be independent of the hidden resource value. Roles should be decorations, not encoded by round parity.

## 10.2 Resource context

A context should be a heterogeneous collection of stable handles:

```text
ResourceId
ResourceSchema(id):
  value type
  oracle interface(s)
  visibility
  origin
  provenance
```

Origins should include input, setup/indexer, sent message, and virtual derivation.

## 10.3 Virtual resource

A virtual handle should consist of:

1. its public query/response interface;
2. a query simulator over an explicitly scoped source context;
3. an extensional correctness law relating simulation to the honest materialized value;
4. a provenance DAG;
5. optional cost/batching metadata.

The materialized value is useful on the honest-prover side but must not be required by the verifier-side output.

## 10.4 Claims and relations

A statement should contain public scalars plus resource handles. A relation should interpret those handles against an environment of honest backing values. This separates:

- public syntax of a claim;
- operational query access;
- semantic truth;
- honest witness materialization.

## 10.5 Security layers

Build independent libraries for:

- perfect/statistical/computational completeness;
- soundness;
- straight-line knowledge soundness;
- RBR soundness;
- RBR knowledge soundness, including WARP’s relaxed variant;
- special soundness over transcript trees;
- state-restoration soundness and knowledge soundness;
- zero knowledge and view simulation.

Then prove implication and composition theorems between them. Do not require every protocol to inhabit one monolithic “secure IOR” structure.

## 10.6 Compiler interface

BCS, PCS, and Fiat–Shamir compilers should consume:

- interaction syntax;
- visibility;
- replayable public-coin evidence;
- resource interfaces;
- provenance and query plans;
- serialization/domain-separation data;
- the security property required by the compiler theorem.

---

# 11. Scope extensions that should remain possible

## Multiparty IOPs and distributed provers

A literal “all interactive oracle protocols” abstraction should eventually allow more than two roles, directed messages, broadcast, and corruption profiles. These are not needed to express ordinary SNARK IOPs, so a two-party reduction can remain the primary API if it is implemented as a specialization of role-decorated interaction syntax.

## Quantum IOPs

Quantum IOPs appeared in 2026 and include quantum interaction, EPR setup, and restricted quantum access. Classical oracle handles assume freely reusable query functions and therefore cannot faithfully model quantum messages. [Quantum Interactive Oracle Proofs](https://arxiv.org/abs/2601.12874).

ArkLib should state one of two positions explicitly:

1. the definitive abstraction is definitive for **classical** IORs; or
2. oracle effects are generalized to linear, state-transforming resources with no-cloning semantics.

The first is the practical choice for ArkLib today.

---

# 12. The four hardest requirements to satisfy simultaneously

## 1. Transcript-dependent interaction together with hidden-oracle noninterference

Later message types genuinely depend on earlier public challenges, so a dependent interaction tree is necessary. But later structure must not depend on hidden oracle values. A naïve dependent tree is too permissive; a flat list is too restrictive. Encoding public branching and oracle-hidden constant continuation in one compositional W-type is foundationally difficult, especially once append, replay, and transcript splitting must compute definitionally.

## 2. Virtual outputs together with provenance-safe composition

Extensional query simulation is easy to define. What is hard is preserving intensional identity through nested folds, quotients, lenses, batches, and sequential composition. Erasing provenance breaks BCS/PCS compilation and risks connecting an output claim to the wrong same-typed oracle. Keeping provenance too syntactic makes mathematical equivalence and reassociation painful.

This is the single largest gap in the older ArkLib abstraction.

## 3. One executable semantics supporting incompatible extraction styles

Straight-line extraction, RBR extraction, WARP’s erasure-based variant, transcript-tree special soundness, rewinding, and state restoration require different access patterns to adversaries and verifier continuations. The protocol representation must expose enough structure for all of them without forcing every executable protocol to be public-coin or rewindable.

## 4. General composition together with compiler-faithful cost and visibility

Mathematical composition wants to identify extensionally equal virtual resources. Compilation needs to remember exactly which commitments are opened, which hashes precede each challenge, and how many source queries implement a virtual query. Thus the library must preserve both abstract semantics and concrete resource structure through the same composition operations.

---

# 13. Final recommendation

Adopt the current interaction-tree foundation, but make the next central abstraction a **provenance-carrying oracle context**.

The definitive `OracleReduction` should output neither a tuple of full oracle values nor a mere embedding into previous message indices. It should output a transcript-indexed context of typed handles, each backed by either:

- a newly sent resource;
- an input or preprocessed resource;
- a lawful query simulator over earlier handles.

Make provenance structural, keep extensional oracle equality separate, and formulate security over relations on these contexts. This design directly covers sumcheck, FRI, STIR, WHIR, Ligero, Marlin, Nova, ProtoStar, ProtoGalaxy, ARC, WARP, tensor-code IOPPs, and recursive composition while leaving clean extension points for multiparty and quantum protocols.