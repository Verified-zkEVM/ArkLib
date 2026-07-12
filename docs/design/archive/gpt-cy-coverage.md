# Chiesa–Yogev coverage audit of the proposed ArkLib oracle-reduction design

## Executive verdict

The design cannot presently state, let alone prove, all results in Chiesa–Yogev (CY).

Its deterministic oracle-reduction core—`SourceCtx`, `VirtualOracle`, substitution, boundary closure, and the compiler pipeline—is a plausible substrate for representing IOP computations. It is not yet a cryptographic semantics adequate for CY. In particular, CY’s BCS proof is built around objects that the design currently names only informally or defers:

1. an ordered, global query-answer trace across several persistent random oracles and execution phases;
2. a first-class state-restoration game, whose adversary may request random continuations of arbitrary transcript prefixes;
3. stateful, online, multi-configuration Merkle extraction from increments of that global trace;
4. a trace translator that reconstructs state-restoration moves by hash-chain backtracking;
5. oracle programming and query-before-program events for zero knowledge;
6. black-box replay/reprogramming semantics for special-soundness extractors;
7. resource-indexed query budgets, failure probabilities, and expected-running-time bounds;
8. preprocessing games whose honest indexer and both adversarial phases share the same oracle state.

The design’s §6.10.7 capability taxonomy recognizes several of the right *property names*, but capability names are not enough. CY needs concrete game records, trace ownership rules, resource identity, budget algebra, extractor composition laws, and distributional simulation theorems.

The strongest conclusion is therefore:

> The claim under audit is correct. Once the design reaches the precise cryptographic reductions, substantial complications appear. They are structural rather than merely proof-engineering overhead.

References below use:

- **CY** = [snargs-book.tex](</Users/quangdao/Downloads/Papers/hash-based-snargs-book/snargs-book.tex:2396>)
- **Design** = [ArkLib-Oracle-Reduction-Design.md](/Users/quangdao/Documents/Lean/ArkLib-Oracle-Reduction-Design.md:1)

Verdicts:

- **OK**: the proposed object can naturally state the result, and the required proof ingredients are present in principle.
- **OK-with-work**: the design can host it, but named supporting definitions or theorems must be added.
- **GAP**: a central game, semantic object, or interface is missing or mismatched.

---

# Part 1: Result inventory and coverage matrix

## 1. Random-oracle semantics and basic properties

### 1.1 The random oracle model

**CY definition.** Definition `definition:the-rom`, CY 2451–2454, samples a random function and gives every party oracle access to the *same* function. Oracle algorithms have a uniform query bound independent of the answers they receive, CY 2435–2446. An execution produces an ordered query-answer trace, CY 2484–2490. Lazy sampling is presented as a stateful partial table, CY 2519–2536.

The important semantic facts are:

- repeated queries return the same answer;
- different parties and phases share the table;
- query order is observable to trace-based reductions;
- the query budget covers the entire oracle algorithm;
- the same execution can expose both a result and its trace.

**Design mapping.**

- The RO belongs in `WorldSpec Γ`, not `SourceCtx Δ`, under Design §6.2.
- `WorldSpec.State` should be the lazy table.
- `step` handles one query.
- `runΓ` is supposed to return `(Result × State × Trace)`.
- `SourceCtx` should contain local IOP-message oracles but not the global RO.

**Assessment.**

- **Can state:** only after the sketch in §6.2 is made concrete.
- **Can prove:** not presently. There is no defined global trace API, query-count measure, lazy-table distribution, or multi-party shared execution theorem.

**Verdict: GAP.** `WorldSpec` is presently a design sketch, while CY’s ordered trace is a foundational proof object.

The current Lean implementation confirms this gap. The existing Fiat–Shamir transform treats its replay oracle as ordinary input data and explicitly defers the ROM formulation in [FiatShamir/Transform.lean](/Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/FiatShamir/Transform.lean:35).

---

### 1.2 Unpredictability, inversion, high-entropy inputs, and collisions

CY proves:

- unqueried-pair unpredictability, Lemma `rom-not-queried-pair`, CY 2803–2821;
- inversion of a fixed target with probability at most \(Q/2^n\), Lemma `rom-ow`, CY 2911–2929;
- hidden-salt/high-entropy inversion bounds, CY 2970–3044;
- collision probability \(Q(Q-1)/(2\cdot2^n)\), Lemma `rom-cr`, CY 3101–3120.

The quantification is uniformly over bounded adaptive oracle algorithms. The proofs inspect membership in, or collisions inside, the global trace.

**Design mapping.**

These should be generic lemmas about a concrete random-function `WorldSpec`, parameterized by:

- the world’s domain and range;
- trace length or a budget certificate;
- a possibly adaptive program;
- trace projections when several oracle functions share the execution.

They are not properties of `VirtualOracle` or `ClosedClaim`.

**Verdict: OK-with-work for statement; GAP for proof infrastructure.** A finite lazy table model could support them, but the design neither specifies that model nor identifies the probability library lemmas needed for adaptive lazy sampling.

---

### 1.3 Regularity and random-oracle pseudorandomness

CY proves expected regularity bounds for a random function, including the maximum across a family of message prefixes, Claim `ro-regularity`, CY 3355–3367. Lemma `ro-pseudorandomness`, CY 3422–3458, constructs an inverter and compares:

- forward sampling a random suffix and hashing it; with
- sampling a target and then sampling a consistent preimage.

These are distributional statements over the *entire sampled function*, not merely over query transcripts.

**Design mapping.**

A concrete RO world must expose:

- the distribution of the whole finite function, or an equivalence between full-function and lazy-table semantics;
- statistical distance and expectation;
- oracle-preserving inverter programs;
- hybrid composition.

`≈sem` in Design §6.5 is too abstract unless it is instantiated with statistical-distance bounds.

**Verdict: GAP.** The design’s semantic-equivalence distinction is useful, but there is no quantitative distributional relation strong enough to state CY’s regularity and inversion hybrids.

---

## 2. Arguments in general oracle settings

### 2.1 Oracle distributions

CY Definition `oracle-distribution`, CY 5632–5635, defines a distribution indexed by security parameter and instance-size bound that samples a *list of functions*. These functions may be correlated.

This is more general than “one random oracle” and more general than a product of independently initialized worlds.

**Design mapping.**

A single `WorldSpec Γ` can represent the sampled tuple if:

- its state stores the entire correlated tuple;
- requests carry an oracle/configuration index;
- initialization samples the tuple jointly;
- traces identify the target function.

A list of separately initialized `WorldSpec`s would not preserve correlation.

**Verdict: OK-with-work.** `WorldSpec` has enough conceptual generality if Γ is allowed to be a joint world. The design should explicitly reject an independence-by-default interpretation.

---

### 2.2 Completeness and nonadaptive/adaptive soundness

CY defines:

- completeness, CY 5637–5651;
- nonadaptive soundness, CY 5653–5669: the false instance is fixed after public parameters but before the oracle sample;
- adaptive soundness, CY 5671–5691: the oracle is sampled first, then the adversary outputs both the instance and argument.

This quantifier order matters. Adaptive soundness is not obtained merely by making the statement a prover output inside an ordinary closed claim.

**Design mapping.**

`ClosedClaim` can express the final acceptance predicate, but the experiment must distinguish:

```text
nonadaptive: ∀x∉L, H ← O, (π ← Aᴴ(x))
adaptive:    H ← O, ((x,π) ← Aᴴ)
```

This belongs in the security-game layer of Design §6.6, not in `ClosedClaim` itself.

**Verdict: OK-with-work.** Add explicit adaptive and nonadaptive game constructors with the correct sampling order.

---

### 2.3 Straightline and rewinding knowledge soundness

CY straightline KS, CY 5693–5716, has quantifier order:

```text
∃ probabilistic extractor E,
  ∀ deterministic Q-query adversaries A,
    H ← O;
    (x,π) with prover trace T_A;
    verifier with trace T_V;
    w ← E(x,π,T_A,T_V);
    Pr[accept ∧ (x,w)∉R] ≤ ε(λ,N,Q).
```

The rewinding version, CY 5739–5762, additionally gives `E` black-box access to `A`; its error and expected time depend on the adversary’s failure probability, and time also depends on adversary running time.

**Design mapping.**

- Straightline CY extraction is `OfflineLoggedExecution`, not the current concrete-message `Straightline` extractor.
- Rewinding extraction is a combination of `OfflineLoggedExecution` and a black-box access mode.
- The design’s §6.6.4 taxonomy names these axes but does not define a product/composite extractor interface.
- Current [Oracle/Security/Basic.lean](/Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Security/Basic.lean:132) gives the extractor the full concrete IOP transcript and output simulator. It does not give it the adversary’s RO trace or verifier trace.

**Verdict: GAP.** The current and proposed “straightline” notions are materially different from CY’s general-oracle straightline KS.

---

### 2.4 Zero knowledge in an extendable programmable oracle model

CY’s adaptive ZK definition, CY 5764–5796, lets an adversary:

1. interact with the sampled oracle;
2. choose a valid instance, witness, and retained state;
3. see either an honest proof or a simulated proof;
4. continue its computation;
5. in the simulated experiment, use an oracle modified by the simulator’s programming list.

This requires programming semantics, conflict handling, and preservation of earlier query answers.

**Design mapping.**

`WorldSpec Γ` could host an EPROM world, but Design §8 explicitly defers ZK. `SelectiveOpeningHiding` in §6.10.7 does not supply a programmable-world simulator.

**Verdict: GAP.**

---

### 2.5 Indifferentiability and replacing oracle distributions

CY defines basic, efficiency-preserving, and simulator-friendly indifferentiability at CY 5818–5947, then transfers arguments from one oracle distribution to another. It also constructs several separated logical ROs from one RO, CY 6638–6854, with explicit simulators and trace translators.

**Design mapping.**

This resembles `LowerAccesses` plus domain separation in `ResourceMeta`, but CY needs more:

- a construction translating requests;
- a simulator for the source oracle;
- an adversarial-view equivalence;
- trace translation for extractors;
- quantitative security and running-time transport.

**Verdict: GAP.** Compiler lowering is operational; CY’s result is a cryptographic indifferentiability theorem. Domain separators alone do not establish it.

---

## 3. Basic hash commitment

### 3.1 Construction, correctness, and binding

CY commits to a message with random salt as \(c=H(m,s)\), CY 11755–11768. Binding, Lemma `cm-binding`, CY 11803–11881, bounds the probability of two valid unequal openings by separating:

- collisions found in the trace;
- openings never queried and hence guessed.

**Design mapping.**

A committed `VirtualOracle` boundary can carry the value, commitment, and opening relation. `NodeCommitment` in the current [Oracle/BCS.lean](/Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/BCS.lean:67) can represent the honest commit algorithm.

It cannot state binding: `NodeCommitment` has only `CommType`, `WitnessType`, and `commit`. There is no opening verifier or security game.

**Verdict: OK-with-work at the proposed §6.10.7 level; GAP in current Lean.**

---

### 3.2 Single extraction from the commitment-phase trace

Lemma `cm-extractability`, CY 11941–12007, quantifies:

```text
∃ deterministic polynomial-time E,
  ∀Q-query A,
    H ← RO;
    (c,state), Tcommit ← Aᴴ;
    (m',s') ← E(c,Tcommit);
    (m,s) ← Aᴴ(state);
    Pr[Checkᴴ(c,m,s)=1 ∧ (m',s')≠(m,s)] ≤ ε.
```

Crucially, extraction sees only the trace *up to the commitment*, while the opening phase continues in the same RO world. The proof splits the total budget as \(Q_1+Q_2\le Q\), CY 11977 onward.

**Design mapping.**

This is `OfflineQueryOnly` with:

- a prefix trace;
- a persistent world shared by commitment and opening;
- a phase split;
- a global budget;
- output comparison against a later execution.

**Verdict: GAP.** The taxonomy names the extractor’s information source but provides no two-phase game or prefix-trace discipline.

---

### 3.3 Stateful multi-extraction

Lemma `cm-multi-extractability`, CY 12030–12109, uses a deterministic *stateful* extractor. The adversary emits commitments sequentially; each extractor invocation receives only the trace increment since the previous commitment and accumulates it internally. The error is not a naïve union bound: collision failure is global, while guessing prior commitments is per commitment.

**Design mapping.**

This needs an online transducer:

```text
ExtractorState × commitment × TraceChunk
  → extraction × ExtractorState
```

with an invariant that the chunks concatenate to an ordered prefix of one shared execution.

**Verdict: GAP.** “Multi-extractability” in §6.10.7 is only a capability label; it does not specify state, chunk ownership, or global-event error accounting.

---

### 3.4 Hiding

Lemma `cm-hiding`, CY 12182 onward, has:

- bounded-query error \(Q/2^s\), obtained by a hidden-salt hit event across both phases;
- an unbounded-adversary case based on RO regularity rather than query counting;
- a tightness discussion, CY 12329 onward.

**Design mapping.**

This requires a hiding simulator, statistical distance, salt entropy, and either query-budget or full-function regularity reasoning.

**Verdict: GAP.** `SelectiveOpeningHiding` does not cover even the exact basic-commitment hiding games unless parameterized by adversary phases, simulator outputs, query bounds, and statistical distance.

---

## 4. Merkle commitments in the ROM

### 4.1 Exact construction and corner cases

CY’s Merkle construction, CY 12413–12585, uses:

- a perfect binary tree, initially requiring message length to be a power of two;
- an independent random salt for every leaf;
- leaf labels \(H(m_i,s_i)\);
- internal labels \(H(\mathsf{left},\mathsf{right})\);
- openings containing each opened leaf salt and authentication-path siblings;
- a deterministic checker that recomputes all paths.

The unblinded variant has salt length zero and may store messages directly at the leaves, CY 12595–12605. Arbitrary leaf counts are treated by explicit tree-shape/padding conventions at CY 20078–20093.

Duplicate issues are more subtle than “unique leaves”:

- repeated message values at distinct positions are legal;
- position is semantically significant even when values repeat;
- the extractor performs reverse lookup by hash answer;
- repeated roots across commitments must yield identical extracted message and trapdoor;
- padding and domain encodings affect which queries count as leaf or internal-node queries.

**Design mapping.**

A Merkle backend needs explicit associated data:

- message length and tree shape;
- leaf and internal encodings;
- salt family indexed by leaf;
- configuration identity;
- opening query set;
- extracted total vector and trapdoor;
- handling of missing vertices;
- equality/coherence for duplicate roots.

`ResourceMeta` can record origin, stable ID, and domain separator, but not this semantic structure.

**Verdict: OK-with-work for construction; GAP for a reusable exact backend interface.**

---

### 4.2 Merkle completeness and binding

CY proves completeness, Lemma `mt-completeness`, CY 12644–12678, and two binding forms:

- malicious opening consistency, Lemma `mt-binding`, CY 12981 onward;
- consistency with an honestly generated tree, Lemma `mt-other-binding`, CY 13076 onward.

The central combinatorial lemmas locate colliding paths, CY 12744–12974.

**Design mapping.**

These can be backend correctness and finite/adaptive function-binding capabilities, but the capability record must expose the authenticated tree relation—not just an abstract commitment/opening protocol.

**Verdict: OK-with-work.** The core mathematics is formalizable once the concrete Merkle representation exists.

---

### 4.3 Single Merkle extraction

Lemma `mt-extractability`, CY 13185–13212, is the first major mismatch.

The extractor receives the root and commitment-phase RO trace. It:

1. classifies trace queries as leaf, internal, or irrelevant, Definition `query-types`, CY 13218–13229;
2. reconstructs a partial tree by reverse lookup from answers to inputs;
3. fills unknown leaves arbitrarily;
4. returns a *total* message vector and trapdoor.

The bad event is not “the extractor recovered the adversary’s unique committed vector.” It is:

- a later opening verifies but disagrees with the extracted vector on an opened position; or
- the proof generated from the extracted trapdoor differs from the adversary’s accepted proof.

The proof uses three consecutive ordered traces—commit phase, opening phase, and honest checker—and isolates collision, tree-change, and unqueried-checker-query events, CY 13267–13452.

**Design mapping.**

The exact extractor is:

- offline with respect to the commitment prefix;
- trace-based rather than message-based;
- deterministic and partial-tree reconstructing;
- world-dependent;
- followed by a later same-world test.

**Verdict: GAP.**

`StraightLineExtractability` or `FunctionBinding` as a proposition over a backend is insufficient unless it includes:

- the three-phase experiment;
- the trace prefix supplied to extraction;
- partial-tree reconstruction semantics;
- arbitrary completion;
- proof canonicality;
- the precise later-opening bad event.

---

### 4.4 Multi-extraction and multiple configurations

Lemma `mt-multi-extractability`, CY 13534–13580, requires sequential commitments and a deterministic stateful extractor. Besides later-opening inconsistency, its bad event includes:

> equal commitment roots extracted at different times to unequal message/trapdoor pairs.

Lemma `mt-multi-configuration-multi-extractability`, CY 13874–13932, handles multiple Merkle configurations, with one RO per configuration. The adversary may interleave configurations. The extractor receives a global trace increment, filters it by configuration, and updates the corresponding cumulative state.

One opening per configuration is sufficient for the later BCS application; CY discusses multiple openings separately, CY 13768 and 13990.

**Design mapping.**

This requires a family of stateful extractors keyed by stable resource identity:

```text
GlobalTraceChunk
  → per-configuration projections
  → cumulative extractor databases
```

and a coherence theorem for identical roots.

**Verdict: GAP.**

Design §6.10.7’s “adaptive/multi-function binding” and “multi-extractability” headings identify the desired destination, but not CY’s interface. In particular, the record must say whether:

- the extractor consumes the full trace or increments;
- configuration traces may interleave;
- repeated roots reuse the old extraction;
- extracted trapdoors must be equal;
- one global \(Q\) or per-configuration \(Q_i\) is charged.

---

### 4.5 Merkle hiding, privacy, and equivocation

CY proves:

- root hiding, Lemma `mt-root-hiding`, CY 14063 onward;
- selective-opening privacy of root plus authentication paths, Lemma `mt-privacy`, CY 14234 onward;
- an explicit local-view simulator, Constructions CY 14299–14367;
- inefficient equivocation, Lemma `mt-equivocation`, CY 14443 onward.

The privacy simulator receives only the opened positions and values. It samples salts for opened leaves, simulates independent co-path subtrees, and hashes the remaining path vertices. The error is a sum over independent co-path components and is later assumed superadditive/monotone for convenient BCS bounds, CY 14409–14437.

**Design mapping.**

This is substantially richer than one `SelectiveOpeningHiding` proposition. A useful backend record needs:

- a local-view simulator;
- a specification of exactly which message fragment it receives;
- a proof that simulated openings verify;
- statistical-distance error indexed by length, opening size, salt size, and query budget;
- optional equivocation with an inefficient RO inverter;
- superadditivity/monotonicity witnesses when later theorems use them.

**Verdict: GAP.**

---

## 5. IOPs and state restoration

### 5.1 IOP security definitions

CY defines:

- completeness, CY 16654–16664;
- soundness, CY 16666–16678;
- public coin, CY 16685–16692;
- rewinding KS, CY 16746–16772;
- straightline KS, CY 16778–16797;
- verifier view and HVZK, CY 16802–16821;
- local view, CY 16827–16834.

For a public-coin IOP, verifier oracle queries can be postponed until after the interaction, CY 16694–16698. The HVZK view contains verifier randomness plus queried locations and answers—not entire IOP strings.

**Design mapping.**

The `Oracle.Spec` and `PublicQueryVerifier` separation is compatible with postponing oracle queries. The current BCS code explicitly separates public query selection and the decision procedure in [Oracle/BCS.lean](/Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/BCS.lean:320).

However:

- the current extractor receives complete prover-oracle values, not CY’s query view;
- there is no HVZK local-view simulator;
- public coin in the current FS code is “replayable input oracle,” not a sampled RO-derived challenge process.

**Verdict: OK-with-work for ordinary IOP syntax and completeness; GAP for the full security suite.**

---

### 5.2 IOP state-restoration game

Definition `iop-state-restoration-game`, CY 16854–16877, samples one random function \(R_j\) for every round. A malicious state-restoration prover may make up to \(B\) moves. A move may name:

- any round \(j\);
- an instance;
- all IOP strings through round \(j\);
- all state-restoration salts through round \(j\).

The game answers with

\[
R_j(x,\pi_1,\ldots,\pi_j,s_1,\ldots,s_j).
\]

Moves need not follow one consistent execution. Repeated moves must be answered consistently. At the end, the prover outputs a full tuple and the game recomputes every challenge from the corresponding full prefix.

State-restoration soundness is then quantified over all salt sizes, instance bounds, move budgets, and \(B\)-move provers, CY 16879–16898.

**Design mapping.**

This is not an ordinary protocol run, a transcript tree, or a checkpointable interactive prover. It is an oracle game whose request type contains arbitrary purported transcript prefixes.

Design §6.6.4’s `CheckpointRestore` mode is therefore not the definition. Design §6.6.6 itself acknowledges that state restoration requires matching replay semantics, query bounds, and stable resource identity, but does not supply them.

**Verdict: GAP.** State restoration must become a first-class game before CY’s BCS soundness theorem is even stateable with its correct assumption.

---

### 5.3 State-restoration knowledge soundness

CY straightline SRKS, CY 16900–16921, has:

```text
∃ probabilistic E,
  ∀ deterministic B-move SR provers P,
    sample round functions;
    run SR game obtaining final tuple and full move-response trace;
    w ← E(final tuple, SR trace);
    Pr[accept ∧ invalid witness] ≤ ε(s,N,B).
```

Rewinding SRKS, CY 16943–16968, additionally gives the extractor black-box access to the SR prover. Error depends on its failure probability; expected time depends on failure probability and prover time.

**Design mapping.**

The straightline case is `OfflineLoggedExecution` over an SR-game trace. The rewinding case combines that log with black-box access. Neither is represented by the current `Reduction.Extractor.Straightline`.

**Verdict: GAP.**

---

## 6. Interactive BCS warmup and BCS variants

### 6.1 iBCS

The interactive BCS construction starts at CY 16984. It commits to IOP strings with Merkle roots during interaction, then sends openings after the verifier determines its query sets.

CY separately proves:

- nonadaptive soundness reduction, Lemma `ibcs-reduction`, CY 17138 onward;
- adaptive soundness reduction, Lemma `ibcs-adaptive-reduction`, CY 17357 onward.

Adaptive soundness requires extraction to bind not only oracle strings but the adaptively chosen instance and all roots under a shared execution.

**Design mapping.**

Current `bcsSpec`, `wrapWithCommitmentsExt`, `QueryBundle`, and `PublicQueryVerifier` cover much of iBCS’s *honest syntax*. See [Oracle/BCS.lean](/Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/BCS.lean:130) and its phase split at lines 368–438.

They do not implement actual opening interactions or any security transfer theorem. `OpeningDeco` is only a type-valued placeholder, lines 442–469.

**Verdict: OK for a syntax skeleton; GAP for CY’s iBCS theorem.**

---

### 6.2 Exact BCS construction and variants

Construction `bcs-transformation`, CY 17618–17712, uses \(2r\) logical ROs:

- one Merkle RO per IOP round;
- one Fiat–Shamir RO per IOP round.

At each round the prover:

1. computes an IOP string;
2. commits with per-leaf Merkle salts;
3. samples an FS salt;
4. derives the next verifier challenge through a hash-chain query.

After all rounds it evaluates the IOP verifier’s query sets and supplies the requested entries, salts, and Merkle paths.

CY also treats:

- non-oracle prover messages in the FS query, CY 17737–17769;
- a basic FS variant rather than hash-chain FS, CY 17772–17786;
- verifier randomness that is itself oracle-accessible and derived coordinate-by-coordinate, CY 17789–17817.

**Terminology correction.** This TeX does not define “restricted BCS,” “unrestricted BCS,” or “restricted completeness.” The relevant axes are:

- adaptive versus nonadaptive argument security;
- iBCS versus noninteractive BCS;
- basic versus hash-chain Fiat–Shamir;
- protocols with additional non-oracle messages;
- ordinary finite verifier randomness versus oracle-accessible randomness.

Public-coin IOP queries are postponed to a final phase, but that is not called “nonadaptive BCS.”

**Design mapping.**

- `RepresentOracles` and `LowerAccesses` fit the Merkle materialization step.
- `TransportBoundary` fits changing an oracle-valued boundary into a commitment/opening relation.
- `FiatShamir` fits challenge derivation only at a high level.
- `ResourceMeta` must preserve each round/configuration’s stable identity and domain separation.

The pipeline does not presently capture the interleaving between Merkle queries and FS queries, which is central to security.

**Verdict: OK-with-work for honest construction; GAP for cryptographic semantics.**

---

## 7. BCS soundness

### 7.1 Exact theorem

Theorem `bcs-soundness`, CY 17830–17843, gives adaptive soundness bounded by

\[
\varepsilon_{\mathrm{IOP\text{-}SR}}
  (\lambda+s_{\mathrm{FS}},N,Q)
+
\varepsilon_{\mathrm{MT\text{-}multi}}
  (\lambda,\vec L,Q,Q+1)
+
\frac{Q^2}{2^\lambda},
\]

with more exact bounds in terms of separate Merkle and FS budgets.

The assumption is IOP *state-restoration* soundness, not ordinary soundness.

### 7.2 Exact reduction

Lemma `bcs-soundness-reduction`, CY 17854–17897, transforms a BCS adversary with budget \((Q_{\mathrm{MT}},Q_{\mathrm{FS}})\) into a state-restoration prover making at most \(Q_{\mathrm{FS}}\) moves.

Construction `bcs-direct-reduction`, CY 17901–17952, does the following:

1. maintains the adversary’s ordered global query trace;
2. on every FS query, takes the Merkle-query trace segment since the preceding FS query;
3. hash-chain-backtracks the purported prior roots and FS salts;
4. invokes the stateful multi-configuration Merkle extractor on every root in that prefix, passing the new trace increment;
5. converts extracted IOP strings plus \((\text{root},\text{FS salt})\) into a state-restoration move;
6. answers malformed FS queries using a separate lazy-sampled “garbage” oracle;
7. after adversary termination, processes the final Merkle trace segment and outputs the final SR tuple.

Claim `bcs-reduction`, CY 17954–17985, compares a joint distribution containing the instance, extracted IOP strings, challenges, decision, and Merkle trace.

The modular proof, CY 17990–18114, factors BCS as hash-chain FS applied to iBCS and supplies an explicit IP-to-IOP state-restoration trace translator.

### 7.3 Design assessment

The user’s “computation tree from the RO trace” is directionally accurate but not CY’s terminology here. CY’s actual reduction object is:

- an ordered trace;
- segmented at FS queries;
- hash-chain backtracking over prior FS trace entries;
- a stateful database of Merkle extractions;
- an SR move-response trace.

There is no explicit computation-tree datatype in the BCS chapter. A formalization might choose to package the extracted prefixes as a computation DAG/tree, but it must prove equivalence to CY’s ordered-trace procedure.

`WorldSpec Γ` is the correct location for the shared ROs, but the design lacks:

- heterogeneous trace events tagged by resource identity;
- order-preserving trace projections;
- prefix and interval extraction;
- a theorem that `runΓ` trace segmentation commutes with handler substitution;
- stateful multi-Merkle extraction;
- hash-chain backtracking;
- malformed-query routing;
- the SR game and reduction;
- the joint distributional coupling in Claim `bcs-reduction`.

**Verdict: GAP.** Design §6.6 does not provide state restoration as a first-class game, and §6.10.7 does not provide the online extraction interface required by this proof.

---

## 8. BCS knowledge soundness

### 8.1 Exact theorem and quantifier structure

Theorem `bcs-knowledge-soundness`, CY 18423–18483, assumes rewinding IOP SRKS and concludes rewinding adaptive NARG KS.

Its error is not a simple sum. The IOP extractor is invoked with an *inflated failure probability*:

\[
\delta'_A
=
\delta_A
+
\varepsilon_{\mathrm{MT}}
+
\varepsilon_{\mathrm{hashchain}},
\]

and the outer error adds the same Merkle/hash-chain term. Running time similarly feeds an inflated prover runtime to the IOP extractor and adds Merkle multi-extraction and hash-chain costs.

If the IOP SR extractor is straightline, the resulting BCS extractor is straightline.

### 8.2 Exact extractor composition

Construction `bcs-extractor-direct`, CY 18550–18586, gives the BCS extractor:

- the instance and argument;
- the BCS prover’s ordered RO trace;
- the verifier’s RO trace;
- black-box access to the BCS prover in the rewinding case.

It then:

1. scans prover trace events in order;
2. segments Merkle events at FS events;
3. statefully multi-extracts each relevant root;
4. hash-chain-backtracks prior prefixes;
5. constructs the SR move-response trace;
6. processes the final trace segment;
7. parses the verifier trace;
8. constructs the transformed SR prover;
9. invokes the IOP SR extractor.

Thus this is not simply

\[
E_{\mathrm{IOP}}\circ E_{\mathrm{Merkle}}.
\]

It is:

\[
\text{trace segmentation}
\to
\text{stateful multi-Merkle extraction}
\to
\text{hash-chain prefix reconstruction}
\to
\text{SR trace/prover adapter}
\to
E_{\mathrm{IOP\text{-}SR}}.
\]

### 8.3 Exact taxonomy point

In Design §6.6.4 the straightline BCS extractor occupies:

- `OfflineLoggedExecution` for the BCS prover and verifier traces;
- a stateful online sub-extractor over successive trace prefixes;
- an `OfflineLoggedExecution` SR extractor at the IOP layer.

The rewinding version additionally requires:

- black-box access to the original BCS prover;
- construction of a black-box SR prover wrapper;
- whichever replay/checkpoint semantics the IOP SR extractor assumes.

It is therefore a *composite point across several taxonomy axes*, not one named leaf.

### 8.4 Design assessment

The taxonomy is descriptively useful, but there are no bridge theorems supporting:

- trace-adapter composition;
- deterministic stateful extractor composition;
- transformation of black-box access through a prover wrapper;
- preservation of failure probability;
- expected-time substitution;
- accumulation of extractor errors.

**Verdict: GAP.** The exact composition required by CY is not supported by the stated bridge theorems.

---

## 9. BCS zero knowledge and salting

### 9.1 Exact theorem

Theorem `bcs-zero-knowledge`, CY 18957 onward, bounds adaptive EPROM ZK by

\[
\varepsilon_{\mathrm{IOP\text{-}HVZK}}(N)
+
\sum_i
  \varepsilon_{\mathrm{MT\text{-}privacy}}
    (\lambda,A_i,L_i,s_{\mathrm{MT}},q_i,Q)
+
\frac{Q}{2^{s_{\mathrm{FS}}}}.
\]

Construction `bcs-simulator`, CY 18972–19004:

1. samples an IOP HVZK local view;
2. simulates each Merkle root and authentication paths from only the opened positions and values;
3. samples FS salts;
4. programs the FS oracle at one query per round.

The proof uses:

- a query-before-program bad event, bounded by the FS salt entropy;
- Merkle selective-opening privacy;
- IOP HVZK.

### 9.2 Objects forced by salting

A faithful design needs:

- per-leaf salt vectors, indexed by position;
- FS salts separate from Merkle salts;
- explicit salt entropy and length parameters;
- a Merkle local-view simulator;
- selective-opening hiding with adaptive query sets;
- a programmable RO world;
- a record of programmed points;
- rules for programming a previously queried point;
- proof that prior answers are preserved away from programmed points;
- query-before-program events;
- simulation of verifier-local oracle views rather than full IOP strings.

### 9.3 Design assessment

Design §6.10.7’s `SelectiveOpeningHiding` is necessary but insufficient. Design §8 explicitly postpones ZK, so full CY coverage is knowingly absent.

**Verdict: GAP.**

---

## 10. Special soundness

### 10.1 Definitions

CY defines:

- a fork of transcripts for a three-message protocol, CY 20570–20599;
- a tree of transcripts for a multi-round IP, CY 20605–20634;
- subtrees rooted at partial transcripts, CY 20639–20647;
- deterministic special-soundness extractors from every valid fork/tree.

Outgoing challenges at a node must be distinct, prover messages are shared along prefixes, and every root-to-leaf transcript accepts.

### 10.2 Knowledge theorems

CY proves:

- special soundness implies ordinary KS for sigma protocols, Theorem CY 20675–20686;
- special soundness implies SRKS for sigma protocols, CY 20836 onward;
- multi-round special soundness implies ordinary KS, CY 21313 onward;
- multi-round special soundness implies SRKS, Theorem CY 21935–21956.

The SR extractor repeatedly invokes and reprograms the lazy SR functions at selected prefix queries. Its analysis conditions on the original move trace and final output, uses early-abort rules, proves independence facts about prover private randomness, and derives expected-running-time recurrences. The equal-arity bound includes the \((B+1)\) multiplier.

### 10.3 Design assessment

`SpecialSoundnessTree` and `RBRTranscriptTree` in §6.6.4 name the right extraction shapes. They do not provide:

- distinct-challenge dependent trees;
- consistency of shared prefixes;
- lazy-function reprogramming;
- conditional distributions after fixing an original SR execution;
- prover-state replay;
- negative-hypergeometric sampling;
- expected-time recurrence infrastructure.

**Verdict: GAP.**

---

## 11. Round-by-round soundness and knowledge

### 11.1 CY’s state function and RBR soundness

Definition `iop-state`, CY 23543–23558, is one deterministic bit predicate on partial transcripts:

- the empty transcript has state \(0\);
- if the state is \(0\), appending any prover message preserves \(0\);
- a full transcript with state \(0\) must reject.

CY calls state \(1\) “doomed.” RBR soundness, CY 23563–23587, says that for every false instance, round, and adversarial prefix generator, conditioned on the pre-challenge state being \(0\), a uniform challenge changes the state to \(1\) with probability at most \(\varepsilon_j(x)\).

It proves:

- RBR soundness implies ordinary soundness with \(\sum_j\varepsilon_j\), CY 23593–23606;
- ordinary soundness implies an inefficient RBR state with a root-type loss, CY 23665 onward;
- RBR soundness implies SR soundness with
  \[
  \varepsilon_{\mathrm{SR}}(s,N,B)
  \le (B+r)\varepsilon_{\mathrm{RBR}}(N),
  \]
  CY 23952–23963.

### 11.2 CY’s RBR knowledge notion

Definition `iop-round-by-round-knowledge`, CY 23793–23820, uses:

- one polynomial-time extractor on the *entire tuple of IOP strings*;
- the same kind of state function;
- a two-phase adversary around a selected challenge;
- the bad event that the challenge crosses from state \(0\) to state \(1\), yet the whole-transcript extractor fails.

It then proves ordinary straightline KS with the sum of round errors and SRKS with the \((B+r)\) multiplier, CY 23826–23842 and 24160–24174.

### 11.3 Mismatch with the design

Design §6.6.5 proposes:

- prefix-indexed `MidWit p`;
- prefix-indexed `KState p`;
- edge-local backward maps;
- path accumulation via \(\kappa\).

That is not CY’s definition. It may be useful for compositional oracle reductions, but it is a stronger/different local-witness discipline. CY’s extractor is whole-transcript and does not require an edge-local witness to exist or transport backward.

The current `KnowledgeClaimTree` is stronger still: every edge carries an exact left inverse `extractAdvance`, [KnowledgeClaimTree.lean](/Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Security/KnowledgeClaimTree.lean:34). This is not CY RBRK.

The current plain claim-tree implementation is closer to CY’s state-function semantics, but even there it accumulates a structural `maxPathError`, whereas CY’s exact statement is indexed by protocol rounds and conditional transition events.

**Verdict:**

- CY RBR soundness: **OK-with-work** using a specialized `ClaimTree` representation and equivalence theorem.
- CY RBR knowledge: **GAP** unless a separate whole-transcript CY notion is added.
- RBR-to-SR bridges: **GAP** until the SR game exists.

The design should not claim that its proposed edge-local RBRK *is* CY’s definition. It should prove an implication from the stronger ArkLib notion to CY RBRK.

---

## 12. Preprocessing and holography

### 12.1 Exact games

CY defines indexed relations, CY 24436–24439, and an honest deterministic indexer sharing the oracle distribution with the proof system.

Adaptive preprocessing soundness, CY 24636–24660, has the order:

1. sample the global oracle tuple;
2. adversary phase 1 chooses an index and state;
3. honest deterministic indexer runs using the same oracles and produces PIK/VIK;
4. adversary phase 2 sees both keys and chooses the instance and argument;
5. verifier runs under the same oracle tuple.

Straightline KS, CY 24670–24696, supplies the extractor four logs:

- adversary phase-1 trace;
- honest indexer trace;
- adversary phase-2 trace;
- verifier trace.

The rewinding and ZK notions add black-box access and programming, CY 24722–24793.

### 12.2 Holographic IOP and COS

A HIOP verifier has trusted query access to an encoded verification index, CY 24485–24531 and 24813 onward. Its state-restoration game includes the index and honest indexer semantics, CY 25030 onward.

Construction `argument-indexer`, CY 24550 onward, commits to the encoded index with an unsalted Merkle tree and hashes the index for later FS use.

The COS transformation’s security is transferred through:

- an indexed-to-nonindexed relation conversion;
- a HIOP-to-IOP construction;
- an explicit trace translation;
- soundness, KS, and ZK theorems, CY 25315–25972.

### 12.3 Design assessment

`ResourceMeta.origin = setup/index` is only provenance metadata. It does not provide:

- the two-stage adversary;
- deterministic honest indexing inside the same persistent world;
- separate phase traces;
- a trusted encoded-index oracle;
- PIK/VIK visibility rules;
- adaptive index selection;
- indexed relation closure;
- trace conversion between COS and BCS;
- unsalted-index Merkle binding.

**Verdict: GAP.** The setup story is not adequate for CY preprocessing.

---

## 13. Witness indistinguishability

CY defines WI for ordinary and preprocessing NARGs and for SP/IP/PCP/IOP/HIOP systems, CY 26046–26249. It proves ZK implies WI and that BCS and COS preserve appropriate WI properties, including Merkle equivocation-based arguments, CY 26293–26622.

**Design mapping.**

WI needs paired experiments differing only in the witness, plus adversary-selected statements, shared worlds, and statistical/computational indistinguishability. None is present in §6.6.

**Verdict: GAP.**

---

## 14. Exact error bounds

CY’s summary tables are at CY 26751–27000. Their bounds depend on more than an additive security-error scalar.

### Required parameter structure

CY tracks:

- security parameter \(\lambda\);
- instance-size bound \(N\);
- total query bound \(Q\);
- resource-specific bounds such as \(Q_{\mathrm{MT}}\) and \(Q_{\mathrm{FS}}\);
- per-round proof lengths and alphabets;
- number of commitments and configurations;
- opening-set size;
- Merkle and FS salt lengths;
- state-restoration move budget \(B\);
- challenge-set cardinalities;
- adversary failure probability;
- adversary running time;
- extractor expected running time.

The total \(Q\) is global across phases and oracle functions unless explicitly refined to a vector; see CY 5798–5801.

### Non-additive features

The design’s \(\varepsilon_s+\varepsilon_{\mathrm{adm}}+\varepsilon_{\mathrm{fault}}\) and pathwise \(\kappa\) do not directly express:

- \(Q(Q-1)/2^{n+1}\);
- native multi-extraction error avoiding a factor equal to the number of commitments;
- resource-budget optimization under \(Q_{\mathrm{MT}}+Q_{\mathrm{FS}}\le Q\);
- \((B+r)\varepsilon_{\mathrm{RBR}}\);
- substitution of an inflated failure probability into another error function;
- expected-time functions depending on failure probability;
- sums over Merkle configurations with heterogeneous lengths and opening sizes;
- superadditive hiding-error simplification.

### Γ is not “per-world,” but budgets may accidentally become so

The design correctly says the persistent RO is one global world. The risk is that an implementation associates independent counters/errors with each Γ component. CY ordinarily gives the adversary one total budget across all oracle functions and phases, then derives the vector bounds under a sum constraint.

The required abstraction is therefore a global budget ledger with projections, not one budget per world.

**Verdict: GAP.** The design’s error vocabulary is too coarse for CY’s quantitative theorems.

---

# Consolidated coverage matrix

| CY area | Can state now? | Can prove in proposed design? | Verdict |
|---|---:|---:|---|
| Shared lazy random oracle and ordered trace | No concrete game | No | **GAP** |
| RO unpredictability/inversion/collision | After concrete RO world | Missing lazy-sampling probability library | **OK-with-work / GAP** |
| RO regularity and inversion hybrids | No quantitative semantic relation | No | **GAP** |
| General correlated oracle distributions | Conceptually | With joint-world and trace projection work | **OK-with-work** |
| Adaptive/nonadaptive argument soundness | Mostly | Needs explicit sampling-order games | **OK-with-work** |
| CY straightline/rewinding KS | Not exactly | No trace/BB composite extractors | **GAP** |
| Basic commitment correctness/binding | Yes conceptually | Needs concrete security record | **OK-with-work** |
| Basic trace extraction/multi-extraction | No exact game | No | **GAP** |
| Merkle construction/completeness | Yes | Concrete implementation work | **OK-with-work** |
| Merkle binding | Conceptually | Needs tree/collision library | **OK-with-work** |
| Merkle trace extraction | No exact interface | No | **GAP** |
| Stateful multi-config Merkle extraction | No | No | **GAP** |
| Merkle hiding/privacy/equivocation | No | ZK machinery absent | **GAP** |
| Ordinary IOP syntax and public queries | Largely | Partially | **OK-with-work** |
| IOP state-restoration game | No | No | **GAP** |
| IOP SR knowledge extraction | No | No | **GAP** |
| iBCS honest transformation | Skeleton exists | Security absent | **OK-with-work / GAP** |
| BCS honest construction | Pipeline can describe it | ROM FS deferred | **OK-with-work / GAP** |
| BCS adaptive soundness | No exact assumption/reduction | No | **GAP** |
| BCS knowledge soundness | No exact extractor composition | No | **GAP** |
| BCS zero knowledge | Deliberately deferred | No | **GAP** |
| CY RBR soundness | Close via claim trees | Needs equivalence and SR bridge | **OK-with-work** |
| CY RBR knowledge | Mismatched notion | No bridge | **GAP** |
| Special soundness → SRKS | Tree names only | No replay/reprogramming semantics | **GAP** |
| Preprocessing/HIOP/COS | Provenance only | No games or trace translations | **GAP** |
| WI | No paired game | No | **GAP** |
| CY exact error tables | No adequate budget/error algebra | No | **GAP** |

---

# Part 2: Severity-ranked complication catalog

## Critical

### 1. No first-class state-restoration game

- **CY:** Definitions at 16854–16968; BCS soundness at 17830 onward.
- **Design:** §§6.6.4–6.6.6.
- **Missing:** arbitrary-prefix SR request type, per-round random functions, salt-indexed replay, consistent repeated requests, move budget, final recomputation, SR trace.
- **Impact:** BCS soundness, BCS KS, RBR-to-SR, special-soundness-to-SR, and preprocessing BCS cannot be stated faithfully.

### 2. No global ordered heterogeneous oracle trace

- **CY:** ROM trace 2484–2490; BCS direct reduction 17901–17952.
- **Design:** §6.2 only sketches `runΓ`.
- **Missing:** events tagged with stable oracle identity, order, request, response, phase, and possibly caller; prefix/interval/projection APIs.
- **Impact:** The BCS reduction cannot determine “Merkle queries since the previous FS query.”

### 3. No stateful online multi-configuration Merkle extractor

- **CY:** Lemmas 13534 and 13874; used at 17901 and 18550.
- **Design:** §6.10.7 capability names.
- **Missing:** extractor state, incremental trace input, configuration projection, repeated-root coherence, cumulative invariant, native multi-instance error.
- **Impact:** Both BCS soundness and KS fail at their first cryptographic step.

### 4. No trace-to-state-restoration adapter

- **CY:** hash-chain backtracking and constructions at 10635–10807, 17901–18082, 18550–18586.
- **Design:** no corresponding object.
- **Missing:** parser for well-formed FS queries, backward chain reconstruction, malformed-query semantics, construction of SR move-response logs, proof of joint-distribution closeness.
- **Impact:** Even assuming Merkle extraction and SR soundness, the reduction does not compose.

### 5. No programmable random-oracle semantics

- **CY:** general ZK 5764–5796; BCS simulator 18972–19282.
- **Design:** ZK deferred.
- **Missing:** programming lists, collision policy, preservation of earlier answers, query-before-program events, simulated-world execution.
- **Impact:** BCS ZK, COS ZK, FS ZK, WI-from-ZK, and several oracle-switching arguments are unavailable.

### 6. Extractor taxonomy has no composition calculus

- **CY:** BCS extractor 18550–18586.
- **Design:** §6.6.4.
- **Missing:** composition of logged execution, stateful deterministic extraction, trace translators, and black-box prover wrappers; error, failure, and expected-time transport.
- **Impact:** Naming each extractor model does not yield the BCS KS theorem.

## High

### 7. `SourceCtx Δ`/`WorldSpec Γ` separation lacks trace ownership rules

A Merkle root is a local commitment boundary, but its extractor reads global Γ history. The backend therefore cannot be a property of Δ alone. It must be parameterized by:

- the identity of the Γ resource;
- a trace projection;
- the prefix at which the commitment was emitted;
- future continuation in the same Γ state.

The design does not say who owns or certifies that prefix.

### 8. Current straightline extraction sees the wrong information

[Oracle/Security/Basic.lean](/Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Security/Basic.lean:132) supplies complete prover-oracle values. CY BCS extraction supplies RO logs and reconstructs those values. Treating the former as the latter would assume away the central Merkle extraction theorem.

### 9. Error accounting lacks a resource-budget algebra

- **CY:** global \(Q\), refined budgets, move budget \(B\), heterogeneous Merkle configurations.
- **Design:** §6.10.8.
- **Missing:** budget vectors with a global sum constraint, monotonicity lemmas, trace-length certificates, maximization over admissible splits.
- **Lean pain:** every reduction needs dependent bookkeeping proving projected trace lengths sum to at most the original length.

### 10. Failure-probability and expected-time substitution is absent

BCS rewinding KS feeds \(\delta_A+\varepsilon_{\mathrm{add}}\) and \(T_A+T_{\mathrm{add}}\) into the IOP extractor. A simple additive error theorem cannot express this higher-order dependency.

### 11. CY RBR knowledge does not match the proposed edge-local notion

- **CY:** whole-transcript extractor, 23793–23820.
- **Design:** prefix `MidWit`, edge-local back maps, §6.6.5.
- **Missing:** an explicit theorem that ArkLib’s stronger local property implies CY’s whole-transcript RBRK.
- **Risk:** proving only the ArkLib property may be substantially harder for protocols that satisfy CY’s definition.

### 12. Special-soundness extraction needs controlled reprogramming and replay

CY’s multi-round extractor forks at arbitrary transcript prefixes and reasons about conditional executions. Stable resource identity is necessary but does not define what state is restored, what randomness is resampled, or which oracle entries remain fixed.

### 13. Merkle encoding details affect theorem statements

Leaf/internal query classification is only sound if encodings are disjoint or otherwise typed. Padding, arbitrary leaf counts, zero-salt variants, duplicate positions, and configuration IDs must all be fixed before proving extraction. `domainSep` metadata is not itself an injective-encoding proof.

## Medium

### 14. `bcsSpec` is a syntax transformation, not CY BCS

The current file changes oracle nodes into public commitment nodes and provides query/response decorations. It has no:

- hash-chain FS;
- random-oracle challenges;
- Merkle path verifier;
- security games;
- trace extractor;
- backend capability assumptions.

Calling its output “BCS” risks conflating a front-end lowering step with the full cryptographic transform.

### 15. Public-coin randomness has several non-equivalent forms

CY distinguishes:

- explicit uniform verifier messages;
- hash-chain-derived messages;
- basic-FS-derived messages;
- oracle-accessible verifier randomness derived coordinate-wise.

The design needs one interface that states how much randomness is materialized and what the adversary may query.

### 16. Preprocessing needs more than resource origin

The indexer is an honest computation in the same world between two adversarial phases. This requires temporal placement, not merely `origin = setup`.

### 17. General-oracle replacement is not ordinary lowering

CY indifferentiability supplies a simulator and trace translator. `LowerAccesses` supplies an implementation. A compiler correctness theorem does not imply cryptographic indistinguishability.

### 18. Hiding errors use structural facts about query sets

Merkle privacy depends on co-path independence and sometimes superadditivity/monotonicity of error functions. A generic “hiding error” field loses the conditions needed to simplify later BCS bounds.

## Lean-specific proof pain

### 19. Adaptive lazy sampling over dependent request/response types

A heterogeneous RO family naturally has dependent responses. Proving exchangeability, freshness, and consistency while preserving typed resource IDs will require either a carefully normalized sum type or substantial dependent rewriting.

### 20. Ordered trace slicing

BCS repeatedly slices one trace at FS events and projects Merkle events by configuration. In Lean, list slicing by event predicates will generate obligations about:

- concatenation order;
- partition completeness;
- projected lengths;
- cumulative extractor state;
- preservation under trace translation.

This should be a library, not repeated theorem-local plumbing.

### 21. Forking across a shared world

Special-soundness and rewinding proofs need to say exactly which world cells survive a fork. Copying an entire lazy table is not always correct; reprogramming one prefix while retaining unrelated entries needs a relational world semantics.

### 22. Probability conditioning

CY RBR and special-soundness arguments make heavy use of conditioned probabilities, failure events, expected invocation counts, and statistical-distance hybrids. ArkLib’s current direct `Pr[event | computation] ≤ ε` style will need a substantial finite-probability/conditioning library.

### 23. Equality of extracted total trees

CY fills missing leaves arbitrarily but still requires repeated roots to produce the same total vector/trapdoor. In Lean, this requires a deterministic choice policy and proof that extractor state preserves it across incremental calls.

### 24. Quantifier-order regressions will be easy

Several notions differ only by when the instance, index, oracle, keys, witness, and adversary state are chosen. Encoding all of them through one overly generic `ClosedClaim` risks silently proving a weaker game.

---

# Part 3: Missed insights and recommended consolidation

## 1. Adopt CY’s oracle-algorithm layer explicitly

The design should introduce a security-facing abstraction distinct from `VirtualOracle`:

```lean
structure OracleExecution (Γ : WorldFamily) (α : Type) where
  result : α
  finalWorld : Γ.State
  trace : List Γ.Event
  budget : Γ.cost trace ≤ declaredBudget
```

An oracle algorithm should carry a worst-case query budget independent of answers. The execution API should expose:

- whole trace;
- prefix at an output event;
- interval between two marked events;
- projection to one logical oracle;
- total and per-resource costs.

This is the common substrate for ROM lemmas, commitments, BCS, indifferentiability, preprocessing, and ZK.

---

## 2. Make state restoration a dedicated game, not an extractor mode

A reusable SR layer should define:

```lean
structure SRMove (Π : PublicCoinIOP) where
  round : Fin Π.rounds
  instance : Π.Instance
  proofs : Π.ProofPrefix round
  salts : Π.SaltPrefix round

def SRRequest := SRMove Π
def SRResponse (q : SRRequest Π) := Π.Challenge q.round
```

The world samples one random function per round and keys it by the entire move. Then define:

- `SRGame`;
- `SRTrace`;
- `MoveBound`;
- `SRSoundness`;
- straightline and rewinding `SRKnowledgeSoundness`;
- failure probability;
- expected extraction time.

Only after that should `CheckpointRestore` or transcript-tree extractors receive bridge theorems to SR.

---

## 3. Add an explicit trace transducer abstraction

CY repeatedly transforms one execution trace into another. This deserves a first-class object:

```lean
structure TraceTransducer (Γ₁ Γ₂) where
  State : Type
  step : State → Γ₁.Event → State × List Γ₂.Event
  finish : State → List Γ₂.Event
  coherent : ...
  costBound : ...
```

Instances include:

- selecting one Merkle configuration;
- splitting Merkle events at FS queries;
- hash-chain backtracking;
- BCS trace to SR trace;
- COS trace to BCS trace;
- multiple logical ROs to one domain-separated RO.

This is a major abstraction CY uses implicitly and the design currently lacks.

---

## 4. Replace flat commitment capabilities with game-indexed capability records

A CY-compatible Merkle backend needs at least:

```text
Correctness
Binding
HonestTreeBinding
SingleTraceExtractability
StatefulMultiExtractability
MultiConfigurationExtractability
RootHiding
SelectiveOpeningPrivacy
Equivocation
```

Each record should expose its exact:

- experiment;
- adversary phase structure;
- trace input;
- query-budget function;
- extractor/simulator;
- error function;
- running-time function;
- monotonicity or superadditivity facts.

“Function binding” and “multi-extractability” without these indices are too ambiguous for theorem reuse.

---

## 5. Treat budgets and errors as typed resources

The design should use a structured budget:

```text
Budget = {
  totalQueries,
  perOracleQueries,
  stateRestorationMoves,
  commitmentCount,
  configurationCount,
  openingCount
}
```

with a feasibility predicate such as

\[
\sum_i Q_i \le Q.
\]

Errors should be functions of budgets and protocol parameters, not fixed `ENNReal` values. Composition needs both:

- additive union-bound composition;
- functional substitution, including inflated failure probabilities and runtimes.

This would cover CY’s exact tables far better than a universal \(\varepsilon_s+\varepsilon_{\mathrm{adm}}+\varepsilon_{\mathrm{fault}}\).

---

## 6. Separate three notions currently called “transcript”

CY uses at least:

1. the interaction transcript of an IOP;
2. the verifier’s local query view;
3. the global oracle query-answer trace.

The design and current Lean code sometimes use “full transcript” for concrete prover oracle messages. That object must not be confused with the RO log given to a BCS extractor.

Recommended names:

- `InteractionTranscript`;
- `VerifierLocalView`;
- `WorldTrace`;
- `SRMoveTrace`;
- `ExtractorLog`.

Conversions between them should be explicit theorems.

---

## 7. Add CY-compatible RBR notions alongside ArkLib’s stronger one

The edge-local prefix witness design may be valuable for compositional IORs. It should not replace CY’s RBR definition.

Define:

- `CYStateFunction`;
- `CYRoundByRoundSoundness`;
- `CYRoundByRoundKnowledge`;
- `ArkRoundByRoundKnowledge`.

Then prove, where valid:

```text
Ark RBRK → CY RBRK → straightline KS
Ark RBRK → CY RBRK → SRKS
```

This avoids forcing CY’s textbook theorems through an unnecessarily strong local-witness API.

---

## 8. Model preprocessing as a staged world program

`ResourceMeta.origin` should remain metadata. The security experiment needs an explicit chronology:

```text
initialize Γ
run adversary phase 1 in Γ
run honest indexer in resulting Γ
run adversary phase 2 in resulting Γ
run verifier in resulting Γ
```

Each phase should produce its own trace while preserving a proof that their concatenation is the global trace.

---

## 9. How well does the compiler pipeline match CY?

### `RepresentOracles`

Good match for representing IOP strings as typed queryable resources. It aligns with CY’s separation between full IOP strings and local verifier views.

### `LowerAccesses`

Good match for replacing abstract point queries by concrete Merkle openings, provided it generates the precise query-set and response relation.

It does not by itself prove Merkle binding or extraction.

### `TransportBoundary`

Potentially the most useful stage for iBCS. CY’s iBCS proof can be viewed as transporting a local-view claim across committed oracle boundaries.

The stage must retain:

- the root’s configuration identity;
- the point at which its extraction trace ends;
- the opening verifier’s exact accepted relation.

### `FiatShamir`

The factoring

\[
\mathrm{BCS}
=
\mathrm{HashChainFS}(\mathrm{iBCS})
\]

is exactly CY’s modular viewpoint, CY 17990–18006. This strongly supports keeping Fiat–Shamir separate from commitment lowering.

But CY’s modular proof shows what the FS pass must consume: *state-restoration security of an interactive argument that already has its own persistent oracles*. A pass that merely replaces challenges with a replay oracle cannot support the theorem.

### Overall

The four-stage factoring matches CY’s construction-level structure reasonably well:

```text
IOP
→ materialized/committed IOP (iBCS)
→ state-restoration-secure interactive argument
→ hash-chain Fiat–Shamir
→ BCS NARG
```

It fights CY’s proof structure when each pass is treated as a local syntax rewrite. The security proof crosses pass boundaries through global trace data:

```text
FS trace order
  controls Merkle trace segmentation
    controls extraction of committed IOP strings
      controls construction of SR moves
        controls the final soundness/knowledge reduction.
```

Therefore the compiler needs proof-relevant execution artifacts and trace translators, not only transformed syntax and semantic equivalence.

---

# Final assessment

The design has the right high-level separation between local oracle resources and persistent cryptographic worlds, and the proposed compiler stages broadly agree with CY’s modular presentation of BCS as Fiat–Shamir applied to interactive BCS.

Nevertheless, full CY coverage would require a major additional layer. The missing center is not another variation of `ClosedClaim`; it is a formal semantics of adversarial oracle execution:

- persistent joint worlds;
- ordered typed logs;
- global budgets;
- trace slicing and translation;
- state-restoration games;
- stateful online extraction;
- reprogramming and replay;
- quantitative error, failure, and time transport.

Until those objects exist, the design can describe *what the BCS compiler should produce*, but it cannot express the exact hypotheses and reductions by which CY proves that the output is sound, knowledge-sound, zero-knowledge, preprocessing-secure, or quantitatively secure.

The most important design change is therefore:

> Promote `WorldSpec` execution traces, state restoration, trace transducers, and game-indexed commitment capabilities from handover notes and taxonomy entries into the primary formal API before stabilizing the security or compiler interfaces.