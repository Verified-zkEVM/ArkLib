# 03 — Adversarial Oracle Execution: Worlds, Games, Extractors, Budgets

**Architecture and security requirements.** This chapter explains the persistent oracle-world
layer, denoted Γ, and the experiments in which protocol security is stated. It complements the
[claim-resource chapter](02-oracle-reduction-core.md), which describes deterministic read-only
resources Δ, closing, and native effect order. The reader is assumed to know provers, verifiers,
transcripts, and soundness. The probability contracts below distinguish existing results from
proposed world-backed theorems. [Current status](00-current-status.md) owns the theorem inventory;
the [roadmap](05-roadmap.md) owns implementation stages and dependencies.

## 1. Worlds

A world Γ is a VCVio `OracleRuntime`: a stateful query handler with an explicit initialization
computation. Initialization happens once, and all parties and phases use the same persistent state
in execution order. Δ resources are read-only and per-reduction; Γ is shared and never closed into
a claim. Source sums and disjoint unions of named contexts do not duplicate the world. A product
of state types does not establish independence: joint initialization and the underlying probability
semantics must justify any independence claim.

A random-oracle model uses a lazy-function world. An indexed family of logical oracles is one
joint world; independence and domain separation are properties to prove. An algebraic-group model
instead restricts the adversary class and instruments its trace, with basis ownership and extension
rules specified by each theorem. Relations which themselves query the model random oracle are
outside the present scope. Common theorems may use a trivial runtime; each theorem involving a
nontrivial world names its runtime family explicitly.

The existing VCVio `OracleRuntime.runFrom_bind` and `run_bind` laws sequence programs while
retaining final state and concatenating query logs. `resume` continues from a previous result
without repeating initialization. These laws supply ordinary world sequencing. A general
operational-machine prefix-concatenation API is needed only if a concrete client cannot use that
monadic route.

## 2. The execution artifact

An execution artifact keeps observations from one actual run together. It does not establish
that the run occurred merely by having the right fields. Supported experiments sample from the
runner's evaluation measure, and statements about particular results use executor equations or
`GeneratedBy`/support membership as provenance evidence.

The current layers are:

| Layer | Paired observations | Source |
|---|---|---|
| `CoreRun` | Concrete execution path, input behavior, private prover output, optional verifier claim | [`CoreRun.lean`](../../ArkLib/Interaction/Oracle/CoreRun.lean) |
| `LoggedRun` | Core run and verifier source-query answers in order | [`LoggedRun.lean`](../../ArkLib/Interaction/Oracle/LoggedRun.lean) |
| `TerminalRun` | Logged result with explicit accept, reject, or fault, and the same input behavior | [`TerminalRun.lean`](../../ArkLib/Interaction/Oracle/TerminalRun.lean) |
| `PhasedRun` | Input behavior, setup log, source observations, and world-query regions at concrete action boundaries | [`PhasedRun.lean`](../../ArkLib/Interaction/Oracle/PhasedRun.lean) |
| VCVio `RunResult` | Runner output, residual world state, and ordered surface-query log | `VCVio.OracleComp.Runtime` |

`executeStrategiesCore` executes ordinary prover and restricted verifier strategies directly.
`executeCore` prepares a reduction's prover strategy and delegates to that shared path. The
logged, terminal, and phased adapters have erasure or observation laws relating their outputs to
the corresponding ordinary execution. Extending this direct-strategy path through composed
world-backed execution remains a target, rather than a new independent state-machine semantics.

Closing uses the recorded input behavior and messages from the same concrete path. Source logs
record Δ queries; world logs record Γ surface queries. `LoggedRun.verifierLocalView` is derived
from the enclosing log, public path, and terminal output, without replay. Recovering local query
observations by replay would require an additional determinism theorem. A runtime surface log
also omits import queries performed by initialization or the handler, so it need not determine the
residual state.

Keep four views distinct: the concrete `ExecutionPath`, the `VerifierLocalView`, the world-query
log, and the proposed state-restoration move trace. A public path and verifier result omit local
query order and answers. Compiled extractors need the relevant world-query evidence; an ordinary
execution path does not substitute for it. `WorldTrace` should be a named view of the existing
surface `QueryLog`, with the needed routing evidence, rather than another trace carrier.

## 3. Outcomes and missing probability mass

The implemented terminal type separates three returned outcomes:

```lean
inductive Terminal (Claim Fault)
  | accept : Claim → Terminal Claim Fault
  | reject : Terminal Claim Fault
  | fault : Fault → Terminal Claim Fault
```

Acceptance carries a claim. Rejection is an ordinary returned result, and malformed parsing or
openings fail closed by rejecting. A fault reports model failure. Composition continues only
from acceptance and short-circuits on rejection or fault. Legacy protocols using `Option` or
`Bool` need a protocol-specific outcome decoder and correspondence theorem; `none` in the
optional-claim convention means rejection, never a returned fault.

Evaluation measures can also have missing mass, representing failure to return. This differs
from an explicit returned fault. [`Terminal.observe`](../../ArkLib/Interaction/Oracle/TerminalMeasure.lean)
uses VCVio's failure-to-return boundary and requires the caller to name the fault assigned to
missing mass. Its proved laws preserve accepted and rejected mass exactly. The named fault
receives its original returned mass plus the missing mass; the observation has total mass one.
No decoder silently turns missing mass into rejection or acceptance.

A theorem counting only “accept and output a true claim” does not need to charge missing mass as
acceptance, and may require no losslessness hypothesis. Add a fault error when faults count as a
security failure or the theorem promises a separate fault bound. Such a claim states exactly
which returned faults and materialized failure-to-return events it covers. Extractor failure
belongs inside the knowledge-soundness bad event.

## 4. Games and ordinary soundness composition

Each security notion fixes sampling order, adversary phases, trace visibility, budget, observation,
and error/time parameters. An adaptive experiment samples its world before the adversary chooses
an instance; a static experiment fixes the instance first. The distinction changes the quantifiers
and must appear in the game definition.

Protocol games sequence the actual parties in one runtime. Preprocessing or an honest indexer
remains in that runtime between adversarial phases. A persistent state can be correlated with the
prover's memory and prior oracle answers; using the same oracle label in two stages does not
establish a common experiment.

### 4.1 Existing plain composition and the oracle target

For a false input, ordinary reduction soundness bounds the successful-output mass of a true output
claim. The proved plain native append theorem combines a prefix truth-transition bound `ε₁` with
a suffix bound `ε₂`, yielding `ε₁ + ε₂`. Its admissibility variant additionally charges `δ` for
intermediate outputs outside the suffix theorem's domain, yielding `ε₁ + δ + ε₂`. The suffix
premise covers every false, admissible prefix result, including unreachable ones, and every
native suffix strategy. The execution equation needs only a lawful monad; its probability theorem
needs lawful distribution semantics. It does not assume independent stages, uniform challenges,
finite message sets, or lossless execution.

Restricted oracle composition must additionally identify the actual intermediate closed claim,
route suffix queries through its exported interface, and preserve the world interpretation and
schedule. Those bridges are targets. Existing phase logs and profile-additivity laws do not
already prove their security premises.

### 4.2 Probability premises at the actual boundary

There is no single weakest assumption without fixing the experiment, its success event, and the
boundary observation. For a fixed execution, the relevant quantity is success of its actual
remaining computation, averaged over boundary results the prefix produces. A reusable uniform
bound is convenient, but stronger than necessary.

Let `μ` be the prefix's successful-output measure on complete boundary results. A boundary retains
whatever determines continuation: the intermediate claim, the actual prover continuation including
private memory, verifier-local values, and relevant history. For a world-backed experiment it also
retains the actual residual world state, jointly distributed with those values. This description
is for the proof and does not grant the prover access to hidden fields.

Let `E` be the prefix event charged as an error: a true intermediate claim reached from a false
input, or an accepted claim outside the suffix's admissibility assumptions. If the actual suffix
success probability after boundary `b` is bounded by a measurable `e(b)` outside `E`, the proposed
weighted bound is

```text
Pr[final success] ≤ μ(E) + ∫ over boundaries outside E, e(b) dμ(b).
```

The suffix measure or kernel must describe the actual remaining execution. Its definition needs
an order-preserving sequential decomposition and appropriate lawful measure semantics. Obtaining
it from a coarser observation may need conditional-probability infrastructure; it cannot be
assumed to exist solely because a public transcript is available. Missing prefix mass contributes
no boundary output to `μ`.

Useful sufficient forms of this premise, from easiest to reuse to most specific to an experiment,
are:

- A uniform bound for every false admissible boundary and every allowed continuation.
- A bound restricted to boundaries in the chosen prefix program's support.
- A bound holding almost everywhere under its actual output measure, allowing a probability-zero
  exceptional set.
- A variable suffix bound integrated over the actual boundary distribution, or a direct bound on
  that average when no useful pointwise bound exists.

Support reachability means structural possibility under the chosen program, including the returned
strategy. It is not necessarily positive probability: a supported result may have measure zero.
Almost-everywhere premises and integrals require the relevant measurability facts. Uniform bounds
are corollaries of the broader target, and there is no requirement to prove security at unreachable
boundaries for one fixed execution. The current plain theorem provides the uniform form; these
refinements and their oracle/runtime applications remain planned.

### 4.3 Hidden state and adversary information

The world-backed theorem must preserve the joint prefix distribution of residual world state,
private prover continuation, intermediate claim, and relevant history. A suffix bound for a fixed
public claim in a freshly initialized runtime loses this correlation and does not justify
composition. Nor may a proof choose a new adversary after revealing hidden state.

For example, suppose the world samples a hidden uniform bit and a prover which has learned nothing
about it always guesses zero. Its average success is one-half. Conditional on the secret being
zero, its success is one, so a one-half bound for every fixed secret is false. The correct averaged
premise remains useful. Conversely, if the prefix reveals the bit, the same fresh-world guessing
bound cannot be applied to the actual suffix: its prover now has that information and can succeed
with probability one.

Pointwise suffix bounds for every reachable hidden state are a sufficient special case when a
protocol proves them. The broader target averages over the actual correlated experiment while
restricting strategy selection and adaptation to information the prover really observed. The
boundary may expose hidden state to mathematical analysis without exposing it to the adversary.

### 4.4 Common first scope and error accounting

The first world-backed oracle target uses finite classical interaction trees, deterministic
read-only Δ resources, no terminal-view Γ queries, explicit challenge computations, fail-closed
parsing, and an order-preserving sequential decomposition. These are sufficient initial conditions,
not necessary restrictions on all future composition theorems. Read-only Δ terminal queries can
become ordinary values after interpretation; their observable logs must still be preserved. Broader
effectful boundaries follow the scheduling requirements in
[the claim-resource chapter](02-oracle-reduction-core.md#53-effect-order-and-terminal-computation).

The proposed common-case security contract combines prefix soundness `ε₁`, accepted-output
inadmissibility `δ`, and suffix soundness under the actual remaining distribution. Splitting
successful runs into true, false-admissible, and inadmissible intermediate claims yields the target
`ε₁ + δ + sup ε₂`; retaining variable suffix errors gives the integral above. Add `ε_fault` when
the exported bad event or fault guarantee requires it. A claim of general world-backed composition
waits for the execution, closing, admissibility, and distribution bridges; this contract is not an
already proved theorem.

## 5. State restoration

State restoration is a separate proposed security layer for compiled protocols. It is not a
checkpoint/restore operation: the adversary may submit multiple purported prefixes, with consistent
answers on repeated moves, and the final output re-derives every challenge. The intended salted move
shape is schematic:

```lean
structure SRMove (Π : PublicCoinIOP) where
  round : Fin Π.rounds
  inst  : Π.Instance
  prfx  : Π.ProofPrefix round
  salts : Π.SaltPrefix round

-- One random function per round, keyed on the entire move.
-- The prover has a move budget B; the trace records moves and responses.
```

The target notions include ordinary, straightline knowledge, and rewinding knowledge soundness,
with explicit error and running-time dependence on the experiment and budget. Straightline
extractors receive the state-restoration trace; rewinding extractors additionally receive the named
black-box access. Bridges from round-by-round security, special soundness, and to Fiat–Shamir must
state their entropy, salt, replay, budget, and loss assumptions. The planned round-by-round bridge
includes the `(B+r)` loss; it is not supplied by native ordinary composition.

Cost transport reuses VCVio's `ReductionWithCost`. Additive or substitution-style advantage error
needs the supported error-bearing reduction extension described in the
[foundation chapter](01-foundations.md). The causal trace and conditioning interfaces needed by
these proofs are separate upstream gaps.

## 6. Extractors and knowledge composition

Knowledge soundness requires witness availability, not only a bound on true output claims.
An offline extractor of a final execution path may learn a middle witness too late to supply it
to the second protocol. Terminal offline knowledge soundness therefore does not compose in general.
Valid targets require a prefix-measurable middle extractor, auxiliary-input-robust first-stage
knowledge soundness, or grafting of a suitable round-by-round transcript extractor. Any implication
from knowledge soundness to ordinary soundness also needs the causally available witness supplier
used by its game, rather than a bare existential witness.

Extractor interfaces specify adversary access, execution control, oracle evidence, output shape,
algorithm class, and world model. In particular, an offline concrete execution-path extractor and
an offline world-log extractor are different capabilities. Substituting the former for the latter
would omit the oracle-query evidence needed by compiled Merkle extraction. Further targets include
query-only and black-box interfaces for one pass, prefix queries, and checkpoint/restore, plus
witness transport and special-soundness or round-by-round transcript trees.

Compiled-layer extraction is planned as a causal pipeline:

```text
segment at Fiat–Shamir events
  → stateful multi-configuration Merkle extraction
  → hash-chain backtracking
  → state-restoration trace adaptation
  → inner state-restoration extractor
```

Each step needs order, causality, resource, error, and time evidence. The generic finite-trace
transducer and causality algebra belong in PolyFun; VCVio specializes them to query logs with
external resource certificates. ArkLib supplies protocol adapters, extractor composition, black-box
transport, and error/time substitution. Stateful online Merkle extraction remains a backend
capability consuming the shared runtime artifacts; it is not replaced by a pure list pass. These
are target interfaces and dependencies, not consequences of the ordinary composition theorem.

## 7. Round-by-round trees and implication targets

The planned constrained execution tree uses PolyFun cursors and restricted decorations. It
records shared prover prefixes, verifier forks with explicit conditional challenge computations,
pairwise-distinct sibling challenges where required, world-history agreement, and stable resource
identities. It can be bridged to operational-machine prefixes without identifying the carriers.

Round-by-round state is indexed by full concrete prefixes; public projection is a separate view.
Available sources grow under prefix extension, and no prefix receives future resources. Both
Chiesa–Yogev-compatible whole-transcript notions and ArkLib's stronger edge-local witness notions
are intended to coexist. The roadmap's implication proofs must state which notion they use and
which replay, entropy, and budget hypotheses support the `(B+r)` losses. Legacy formulations or
archived proofs do not establish the corresponding native world-backed theorems. A reversible
strong claim-tree interface must remain distinguishable from the relaxed probabilistic endpoint.

## 8. Budgets, errors, and time

Resource accounting reuses VCVio's `ResourceProfile`, query-bound, cost-model, and reduction
interfaces. ArkLib adds protocol-specific names and feasibility conditions, schematically:

```text
ProtocolResource := oracleQuery(id) | srMove | commitment | configuration | opening
ProtocolBudget := ResourceProfile refined by feasibility predicates
ε, T : ProtocolBudget → Params → FailureRate → RuntimeBound → ℝ≥0∞
```

The existing phase profiles count world queries under a supplied fixed classification. The planned
certification bridge must show that each classified query refers to a resource available at that
phase, preserves identity and aliasing, charges virtual-query expansion, and meets the stated
prefix/suffix budgets. Arithmetic additivity alone establishes none of these facts. A context's
disjoint names do not imply independent world state or fresh copies of shared resources.

Failure probability is experiment-specific. No parallel ledger or universal adversary-characteristics
record is introduced. Budget transport accompanies every reduction or transducer, including claims
such as a state-restoration prover making at most the Fiat–Shamir query budget's number of moves.
Error composition can be additive or substitution-style. Concrete expected-time recurrences remain
ArkLib theorems until multiple clients justify a generic upstream interface; reduction time stays
explicit.

## 9. Deferred obligations

- Zero knowledge and witness indistinguishability need programmable worlds, query-before-program
  events, local-view Merkle simulators, per-leaf and Fiat–Shamir salts, and paired experiments.
- Indifferentiability replaces an oracle distribution through a simulator, trace translator, and
  view-equivalence theorem. It is a cryptographic reduction, rather than compiler lowering.
- Quantum access requires a separate linear execution model and lies outside this classical core.

State restoration and compiler security require causal query evidence, extraction, resource bounds,
and guarantee transport beyond ordinary composition. FRI and Spartan ports and their two-way
legacy correspondences are separate clients; they are not prerequisites for establishing the
composition API against Sumcheck.
