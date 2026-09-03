/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.ProtocolSpec.SeqCompose
import VCVio.OracleComp.SimSemantics.Append

/-!
# Interactive (Oracle) Reductions

This file defines the basic components of a public-coin **Interactive Oracle Reduction** (IOR).
These are interactive protocols between two parties, a prover and a verifier, with the following
format:

  - The protocol proceeds over a number of steps. In each step, either the prover or the verifier
    sends a message to the other. We assume that this sequence of interactions is fixed in advance,
    and is described by a protocol specification (see `ProtocolSpec/Basic.lean`).

    Note that we do _not_ require interleaving prover's messages with verifier's challenges, for
    maximum flexibility in defining reductions.

  - Both parties may have access to some shared oracle, which is modeled as an oracle specification
    `OracleSpec`. These are often probabilistic sampling or random oracles.

  - At the beginning, the prover and verifier both take in an input statement `StmtIn`. There are a
    number of input **oracle** statements `OStmtIn` whose underlying content is known to the prover,
    but is only available via an oracle interface to the verifier. The prover also takes in a
    private witness `WitIn`.

  - During the interaction, the verifier is assumed to always send uniformly random challenges to
    the prover. The prover will send messages, which is either available in full to the verifier, or
    received as oracles. Which is which is specified by the protocol specification.

  - At the end of the interaction, the verifier performs a computation that outputs a new statement
    `StmtOut`. Each output oracle statement is represented either by a coherent embedding into an
    input/message oracle or by a virtual oracle whose query implementation is proved to agree with
    its extensional materialization.

Our formulation of IORs can be seen in the literature as **F-IORs**, where `F` denotes an arbitrary
class of oracles. See the blueprint for more details about our modeling choices.

We can then specialize our definition to obtain specific instantiations in the literature:

  - **Interactive Reductions** (IRs) are a special kind of IORs where _all_ of the prover's messages
    are available in full.
  - **Interactive Oracle Proofs** (IOPs) are a special kind of IORs where the output statement is
    Boolean (i.e. `accept/reject`), there is no oracle output statements, and the output witness is
    trivial.
  - Further specialization of IOPs include **Vector IOPs**, **Polynomial IOPs**, and so on, are
    defined in downstream files. Note that vector IOPs is the original definition of IOPs [BCS16],
    while polynomial IOPs were later introduced in [BCG+19] and others.
  - **Interactive Proofs** (IPs) are a combination of IRs and IOPs.
  - **Non-Interactive Reductions** (for example, folding or accumulation schemes) are IRs with a
    single message from the prover.
  - **Non-Interactive Arguments of Knowledge** (NARKs) are IPs with a single message from the
    prover.

We note that this file only defines the type signature of IORs. The semantics of executing an IOR
can be found in `Execution.lean`, while the security notions are found in the `Security` folder.

Note the appearance of the various dependencies in the type signatures:
- `oSpec : OracleSpec ι` comes first, as we expect this to be the ambient (fixed) shared oracle
  specification for the protocol
- `StmtIn` comes next, as the type of the input statement to the protocol
- Then we have `OStmtIn` for the type of the oracle input statements (for oracle reductions),
  followed by `WitIn`, the type of the input witness
- Then we have `StmtOut` for the type of the output statement, followed by `OStmtOut` for the type
  of the output oracle statements, and finally `WitOut` for the type of the output witness
- Finally, we have `pSpec : ProtocolSpec n`, which is the protocol specification for the (oracle)
  reduction

We arrange things in this way for potential future extensions, where later types may depend on
earlier types (i.e. `WitIn`, `StmtOut`, or `pSpec` may depend on `StmtIn`; though we do not expect,
say, `StmtOut` or `pSpec` to depend on the witness types, as that is not available to the (oracle)
verifier).
-/

open OracleComp OracleSpec SubSpec ProtocolSpec

-- Add an indexer?
structure Indexer {ι : Type} (oSpec : OracleSpec ι) {n : ℕ} (pSpec : ProtocolSpec n) (Index : Type)
    (Encoding : Type) where
  encode : Index → OracleComp oSpec Encoding
  [OracleInterface : OracleInterface.{0, 0} Encoding]

/-
Sketch of the upcoming refactor to the prover's type (dependent on VCVio refactor):

Consider the prover's type in a sigma protocol, denoted using an iterated monad:

`CtxIn → m (Message × m (Challenge → m (Response × m (CtxOut))))`

where `m = OracleComp oSpec` for some `oSpec : OracleSpec`.

How do we translate these into a stateful representation?

Recall:

- `input : CtxIn → PrvState 0`

- `sendMessage 0 : PrvState 0 → m (Message × PrvState 1)`

- `receiveChallenge 1 : PrvState 1 → m (Challenge → PrvState 2)`

- `sendMessage 2 : PrvState 2 → m (Response × PrvState 3)`

- `output : PrvState 3 → m (CtxOut)`

What are `PrvState {0, 1, 2, 3}`?

- `PrvState 0 = m (Message × m (Challenge → m (Response × m (CtxOut))))`

- `PrvState 1 = m (Challenge → m (Response × m (CtxOut)))`

- `PrvState 2 = m (Response × m (CtxOut))`

- `PrvState 3 = m (CtxOut)`

All maps (except `input`) are then identity!

-/

/-- The type signature for the prover's state at each round.

For a protocol with `n` messages exchanged, there will be `(n + 1)` prover states, with the first
state before the first message and the last state after the last message. -/
@[ext]
structure ProverState (n : ℕ) where
  PrvState : Fin (n + 1) → Type

/-- Initialization of prover's state via inputting the statement and witness. -/
@[ext]
structure ProverInput (StmtIn WitIn PrvState : Type) where
  input : StmtIn × WitIn → PrvState
  -- initState : PrvState
  -- if honest prover, then expect that PrvState 0 = WitIn

structure ProverInit (PrvState : Type) where
  init : PrvState

/-- Represents the interaction of a prover for a given protocol specification.

In each step, the prover gets access to the current state, then depending on the direction of the
step, the prover either sends a message or receives a challenge, and updates its state accordingly.

For maximum simplicity, we only define the `sendMessage` function as an oracle computation. All
other functions are pure. We may revisit this decision in the future.
-/
@[ext]
structure ProverRound {ι : Type} (oSpec : OracleSpec ι) {n : ℕ} (pSpec : ProtocolSpec n)
    extends ProverState n where
  /-- Send a message and update the prover's state -/
  sendMessage (i : MessageIdx pSpec) :
    PrvState i.1.castSucc → OracleComp oSpec (pSpec.Message i × PrvState i.1.succ)
  /-- Receive a challenge and update the prover's state -/
  receiveChallenge (i : ChallengeIdx pSpec) :
    PrvState i.1.castSucc → OracleComp oSpec (pSpec.Challenge i → PrvState i.1.succ)

/-- The output function of the prover, which takes in the prover's final state and returns an oracle
    computation that outputs some specified output type `Output`

  We note that an honest prover may output both the output statement and witness (for easier
  composability), but an adversarial prover in the knowledge soundness game may only output the
  witness.
-/
@[ext]
structure ProverOutput {ι : Type} (oSpec : OracleSpec ι) (Output PrvState : Type) where
  output : PrvState → OracleComp oSpec Output

/-- The type of algorithms that participates in an (interactive) reduction in the role of the
  prover. This consists of:

- `PrvState 0, ..., PrvState n`: the types for the private state, from before the first message to
  after the last message
- `init : PrvState 0` is the initial state
- `sendMessage` and `receiveChallenge` are the functions for sending and receiving messages for each
  round, depending on the direction of the round.

This is useful when modeling soundness, since we do not want to mandate that adversarial provers in
the soundness game need to input or output anything. -/
structure ProverInteraction {ι : Type} (oSpec : OracleSpec ι) {n : ℕ} (pSpec : ProtocolSpec n)
    extends ProverState n, ProverInit (PrvState 0), ProverRound oSpec pSpec

/-- The type of algorithms that participates in an (interactive) reduction in the role of the
  prover, and returns some specified output type `Output`. This consists of:

- A `ProverInteraction` type for the interaction with the verifier
- An `output` function that takes in the algorithm's final state and returns an oracle computation
  that outputs the output type `Output`

This is useful when modeling knowledge soundness, since we do not want to mandate that adversarial
provers in the knowledge soundness game need to input the input statement or witness. We also do not
need the adversarial prover to output any output statement, as such values are sourced from the
verifier.
-/
structure ProverInteractionWithOutput {ι : Type} (oSpec : OracleSpec ι) (Output : Type)
    {n : ℕ} (pSpec : ProtocolSpec n) extends
      ProverState n,
      ProverInit (PrvState 0),
      ProverRound oSpec pSpec,
      ProverOutput oSpec Output (PrvState (Fin.last n))

/-- The type of honest provers for an interactive reduction with `n` messages. This consists of:

  - `PrvState 0`, ..., `PrvState n` are the types for the prover's state at each round
  - `input` initializes the prover's state by taking in the input statement and witness
  - `sendMessage` takes in the prover's state, then returns an oracle computation that outputs a
    message and the next prover's state
  - `receiveChallenge` takes in the prover's state, then returns an oracle computation that outputs
    a function that takes in a challenge and returns the next prover's state
  - `output` returns the output statement and witness from the prover's state

Note that the output statement by the prover is present only to facilitate composing honest provers
together. For completeness, we will require that the prover's output statement is always equal to
the verifier's output statement. For soundness and knowledge soundness, we will use more restricted
types of provers (see `ProverInteraction` and `ProverInteractionWithOutput`). -/
@[ext]
structure Prover {ι : Type} (oSpec : OracleSpec ι)
    (StmtIn WitIn StmtOut WitOut : Type)
    {n : ℕ} (pSpec : ProtocolSpec n) extends
      ProverState n,
      ProverInput StmtIn WitIn (PrvState 0),
      ProverRound oSpec pSpec,
      ProverOutput oSpec (StmtOut × WitOut) (PrvState (Fin.last n))

/-

Problem with current prover definition: it's too "rigid" for (knowledge) soundness, to the point
where it's difficult (impossible?) to prove that knowledge soundness implies soundness.

The problem is that any prover (even adversarial) is assumed to have an input & output functions.
This does not really need to be the case. For knowledge soundness, we do not need any input, and
for soundness, we don't even need the output. All we care about that the prover participates in the
interaction to produce a transcript.

TODO: see if the new `ProverInteraction` and `ProverInteractionWithOutput` types can be used to
prove knowledge soundness implies soundness.
-/

/-- A verifier of an interactive protocol is a function that takes in the input statement and the
  transcript, and performs an oracle computation that outputs a new statement -/
@[ext]
structure Verifier {ι : Type} (oSpec : OracleSpec ι)
    (StmtIn StmtOut : Type) {n : ℕ} (pSpec : ProtocolSpec n) where
  verify : StmtIn → FullTranscript pSpec → OptionT (OracleComp oSpec) StmtOut

/-- An **(oracle) prover** in an interactive **oracle** reduction is a prover in the non-oracle
      reduction whose input statement also consists of the underlying messages for the oracle
      statements -/
@[reducible, inline]
def OracleProver {ι : Type} (oSpec : OracleSpec ι)
    (StmtIn : Type) {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type) (WitIn : Type)
    (StmtOut : Type) {ιₛₒ : Type} (OStmtOut : ιₛₒ → Type) (WitOut : Type)
    {n : ℕ} (pSpec : ProtocolSpec n) :=
  Prover oSpec (StmtIn × (∀ i, OStmtIn i)) WitIn (StmtOut × (∀ i, OStmtOut i)) WitOut pSpec

/-- A virtual output-oracle implementation for an `OracleVerifier`.

`materializeOutput` gives the extensional oracle value used by the existing bundled
`toVerifier` security interface. `simulateOutputQuery` gives the query-by-query VCV
implementation used by downstream oracle computations. `simulateOutputQuery_eq` requires
the two views to agree on every query. The output interface is a parameter of
both this structure and `OracleVerifier`; consequently the interface used to
produce virtual answers is definitionally the interface used by a downstream
verifier. -/
structure OracleOutputSimulation {ι : Type} (oSpec : OracleSpec ι)
    {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type)
    {ιₛₒ : Type} (OStmtOut : ιₛₒ → Type)
    {n : ℕ} (pSpec : ProtocolSpec n)
    [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
    [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]
    [Oₛₒ : ∀ i, OracleInterface (OStmtOut i)] where
  /-- Extensional materialization used by relation-facing bundled semantics. -/
  materializeOutput : pSpec.Challenges →
    (∀ i, OStmtIn i) → pSpec.Messages → (∀ i, OStmtOut i)
  /-- Query-by-query implementation of the virtual output family in terms of
  input statement oracles and prover-message oracles. -/
  simulateOutputQuery : pSpec.Challenges →
      QueryImpl [OStmtOut]ₒ
        (OracleComp (oSpec + ([OStmtIn]ₒ + [pSpec.Message]ₒ)))
  /-- The VCV query implementation agrees with the extensional materialization. -/
  simulateOutputQuery_eq : ∀ challenges oStmt messages q,
      simulateQ (OracleInterface.simOracle2 oSpec oStmt messages)
          (simulateOutputQuery challenges q) =
        pure ((Oₛₒ q.1).answer
          (materializeOutput challenges oStmt messages q.1) q.2)

/-- Legacy output-oracle semantics: every output is an input oracle or prover
message, with an explicit coherence proof for its public interface. -/
structure OracleOutputEmbedding {ιₛᵢ ιₛₒ : Type}
    (OStmtIn : ιₛᵢ → Type) {ιₘ : Type} (Message : ιₘ → Type)
    (OStmtOut : ιₛₒ → Type)
    [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
    [Oₘ : ∀ i, OracleInterface (Message i)]
    [Oₛₒ : ∀ i, OracleInterface (OStmtOut i)] where
  embed : ιₛₒ ↪ ιₛᵢ ⊕ ιₘ
  hEq : ∀ i, OStmtOut i = match embed i with
    | Sum.inl j => OStmtIn j
    | Sum.inr j => Message j
  outputInterface_heq : ∀ i, match embed i with
    | Sum.inl j => HEq (Oₛₒ i) (Oₛᵢ j)
    | Sum.inr j => HEq (Oₛₒ i) (Oₘ j)

/-- An **(oracle) verifier** of an interactive **oracle** reduction consists of:

  - an oracle computation `verify` that outputs the next statement. It may make queries to each of
    the prover's messages and each of the oracles present in the statement (according to a specified
    interface defined by `OracleInterface` instances).

  - output oracle statements `OStmtOut : ιₛₒ → Type`. A verifier may expose them as
    virtual oracles implemented query-by-query from its input and message oracles. Legacy
    verifiers instead select a subset of those source oracles through `embed` and `hEq`.

The virtual form supports derived output oracles without materializing them for downstream
oracle computations. Its agreement law connects that query-by-query implementation to the
extensional values used by the bundled security interface. -/
@[ext]
structure OracleVerifier {ι : Type} (oSpec : OracleSpec ι)
    (StmtIn : Type) {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type)
    (StmtOut : Type) {ιₛₒ : Type} (OStmtOut : ιₛₒ → Type)
    {n : ℕ} (pSpec : ProtocolSpec n)
    [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
    [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]
    [Oₛₒ : ∀ i, OracleInterface (OStmtOut i)]
    where

  /-- The core verification logic. Takes the input statement `stmtIn` and all verifier challenges
  `challenges` (which are determined outside this function, typically by sampling for
  public-coin protocols). Returns the output statement `StmtOut` within an `OracleComp` that has
  access to external oracles `oSpec`, input statement oracles `OStmtIn`, and prover message
  oracles `pSpec.Message`. -/
  verify : StmtIn → pSpec.Challenges →
    OptionT (OracleComp (oSpec + ([OStmtIn]ₒ + [pSpec.Message]ₒ))) StmtOut

  /-- The output family has exactly one semantic representation: either the
  legacy embedded-source form or a virtual query implementation. -/
  outputOracle :
    OracleOutputEmbedding OStmtIn pSpec.Message OStmtOut ⊕
      OracleOutputSimulation oSpec OStmtIn OStmtOut pSpec

-- Cannot find synthesization order...
-- instance {ιₛᵢ ιₘ ιₛₒ : Type} {OStmtIn : ιₛᵢ → Type} [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
--     {Message : ιₘ → Type} [Oₘ : ∀ i, OracleInterface (Message i)]
--     (OStmtOut : ιₛₒ → Type) (embed : ιₛₒ ↪ ιₛᵢ ⊕ ιₘ) :
--     ∀ i, OStmtOut i := fun i => by sorry

namespace OracleVerifier

variable {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type}
    {StmtOut : Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type}
    {n : ℕ} {pSpec : ProtocolSpec n}
    [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
    [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]
    [Oₛₒ : ∀ i, OracleInterface (OStmtOut i)]
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec)

/-- Materialize an output-oracle representation independently of the verifier
that owns it. This is useful for adapters that construct and justify a new
output representation explicitly. -/
def materializeOutputOracle
    (outputOracle :
      OracleOutputEmbedding OStmtIn pSpec.Message OStmtOut ⊕
        OracleOutputSimulation oSpec OStmtIn OStmtOut pSpec)
    (challenges : pSpec.Challenges)
    (oStmt : ∀ i, OStmtIn i) (messages : pSpec.Messages) : ∀ i, OStmtOut i :=
  match outputOracle with
    | Sum.inr simulation => simulation.materializeOutput challenges oStmt messages
    | Sum.inl output => fun i => match h : output.embed i with
      | Sum.inl j => (output.hEq i ▸ h ▸ oStmt j : OStmtOut i)
      | Sum.inr j => (output.hEq i ▸ h ▸ messages j : OStmtOut i)

/-- Transport a query across explicit heterogeneous interface coherence. -/
def queryAlongHEq {A B : Type} (OA : OracleInterface A) (OB : OracleInterface B)
    (hType : A = B) (h : HEq OA OB) {ι' : Type} {spec : OracleSpec ι'}
    (impl : (q : OB.Query) → OracleComp spec (OB.Response q))
    (q : OA.Query) : OracleComp spec (OA.Response q) := by
  cases hType
  cases eq_of_heq h
  exact impl q

/-- Materialize the semantic output family, using a virtual simulation when
present and the legacy embedding otherwise. -/
def materializeOutput (challenges : pSpec.Challenges)
    (oStmt : ∀ i, OStmtIn i) (messages : pSpec.Messages) : ∀ i, OStmtOut i :=
  materializeOutputOracle verifier.outputOracle challenges oStmt messages

/-- Query any semantic output oracle in terms of the verifier's input and
message oracles. This operation hides the virtual/legacy distinction from
generic composition. -/
def simulateOutputQuery (challenges : pSpec.Challenges) :
    QueryImpl [OStmtOut]ₒ
      (OracleComp (oSpec + ([OStmtIn]ₒ + [pSpec.Message]ₒ))) :=
  match verifier.outputOracle with
    | Sum.inr simulation => simulation.simulateOutputQuery challenges
    | Sum.inl output => fun q => match h : output.embed q.1 with
      | Sum.inl j => by
          have hType : OStmtOut q.1 = OStmtIn j := by
            simpa only [h] using output.hEq q.1
          have hi : HEq (Oₛₒ q.1) (Oₛᵢ j) := by
            simpa only [h] using output.outputInterface_heq q.1
          exact queryAlongHEq (Oₛₒ q.1) (Oₛᵢ j) hType hi
            (fun t : (Oₛᵢ j).Query =>
              ((QueryImpl.id' [OStmtIn]ₒ).liftTarget
                (OracleComp (oSpec + ([OStmtIn]ₒ + [pSpec.Message]ₒ)))) ⟨j, t⟩) q.2
      | Sum.inr j => by
          have hType : OStmtOut q.1 = pSpec.Message j := by
            simpa only [h] using output.hEq q.1
          have hi : HEq (Oₛₒ q.1) (Oₘ j) := by
            simpa only [h] using output.outputInterface_heq q.1
          exact queryAlongHEq (Oₛₒ q.1) (Oₘ j) hType hi
            (fun t : (Oₘ j).Query =>
              ((QueryImpl.id' [pSpec.Message]ₒ).liftTarget
                (OracleComp (oSpec + ([OStmtIn]ₒ + [pSpec.Message]ₒ)))) ⟨j, t⟩) q.2

private theorem simulateQueryAlongHEq {A B : Type}
    (OA : OracleInterface A) (OB : OracleInterface B)
    (hType : A = B) (hInterface : HEq OA OB)
    {ι' : Type} {spec : OracleSpec ι'}
    (impl : (q : OB.Query) → OracleComp spec (OB.Response q))
    (q : OA.Query) {ι'' : Type} {targetSpec : OracleSpec ι''}
    (sim : QueryImpl spec (OracleComp targetSpec))
    (a : A) (b : B) (hab : HEq a b)
    (hImpl : ∀ q, simulateQ sim (impl q) = pure (OB.answer b q)) :
    simulateQ sim (queryAlongHEq OA OB hType hInterface impl q) =
      pure (OA.answer a q) := by
  cases hType
  cases eq_of_heq hInterface
  cases eq_of_heq hab
  exact hImpl q

/-- Querying the semantic output family agrees with materializing that family,
for both embedded and virtual output representations. -/
theorem simulateOutputQuery_eq
    (challenges : pSpec.Challenges) (oStmt : ∀ i, OStmtIn i)
    (messages : pSpec.Messages) (q : [OStmtOut]ₒ.Domain) :
    simulateQ (OracleInterface.simOracle2 oSpec oStmt messages)
        (verifier.simulateOutputQuery challenges q) =
      pure ((Oₛₒ q.1).answer
        (verifier.materializeOutput challenges oStmt messages q.1) q.2) := by
  rcases q with ⟨i, q⟩
  cases hOutput : verifier.outputOracle with
  | inr simulation =>
    simp only [simulateOutputQuery, materializeOutput, materializeOutputOracle,
      hOutput, MessageIdx, Message]
    exact simulation.simulateOutputQuery_eq challenges oStmt messages ⟨i, q⟩
  | inl output =>
    simp only [simulateOutputQuery, materializeOutput, materializeOutputOracle,
      hOutput, MessageIdx, Message]
    split
    next j hEmbed =>
      have hType : OStmtOut i = OStmtIn j := by
        simpa only [hEmbed] using output.hEq i
      have hInterface : HEq (Oₛₒ i) (Oₛᵢ j) := by
        simpa only [hEmbed] using output.outputInterface_heq i
      let a : OStmtOut i := output.hEq i ▸ hEmbed ▸ oStmt j
      have hab : HEq a (oStmt j) := by
        simp only [a, eqRec_heq_iff]
        exact HEq.rfl
      apply simulateQueryAlongHEq (Oₛₒ i) (Oₛᵢ j) hType hInterface
        _ q _ a (oStmt j) hab
      intro t
      exact QueryImpl.simulateQ_addLift_add_liftM_left (QueryImpl.id oSpec)
        (OracleInterface.simOracle0 OStmtIn oStmt)
        (OracleInterface.simOracle0 pSpec.Message messages)
        (([OStmtIn]ₒ).query ⟨j, t⟩)
    next j hEmbed =>
      have hType : OStmtOut i = pSpec.Message j := by
        simpa only [hEmbed] using output.hEq i
      have hInterface : HEq (Oₛₒ i) (Oₘ j) := by
        simpa only [hEmbed] using output.outputInterface_heq i
      let a : OStmtOut i := output.hEq i ▸ hEmbed ▸ messages j
      have hab : HEq a (messages j) := by
        simp only [a, eqRec_heq_iff]
        exact HEq.rfl
      apply simulateQueryAlongHEq (Oₛₒ i) (Oₘ j) hType hInterface
        _ q _ a (messages j) hab
      intro t
      exact QueryImpl.simulateQ_addLift_add_liftM_right (QueryImpl.id oSpec)
        (OracleInterface.simOracle0 OStmtIn oStmt)
        (OracleInterface.simOracle0 pSpec.Message messages)
        (([pSpec.Message]ₒ).query ⟨j, t⟩)
/-- An oracle verifier can be seen as a (non-oracle) verifier by providing the oracle interface
  using its knowledge of the oracle statements and the transcript messages in the clear -/
def toVerifier : Verifier oSpec (StmtIn × ∀ i, OStmtIn i) (StmtOut × (∀ i, OStmtOut i)) pSpec where
  verify := fun ⟨stmt, oStmt⟩ transcript => OptionT.mk <|
    Option.map (fun stmtOut =>
      (stmtOut, verifier.materializeOutput
        transcript.challenges oStmt transcript.messages)) <$>
      simulateQ (OracleInterface.simOracle2 oSpec oStmt transcript.messages)
        (verifier.verify stmt transcript.challenges).run

/-- The number of queries made to the oracle statements and the prover's messages, for a given input
    statement and challenges.

  This is given as an oracle computation itself, since the oracle verifier may be adaptive and has
  different number of queries depending on the prior responses.

  TODO: define once `numQueries` is defined in `OracleComp` -/
def numQueries (stmt : StmtIn) (challenges : ∀ i, pSpec.Challenge i)
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec) :
  OracleComp (oSpec + ([OStmtIn]ₒ + [pSpec.Message]ₒ)) ℕ := sorry

/-- A **non-adaptive** oracle verifier is an oracle verifier that makes a **fixed** list of queries
    to the input oracle statements and the prover's messages. These queries can depend on the input
    statement and the challenges, but later queries are not dependent on the responses of previous
    queries.

  Formally, we model this as a tuple of functions:
  - `queryOStmt`, which outputs a list of queries to the input oracle statements,
  - `queryMsg`, which outputs a list of queries to the prover's messages,
  - `verify`, which outputs the new statement from the query-response pairs.

  We allow querying the shared oracle (i.e. probabilistic sampling or random oracles) when deriving
  the output statement, but not on the list of queries made to the oracle statements or the prover's
  messages.

  Finally, we also allow for choosing a subset of the input oracle statements + the prover's
  messages to retain for the output oracle statements.
-/
structure NonAdaptive {ι : Type} (oSpec : OracleSpec ι)
    (StmtIn : Type) {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type)
    (StmtOut : Type) {ιₛₒ : Type} (OStmtOut : ιₛₒ → Type)
    {n : ℕ} (pSpec : ProtocolSpec n)
    [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
    [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]
    [Oₛₒ : ∀ i, OracleInterface (OStmtOut i)]
    where

  /-- Makes a list of queries to each of the oracle statements, given the input statement and the
    challenges -/
  queryOStmt : StmtIn → (∀ i, pSpec.Challenge i) → List ((i : ιₛᵢ) × (Oₛᵢ i).Query)

  /-- Makes a list of queries to each of the prover's messages, given the input statement and the
    challenges -/
  queryMsg : StmtIn → (∀ i, pSpec.Challenge i) → List ((i : pSpec.MessageIdx) × (Oₘ i).Query)

  /-- From the query-response pairs, returns a computation that outputs the new output statement -/
  verify : StmtIn → (∀ i, pSpec.Challenge i) →
    List ((i : ιₛᵢ) × ((q : (Oₛᵢ i).Query) × (Oₛᵢ i).Response q)) →
    List ((i : pSpec.MessageIdx) × ((q : (Oₘ i).Query) × (Oₘ i).Response q)) →
      OracleComp oSpec StmtOut

  embed : ιₛₒ ↪ ιₛᵢ ⊕ pSpec.MessageIdx

  hEq : ∀ i, OStmtOut i = match embed i with
    | Sum.inl j => OStmtIn j
    | Sum.inr j => pSpec.Message j

  outputInterface_heq : ∀ i, match embed i with
    | Sum.inl j => HEq (Oₛₒ i) (Oₛᵢ j)
    | Sum.inr j => HEq (Oₛₒ i) (Oₘ j)

namespace NonAdaptive

/-- Converts a non-adaptive oracle verifier into the general oracle verifier interface.

This essentially performs the queries via `List.mapM`, then runs `verify` on the query-response
pairs. -/
def toOracleVerifier
    (naVerifier : OracleVerifier.NonAdaptive oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec) :
    OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec := by
  rcases naVerifier with
    ⟨queryOStmt, queryMsg, verify, embed, hEq, outputInterface_heq⟩
  exact {
  verify := fun stmt challenges => do
    let oc := oSpec + ([OStmtIn]ₒ + [pSpec.Message]ₒ)
    let queryResponsesOStmt : List ((i : ιₛᵢ) × ((q : (Oₛᵢ i).Query) × (Oₛᵢ i).Response q)) ←
      (queryOStmt stmt challenges).mapM
      (fun q => do
        let resp ← liftM <|
          query (spec := [OStmtIn]ₒ) (m := OracleComp oc) q
        return ⟨q.1, ⟨q.2, resp⟩⟩)
    let queryResponsesOMsg :
        List ((i : pSpec.MessageIdx) × ((q : (Oₘ i).Query) × (Oₘ i).Response q)) ←
      (queryMsg stmt challenges).mapM
      (fun q => do
        let resp ← liftM <|
          query (spec := [pSpec.Message]ₒ) (m := OracleComp oc) q
        return ⟨q.1, ⟨q.2, resp⟩⟩)
    let stmtOut ← liftM <| verify stmt challenges queryResponsesOStmt queryResponsesOMsg
    return stmtOut

  outputOracle := .inl {
    embed := embed
    hEq := fun i => by
      have hi := hEq i
      rcases h : embed i with j | j <;> simp only [h, Message] at hi ⊢ <;> exact hi
    outputInterface_heq := fun i => by
      have hi := outputInterface_heq i
      rcases h : embed i with j | j <;> simp only [h, Message] at hi ⊢ <;> exact hi } }

/-- The number of queries made to the `i`-th oracle statement, for a given input statement and
    challenges. -/
def numOStmtQueries [DecidableEq ιₛᵢ] (i : ιₛᵢ)
    (stmt : StmtIn) (challenges : ∀ i, pSpec.Challenge i)
    (naVerifier : OracleVerifier.NonAdaptive oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec) : ℕ :=
  (naVerifier.queryOStmt stmt challenges).filter (fun q => q.1 = i) |>.length

/-- The number of queries made to the `i`-th prover's message, for a given input statement and
    challenges. -/
def numOMsgQueries (i : pSpec.MessageIdx)
    (stmt : StmtIn) (challenges : ∀ i, pSpec.Challenge i)
    (naVerifier : OracleVerifier.NonAdaptive oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec) : ℕ :=
  (naVerifier.queryMsg stmt challenges).filter (fun q => q.1 = i) |>.length

/-- The total number of queries made to the oracle statements and the prover's messages, for a
    given input statement and challenges. -/
def totalNumQueries (stmt : StmtIn) (challenges : ∀ i, pSpec.Challenge i)
    (naVerifier : OracleVerifier.NonAdaptive oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec) : ℕ :=
  (naVerifier.queryOStmt stmt challenges).length + (naVerifier.queryMsg stmt challenges).length

end NonAdaptive

end OracleVerifier

/-- An **interactive reduction** for a given protocol specification `pSpec`, and relative to oracles
  defined by `oSpec`, consists of a prover and a verifier. -/
@[ext]
structure Reduction {ι : Type} (oSpec : OracleSpec ι)
    (StmtIn WitIn StmtOut WitOut : Type) {n : ℕ} (pSpec : ProtocolSpec n) where
  prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec
  verifier : Verifier oSpec StmtIn StmtOut pSpec

/-- An **interactive oracle reduction** for a given protocol specification `pSpec`, and relative to
  oracles defined by `oSpec`, consists of a prover and an **oracle** verifier. -/
@[ext]
structure OracleReduction {ι : Type} (oSpec : OracleSpec ι)
    (StmtIn : Type) {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type) (WitIn : Type)
    (StmtOut : Type) {ιₛₒ : Type} (OStmtOut : ιₛₒ → Type) (WitOut : Type)
    {n : ℕ} (pSpec : ProtocolSpec n)
    [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)] [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]
    [Oₛₒ : ∀ i, OracleInterface (OStmtOut i)]
    where
  prover : OracleProver oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec
  verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec

/-- An interactive oracle reduction can be seen as an interactive reduction, via coercing the
  oracle verifier to a (normal) verifier -/
def OracleReduction.toReduction {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} {WitIn : Type}
    {StmtOut : Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} {WitOut : Type}
    {n : ℕ} {pSpec : ProtocolSpec n}
    [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)] [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]
    [Oₛₒ : ∀ i, OracleInterface (OStmtOut i)]
    (oracleReduction : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec) :
      Reduction oSpec (StmtIn × (∀ i, OStmtIn i)) WitIn
        (StmtOut × (∀ i, OStmtOut i)) WitOut pSpec :=
  ⟨oracleReduction.prover, oracleReduction.verifier.toVerifier⟩

/-- An **interactive proof (IP)** is an interactive reduction where the output statement is a
    boolean, the output witness is trivial (a `Unit`), and the relation checks whether the output
    statement is true. -/
@[reducible] def Proof {ι : Type} (oSpec : OracleSpec ι)
    (Statement Witness : Type) {n : ℕ} (pSpec : ProtocolSpec n) :=
  Reduction oSpec Statement Witness Bool Unit pSpec

/-- An **interactive oracle proof (IOP)** is an interactive oracle reduction where the output
    statement is a boolean, while both the output oracle statement & the output witness are
    trivial (`Unit` type).

    As a consequence, the output relation in an IOP is effectively a function `Bool → Prop`, which
    we can again assume to be the trivial one (sending `true` to `True`). -/
@[reducible] def OracleProof {ι : Type} (oSpec : OracleSpec ι)
    (Statement : Type) {ιₛᵢ : Type} (OStatement : ιₛᵢ → Type) (Witness : Type)
    {n : ℕ} (pSpec : ProtocolSpec n)
    [Oₛᵢ : ∀ i, OracleInterface (OStatement i)]
    [Oₘ : ∀ i, OracleInterface (pSpec.Message i)] :=
  @OracleReduction ι oSpec Statement ιₛᵢ OStatement Witness Bool Empty
    (fun _ : Empty => Unit) Unit n pSpec Oₛᵢ Oₘ (fun i => nomatch i)

/-- The verifier type underlying an interactive oracle proof. Its output-oracle
family is empty, so its interface is supplied by elimination rather than by a
global `OracleInterface Unit` instance. -/
@[reducible] def OracleProofVerifier {ι : Type} (oSpec : OracleSpec ι)
    (Statement : Type) {ιₛ : Type} (OStatement : ιₛ → Type)
    {n : ℕ} (pSpec : ProtocolSpec n)
    [Oₛ : ∀ i, OracleInterface (OStatement i)]
    [Oₘ : ∀ i, OracleInterface (pSpec.Message i)] :=
  @OracleVerifier ι oSpec Statement ιₛ OStatement Bool Empty
    (fun _ : Empty => Unit) n pSpec Oₛ Oₘ
      (fun i => nomatch i)

namespace OracleProofVerifier

/-- Construct the verifier of an interactive oracle proof. The empty output
family is discharged locally, without introducing a global interface instance
for `Unit`. -/
def ofVerify {ι : Type} {oSpec : OracleSpec ι}
    {Statement : Type} {ιₛ : Type} {OStatement : ιₛ → Type}
    {n : ℕ} {pSpec : ProtocolSpec n}
    [Oₛ : ∀ i, OracleInterface (OStatement i)]
    [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]
    (verify : Statement → pSpec.Challenges →
      OptionT (OracleComp (oSpec + ([OStatement]ₒ + [pSpec.Message]ₒ))) Bool) :
      OracleProofVerifier oSpec Statement OStatement pSpec :=
  @OracleVerifier.mk ι oSpec Statement ιₛ OStatement Bool Empty
    (fun _ : Empty => Unit) n pSpec Oₛ Oₘ
    (fun i => nomatch i) verify
    (.inl <| @OracleOutputEmbedding.mk ιₛ Empty OStatement
      pSpec.MessageIdx pSpec.Message (fun _ : Empty => Unit)
      Oₛ Oₘ (fun i => nomatch i)
      ⟨Empty.elim, fun a _ => Empty.elim a⟩
      (fun i => Empty.elim i) (fun i => Empty.elim i))

end OracleProofVerifier

/-- Obtain the verifier of an `OracleProof` without requiring a global
interface for its uninhabited output-oracle family. -/
@[reducible] def OracleProof.toOracleVerifier {ι : Type}
    {oSpec : OracleSpec ι} {Statement : Type} {ιₛ : Type}
    {OStatement : ιₛ → Type} {Witness : Type} {n : ℕ}
    {pSpec : ProtocolSpec n}
    [Oₛ : ∀ i, OracleInterface (OStatement i)]
    [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]
    (oracleProof : OracleProof oSpec Statement OStatement Witness pSpec) :
      OracleProofVerifier oSpec Statement OStatement pSpec :=
  @OracleReduction.verifier ι oSpec Statement ιₛ OStatement Witness
    Bool Empty (fun _ : Empty => Unit) Unit n pSpec Oₛ
      Oₘ (fun i => nomatch i) oracleProof

/-- A **non-interactive prover** is a prover that only sends a single message to the verifier. -/
@[reducible] def NonInteractiveProver (Message : Type) {ι : Type} (oSpec : OracleSpec ι)
    (StmtIn WitIn StmtOut WitOut : Type) :=
  Prover oSpec StmtIn WitIn StmtOut WitOut ⟨!v[.P_to_V], !v[Message]⟩

/-- A **non-interactive verifier** is a verifier that only receives a single message from the
  prover. -/
@[reducible] def NonInteractiveVerifier (Message : Type) {ι : Type} (oSpec : OracleSpec ι)
    (StmtIn StmtOut : Type) :=
  Verifier oSpec StmtIn StmtOut ⟨!v[.P_to_V], !v[Message]⟩

/-- A **non-interactive reduction** is an interactive reduction with only a single message from the
  prover to the verifier (and none in the other direction). -/
@[reducible] def NonInteractiveReduction (Message : Type) {ι : Type} (oSpec : OracleSpec ι)
    (StmtIn WitIn StmtOut WitOut : Type) :=
  Reduction oSpec StmtIn WitIn StmtOut WitOut ⟨!v[.P_to_V], !v[Message]⟩

section Trivial

variable {ι : Type} {oSpec : OracleSpec ι}
    {Statement : Type} {ιₛ : Type} {OStatement : ιₛ → Type} {Witness : Type}
    [Oₛ : ∀ i, OracleInterface (OStatement i)]

/-- The trivial / identity prover, which does not send any messages to the verifier, and returns its
  input context (statement & witness) as output. -/
protected def Prover.id : Prover oSpec Statement Witness Statement Witness !p[] where
  PrvState := fun _ => Statement × Witness
  input := _root_.id
  sendMessage := fun i => Fin.elim0 i
  receiveChallenge := fun i => Fin.elim0 i
  output := pure

/-- The trivial / identity verifier, which does not receive any messages from the prover, and
  returns its input statement as output. -/
protected def Verifier.id : Verifier oSpec Statement Statement !p[] where
  verify := fun stmt _ => pure stmt

/-- The trivial / identity reduction, which consists of the trivial prover and verifier. -/
protected def Reduction.id : Reduction oSpec Statement Witness Statement Witness !p[] where
  prover := Prover.id
  verifier := Verifier.id

/-- The trivial / identity prover in an oracle reduction, which unfolds to the trivial prover for
  the associated non-oracle reduction. -/
protected def OracleProver.id :
    OracleProver oSpec Statement OStatement Witness Statement OStatement Witness !p[] :=
  Prover.id

/-- The trivial / identity verifier in an oracle reduction, which receives no messages from the
  prover, and returns its input statement as output. -/
protected def OracleVerifier.id :
    OracleVerifier oSpec Statement OStatement Statement OStatement !p[] where
  verify := fun stmt _ => pure stmt
  outputOracle := .inl {
    embed := Function.Embedding.inl
    hEq := fun _ => rfl
    outputInterface_heq := fun i => by
      change HEq (Oₛ i) (Oₛ i)
      rfl }

/-- The trivial / identity oracle reduction, which consists of the trivial oracle prover and
  verifier. -/
protected def OracleReduction.id :
    OracleReduction oSpec Statement OStatement Witness Statement OStatement Witness !p[] :=
  ⟨OracleProver.id, OracleVerifier.id⟩

alias Prover.trivial := Prover.id
alias Verifier.trivial := Verifier.id
alias Reduction.trivial := Reduction.id
alias OracleProver.trivial := OracleProver.id
alias OracleVerifier.trivial := OracleVerifier.id
alias OracleReduction.trivial := OracleReduction.id

@[simp]
lemma OracleVerifier.id_toVerifier :
    (OracleVerifier.id : OracleVerifier oSpec Statement OStatement _ _ _).toVerifier =
      Verifier.id := by
  ext ⟨s, o⟩ t
  have hOutput :
      (OracleVerifier.id : OracleVerifier oSpec Statement OStatement _ _ _).materializeOutput
        t.challenges o t.messages = o := by
    funext i
    rfl
  simp only [OracleVerifier.toVerifier, Verifier.id, OptionT.run]
  rw [hOutput]
  rfl

@[simp]
lemma OracleReduction.id_toReduction :
    (OracleReduction.id : OracleReduction oSpec Statement OStatement Witness _ _ _ _).toReduction =
      Reduction.id := by
  simp [OracleReduction.id, OracleReduction.toReduction, Reduction.id, OracleProver.id]

end Trivial

section Classes

namespace ProtocolSpec

variable {n : ℕ}

/-- A protocol specification with the prover speaking first -/
class ProverFirst (pSpec : ProtocolSpec n) [NeZero n] where
  prover_first' : pSpec.dir 0 = .P_to_V

class VerifierFirst (pSpec : ProtocolSpec n) [NeZero n] where
  verifier_first' : pSpec.dir 0 = .V_to_P

class ProverLast (pSpec : ProtocolSpec n) [inst : NeZero n] where
  prover_last' : pSpec.dir ⟨n - 1, by simp [Nat.pos_of_neZero]⟩ = .P_to_V

/-- A protocol specification with the verifier speaking last -/
class VerifierLast (pSpec : ProtocolSpec n) [NeZero n] where
  verifier_last' : pSpec.dir ⟨n - 1, by simp [Nat.pos_of_neZero]⟩ = .V_to_P

class ProverOnly (pSpec : ProtocolSpec 1) extends ProverFirst pSpec

/-- A non-interactive protocol specification with a single message from the prover to the verifier
-/
alias NonInteractive := ProverOnly

class VerifierOnly (pSpec : ProtocolSpec 1) extends VerifierFirst pSpec

@[simp]
theorem prover_first (pSpec : ProtocolSpec n) [NeZero n] [h : ProverFirst pSpec] :
    pSpec.dir 0 = .P_to_V := h.prover_first'

@[simp]
theorem verifier_first (pSpec : ProtocolSpec n) [NeZero n] [h : VerifierFirst pSpec] :
    pSpec.dir 0 = .V_to_P := h.verifier_first'

@[simp]
theorem prover_last (pSpec : ProtocolSpec n) [NeZero n] [h : ProverLast pSpec] :
    pSpec.dir ⟨n - 1, by simp [Nat.pos_of_neZero]⟩ = .P_to_V := h.prover_last'

@[simp]
theorem verifier_last (pSpec : ProtocolSpec n) [NeZero n] [h : VerifierLast pSpec] :
    pSpec.dir ⟨n - 1, by simp [Nat.pos_of_neZero]⟩ = .V_to_P := h.verifier_last'

section SingleMessage

variable {pSpec : ProtocolSpec 1}

--  For protocols with a single message, first and last are the same
instance [ProverFirst pSpec] : ProverLast pSpec where
  prover_last' := by simp
instance [VerifierFirst pSpec] : VerifierLast pSpec where
  verifier_last' := by simp
instance [h : ProverLast pSpec] : ProverFirst pSpec where
  prover_first' := by simpa using h.prover_last'
instance [h : VerifierFirst pSpec] : VerifierFirst pSpec where
  verifier_first' := by simp

instance [ProverFirst pSpec] : Unique (pSpec.MessageIdx) where
  default := ⟨0, by simp⟩
  uniq := fun ⟨i, _⟩ => by congr; exact Unique.uniq _ i

instance [VerifierFirst pSpec] : Unique (pSpec.ChallengeIdx) where
  default := ⟨0, by simp⟩
  uniq := fun ⟨i, _⟩ => by congr; exact Unique.uniq _ i

instance [h : ProverFirst pSpec] : IsEmpty (pSpec.ChallengeIdx) where
  false | ⟨0, h'⟩ => by have := h.prover_first'; simp_all

instance [h : VerifierFirst pSpec] : IsEmpty (pSpec.MessageIdx) where
  false | ⟨0, h'⟩ => by have := h.verifier_first'; simp_all

instance [ProverFirst pSpec] : ∀ i, VCVCompatible (pSpec.Challenge i) := isEmptyElim
instance [VerifierFirst pSpec] : ∀ i, OracleInterface (pSpec.Message i) := isEmptyElim

instance [ProverFirst pSpec] [h : OracleInterface (pSpec.«Type» 0)] :
    ∀ i, OracleInterface (pSpec.Message i)
  | ⟨0, _⟩ => inferInstance
instance [VerifierFirst pSpec] [h : VCVCompatible (pSpec.«Type» 0)] :
    ∀ i, VCVCompatible (pSpec.Challenge i)
  | ⟨0, _⟩ => inferInstance

end SingleMessage

@[simp]
theorem prover_last_of_two (pSpec : ProtocolSpec 2) [ProverLast pSpec] :
    pSpec.dir 1 = .P_to_V := prover_last pSpec

@[simp]
theorem verifier_last_of_two (pSpec : ProtocolSpec 2) [VerifierLast pSpec] :
    pSpec.dir 1 = .V_to_P := verifier_last pSpec

/-- A protocol specification with a single round of interaction consisting of two messages, with the
  prover speaking first and the verifier speaking last

This notation is currently somewhat ambiguous, given that there are other valid ways of defining a
"single-round" protocol, such as letting the verifier speaks first, letting the prover speaks
multiple times, etc. -/
class IsSingleRound (pSpec : ProtocolSpec 2) extends ProverFirst pSpec, VerifierLast pSpec

alias ProverThenVerifier := IsSingleRound

namespace IsSingleRound

variable {pSpec : ProtocolSpec 2}

/-- The first message is the only message from the prover to the verifier -/
instance [IsSingleRound pSpec] : Unique (pSpec.MessageIdx) where
  default := ⟨0, by simp⟩
  uniq := fun ⟨i, hi⟩ => by
    congr
    contrapose! hi
    have : i = 1 := by omega
    subst this
    simp only [verifier_last_of_two, ne_eq, reduceCtorEq, not_false_eq_true]

/-- The second message is the only challenge from the verifier to the prover -/
instance [IsSingleRound pSpec] : Unique (pSpec.ChallengeIdx) where
  default := ⟨1, by simp⟩
  uniq := fun ⟨i, hi⟩ => by
    congr
    contrapose! hi
    have : i = 0 := by omega
    subst this
    simp only [prover_first, ne_eq, reduceCtorEq, not_false_eq_true]

instance [IsSingleRound pSpec] [h : OracleInterface (pSpec.Message default)] :
    (i : pSpec.MessageIdx) → OracleInterface (pSpec.Message i) := fun i => by
  haveI : i = default := Unique.uniq _ i
  subst this
  exact h

instance [IsSingleRound pSpec] [h : VCVCompatible (pSpec.Challenge default)] :
    (i : pSpec.ChallengeIdx) → VCVCompatible (pSpec.Challenge i) := fun i => by
  haveI : i = default := Unique.uniq _ i
  subst this
  exact h

end IsSingleRound

@[inline, reducible]
def FullTranscript.mk2 {pSpec : ProtocolSpec 2} (msg0 : pSpec.«Type» 0) (msg1 : pSpec.«Type» 1) :
    FullTranscript pSpec := fun | ⟨0, _⟩ => msg0 | ⟨1, _⟩ => msg1

theorem FullTranscript.mk2_eq_snoc_snoc {pSpec : ProtocolSpec 2} (msg0 : pSpec.«Type» 0)
    (msg1 : pSpec.«Type» 1) :
      FullTranscript.mk2 msg0 msg1 = ((default : pSpec.Transcript 0).concat msg0).concat msg1 := by
  funext i
  fin_cases i
  · change msg0 = ((default : pSpec.Transcript 0).concat msg0).concat msg1
      (Fin.castSucc (Fin.last 0))
    rw [Transcript.concat_castSucc]
    exact (Transcript.concat_last msg0 (default : pSpec.Transcript 0)).symm
  · change msg1 = ((default : pSpec.Transcript 0).concat msg0).concat msg1 (Fin.last 1)
    exact (Transcript.concat_last msg1 ((default : pSpec.Transcript 0).concat msg0)).symm

end ProtocolSpec

section IsPure

variable {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}

class Prover.IsPure (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) where
    is_pure : ∃ sendMessage : ∀ _, _ → _, ∀ i st,
      P.sendMessage i st = pure (sendMessage i st)

/-- A prover has **pure output** when its `output` step makes no oracle queries: it is some plain
function of the prover's final state, wrapped in `pure`.

This is deliberately kept separate from `Prover.IsPure`, which constrains `sendMessage` instead.
Sequential composition needs purity of `output` alone, so bundling the two would impose a stronger
hypothesis than the composition theorems require. See `Prover.append_run`, whose statement is
*false* without this assumption: the appended prover runs `P₁.output` from inside the seam round,
after that round's challenge has already been drawn, so an `output` step that queries oracles
issues its queries in a different order than running the two provers separately does. -/
class Prover.OutputIsPure (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) where
    output_is_pure : ∃ output : _ → _, ∀ st, P.output st = pure (output st)

class Verifier.IsPure (V : Verifier oSpec StmtIn StmtOut pSpec) where
    is_pure : ∃ verify : _ → _ → _, ∀ stmtIn transcript,
      V.verify stmtIn transcript = pure (verify stmtIn transcript)

class Reduction.IsPure (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) where
    prover_is_pure : R.prover.IsPure
    verifier_is_pure : R.verifier.IsPure

/-- A **purity witness carrying its verdict function as data**: the bundled form of
  `Verifier.IsPure`, playing the role `Equiv` plays for `Function.Bijective`.

  `IsPure` only asserts that *some* deterministic verdict function exists, so reading that
  function off an `IsPure` instance costs `Classical.choice`. Consumers that need the verdict as
  *data* — sequential composition, which must run the right factor at the statement the left
  verifier outputs at the seam — carry a `PureForm` instead. Purity data
  composes computably (`Verifier.PureForm.append`), and `Verifier.PureForm.isPure` forgets back to
  the class, so the class and all of its instances stay untouched. -/
structure Verifier.PureForm (V : Verifier oSpec StmtIn StmtOut pSpec) where
  /-- The verdict: the statement the verifier outputs on `(stmtIn, transcript)`. -/
  verify : StmtIn → pSpec.FullTranscript → StmtOut
  /-- The verifier computes exactly that verdict. -/
  verify_eq : ∀ stmtIn transcript, V.verify stmtIn transcript = pure (verify stmtIn transcript)

/-- Forget the data: a `Verifier.PureForm` yields the `Verifier.IsPure` class. -/
theorem Verifier.PureForm.isPure {V : Verifier oSpec StmtIn StmtOut pSpec} (P : V.PureForm) :
    V.IsPure :=
  ⟨P.verify, P.verify_eq⟩

end IsPure

end Classes
