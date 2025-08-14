/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.ProtocolSpec.SeqCompose

/-!
# Interactive (Oracle) Reductions

This file defines the basic components of a public-coin **Interactive Oracle Reduction** (IOR).
These are interactive protocols between two parties, a prover and a verifier, with the following
format:

  - The protocol proceeds over a number of steps. In each step, either the prover or the verifier
    sends a message to the other. We assume that this sequence of interactions is fixed in advance,
    and is described by a protocol specification (see `ProtocolSpec.lean`).

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
    `StmtOut`, and specify a _subset_ of the oracles it has received to be the output oracle
    statements.

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
  [OracleInterface : OracleInterface Encoding]

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
  verify : StmtIn → FullTranscript pSpec → OracleComp oSpec StmtOut

/-- An **(oracle) prover** in an interactive **oracle** reduction is a prover in the non-oracle
      reduction whose input statement also consists of the underlying messages for the oracle
      statements -/
@[reducible, inline]
def OracleProver {ι : Type} (oSpec : OracleSpec ι)
    (StmtIn : Type) {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type) (WitIn : Type)
    (StmtOut : Type) {ιₛₒ : Type} (OStmtOut : ιₛₒ → Type) (WitOut : Type)
    {n : ℕ} (pSpec : ProtocolSpec n) :=
  Prover oSpec (StmtIn × (∀ i, OStmtIn i)) WitIn (StmtOut × (∀ i, OStmtOut i)) WitOut pSpec

/-- An **(oracle) verifier** of an interactive **oracle** reduction consists of:

  - an oracle computation `verify` that outputs the next statement. It may make queries to each of
    the prover's messages and each of the oracles present in the statement (according to a specified
    interface defined by `OracleInterface` instances).

  - output oracle statements `OStmtOut : ιₛₒ → Type`, meant to be a **subset** of the input oracle
    statements and the prover's oracle messages. Formally, this is specified by an embedding `ιₛₒ ↪
    ιₛᵢ ⊕ pSpec.MessageIdx` and a proof that `OStmtOut` is compatible with `OStmtIn` and
    `pSpec.Messages` via this embedding.

Intuitively, the oracle verifier cannot do anything more in returning the output oracle statements,
other than specifying a subset of the ones it has received (and dropping the rest). -/
@[ext]
structure OracleVerifier {ι : Type} (oSpec : OracleSpec ι)
    (StmtIn : Type) {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type)
    (StmtOut : Type) {ιₛₒ : Type} (OStmtOut : ιₛₒ → Type)
    {n : ℕ} (pSpec : ProtocolSpec n)
    [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
    [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]
    where
    -- This will be needed after the switch to `simOStmt`
    -- [Oₛₒ : ∀ i, OracleInterface (OStmtOut i)]

  /-- The core verification logic. Takes the input statement `stmtIn` and all verifier challenges
  `challenges` (which are determined outside this function, typically by sampling for
  public-coin protocols). Returns the output statement `StmtOut` within an `OracleComp` that has
  access to external oracles `oSpec`, input statement oracles `OStmtIn`, and prover message
  oracles `pSpec.Message`. -/
  verify : StmtIn → pSpec.Challenges →
    OracleComp (oSpec ++ₒ ([OStmtIn]ₒ ++ₒ [pSpec.Message]ₒ)) StmtOut

  -- TODO: this seems like the right way for compositionality
  -- Makes it potentially more difficult for compilation with commitment schemes
  -- Can recover the old version (with `embed` and `hEq`) via a constructor `QueryImpl.ofEmbed`

  -- simOStmt : QueryImpl [OStmtOut]ₒ (OracleComp ([OStmtIn]ₒ ++ₒ [pSpec.Message]ₒ))

  /-- An embedding that specifies how each output oracle statement (indexed by `ιₛₒ`) is derived.
  It maps an index `i : ιₛₒ` to either an index `j : ιₛᵢ` (meaning `OStmtOut i` comes from
  `OStmtIn j`) or an index `k : pSpec.MessageIdx` (meaning `OStmtOut i` comes from the
  prover's message `pSpec.Message k`). This enforces that output oracles are a subset of
  input oracles or received prover messages. -/
  embed : ιₛₒ ↪ ιₛᵢ ⊕ pSpec.MessageIdx

  /-- A proof term ensuring that the type of each `OStmtOut i` matches the type of the
    corresponding source oracle statement (`OStmtIn j` or `pSpec.Message k`) as determined
    by the `embed` mapping. -/
  hEq : ∀ i, OStmtOut i = match embed i with
    | Sum.inl j => OStmtIn j
    | Sum.inr j => pSpec.Message j

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
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec)

/-- An oracle verifier can be seen as a (non-oracle) verifier by providing the oracle interface
  using its knowledge of the oracle statements and the transcript messages in the clear -/
def toVerifier : Verifier oSpec (StmtIn × ∀ i, OStmtIn i) (StmtOut × (∀ i, OStmtOut i)) pSpec where
  verify := fun ⟨stmt, oStmt⟩ transcript => do
    let stmtOut ← simulateQ (OracleInterface.simOracle2 oSpec oStmt transcript.messages)
      (verifier.verify stmt transcript.challenges)
    letI oStmtOut := fun i => match h : verifier.embed i with
      | Sum.inl j => by simpa only [verifier.hEq, h] using (oStmt j)
      | Sum.inr j => by simpa only [verifier.hEq, h] using (transcript j)
    return (stmtOut, oStmtOut)

/-- The number of queries made to the oracle statements and the prover's messages, for a given input
    statement and challenges.

  This is given as an oracle computation itself, since the oracle verifier may be adaptive and has
  different number of queries depending on the prior responses.

  TODO: define once `numQueries` is defined in `OracleComp` -/
def numQueries (stmt : StmtIn) (challenges : ∀ i, pSpec.Challenge i)
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec) :
  OracleComp (oSpec ++ₒ ([OStmtIn]ₒ ++ₒ [pSpec.Message]ₒ)) ℕ := sorry

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
    where

  /-- Makes a list of queries to each of the oracle statements, given the input statement and the
    challenges -/
  queryOStmt : StmtIn → (∀ i, pSpec.Challenge i) → List ((i : ιₛᵢ) × (Oₛᵢ i).Query)

  /-- Makes a list of queries to each of the prover's messages, given the input statement and the
    challenges -/
  queryMsg : StmtIn → (∀ i, pSpec.Challenge i) → List ((i : pSpec.MessageIdx) × (Oₘ i).Query)

  /-- From the query-response pairs, returns a computation that outputs the new output statement -/
  verify : StmtIn → (∀ i, pSpec.Challenge i) →
    List ((i : ιₛᵢ) × ((Oₛᵢ i).Query × (Oₛᵢ i).Response)) →
    List ((i : pSpec.MessageIdx) × ((Oₘ i).Query × (Oₘ i).Response)) → OracleComp oSpec StmtOut

  embed : ιₛₒ ↪ ιₛᵢ ⊕ pSpec.MessageIdx

  hEq : ∀ i, OStmtOut i = match embed i with
    | Sum.inl j => OStmtIn j
    | Sum.inr j => pSpec.Message j

namespace NonAdaptive

/-- Converts a non-adaptive oracle verifier into the general oracle verifier interface.

This essentially performs the queries via `List.mapM`, then runs `verify` on the query-response
pairs. -/
def toOracleVerifier
    (naVerifier : OracleVerifier.NonAdaptive oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec) :
    OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec where
  verify := fun stmt challenges => do
    let queryResponsesOStmt : List ((i : ιₛᵢ) × ((Oₛᵢ i).Query × (Oₛᵢ i).Response)) ←
      (naVerifier.queryOStmt stmt challenges).mapM
      (fun q => do
        let resp ← liftM <| query (spec := [OStmtIn]ₒ) q.1 q.2
        return ⟨q.1, (q.2, by simpa only using resp)⟩)
    let queryResponsesOMsg : List ((i : pSpec.MessageIdx) × ((Oₘ i).Query × (Oₘ i).Response)) ←
      (naVerifier.queryMsg stmt challenges).mapM
      (fun q => do
        let resp ← liftM <| query (spec := [pSpec.Message]ₒ) q.1 q.2
        return ⟨q.1, ⟨q.2, by simpa only using resp⟩⟩)
    let stmtOut ← liftM <| naVerifier.verify stmt challenges queryResponsesOStmt queryResponsesOMsg
    return stmtOut

  embed := naVerifier.embed

  hEq := naVerifier.hEq

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
  OracleReduction oSpec Statement OStatement Witness Bool (fun _ : Empty => Unit) Unit pSpec

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
  embed := Function.Embedding.inl
  hEq := fun _ => rfl

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
  simp [OracleVerifier.id, OracleVerifier.toVerifier, Verifier.id]

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
  unfold FullTranscript.mk2 Transcript.concat
  simp only [default, Fin.isValue]
  funext i
  by_cases hi : i = 0
  · subst hi; simp [Fin.snoc]
  · have : i = 1 := by omega
    subst this; simp [Fin.snoc]

end ProtocolSpec

section IsPure

variable {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}

class Prover.IsPure (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) where
    is_pure : ∃ sendMessage : ∀ _, _ → _, ∀ i st,
      P.sendMessage i st = pure (sendMessage i st)

class Verifier.IsPure (V : Verifier oSpec StmtIn StmtOut pSpec) where
    is_pure : ∃ verify : _ → _ → _, ∀ stmtIn transcript,
      V.verify stmtIn transcript = pure (verify stmtIn transcript)

class Reduction.IsPure (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) where
    prover_is_pure : R.prover.IsPure
    verifier_is_pure : R.verifier.IsPure

end IsPure

end Classes
