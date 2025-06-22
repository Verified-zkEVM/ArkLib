/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.ProtocolSpec

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

-/

open OracleComp OracleSpec SubSpec ProtocolSpec

variable {n : ℕ}

-- Add an indexer?
structure Indexer (pSpec : ProtocolSpec n) {ι : Type} (oSpec : OracleSpec ι) (Index : Type)
    (Encoding : Type) where
  encode : Index → OracleComp oSpec Encoding
  [OracleInterface : OracleInterface Encoding]

/-- The type signature for the prover's state at each round.

For a protocol with `n` messages exchanged, there will be `(n + 1)` prover states, with the first
state before the first message and the last state after the last message. -/
@[ext]
structure ProverState (n : ℕ) where
  PrvState : Fin (n + 1) → Type

/-- Initialization of prover's state via inputting the statement and witness. -/
@[ext]
structure ProverIn (StmtIn WitIn PrvState : Type) where
  input : StmtIn → WitIn → PrvState
  -- initState : PrvState
  -- if honest prover, then expect that PrvState 0 = WitIn

/-- Represents the interaction of a prover for a given protocol specification.

In each step, the prover gets access to the current state, then depending on the direction of the
step, the prover either sends a message or receives a challenge, and updates its state accordingly.

For maximum simplicity, we only define the `sendMessage` function as an oracle computation. All
other functions are pure. We may revisit this decision in the future.
-/
@[ext]
structure ProverRound (pSpec : ProtocolSpec n) {ι : Type} (oSpec : OracleSpec ι)
    extends ProverState n where
  /-- Send a message and update the prover's state -/
  sendMessage (i : MessageIdx pSpec) :
    PrvState i.1.castSucc → OracleComp oSpec (pSpec.Message i × PrvState i.1.succ)
  /-- Receive a challenge and update the prover's state -/
  receiveChallenge (i : ChallengeIdx pSpec) :
    PrvState i.1.castSucc → (pSpec.Challenge i) → PrvState i.1.succ

/-- The output of the prover, which is a function from the prover's state to the output witness -/
@[ext]
structure ProverOut (StmtOut WitOut PrvState : Type) where
  output : PrvState → StmtOut × WitOut

/-- A prover for an interactive protocol with `n` messages consists of a sequence of internal states
    and a tuple of four functions:
  - `PrvState 0`, ..., `PrvState n` are the types for the prover's state at each round
  - `input` initializes the prover's state by taking in the input statement and witness
  - `receiveChallenge` updates the prover's state given a challenge
  - `sendMessage` sends a message and updates the prover's state
  - `output` returns the output statement and witness from the prover's state

Note that the output statement by the prover is present only to facilitate composing two provers
together. For completeness, we will require that the prover's output statement is always equal to
the verifier's output statement. For soundness, we will only use the output statement generated by
the verifier. -/
@[ext]
structure Prover (pSpec : ProtocolSpec n) {ι : Type} (oSpec : OracleSpec ι)
    (StmtIn WitIn StmtOut WitOut : Type) extends
      ProverState n,
      ProverIn StmtIn WitIn (PrvState 0),
      ProverRound pSpec oSpec,
      ProverOut StmtOut WitOut (PrvState (Fin.last n))

/-- A verifier of an interactive protocol is a function that takes in the input statement and the
  transcript, and performs an oracle computation that outputs a new statement -/
@[ext]
structure Verifier (pSpec : ProtocolSpec n) {ι : Type} (oSpec : OracleSpec ι)
    (StmtIn StmtOut : Type) where
  verify : StmtIn → FullTranscript pSpec → OracleComp oSpec StmtOut

/-- An **(oracle) prover** in an interactive **oracle** reduction is a prover in the non-oracle
      reduction whose input statement also consists of the underlying messages for the oracle
      statements -/
@[reducible, inline]
def OracleProver (pSpec : ProtocolSpec n) {ι : Type} (oSpec : OracleSpec ι)
    (StmtIn WitIn StmtOut WitOut : Type)
    {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type) {ιₛₒ : Type} (OStmtOut : ιₛₒ → Type) :=
  Prover pSpec oSpec (StmtIn × (∀ i, OStmtIn i)) WitIn (StmtOut × (∀ i, OStmtOut i)) WitOut

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
structure OracleVerifier (pSpec : ProtocolSpec n) {ι : Type} (oSpec : OracleSpec ι)
    [Oₘ : ∀ i, OracleInterface (pSpec.Message i)] (StmtIn StmtOut : Type)
    {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type) [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
    {ιₛₒ : Type} (OStmtOut : ιₛₒ → Type) where
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

variable {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
    [Oₘ : ∀ i, OracleInterface (pSpec.Message i)] {StmtIn StmtOut : Type}
    {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
    {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type}
    (verifier : OracleVerifier pSpec oSpec StmtIn StmtOut OStmtIn OStmtOut)

/-- An oracle verifier can be seen as a (non-oracle) verifier by providing the oracle interface
  using its knowledge of the oracle statements and the transcript messages in the clear -/
def toVerifier : Verifier pSpec oSpec (StmtIn × ∀ i, OStmtIn i) (StmtOut × (∀ i, OStmtOut i)) where
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
    (verifier : OracleVerifier pSpec oSpec StmtIn StmtOut OStmtIn OStmtOut) :
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
structure NonAdaptive (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι)
    [Oₘ : ∀ i, OracleInterface (pSpec.Message i)] (StmtIn StmtOut : Type)
    {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type) [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
    {ιₛₒ : Type} (OStmtOut : ιₛₒ → Type) where

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
    (naVerifier : OracleVerifier.NonAdaptive pSpec oSpec StmtIn StmtOut OStmtIn OStmtOut) :
    OracleVerifier pSpec oSpec StmtIn StmtOut OStmtIn OStmtOut where
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
    (naVerifier : OracleVerifier.NonAdaptive pSpec oSpec StmtIn StmtOut OStmtIn OStmtOut) : ℕ :=
  (naVerifier.queryOStmt stmt challenges).filter (fun q => q.1 = i) |>.length

/-- The number of queries made to the `i`-th prover's message, for a given input statement and
    challenges. -/
def numOMsgQueries (i : pSpec.MessageIdx)
    (stmt : StmtIn) (challenges : ∀ i, pSpec.Challenge i)
    (naVerifier : OracleVerifier.NonAdaptive pSpec oSpec StmtIn StmtOut OStmtIn OStmtOut) : ℕ :=
  (naVerifier.queryMsg stmt challenges).filter (fun q => q.1 = i) |>.length

/-- The total number of queries made to the oracle statements and the prover's messages, for a
    given input statement and challenges. -/
def totalNumQueries (stmt : StmtIn) (challenges : ∀ i, pSpec.Challenge i)
    (naVerifier : OracleVerifier.NonAdaptive pSpec oSpec StmtIn StmtOut OStmtIn OStmtOut) : ℕ :=
  (naVerifier.queryOStmt stmt challenges).length + (naVerifier.queryMsg stmt challenges).length

end NonAdaptive

end OracleVerifier

/-- An **interactive reduction** for a given protocol specification `pSpec`, and relative to oracles
  defined by `oSpec`, consists of a prover and a verifier. -/
@[ext]
structure Reduction (pSpec : ProtocolSpec n) {ι : Type} (oSpec : OracleSpec ι)
    (StmtIn WitIn StmtOut WitOut : Type) where
  prover : Prover pSpec oSpec StmtIn WitIn StmtOut WitOut
  verifier : Verifier pSpec oSpec StmtIn StmtOut

/-- An **interactive oracle reduction** for a given protocol specification `pSpec`, and relative to
  oracles defined by `oSpec`, consists of a prover and an **oracle** verifier. -/
@[ext]
structure OracleReduction (pSpec : ProtocolSpec n) [∀ i, OracleInterface (pSpec.Message i)]
    {ι : Type} (oSpec : OracleSpec ι) (StmtIn WitIn StmtOut WitOut : Type)
    {ιₛ : Type} (OStmtIn : ιₛ → Type) [Oₛ : ∀ i, OracleInterface (OStmtIn i)]
    {ιₛₒ : Type} (OStmtOut : ιₛₒ → Type) where
  prover : OracleProver pSpec oSpec StmtIn WitIn StmtOut WitOut OStmtIn OStmtOut
  verifier : OracleVerifier pSpec oSpec StmtIn StmtOut OStmtIn OStmtOut

/-- An interactive oracle reduction can be seen as an interactive reduction, via coercing the
  oracle verifier to a (normal) verifier -/
def OracleReduction.toReduction {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn WitIn StmtOut WitOut : Type} [∀ i, OracleInterface (pSpec.Message i)]
    {ιₛ : Type} {OStmtIn : ιₛ → Type} [Oₛ : ∀ i, OracleInterface (OStmtIn i)]
    {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type}
    (oracleReduction : OracleReduction pSpec oSpec StmtIn WitIn StmtOut WitOut OStmtIn OStmtOut) :
      Reduction pSpec oSpec (StmtIn × (∀ i, OStmtIn i)) WitIn
        (StmtOut × (∀ i, OStmtOut i)) WitOut :=
  ⟨oracleReduction.prover, oracleReduction.verifier.toVerifier⟩

/-- An **interactive proof (IP)** is an interactive reduction where the output statement is a
    boolean, the output witness is trivial (a `Unit`), and the relation checks whether the output
    statement is true. -/
abbrev Proof (pSpec : ProtocolSpec n) {ι : Type} (oSpec : OracleSpec ι)
    (Statement Witness : Type) :=
  Reduction pSpec oSpec Statement Witness Bool Unit

/-- An **interactive oracle proof (IOP)** is an interactive oracle reduction where the output
    statement is a boolean, while both the output oracle statement & the output witness are
    trivial (`Unit` type).

    As a consequence, the output relation in an IOP is effectively a function `Bool → Prop`, which
    we can again assume to be the trivial one (sending `true` to `True`). -/
abbrev OracleProof (pSpec : ProtocolSpec n) {ι : Type} (oSpec : OracleSpec ι)
    [Oₘ : ∀ i, OracleInterface (pSpec.Message i)] (Statement Witness : Type)
    {ιₛ : Type} (OStatement : ιₛ → Type) [Oₛ : ∀ i, OracleInterface (OStatement i)] :=
  OracleReduction pSpec oSpec Statement Witness Bool Unit OStatement (fun _ : Empty => Unit)

/-- A **non-interactive prover** is a prover that only sends a single message to the verifier. -/
abbrev NonInteractiveProver (Message : Type) {ι : Type} (oSpec : OracleSpec ι)
    (StmtIn WitIn StmtOut WitOut : Type) :=
  Prover ![(.P_to_V, Message)] oSpec StmtIn WitIn StmtOut WitOut

/-- A **non-interactive verifier** is a verifier that only receives a single message from the
  prover. -/
abbrev NonInteractiveVerifier (Message : Type) {ι : Type} (oSpec : OracleSpec ι)
    (StmtIn StmtOut : Type) :=
  Verifier ![(.P_to_V, Message)] oSpec StmtIn StmtOut

/-- A **non-interactive reduction** is an interactive reduction with only a single message from the
  prover to the verifier (and none in the other direction). -/
abbrev NonInteractiveReduction (Message : Type) {ι : Type} (oSpec : OracleSpec ι)
    (StmtIn WitIn StmtOut WitOut : Type) :=
  Reduction ![(.P_to_V, Message)] oSpec StmtIn WitIn StmtOut WitOut

section Classes

namespace ProtocolSpec

variable {n : ℕ}

/-- A protocol specification with the prover speaking first -/
class ProverFirst (pSpec : ProtocolSpec n) [NeZero n] where
  prover_first' : (pSpec 0).1 = .P_to_V

class VerifierFirst (pSpec : ProtocolSpec n) [NeZero n] where
  verifier_first' : (pSpec 0).1 = .V_to_P

class ProverLast (pSpec : ProtocolSpec n) [NeZero n] where
  prover_last' : (pSpec (n - 1)).1 = .P_to_V

/-- A protocol specification with the verifier speaking last -/
class VerifierLast (pSpec : ProtocolSpec n) [NeZero n] where
  verifier_last' : (pSpec (n - 1)).1 = .V_to_P

class ProverOnly (pSpec : ProtocolSpec 1) extends ProverFirst pSpec

/-- A non-interactive protocol specification with a single message from the prover to the verifier-/
alias NonInteractive := ProverOnly

class VerifierOnly (pSpec : ProtocolSpec 1) extends VerifierFirst pSpec

@[simp]
theorem prover_first (pSpec : ProtocolSpec n) [NeZero n] [h : ProverFirst pSpec] :
    (pSpec 0).1 = .P_to_V := h.prover_first'

@[simp]
theorem verifier_first (pSpec : ProtocolSpec n) [NeZero n] [h : VerifierFirst pSpec] :
    (pSpec 0).1 = .V_to_P := h.verifier_first'

@[simp]
theorem prover_last (pSpec : ProtocolSpec n) [NeZero n] [h : ProverLast pSpec] :
    (pSpec (n - 1)).1 = .P_to_V := h.prover_last'

@[simp]
theorem verifier_last (pSpec : ProtocolSpec n) [NeZero n] [h : VerifierLast pSpec] :
    (pSpec (n - 1)).1 = .V_to_P := h.verifier_last'

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

instance [ProverFirst pSpec] [h : OracleInterface (pSpec 0).2] :
    ∀ i, OracleInterface (pSpec.Message i)
  | ⟨0, _⟩ => inferInstance
instance [VerifierFirst pSpec] [h : VCVCompatible (pSpec 0).2] :
    ∀ i, VCVCompatible (pSpec.Challenge i)
  | ⟨0, _⟩ => inferInstance

end SingleMessage

@[simp]
theorem prover_last_of_two (pSpec : ProtocolSpec 2) [ProverLast pSpec] :
    pSpec.getDir 1 = .P_to_V := prover_last pSpec

@[simp]
theorem verifier_last_of_two (pSpec : ProtocolSpec 2) [VerifierLast pSpec] :
    pSpec.getDir 1 = .V_to_P := verifier_last pSpec

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
def FullTranscript.mk2 {pSpec : ProtocolSpec 2} (msg0 : pSpec.getType 0) (msg1 : pSpec.getType 1) :
    FullTranscript pSpec := fun | ⟨0, _⟩ => msg0 | ⟨1, _⟩ => msg1

theorem FullTranscript.mk2_eq_snoc_snoc {pSpec : ProtocolSpec 2} (msg0 : pSpec.getType 0)
    (msg1 : pSpec.getType 1) :
      FullTranscript.mk2 msg0 msg1 = ((default : pSpec.Transcript 0).concat msg0).concat msg1 := by
  unfold FullTranscript.mk2 Transcript.concat
  simp only [default, Nat.mod_succ, Nat.lt_one_iff,
    not_lt_zero', ↓reduceDIte, Fin.zero_eta, Fin.isValue, Nat.reduceMod, Nat.succ_eq_add_one,
    Nat.reduceAdd, Fin.mk_one]
  funext i
  by_cases hi : i = 0
  · subst hi; simp [Fin.snoc]
  · have : i = 1 := by omega
    subst this; simp [Fin.snoc]

end ProtocolSpec

section IsPure

variable {n : ℕ} {ι : Type} {pSpec : ProtocolSpec n} {oSpec : OracleSpec ι}
    {StmtIn WitIn StmtOut WitOut : Type}

class Prover.IsPure (P : Prover pSpec oSpec StmtIn WitIn StmtOut WitOut) where
    is_pure : ∃ sendMessage : ∀ _, _ → _, ∀ i st,
      P.sendMessage i st = pure (sendMessage i st)

class Verifier.IsPure (V : Verifier pSpec oSpec StmtIn StmtOut) where
    is_pure : ∃ verify : _ → _ → _, ∀ stmtIn transcript,
      V.verify stmtIn transcript = pure (verify stmtIn transcript)

class Reduction.IsPure (R : Reduction pSpec oSpec StmtIn WitIn StmtOut WitOut) where
    prover_is_pure : R.prover.IsPure
    verifier_is_pure : R.verifier.IsPure

end IsPure

end Classes
