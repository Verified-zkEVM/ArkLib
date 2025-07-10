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

/-- The type signature for the prover's state at each step.

For a protocol with `n` messages exchanged, there will be `(n + 1)` prover states, with the first
state before the first message and the last state after the last message. -/
@[ext]
structure ProverState (n : ℕ) where
  /-- The prover's state at each step (before first message and after last message) -/
  PrvState : Fin (n + 1) → Type

/-- Initialization of prover's state via inputting the statement and witness. -/
@[ext]
structure ProverIn (StmtIn WitIn PrvState : Type) where
  /-- Initialize the prover's state via taking in the input statement and witness -/
  input : StmtIn × WitIn → PrvState
  -- initState : PrvState
  -- if honest prover, then expect that PrvState 0 = WitIn

/-- Represents the interaction of a prover for a given protocol specification.

In each step, the prover gets access to the current state, then depending on the direction of the
step, the prover either sends a message or receives a challenge, and updates its state accordingly.

For maximum simplicity, we only define the `sendMessage` function as an oracle computation. All
other functions are pure. We may revisit this decision in the future.
-/
@[ext]
structure ProverRound {ι : Type} (oSpec : OracleSpec ι) {n : ℕ} (pSpec : ProtocolSpec n)
    extends ProverState n where
  /-- Send a message (when the round is a message round) and update the prover's state -/
  sendMessage (i : MessageIdx pSpec) :
    PrvState i.1.castSucc → OracleComp oSpec (pSpec.Message i × PrvState i.1.succ)
  /-- Receive a challenge (when the round is a challenge round) and update the prover's state -/
  receiveChallenge (i : ChallengeIdx pSpec) :
    PrvState i.1.castSucc → (pSpec.Challenge i) → PrvState i.1.succ

/-- The output of the prover, which is a function from the prover's state to the output witness -/
@[ext]
structure ProverOut (StmtOut WitOut PrvState : Type) where
  /-- Output the output statement and witness from the (final) prover's state -/
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
structure Prover {ι : Type} (oSpec : OracleSpec ι)
    (StmtIn WitIn StmtOut WitOut : Type)
    {n : ℕ} (pSpec : ProtocolSpec n) extends
      ProverState n,
      ProverIn StmtIn WitIn (PrvState 0),
      ProverRound oSpec pSpec,
      ProverOut StmtOut WitOut (PrvState (Fin.last n))

/-- A verifier of an interactive protocol is a function that takes in the input statement and the
  transcript, and performs an oracle computation that outputs a new statement -/
@[ext]
structure Verifier {ι : Type} (oSpec : OracleSpec ι)
    (StmtIn StmtOut : Type) {n : ℕ} (pSpec : ProtocolSpec n) where
  /-- Verify the output statement, in terms of the input statement and the transcript, and having
    access to the shared oracle. -/
  verify : StmtIn → FullTranscript pSpec → OracleComp oSpec StmtOut

namespace Verifier

alias reduce := verify

end Verifier

/-- An **(oracle) prover** in an interactive **oracle** reduction is a prover in the non-oracle
      reduction whose input statement also consists of the underlying messages for the oracle
      statements -/
@[reducible, inline]
def OracleProver {ι : Type} (oSpec : OracleSpec ι)
    (StmtIn : Type) {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type) (WitIn : Type)
    (StmtOut : Type) {ιₛₒ : Type} (OStmtOut : ιₛₒ → Type) (WitOut : Type)
    {n : ℕ} (pSpec : ProtocolSpec n) :=
  Prover oSpec (StmtIn × (∀ i, OStmtIn i)) WitIn (StmtOut × (∀ i, OStmtOut i)) WitOut pSpec

namespace OracleVerifier

variable {ι : Type} (oSpec : OracleSpec ι)
    (StmtIn : Type) {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type) [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
    (StmtOut : Type) {ιₛₒ : Type} (OStmtOut : ιₛₒ → Type) [Oₛₒ : ∀ i, OracleInterface (OStmtOut i)]
    {n : ℕ} (pSpec : ProtocolSpec n) [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]

/-- The computation of the output statement from the input statement and the challenges, given
  access to the shared oracle, the input oracle statements, and the prover's messages. -/
@[ext] structure Verify where
  /-- Verify the output statement, in terms of the input statement, the challenges, and having
    access to the shared oracle, the input oracle statements, and the prover's messages. -/
  verify : StmtIn → pSpec.Challenges →
    OracleComp (oSpec ++ₒ ([OStmtIn]ₒ ++ₒ [pSpec.Message]ₒ)) StmtOut

alias Verify.reduce := Verify.verify

/-- The simulation of the (oracles corresponding to the) output oracle statements, in terms of the
    shared oracle, the input oracle statements, and the prover's messages (as oracles). May depend
    on the challenges.
-/
@[ext] structure Simulate where
  /-- Simulate the output oracle statements, in terms of the shared oracle, the input oracle
    statements, and the prover's messages (as oracles), and depends on the challenges.

  NOTE: we do not make this depend on the input statement (yet). This is because if we do, then for
  sequential composition, we need to wrap `QueryImpl` inside an `OracleComp` (i.e. to derive the
  second simulation, we need the second statement, which is only available inside the monad).
  Unfortunately, `QueryImpl` currently raises universe levels (i.e. it contains `OracleComp`), so we
  cannot do this. May revisit this in the future. -/
  simulate : pSpec.Challenges →
    QueryImpl [OStmtOut]ₒ (OracleComp (oSpec ++ₒ ([OStmtIn]ₒ ++ₒ [pSpec.Message]ₒ)))

/-- An oracle verifier that only supports simulation, without an associated reification.

This is sufficient for all downstream definitions, but at the expense of more verbosity due to not
taking advantage of the reification.

Since all known IORs have reifiable oracle verifiers, we have that as the default. -/
@[ext] structure SimulateOnly extends
  Verify oSpec StmtIn OStmtIn StmtOut pSpec,
  Simulate oSpec OStmtIn OStmtOut pSpec

/-- The computation of the (actual) output oracle statements from the input statement, input oracle
  statements, the transcript, and with access to the shared oracle. -/
@[ext] structure Reify where
  /-- Reify the output oracle statements, in terms of the input statement, input oracle statements,
    the transcript, and with access to the shared oracle. -/
  reify : StmtIn × (∀ i, OStmtIn i) → pSpec.FullTranscript → OracleComp oSpec (∀ i, OStmtOut i)

/-- A reification is lawful if the computation of the output oracle statements is compatible with
    the simulation of the (oracles corresponding to the) output oracle statements. -/
@[ext] class LawfulReify (S : Simulate oSpec OStmtIn OStmtOut pSpec)
    (R : Reify oSpec StmtIn OStmtIn OStmtOut pSpec) where
  /-- The reification and simulation are compatible, in the sense that the following two processes
    are equal:
    1. First derive the output oracle statements via reification, then use that to answer queries to
       the oracles.
    2. Answer queries to the oracles by first lifting it (via simulation) to a computation querying
       the shared oracle, the input oracle statement, and the prover's messages, then use the
       provided data for the latter two to reduce it to just an oracle computation. -/
  reify_simulate : ∀ stmtIn oStmtIn transcript i q,
    (do return (Oₛₒ i).oracle ((← R.reify ⟨stmtIn, oStmtIn⟩ transcript) i) q) =
    simulateQ (OracleInterface.simOracle2 oSpec oStmtIn transcript.messages)
      (simulateQ (S.simulate transcript.challenges)
        (query (spec := [OStmtOut]ₒ) i q))

end OracleVerifier

/-- An **(oracle) verifier** of an interactive **oracle** reduction, which consists of the following
  components:

1. `verify`: the main verification logic, derives the output statement from the input statement, the
   challenges, and with access to the shared oracle, the oracle statements, and the prover's
   messages

2. `simulate`: a specification of how to answer queries to the output oracle statements, again
   allowed to make (adaptive) queries to both the input oracle statements and the prover's messages

3. `reify`: a function that derives the output oracle statements from the input statement
   (non-oracle & oracle), the entire transcript, and with access to the shared oracle (essentially
   same interface as the prover)

4. `reify_simulate`: a compatibility condition that ensures that the reification and simulation are
   compatible (see `OracleVerifier.LawfulReify` for the precise theorem statement).
-/
@[ext] structure OracleVerifier {ι : Type} (oSpec : OracleSpec ι)
    (StmtIn : Type) {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type) [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
    (StmtOut : Type) {ιₛₒ : Type} (OStmtOut : ιₛₒ → Type) [Oₛₒ : ∀ i, OracleInterface (OStmtOut i)]
    {n : ℕ} (pSpec : ProtocolSpec n) [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]
  extends
    OracleVerifier.SimulateOnly oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec,
    OracleVerifier.Reify oSpec StmtIn OStmtIn OStmtOut pSpec,
    OracleVerifier.LawfulReify oSpec StmtIn OStmtIn OStmtOut pSpec toSimulate toReify

namespace OracleVerifier

variable {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
    {StmtOut : Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} [Oₛₒ : ∀ i, OracleInterface (OStmtOut i)]
    {n : ℕ} {pSpec : ProtocolSpec n} [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]
    (V : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec)

/-- Convert an oracle verifier to a non-oracle verifier (for the associated reduction where all
    messages are sent in the clear).

  This is done by using the underlying data for the input oracle statement & the prover's messages
  to derive both the output statement (via `verify`) and the output oracle statements (via `reify`).
-/
def toVerifier : Verifier oSpec (StmtIn × ∀ i, OStmtIn i) (StmtOut × (∀ i, OStmtOut i)) pSpec where
  verify := fun ⟨stmt, oStmt⟩ transcript => do
    -- First compute the output statement using `verify` / `reduce`
    let stmtOut ← simulateQ (OracleInterface.simOracle2 oSpec oStmt transcript.messages)
      (V.verify stmt transcript.challenges)
    -- Then compute the output oracle statements using the reification
    let oStmtOut ← V.reify ⟨stmt, oStmt⟩ transcript
    return (stmtOut, oStmtOut)

/-- The number of queries made to the oracle statements and the prover's messages, for a given input
    statement and challenges.

  This is given as an oracle computation itself, since the oracle verifier may be adaptive and has
  different number of queries depending on the prior responses.

  TODO: define once `numQueries` is defined in `OracleComp` -/
def numQueries (stmt : StmtIn) (challenges : ∀ i, pSpec.Challenge i)
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec) :
  OracleComp (oSpec ++ₒ ([OStmtIn]ₒ ++ₒ [pSpec.Message]ₒ)) ℕ := sorry

/-- Construct an oracle verifier whose output oracle statements are a subset of the input oracle
  statements and the prover's messages (without any fancy simulation semantics).

  This is the case for most IORs under consideration. -/
def ofEmbed
    (verify : StmtIn → pSpec.Challenges →
      OracleComp (oSpec ++ₒ ([OStmtIn]ₒ ++ₒ [pSpec.Message]ₒ)) StmtOut)
    (embed : ιₛₒ ↪ ιₛᵢ ⊕ pSpec.MessageIdx)
    (hData : ∀ i, OStmtOut i = match embed i with
      | Sum.inl j => OStmtIn j
      | Sum.inr j => pSpec.Message j)
    (hInterface : ∀ i, Oₛₒ i = match h : embed i with
      | Sum.inl j => by simpa [hData, h] using Oₛᵢ j
      | Sum.inr j => by simpa [hData, h] using Oₘ j) :
  OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec where
  verify := verify
  simulate := fun _ => {
    impl | query i q => match h : embed i with
      | Sum.inl j => sorry
    -- liftM <| query (spec := [OStmtIn]ₒ) j
    --     (by
    --       have h1 := hData i
    --       have h2 := hInterface i
    --       rw! [h] at h2
    --       simp [h] at h1 h2
    --       -- rw [← cast_symm] at h2
    --       simp [OracleInterface.toOracleSpec, OracleSpec.domain] at q ⊢
    --       let q' := h2 ▸ q
    --       sorry
    --       )
      | Sum.inr j => sorry
  }
  reify := fun ⟨stmt, oStmt⟩ transcript => do
    let oStmtOut := fun i => match h : embed i with
      | Sum.inl j => by simpa [hData, h] using oStmt j
      | Sum.inr j => by simpa [hData, h] using transcript.messages j
    return oStmtOut
  reify_simulate := sorry

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

  We keep the same simulate and reification components, only changing the `verify` component to
  only make non-adaptive queries to the oracle statements and the prover's messages.
-/
structure NonAdaptive {ι : Type} (oSpec : OracleSpec ι)
    (StmtIn : Type) {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type) [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
    (StmtOut : Type) {ιₛₒ : Type} (OStmtOut : ιₛₒ → Type) [Oₛₒ : ∀ i, OracleInterface (OStmtOut i)]
    {n : ℕ} (pSpec : ProtocolSpec n) [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]
    extends
    OracleVerifier.Simulate oSpec OStmtIn OStmtOut pSpec,
    OracleVerifier.Reify oSpec StmtIn OStmtIn OStmtOut pSpec,
    OracleVerifier.LawfulReify oSpec StmtIn OStmtIn OStmtOut pSpec toSimulate toReify
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

namespace NonAdaptive

/-- Converts a non-adaptive oracle verifier into the general oracle verifier interface.

This essentially performs the queries via `List.mapM`, then runs `verify` on the query-response
pairs. -/
def toOracleVerifier
    (nonAdaptiveV : OracleVerifier.NonAdaptive oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec) :
    OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec where
  verify := fun stmt challenges => do
    let queryResponsesOStmt : List ((i : ιₛᵢ) × ((Oₛᵢ i).Query × (Oₛᵢ i).Response)) ←
      (nonAdaptiveV.queryOStmt stmt challenges).mapM
      (fun q => do
        let resp ← liftM <| query (spec := [OStmtIn]ₒ) q.1 q.2
        return ⟨q.1, (q.2, by simpa only using resp)⟩)
    let queryResponsesOMsg : List ((i : pSpec.MessageIdx) × ((Oₘ i).Query × (Oₘ i).Response)) ←
      (nonAdaptiveV.queryMsg stmt challenges).mapM
      (fun q => do
        let resp ← liftM <| query (spec := [pSpec.Message]ₒ) q.1 q.2
        return ⟨q.1, ⟨q.2, by simpa only using resp⟩⟩)
    let stmtOut ← liftM <|
      nonAdaptiveV.verify stmt challenges queryResponsesOStmt queryResponsesOMsg
    return stmtOut
  simulate := nonAdaptiveV.simulate
  reify := nonAdaptiveV.reify
  reify_simulate := nonAdaptiveV.reify_simulate

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
    (StmtIn : Type) {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type) [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
    (WitIn : Type)
    (StmtOut : Type) {ιₛₒ : Type} (OStmtOut : ιₛₒ → Type) [Oₛₒ : ∀ i, OracleInterface (OStmtOut i)]
    (WitOut : Type)
    {n : ℕ} (pSpec : ProtocolSpec n) [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]
    where
  prover : OracleProver oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec
  verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec

/-- An interactive oracle reduction can be seen as an interactive reduction, via coercing the
  oracle verifier to a (normal) verifier -/
def OracleReduction.toReduction {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
    {WitIn : Type}
    {StmtOut : Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} [Oₛₒ : ∀ i, OracleInterface (OStmtOut i)]
    {WitOut : Type}
    {n : ℕ} {pSpec : ProtocolSpec n} [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]
    (oracleReduction : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec) :
      Reduction oSpec (StmtIn × (∀ i, OStmtIn i)) WitIn
        (StmtOut × (∀ i, OStmtOut i)) WitOut pSpec :=
  ⟨oracleReduction.prover, oracleReduction.verifier.toVerifier⟩

/-- Since `TrivialOracleStatement` is `Empty`-indexed, it has an (indexed family of)
  `OracleInterface` instance via empty elimination. -/
instance : ∀ i, OracleInterface (TrivialOracleStatement i) := isEmptyElim

/-- An **interactive proof (IP)** is an interactive reduction where the output statement is a
    boolean, the output witness is trivial (a `Unit`), and the relation checks whether the output
    statement is true. -/
@[reducible] def Proof {ι : Type} (oSpec : OracleSpec ι)
    (Statement Witness : Type) {n : ℕ} (pSpec : ProtocolSpec n) :=
  Reduction oSpec Statement Witness TrivialStatement TrivialWitness pSpec

/-- An **interactive oracle proof (IOP)** is an interactive oracle reduction where the output
    statement is a boolean, while both the output oracle statement & the output witness are
    trivial (`Unit` type).

    As a consequence, the output relation in an IOP is effectively a function `Bool → Prop`, which
    we can again assume to be the trivial one (sending `true` to `True`). -/
@[reducible] def OracleProof {ι : Type} (oSpec : OracleSpec ι)
    (Statement : Type) {ιₛ : Type} (OStatement : ιₛ → Type)
    [Oₛ : ∀ i, OracleInterface (OStatement i)] (Witness : Type)
    {n : ℕ} (pSpec : ProtocolSpec n) [Oₘ : ∀ i, OracleInterface (pSpec.Message i)] :=
  OracleReduction oSpec Statement OStatement Witness
    TrivialStatement TrivialOracleStatement TrivialWitness pSpec

/-- A **non-interactive prover** is a prover that only sends a single message to the verifier. -/
@[reducible] def NonInteractiveProver (Message : Type) {ι : Type} (oSpec : OracleSpec ι)
    (StmtIn WitIn StmtOut WitOut : Type) :=
  Prover oSpec StmtIn WitIn StmtOut WitOut ![(.P_to_V, Message)]

/-- A **non-interactive verifier** is a verifier that only receives a single message from the
  prover. -/
@[reducible] def NonInteractiveVerifier (Message : Type) {ι : Type} (oSpec : OracleSpec ι)
    (StmtIn StmtOut : Type) :=
  Verifier oSpec StmtIn StmtOut ![(.P_to_V, Message)]

/-- A **non-interactive reduction** is an interactive reduction with only a single message from the
  prover to the verifier (and none in the other direction). -/
@[reducible] def NonInteractiveReduction (Message : Type) {ι : Type} (oSpec : OracleSpec ι)
    (StmtIn WitIn StmtOut WitOut : Type) :=
  Reduction oSpec StmtIn WitIn StmtOut WitOut ![(.P_to_V, Message)]

section Trivial

variable {ι : Type} {oSpec : OracleSpec ι}
    {Statement : Type} {ιₛ : Type} {OStatement : ιₛ → Type} {Witness : Type}
    [Oₛ : ∀ i, OracleInterface (OStatement i)]

/-- The trivial / identity prover, which does not send any messages to the verifier, and returns its
  input context (statement & witness) as output. -/
protected def Prover.id : Prover oSpec Statement Witness Statement Witness ![] where
  PrvState := fun _ => Statement × Witness
  input := _root_.id
  sendMessage := fun i => Fin.elim0 i
  receiveChallenge := fun i => Fin.elim0 i
  output := _root_.id

/-- The trivial / identity verifier, which does not receive any messages from the prover, and
  returns its input statement as output. -/
protected def Verifier.id : Verifier oSpec Statement Statement ![] where
  verify := fun stmt _ => pure stmt

/-- The trivial / identity reduction, which consists of the trivial prover and verifier. -/
protected def Reduction.id : Reduction oSpec Statement Witness Statement Witness ![] where
  prover := Prover.id
  verifier := Verifier.id

/-- The trivial / identity prover in an oracle reduction, which unfolds to the trivial prover for
  the associated non-oracle reduction. -/
protected def OracleProver.id :
    OracleProver oSpec Statement OStatement Witness Statement OStatement Witness ![] :=
  Prover.id

/-- The trivial / identity verifier in an oracle reduction, which receives no messages from the
  prover, and returns its input statement (both non-oracle and oracle) as output. -/
protected def OracleVerifier.id :
    OracleVerifier oSpec Statement OStatement Statement OStatement ![] where
  verify := fun stmt _ => pure stmt
  simulate := fun _ => {
    impl | query i q => (query (Sum.inr (Sum.inl i)) q
      (spec := oSpec ++ₒ ([OStatement]ₒ ++ₒ [ProtocolSpec.Message ![]]ₒ)))
  }
  reify := fun combinedStmt _ => pure combinedStmt.2
  reify_simulate := fun _ _ _ _ _ => rfl

/-- The trivial / identity oracle reduction, which consists of the trivial oracle prover and
  verifier. -/
protected def OracleReduction.id :
    OracleReduction oSpec Statement OStatement Witness Statement OStatement Witness ![] :=
  ⟨OracleProver.id, OracleVerifier.id⟩

alias Prover.trivial := Prover.id
alias Verifier.trivial := Verifier.id
alias Reduction.trivial := Reduction.id
alias OracleProver.trivial := OracleProver.id
alias OracleVerifier.trivial := OracleVerifier.id
alias OracleReduction.trivial := OracleReduction.id

end Trivial

section Classes

namespace ProtocolSpec

variable {n : ℕ}

/-- A protocol specification with the prover speaking first -/
class ProverFirst (pSpec : ProtocolSpec n) [NeZero n] where
  prover_first' : (pSpec 0).1 = .P_to_V

class VerifierFirst (pSpec : ProtocolSpec n) [NeZero n] where
  verifier_first' : (pSpec 0).1 = .V_to_P

class ProverLast (pSpec : ProtocolSpec n) [inst : NeZero n] where
  prover_last' : (pSpec ⟨n - 1, by simp [Nat.pos_of_neZero]⟩).1 = .P_to_V

/-- A protocol specification with the verifier speaking last -/
class VerifierLast (pSpec : ProtocolSpec n) [NeZero n] where
  verifier_last' : (pSpec ⟨n - 1, by simp [Nat.pos_of_neZero]⟩).1 = .V_to_P

class ProverOnly (pSpec : ProtocolSpec 1) extends ProverFirst pSpec

/-- A non-interactive protocol specification with a single message from the prover to the verifier
-/
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
    (pSpec ⟨n - 1, by simp [Nat.pos_of_neZero]⟩).1 = .P_to_V := h.prover_last'

@[simp]
theorem verifier_last (pSpec : ProtocolSpec n) [NeZero n] [h : VerifierLast pSpec] :
    (pSpec ⟨n - 1, by simp [Nat.pos_of_neZero]⟩).1 = .V_to_P := h.verifier_last'

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
