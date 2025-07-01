/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Security.Basic

/-!
  # Round-by-Round Security Definitions

  This file defines round-by-round security notions for (oracle) reductions.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

variable {ι : Type} {oSpec : OracleSpec ι} [oSpec.FiniteRange]
variable {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
variable [oSpec.FiniteRange] [∀ i, VCVCompatible (pSpec.Challenge i)]

namespace Extractor

/-- A round-by-round extractor with index `m` is given the input statement, a partial transcript
  of length `m`, the prover's query log, and returns a witness to the statement.

  Note that the RBR extractor does not need to take in the output statement or witness. -/
def RoundByRound (oSpec : OracleSpec ι) (StmtIn WitIn : Type) {n : ℕ} (pSpec : ProtocolSpec n) :=
  (m : Fin (n + 1)) → StmtIn → Transcript m pSpec → QueryLog oSpec → WitIn

/-- A round-by-round extractor is **monotone** if its success probability on a given query log
  is the same as the success probability on any extension of that query log. -/
class RoundByRound.IsMonotone (E : RoundByRound oSpec StmtIn WitIn pSpec)
    (relIn : Set (StmtIn × WitIn)) where
  is_monotone : ∀ roundIdx stmtIn transcript,
    ∀ proveQueryLog₁ proveQueryLog₂ : oSpec.QueryLog,
    -- ∀ verifyQueryLog₁ verifyQueryLog₂ : oSpec.QueryLog,
    proveQueryLog₁.Sublist proveQueryLog₂ →
    -- verifyQueryLog₁.Sublist verifyQueryLog₂ →
    -- Placeholder condition for now, will need to consider the whole game w/ probabilities
    (stmtIn, E roundIdx stmtIn transcript proveQueryLog₁) ∈ relIn →
      (stmtIn, E roundIdx stmtIn transcript proveQueryLog₂) ∈ relIn

end Extractor

namespace Verifier

section RoundByRound

instance : Fintype (pSpec.ChallengeIdx) := Subtype.fintype (fun i => pSpec.getDir i = .V_to_P)

/-- A (deterministic) state function for a verifier, with respect to input language `langIn` and
  output language `langOut`. This is used to define round-by-round soundness. -/
structure StateFunction
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    where
  toFun : (m : Fin (n + 1)) → StmtIn → Transcript m pSpec → Prop
  /-- For all input statement not in the language, the state function is false for the empty
    transcript -/
  toFun_empty : ∀ stmt ∉ langIn, ¬ toFun 0 stmt default
  /-- If the state function is false for a partial transcript, and the next message is from the
    prover to the verifier, then the state function is also false for the new partial transcript
    regardless of the message -/
  toFun_next : ∀ m, pSpec.getDir m = .P_to_V →
    ∀ stmt tr, ¬ toFun m.castSucc stmt tr →
    ∀ msg, ¬ toFun m.succ stmt (tr.concat msg)
  /-- If the state function is false for a full transcript, the verifier will not output a statement
    in the output language -/
  toFun_full : ∀ stmt tr, ¬ toFun (.last n) stmt tr →
    [(· ∈ langOut) | verifier.run stmt tr] = 0

/-- A knowledge state function for a verifier, with respect to input relation `relIn`, output
  relation `relOut`, and intermediate witness types `WitMid`. This is used to define
  round-by-round knowledge soundness. -/
structure KnowledgeStateFunction
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (WitMid : Fin (n + 1) → Type)
    where
  /-- The knowledge state function: takes in round index, input statement, transcript up to that
      round, and intermediate witness of that round, and returns True/False. -/
  toFun : (m : Fin (n + 1)) → StmtIn → Transcript m pSpec → WitMid m → Prop
  /-- For all input statement such that for all input witness, the statement and witness is not
    in the input relation, the state function is false for the empty transcript and any witness. -/
  toFun_empty : ∀ stmtIn, stmtIn ∉ relIn.language →
    ∀ witMid, ¬ toFun 0 stmtIn default witMid
  /-- If the state function is false for a partial transcript, and the next message is from the
    prover to the verifier, then the state function is also false for the new partial transcript
    regardless of the message and the next intermediate witness. -/
  toFun_next : ∀ m, pSpec.getDir m = .P_to_V →
    ∀ stmtIn tr, (∀ witMid, ¬ toFun m.castSucc stmtIn tr witMid) →
    ∀ msg, (∀ witMid', ¬ toFun m.succ stmtIn (tr.concat msg) witMid')
  toFun_full : ∀ stmtIn tr, (∀ witMid, ¬ toFun (.last n) stmtIn tr witMid) →
    [fun stmtOut => stmtOut ∈ relOut.language | verifier.run stmtIn tr ] = 0

/-- A knowledge state function gives rise to a state function -/
def KnowledgeStateFunction.toStateFunction
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec} {WitMid : Fin (n + 1) → Type}
    (kSF : KnowledgeStateFunction relIn relOut verifier WitMid) :
      verifier.StateFunction relIn.language relOut.language where
  toFun := fun m stmtIn tr => ∃ witMid, kSF.toFun m stmtIn tr witMid
  toFun_empty := fun stmtIn hStmtIn => by
    simp; exact kSF.toFun_empty stmtIn (by simpa [Set.language] using hStmtIn)
  toFun_next := fun m hDir stmtIn tr hToFunNext msg => by
    simp; exact kSF.toFun_next m hDir stmtIn tr (by simpa [Set.language] using hToFunNext) msg
  toFun_full := fun stmtIn tr hToFunFull => by
    exact kSF.toFun_full stmtIn tr (by simpa [Set.language] using hToFunFull)

/-- A round-by-round extractor basically goes backwards, extracting witnesses round-by-round in
opposite to the prover. -/
structure NewExtractor.RoundByRound (WitMid : Fin (n + 1) → Type) where
  -- what if, just one function?
  -- extract : (m : Fin (n + 1)) → StmtIn → Transcript m pSpec → WitMid m → QueryLog oSpec → WitIn
  extractIn : WitMid 0 → WitIn
  extractMid : (m : Fin n) → StmtIn → Transcript m.succ pSpec →
    WitMid m.succ → QueryLog oSpec → WitMid m.castSucc
  extractOut : WitOut → WitMid (.last n)

instance {langIn : Set StmtIn} {langOut : Set StmtOut}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec} :
    CoeFun (verifier.StateFunction langIn langOut)
    (fun _ => (m : Fin (n + 1)) → StmtIn → Transcript m pSpec → Prop) := ⟨fun f => f.toFun⟩

instance {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec} {WitMid : Fin (n + 1) → Type} :
    CoeFun (verifier.KnowledgeStateFunction relIn relOut WitMid)
    (fun _ => (m : Fin (n + 1)) → StmtIn → Transcript m pSpec → WitMid m → Prop) :=
      ⟨fun f => f.toFun⟩

/-- A protocol with `verifier` satisfies round-by-round soundness with respect to input language
  `langIn`, output language `langOut`, and error `rbrSoundnessError` if:

  - there exists a state function `stateFunction` for the verifier and the input/output languages,
    such that
  - for all initial statement `stmtIn` not in `langIn`,
  - for all initial witness `witIn`,
  - for all provers `prover`,
  - for all `i : Fin n` that is a round corresponding to a challenge,

  the probability that:
  - the state function is false for the partial transcript output by the prover
  - the state function is true for the partial transcript appended by next challenge (chosen
    randomly)

  is at most `rbrSoundnessError i`.
-/
def rbrSoundness (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0) : Prop :=
  ∃ stateFunction : verifier.StateFunction langIn langOut,
  ∀ stmtIn ∉ langIn,
  ∀ WitIn WitOut : Type,
  ∀ witIn : WitIn,
  ∀ prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec,
  ∀ i : pSpec.ChallengeIdx,
    let ex : OracleComp (oSpec ++ₒ [pSpec.Challenge]ₒ) _ := do
      return (← prover.runToRound i.1.castSucc stmtIn witIn, ← pSpec.getChallenge i)
    [fun ⟨⟨transcript, _⟩, challenge⟩ =>
      ¬ stateFunction i.1.castSucc stmtIn transcript ∧
        stateFunction i.1.succ stmtIn (transcript.concat challenge)
    | ex] ≤
      rbrSoundnessError i

/-- Type class for round-by-round soundness for a verifier

Note that we put the error as a field in the type class to make it easier for synthesization
(often the rbr error will need additional simplification / proof) -/
class IsRBRSound (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec) where
  rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0
  is_rbr_sound : rbrSoundness langIn langOut verifier rbrSoundnessError

/-- A protocol with `verifier` satisfies round-by-round knowledge soundness with respect to input
  relation `relIn`, output relation `relOut`, and error `rbrKnowledgeError` if:

  - there exists a state function `stateFunction` for the verifier and the languages of the
    input/output relations, such that
  - for all initial statement `stmtIn` not in the language of `relIn`,
  - for all initial witness `witIn`,
  - for all provers `prover`,
  - for all `i : Fin n` that is a round corresponding to a challenge,

  the probability that:
  - the state function is false for the partial transcript output by the prover
  - the state function is true for the partial transcript appended by next challenge (chosen
    randomly)

  is at most `rbrKnowledgeError i`.
-/
def rbrKnowledgeSoundness (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0) : Prop :=
  ∃ stateFunction : verifier.StateFunction relIn.language relOut.language,
  ∃ extractor : Extractor.RoundByRound oSpec StmtIn WitIn pSpec,
  ∀ stmtIn : StmtIn,
  ∀ witIn : WitIn,
  ∀ prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec,
  ∀ i : pSpec.ChallengeIdx,
    let ex : OracleComp (oSpec ++ₒ [pSpec.Challenge]ₒ) _ := (do
      let result ← prover.runWithLogToRound i.1.castSucc stmtIn witIn
      let chal ← pSpec.getChallenge i
      return (result, chal))
    [fun ⟨⟨transcript, _, proveQueryLog⟩, challenge⟩ =>
      letI extractedWitIn := extractor i.1.castSucc stmtIn transcript proveQueryLog.fst
      (stmtIn, extractedWitIn) ∉ relIn ∧
        ¬ stateFunction i.1.castSucc stmtIn transcript ∧
          stateFunction i.1.succ stmtIn (transcript.concat challenge)
    | ex] ≤ rbrKnowledgeError i

-- Tentative new definition of rbr knowledge soundness, using the knowledge state function
def newRbrKnowledgeSoundness (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0) : Prop :=
  ∃ WitMid : Fin (n + 1) → Type,
  ∃ kSF : verifier.KnowledgeStateFunction relIn relOut WitMid,
  ∃ extractor : NewExtractor.RoundByRound WitMid (WitIn := WitIn) (WitOut := WitOut),
  ∀ stmtIn : StmtIn,
  ∀ witIn : WitIn,
  ∀ prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec,
  ∀ i : pSpec.ChallengeIdx,
    let ex : OracleComp (oSpec ++ₒ [pSpec.Challenge]ₒ) _ := (do
      let result ← prover.runWithLogToRound i.1.castSucc stmtIn witIn
      let chal ← pSpec.getChallenge i
      return (result, chal))
    [fun ⟨⟨transcript, _, proveQueryLog⟩, challenge⟩ =>
      ∃ witMid,
        ¬ kSF i.1.castSucc stmtIn transcript
          (extractor.extractMid i.1 stmtIn (transcript.concat challenge) witMid proveQueryLog) ∧
          kSF i.1.succ stmtIn (transcript.concat challenge) witMid
    | ex] ≤ rbrKnowledgeError i

/-- Type class for round-by-round knowledge soundness for a verifier

Note that we put the error as a field in the type class to make it easier for synthesization
(often the rbr error will need additional simplification / proof)
-/
class IsRBRKnowledgeSound (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec) where
  rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0
  is_rbr_knowledge_sound : rbrKnowledgeSoundness relIn relOut verifier rbrKnowledgeError

end RoundByRound

end Verifier

open Verifier

section OracleProtocol

variable
  {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type}
  {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type}
  [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
  [∀ i, OracleInterface (pSpec.Message i)]

namespace OracleVerifier

@[reducible, simp]
def StateFunction
    (langIn : Set (StmtIn × ∀ i, OStmtIn i))
    (langOut : Set (StmtOut × ∀ i, OStmtOut i))
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec) :=
  verifier.toVerifier.StateFunction langIn langOut

/-- Round-by-round soundness of an oracle reduction is the same as for non-oracle reductions. -/
def rbrSoundness
    (langIn : Set (StmtIn × ∀ i, OStmtIn i))
    (langOut : Set (StmtOut × ∀ i, OStmtOut i))
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec)
    (rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0) : Prop :=
  verifier.toVerifier.rbrSoundness langIn langOut rbrSoundnessError

/-- Round-by-round knowledge soundness of an oracle reduction is the same as for non-oracle
reductions. -/
def rbrKnowledgeSoundness
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut))
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec)
    (rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0) : Prop :=
  verifier.toVerifier.rbrKnowledgeSoundness relIn relOut rbrKnowledgeError

end OracleVerifier

end OracleProtocol

variable {Statement : Type} {ιₛ : Type} {OStatement : ιₛ → Type} {Witness : Type}
  [∀ i, OracleInterface (OStatement i)]
  [∀ i, OracleInterface (pSpec.Message i)]

namespace Proof

@[reducible, simp]
def rbrSoundness (langIn : Set Statement)
    (verifier : Verifier oSpec Statement Bool pSpec)
    (rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0) : Prop :=
  verifier.rbrSoundness langIn acceptRejectRel.language rbrSoundnessError

@[reducible, simp]
def rbrKnowledgeSoundness (relation : Set (Statement × Bool))
    (verifier : Verifier oSpec Statement Bool pSpec)
    (rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0) : Prop :=
  verifier.rbrKnowledgeSoundness relation acceptRejectRel rbrKnowledgeError

end Proof

namespace OracleProof

/-- Round-by-round soundness of an oracle reduction is the same as for non-oracle reductions. -/
@[reducible, simp]
def rbrSoundness
    (langIn : Set (Statement × ∀ i, OStatement i))
    (verifier : OracleVerifier oSpec Statement OStatement Bool (fun _ : Empty => Unit) pSpec)
    (rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0) : Prop :=
  verifier.rbrSoundness langIn acceptRejectOracleRel.language rbrSoundnessError

/-- Round-by-round knowledge soundness of an oracle reduction is the same as for non-oracle
reductions. -/
def rbrKnowledgeSoundness
    (relIn : Set ((Statement × ∀ i, OStatement i) × Witness))
    (verifier : OracleVerifier oSpec Statement OStatement Bool (fun _ : Empty => Unit) pSpec)
    (rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0) : Prop :=
  verifier.rbrKnowledgeSoundness relIn acceptRejectOracleRel rbrKnowledgeError

end OracleProof
