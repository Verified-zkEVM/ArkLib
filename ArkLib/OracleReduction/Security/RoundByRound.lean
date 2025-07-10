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

/-- A **one-shot** round-by-round extractor is a function that:
- Takes in index `m : Fin (n + 1)`
- Takes in the input statement `stmtIn : StmtIn`
- Takes in a partial transcript up to round `m`
- Takes in the prover's query log (TODO: refine this, verifier's query log as well?)

and returns an input witness `witIn : WitIn`.

This is the old definition of round-by-round extractor, which is less general than the new
definition (i.e. the input witness is extracted immediately, "in one shot", unlike the general
definition where the input witness is derived via intermediate witnesses). -/
def RoundByRoundOneShot
    (oSpec : OracleSpec ι) (StmtIn WitIn : Type) {n : ℕ} (pSpec : ProtocolSpec n) :=
  (m : Fin (n + 1)) → StmtIn → Transcript m pSpec → QueryLog oSpec → WitIn

/-- A one-shot round-by-round extractor is **monotone** if its success probability on a given query
  log is the same as the success probability on any extension of that query log.

  TODO: refine this -/
class RoundByRoundOneShot.IsMonotone (E : RoundByRoundOneShot oSpec StmtIn WitIn pSpec)
    (relIn : Set (StmtIn × WitIn)) where
  is_monotone : ∀ roundIdx stmtIn transcript,
    ∀ proveQueryLog₁ proveQueryLog₂ : oSpec.QueryLog,
    -- ∀ verifyQueryLog₁ verifyQueryLog₂ : oSpec.QueryLog,
    proveQueryLog₁.Sublist proveQueryLog₂ →
    -- verifyQueryLog₁.Sublist verifyQueryLog₂ →
    -- Placeholder condition for now, will need to consider the whole game w/ probabilities
    (stmtIn, E roundIdx stmtIn transcript proveQueryLog₁) ∈ relIn →
      (stmtIn, E roundIdx stmtIn transcript proveQueryLog₂) ∈ relIn

/-- A **round-by-round extractor** is a tuple of algorithms that iteratively extracts the input
  witness from the output witness, through a series of intermediate witnesses
  (indexed by `m : Fin (n + 1)`). Formally, it is a tuple of algorithms:

  - `extractIn : StmtIn → WitMid 0 → WitIn`
  - `extractMid : (m : Fin n) → StmtIn → Transcript m.succ pSpec`
    `→ WitMid m.succ → WitMid m.castSucc`
  - `extractOut : StmtIn → FullTranscript pSpec → WitOut → WitMid (.last n)`

  The extractor processes rounds in decreasing order: `n → n-1 → ... → 1 → 0`, using
  intermediate witness types `WitMid m` for each round `m`.
-/
structure RoundByRound
    (oSpec : OracleSpec ι) (StmtIn WitIn WitOut : Type) {n : ℕ} (pSpec : ProtocolSpec n)
    (WitMid : Fin (n + 1) → Type) where
  /-- Extract the input witness from the intermediate witness at round 0 -/
  extractIn : StmtIn → WitMid 0 → WitIn
  /-- Extract intermediate witness for round `m` from intermediate witness for round `m+1`,
    using the transcript up to round `m+1` -/
  extractMid : (m : Fin n) → StmtIn → Transcript m.succ pSpec → WitMid m.succ → WitMid m.castSucc
  /-- Construct the intermediate witness for the final round from the output witness -/
  extractOut : StmtIn → FullTranscript pSpec → WitOut → WitMid (.last n)

namespace RoundByRoundOneShot

/-- A one-shot round-by-round extractor can be converted to the general round-by-round extractor
  format, where all intermediate witness types are equal to the input witness type.

  (something is wrong here...)

  Note that the converse is _not_ true: it's not possible in general to convert a general
  round-by-round extractor to a one-shot one. -/
def toRoundByRound (E : RoundByRoundOneShot oSpec StmtIn WitIn pSpec) :
    RoundByRound oSpec StmtIn WitIn WitOut pSpec (fun _ => WitIn) where
  extractIn := fun stmtIn _ => E 0 stmtIn default default
  extractMid := fun m stmtIn tr _ => E m.succ stmtIn tr default
  extractOut := fun stmtIn tr _ => E (.last n) stmtIn tr default

end RoundByRoundOneShot

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
  /-- For all input statement not in the language, the state function is false for that statement
    and the empty transcript -/
  toFun_empty : ∀ stmt, stmt ∈ langIn ↔ toFun 0 stmt default
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
    (extractor : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid)
    where
  /-- The knowledge state function: takes in round index, input statement, transcript up to that
      round, and intermediate witness of that round, and returns True/False. -/
  toFun : (m : Fin (n + 1)) → StmtIn → Transcript m pSpec → WitMid m → Prop
  /-- If the state function is true for the empty transcript and some initial intermediate witness,
    then the input statement and extracted witness are in the input relation -/
  toFun_empty : ∀ stmtIn, stmtIn ∈ relIn.language ↔ ∃ witMid, toFun 0 stmtIn default witMid
  /-- If the state function is true for a partial transcript extended with a prover message, then
    the state function is also true for the original partial transcript with the extracted
    intermediate witness -/
  toFun_next : ∀ m, pSpec.getDir m = .P_to_V →
    ∀ stmtIn tr msg witMid, toFun m.succ stmtIn (tr.concat msg) witMid →
      toFun m.castSucc stmtIn tr (extractor.extractMid m stmtIn (tr.concat msg) witMid)
  /-- If the verifier can output a statement `stmtOut` that is in the output relation with some
    output witness `witOut`, then the state function is true for the full transcript and the
    extracted last middle witness. -/
  toFun_full : ∀ stmtIn tr witOut,
    [fun stmtOut => (stmtOut, witOut) ∈ relOut | verifier.run stmtIn tr ] > 0 →
    toFun (.last n) stmtIn tr (extractor.extractOut stmtIn tr witOut)

/-- A knowledge state function gives rise to a state function via quantifying over the witness -/
def KnowledgeStateFunction.toStateFunction
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec} {WitMid : Fin (n + 1) → Type}
    {extractor : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid}
    (kSF : KnowledgeStateFunction relIn relOut verifier WitMid extractor) :
      verifier.StateFunction relIn.language relOut.language where
  toFun := fun m stmtIn tr => ∃ witMid, kSF.toFun m stmtIn tr witMid
  toFun_empty := kSF.toFun_empty
    -- simp only [not_exists]
    -- intro witMid hToFun
    -- have := kSF.toFun_empty stmtIn witMid hToFun
    -- simp_all
  toFun_next := fun m hDir stmtIn tr hToFunNext msg => by
    simp only [not_exists]
    intro witMid hToFunNext
    have := kSF.toFun_next m hDir stmtIn tr msg witMid hToFunNext
    simp_all
  toFun_full := fun stmtIn tr hToFunFull => by
    simp only [Fin.val_last, Set.mem_image, Prod.exists, exists_and_right, exists_eq_right,
      probEvent_eq_zero_iff, not_exists]
    intro stmtOut hStmtOut witOut hRelOut
    have hProb : [fun stmtOut ↦ (stmtOut, witOut) ∈ relOut | run stmtIn tr verifier] > 0 := by
      simp only [Fin.val_last, gt_iff_lt, probEvent_pos_iff]
      exact ⟨stmtOut, hStmtOut, hRelOut⟩
    have := kSF.toFun_full stmtIn tr witOut hProb
    simp_all

/-- A state function & a one-shot round-by-round extractor gives rise to a knowledge state function
  where the intermediate witness types are all equal to the input witness type -/
def StateFunction.toKnowledgeStateFunction
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    (oneShotE : Extractor.RoundByRoundOneShot oSpec StmtIn WitIn pSpec)
    (stF : verifier.StateFunction relIn.language relOut.language) :
    verifier.KnowledgeStateFunction relIn relOut (fun _ => WitIn) oneShotE.toRoundByRound where
  toFun := fun m stmtIn tr _ => stF.toFun m stmtIn tr
  toFun_empty := fun stmtIn => by
    exact Iff.trans (stF.toFun_empty stmtIn) (by simp; sorry)
    -- stop
    -- contrapose! this
    -- simp_all [Extractor.RoundByRoundOneShot.toRoundByRound]
    -- sorry
  toFun_next := fun m hDir stmtIn tr msg witMid h => by
    have := stF.toFun_next m hDir stmtIn tr
    contrapose! this
    simp_all
    exact ⟨msg, h⟩
  toFun_full := fun stmtIn tr witOut h => by
    have := stF.toFun_full stmtIn tr
    contrapose! this
    simp_all
    obtain ⟨x, hx, hRelOut⟩ := h
    exact ⟨x, hx, witOut, hRelOut⟩

/-- Coercion to the underlying function of a state function -/
instance {langIn : Set StmtIn} {langOut : Set StmtOut}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec} :
    CoeFun (verifier.StateFunction langIn langOut)
    (fun _ => (m : Fin (n + 1)) → StmtIn → Transcript m pSpec → Prop) := ⟨fun f => f.toFun⟩

/-- Coercion to the underlying function of a knowledge state function -/
instance {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec} {WitMid : Fin (n + 1) → Type}
    {extractor : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid} :
    CoeFun (verifier.KnowledgeStateFunction relIn relOut WitMid extractor)
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
    letI ex : OracleComp (oSpec ++ₒ [pSpec.Challenge]ₒ) _ := do
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
def rbrKnowledgeSoundnessOneShot (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0) : Prop :=
  ∃ stateFunction : verifier.StateFunction relIn.language relOut.language,
  ∃ extractor : Extractor.RoundByRoundOneShot oSpec StmtIn WitIn pSpec,
  ∀ stmtIn : StmtIn,
  ∀ witIn : WitIn,
  ∀ prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec,
  ∀ i : pSpec.ChallengeIdx,
    letI ex : OracleComp (oSpec ++ₒ [pSpec.Challenge]ₒ) _ := (do
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
def rbrKnowledgeSoundness (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0) : Prop :=
  ∃ WitMid : Fin (n + 1) → Type,
  ∃ extractor : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid,
  ∃ kSF : verifier.KnowledgeStateFunction relIn relOut WitMid extractor,
  ∀ stmtIn : StmtIn,
  ∀ witIn : WitIn,
  ∀ prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec,
  ∀ i : pSpec.ChallengeIdx,
    letI ex : OracleComp (oSpec ++ₒ [pSpec.Challenge]ₒ) _ := (do
      let result ← prover.runWithLogToRound i.1.castSucc stmtIn witIn
      let chal ← pSpec.getChallenge i
      return (result, chal))
    [fun ⟨⟨transcript, _, _⟩, challenge⟩ =>
      ∃ witMid,
        ¬ kSF i.1.castSucc stmtIn transcript
          (extractor.extractMid i.1 stmtIn (transcript.concat challenge) witMid) ∧
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

/-- Implication: old rbr knowledge soundness implies new rbr knowledge soundness (with the same
  error) -/
theorem rbrKnowledgeSoundnessOneShot_implies_rbrKnowledgeSoundness
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0}
    (h : verifier.rbrKnowledgeSoundnessOneShot relIn relOut rbrKnowledgeError) :
    verifier.rbrKnowledgeSoundness relIn relOut rbrKnowledgeError := by
  unfold rbrKnowledgeSoundness
  unfold rbrKnowledgeSoundnessOneShot at h
  obtain ⟨stF, oneShotE, h⟩ := h
  refine ⟨fun _ => WitIn, oneShotE.toRoundByRound, stF.toKnowledgeStateFunction oneShotE, ?_⟩
  intro stmtIn witIn prover i
  have := h stmtIn witIn prover i
  simp at h ⊢
  clear h
  refine le_trans ?_ this
  simp
  refine probEvent_mono ?_
  intro ⟨⟨tr, _, _⟩, chal⟩ hx
  simp [StateFunction.toKnowledgeStateFunction]
  intro hCastSucc witIn' hSucc
  simp_all
  have := stF.toFun_empty
  -- refine ⟨?_, hCastSucc, hSucc⟩
  sorry
  -- obtain ⟨WitMid, extractor, kSF⟩

end RoundByRound

end Verifier

open Verifier

section OracleProtocol

variable
  {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
  {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} [Oₛₒ : ∀ i, OracleInterface (OStmtOut i)]
  [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]

namespace OracleVerifier

@[reducible, simp]
def StateFunction
    (langIn : Set (StmtIn × ∀ i, OStmtIn i))
    (langOut : Set (StmtOut × ∀ i, OStmtOut i))
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec) :=
  verifier.toVerifier.StateFunction langIn langOut

@[reducible, simp]
def KnowledgeStateFunction
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut))
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec)
    (WitMid : Fin (n + 1) → Type)
    (extractor : Extractor.RoundByRound oSpec
      (StmtIn × (∀ i, OStmtIn i)) WitIn WitOut pSpec WitMid) :=
  verifier.toVerifier.KnowledgeStateFunction relIn relOut WitMid extractor

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
    (verifier : OracleVerifier oSpec Statement OStatement Bool (fun _ : Empty => Unit)
      (Oₛₒ := isEmptyElim) pSpec)
    (rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0) : Prop :=
  verifier.rbrSoundness (Oₛₒ := isEmptyElim) langIn acceptRejectOracleRel.language rbrSoundnessError

/-- Round-by-round knowledge soundness of an oracle reduction is the same as for non-oracle
reductions. -/
def rbrKnowledgeSoundness
    (relIn : Set ((Statement × ∀ i, OStatement i) × Witness))
    (verifier : OracleVerifier oSpec Statement OStatement Bool (fun _ : Empty => Unit)
      (Oₛₒ := isEmptyElim) pSpec)
    (rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0) : Prop :=
  verifier.rbrKnowledgeSoundness (Oₛₒ := isEmptyElim) relIn acceptRejectOracleRel rbrKnowledgeError

end OracleProof
