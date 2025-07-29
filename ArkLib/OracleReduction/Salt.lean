/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Execution
import ArkLib.OracleReduction.Cast

/-!
  # Adding Salt to an (Oracle) Reduction

  This file defines the `addSalt` transformation, which adds a salt type to every prover's message
  in an (oracle) reduction.

  Salting is useful for the following reasons:
  - To add zero-knowledge to the prover in Fiat-Shamir and (interactive) BCS
  - To add dummy slots for "tagging" the extracted messages in the state-restoration knowledge
    soundness proof of BCS

  We will show (in another file) that round-by-round security for an (oracle) reduction implies
  state-restoration security for that same (oracle) reduction with any (finite, non-empty) salt type
  added.
-/

open OracleComp OracleSpec

namespace ProtocolSpec

variable {n : ℕ}

/-- Add a salt type to every prover's message in a protocol specification -/
@[reducible]
def addSalt (pSpec : ProtocolSpec n) (Salt : pSpec.MessageIdx → Type) :
    ProtocolSpec n :=
  fun i => match hDir : (pSpec i).1 with
    | .P_to_V => ⟨.P_to_V, (pSpec i).2 × Salt ⟨i, hDir⟩⟩
    | .V_to_P => ⟨.V_to_P, (pSpec i).2⟩

variable {pSpec : ProtocolSpec n} {Salt : pSpec.MessageIdx → Type}

@[simp]
lemma addSalt_getDir (i : Fin n) :
    (pSpec.addSalt Salt i).1 = (pSpec i).1 := by
  simp only [addSalt]
  split <;> simp_all

def MessageIdx.toSaltedIdx (i : pSpec.MessageIdx) : (pSpec.addSalt Salt).MessageIdx :=
  match hDir : (pSpec i).1 with
    | .P_to_V => ⟨i, by simpa using hDir⟩
    | .V_to_P => by have := i.property; simp_all

def ChallengeIdx.toSaltedIdx (i : pSpec.ChallengeIdx) : (pSpec.addSalt Salt).ChallengeIdx :=
  match hDir : (pSpec i).1 with
    | .P_to_V => by have := i.property; simp_all
    | .V_to_P => ⟨i, by simpa using hDir⟩

@[simp]
lemma MessageIdx.toSaltedIdx_val (i : pSpec.MessageIdx) :
    (i.toSaltedIdx (Salt := Salt)).val = i.val := by
  simp only [MessageIdx.toSaltedIdx]
  have := i.property
  split <;> simp_all

@[simp]
lemma ChallengeIdx.toSaltedIdx_val (i : pSpec.ChallengeIdx) :
    (i.toSaltedIdx (Salt := Salt)).val = i.val := by
  simp only [ChallengeIdx.toSaltedIdx]
  have := i.property
  split <;> simp_all

@[simp]
lemma addSalt_getType (i : Fin n) :
    (pSpec.addSalt Salt i).2 = match hDir : (pSpec i).1 with
      | .P_to_V => (pSpec i).2 × Salt ⟨i, hDir⟩
      | .V_to_P => (pSpec i).2 := by
  unfold addSalt
  split <;> simp only

-- lemma addSalt_val_cast (i : Fin n) (p : Fin n → Prop) (h : p i) :
--     (⟨cast (by simp) i, by simp [h]⟩)= (⟨i, h⟩ : Subtype p).val

lemma addSalt_Message (i : pSpec.MessageIdx) :
    (pSpec.addSalt Salt).Message i.toSaltedIdx = (pSpec.Message i × Salt i) := by
  obtain ⟨i, hDir⟩ := i
  simp only [Message, addSalt]
  split <;> simp_all

lemma addSalt_Challenge (i : pSpec.ChallengeIdx) :
    (pSpec.addSalt Salt).Challenge i.toSaltedIdx = pSpec.Challenge i := by
  obtain ⟨i, hDir⟩ := i
  simp only [Challenge, addSalt]
  split <;> simp_all
  rename_i h'; simp at h'; simp_all

/-- Remove the salt from a (partial) transcript of a salted protocol -/
def Transcript.removeSalt {k : Fin (n + 1)} (transcript : (pSpec.addSalt Salt).Transcript k) :
    pSpec.Transcript k :=
-- TODO: would be nice not to need `by` block
  fun i => by
  letI data := transcript i
  unfold addSalt at data
  split at data
  · exact data.1
  · exact data

/-- Extract the salt from a (partial) transcript of a salted protocol -/
def Transcript.extractSalt {k : Fin (n + 1)} (transcript : (pSpec.addSalt Salt).Transcript k) :
    (i : pSpec.MessageIdxUpTo k) → Salt ⟨i.val.castLE (by omega), by simpa using i.property⟩ :=
  fun ⟨i, hDir⟩ => by
  letI data := transcript i
  unfold addSalt at data
  split at data
  · exact data.2
  · simp_all

/-- Remove the salt from a full transcript of a salted protocol -/
def FullTranscript.removeSalt (transcript : (pSpec.addSalt Salt).FullTranscript) :
    pSpec.FullTranscript :=
  Transcript.removeSalt (pSpec := pSpec) (k := Fin.last n) transcript

def FullTranscript.extractSalt (transcript : (pSpec.addSalt Salt).FullTranscript) :
    (i : pSpec.MessageIdx) → Salt i :=
  Transcript.extractSalt (pSpec := pSpec) (k := Fin.last n) transcript

-- theorem test2 {b : Bool} (h : b = true) : (match b with | true => Nat | false => Bool) = Nat :=
--   match b with
--   | true => rfl
--   | false => by contradiction

-- def test {α β : Type} {b : Bool}
--     (x : match hb : b.not with | true => (α × {y : Bool // y = true}) | false => β)
--     (h : b = false) :
--     {y : Bool // y = true} × α :=
--   match (generalizing := true) hb : b with
--   | true => by contradiction
--   | false => Prod.swap x

-- #print test

/-- The oracle interface for each of the prover's messages in a salted protocol is defined to be
  the same as the oracle interface for the original message (ignoring the salt). -/
instance [Oₘ : ∀ i, OracleInterface (pSpec.Message i)] :
    ∀ i, OracleInterface ((pSpec.addSalt Salt).Message i) :=
  fun i => {
    Query := (Oₘ (by simpa using i)).Query
    Response := (Oₘ (by simpa using i)).Response
    oracle := fun msg => (Oₘ (by simpa using i)).oracle sorry
  }

end ProtocolSpec

open ProtocolSpec

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
  {WitIn : Type}
  {StmtOut : Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} [Oₛₒ : ∀ i, OracleInterface (OStmtOut i)]
  {WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n} [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]
  (Salt : pSpec.MessageIdx → Type)

/-- Transform a prover for a protocol specification `pSpec` into a prover for the salted protocol
  specification `pSpec.addSalt Salt`. Require additional computation of the salt for each prover's
  round. -/
def Prover.addSalt (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (saltComp : (i : pSpec.MessageIdx) → P.PrvState i.1.castSucc → Salt i) :
  Prover oSpec StmtIn WitIn StmtOut WitOut (pSpec.addSalt Salt) where
  PrvState := P.PrvState
  input := P.input
  sendMessage := fun i st => sorry
  receiveChallenge := fun i st ch => sorry
  output := P.output

/-- Transform an oracle prover for a protocol specification `pSpec` into an oracle prover for the
  salted protocol specification `pSpec.addSalt Salt`. Require additional computation of the salt
  for each prover's round. -/
def OracleProver.addSalt (P : OracleProver oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec)
    (saltComp : (i : pSpec.MessageIdx) → P.PrvState i.1.castSucc → Salt i) :
  OracleProver oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut (pSpec.addSalt Salt) :=
  Prover.addSalt Salt P saltComp

/-- Transform a verifier for a protocol specification `pSpec` into a verifier for the salted
  protocol. The new verifier takes in the salted transcript, remove the salt, then run the
  original verifier. -/
def Verifier.addSalt (V : Verifier oSpec StmtIn StmtOut pSpec) :
    Verifier oSpec StmtIn StmtOut (pSpec.addSalt Salt) where
  verify := fun stmtIn transcript => V.verify stmtIn transcript.removeSalt

/-- Transform an oracle verifier for a protocol specification `pSpec` into an oracle verifier for
  the salted protocol specification `pSpec.addSalt Salt`. The new oracle verifier is the same as
  the old one, modulo casting of oracle interfaces. -/
def OracleVerifier.addSalt (V : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec) :
    OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut (pSpec.addSalt Salt) where
  verify := fun stmtIn challenges => sorry
  -- (V.verify stmtIn challenges.removeSalt).castOracle
  -- OracleInterface (pSpec.addSalt Salt).Message = OracleInterface pSpec.Message
  embed := sorry
  hEq := sorry

/-- Transform a reduction for a protocol specification `pSpec` into a reduction for the salted
  protocol specification `pSpec.addSalt Salt`. Require additional computation of the salt for each
  prover's round. -/
def Reduction.addSalt (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (saltComp : (i : pSpec.MessageIdx) → R.prover.PrvState i.1.castSucc → Salt i) :
    Reduction oSpec StmtIn WitIn StmtOut WitOut (pSpec.addSalt Salt) where
  prover := R.prover.addSalt Salt saltComp
  verifier := R.verifier.addSalt Salt

/-- Transform an oracle reduction for a protocol specification `pSpec` into an oracle reduction
  for the salted protocol specification `pSpec.addSalt Salt`. Require additional computation of
  the salt for each prover's round. -/
def OracleReduction.addSalt
    (R : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec)
    (saltComp : (i : pSpec.MessageIdx) → R.prover.PrvState i.1.castSucc → Salt i) :
    OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut (pSpec.addSalt Salt) where
  prover := R.prover.addSalt Salt saltComp
  verifier := R.verifier.addSalt Salt

-- Theorems to prove
-- Execution returns the same transcript as the original reduction (modulo salt)
-- Completeness is preserved (for any salt computation)
-- (Knowledge) soundness should be preserved
-- HOWEVER, state-restoration (knowledge) soundness is _not_ preserved
-- There are counter-examples that we can formalize
-- (the verifier sends one random bit per round, and accepts iff it sends zero for every round)
