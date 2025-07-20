/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Security.Basic

/-!
  # The Fiat-Shamir Transformation

  This file defines the Fiat-Shamir transformation. This transformation takes in a (public-coin)
  interactive reduction (IR) `R` and transforms it into a non-interactive reduction via removing
  interaction from `R`. In particular, in the transformed reduction, queries to the verifier's
  challenges are replaced by queries to a random oracle.

  We will show that the transformation satisfies security properties as follows:

  - Completeness is preserved
  - State-restoration (knowledge) soundness implies (knowledge) soundness
  - Honest-verifier zero-knowledge implies zero-knowledge

  ## Notes

  Our formalization mostly follows the treatment in the Chiesa-Yogev textbook.

  There are many variants of Fiat-Shamir. The most theoretical one is that one hashes the entire
  statement and transcript up to the point of deriving a new challenge. This is inefficient and not
  actually how it is implemented in practice.

  In contrast, most implementations today use the hash function as a **cryptographic sponge**, which
  permits adding in bitstrings (serialized from the messages) and squeezing out new bitstrings (that
  are then de-serialized into challenges).
-/

open ProtocolSpec OracleComp OracleSpec

variable {n : ℕ}

variable {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]

-- In order to define the Fiat-Shamir transformation for the prover, we need to define
-- a slightly altered execution for the prover

/--
Prover's function for processing the next round, given the current result of the previous round.

  This is modified for Fiat-Shamir, where we only accumulate the messages and not the challenges.
-/
@[inline, specialize]
def Prover.processRoundFS [∀ i, VCVCompatible (pSpec.Challenge i)] (j : Fin n)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (currentResult : OracleComp (oSpec ++ₒ fiatShamirSpec StmtIn pSpec)
      (pSpec.MessagesUpTo j.castSucc × StmtIn × prover.PrvState j.castSucc)) :
      OracleComp (oSpec ++ₒ fiatShamirSpec StmtIn pSpec)
        (pSpec.MessagesUpTo j.succ × StmtIn × prover.PrvState j.succ) := do
  let ⟨messages, stmtIn, state⟩ ← currentResult
  match hDir : pSpec.getDir j with
  | .V_to_P => do
    let challenge ← query (spec := fiatShamirSpec StmtIn pSpec) ⟨j, hDir⟩ ⟨stmtIn, messages⟩
    letI newState := prover.receiveChallenge ⟨j, hDir⟩ state challenge
    return ⟨messages.extend hDir, stmtIn, newState⟩
  | .P_to_V => do
    let ⟨msg, newState⟩ ← prover.sendMessage ⟨j, hDir⟩ state
    return ⟨messages.concat hDir msg, stmtIn, newState⟩

/--
Run the prover in an interactive reduction up to round index `i`, via first inputting the
  statement and witness, and then processing each round up to round `i`. Returns the transcript up
  to round `i`, and the prover's state after round `i`.
-/
@[inline, specialize]
def Prover.runToRoundFS [∀ i, VCVCompatible (pSpec.Challenge i)] (i : Fin (n + 1))
    (stmt : StmtIn) (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (state : prover.PrvState 0) :
        OracleComp (oSpec ++ₒ fiatShamirSpec StmtIn pSpec)
          (pSpec.MessagesUpTo i × StmtIn × prover.PrvState i) :=
  Fin.induction
    (pure ⟨default, stmt, state⟩)
    prover.processRoundFS
    i

/-- The (slow) Fiat-Shamir transformation for the prover. -/
def Prover.fiatShamir (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    NonInteractiveProver (∀ i, pSpec.Message i) (oSpec ++ₒ fiatShamirSpec StmtIn pSpec)
      StmtIn WitIn StmtOut WitOut where
  PrvState := fun i => match i with
    | 0 => StmtIn × P.PrvState 0
    | _ => P.PrvState (Fin.last n)
  input := fun ctx => ⟨ctx.1, P.input ctx⟩
  -- Compute the messages to send via the modified `runToRoundFS`
  sendMessage | ⟨0, _⟩ => fun ⟨stmtIn, state⟩ => do
    let ⟨messages, _, state⟩ ← P.runToRoundFS (Fin.last n) stmtIn state
    return ⟨messages, state⟩
  -- This function is never invoked so we apply the elimination principle
  receiveChallenge | ⟨0, h⟩ => nomatch h
  output := P.output

/-- Derive the full transcript from the (full) messages, via querying the Fiat-Shamir oracle for the
  challenges. -/
def ProtocolSpec.Messages.deriveTranscriptFS (messages : pSpec.Messages) (stmt : StmtIn)
    (k : Fin (n + 1)) :
    OracleComp (oSpec ++ₒ fiatShamirSpec StmtIn pSpec) (pSpec.Transcript k) := do
  Fin.induction
    (pure default)
    (fun i ih => do
      let prevTranscript ← ih
      match hDir : pSpec.getDir i with
      | .V_to_P =>
        let challenge ←
          query (spec := fiatShamirSpec _ _) ⟨i, hDir⟩ ⟨stmt, messages.take i.castSucc⟩
        return prevTranscript.concat challenge
      | .P_to_V => return prevTranscript.concat (messages ⟨i, hDir⟩))
    k

/-- The (slow) Fiat-Shamir transformation for the verifier. -/
def Verifier.fiatShamir (V : Verifier oSpec StmtIn StmtOut pSpec) :
    NonInteractiveVerifier (∀ i, pSpec.Message i) (oSpec ++ₒ fiatShamirSpec StmtIn pSpec)
      StmtIn StmtOut where
  verify := fun stmtIn proof => do
    let messages : pSpec.Messages := proof 0
    let transcript ← messages.deriveTranscriptFS stmtIn (Fin.last n)
    V.verify stmtIn transcript

/-- The Fiat-Shamir transformation for an (interactive) reduction, which consists of applying the
  Fiat-Shamir transformation to both the prover and the verifier. -/
def Reduction.fiatShamir (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    NonInteractiveReduction (∀ i, pSpec.Message i) (oSpec ++ₒ fiatShamirSpec StmtIn pSpec)
      StmtIn WitIn StmtOut WitOut where
  prover := R.prover.fiatShamir
  verifier := R.verifier.fiatShamir

section Security

noncomputable section

open scoped NNReal

variable [oSpec.FiniteRange] [∀ i, VCVCompatible (pSpec.Challenge i)]

theorem fiatShamir_completeness (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (completenessError : ℝ≥0) (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
  R.completeness relIn relOut completenessError →
    R.fiatShamir.completeness relIn relOut completenessError := sorry

-- TODO: state-restoration (knowledge) soundness implies (knowledge) soundness after Fiat-Shamir

end

end Security
