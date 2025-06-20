/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Composition.Sequential.General

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

open ProtocolSpec

variable {n : ℕ}

section Instances

variable {Message : Type}

instance : IsEmpty (ChallengeIdx ![(.P_to_V, Message)]) := by
  simp [ChallengeIdx]
  infer_instance

instance : Unique (MessageIdx ![(.P_to_V, Message)]) where
  default := ⟨0, by simp⟩
  uniq := fun i => by ext; simp

instance : ∀ i, VCVCompatible (Challenge ![(.P_to_V, Message)] i) :=
  fun i => isEmptyElim i

end Instances

/-- Turn each verifier's challenge into an oracle, where one needs to query
  with an input statement
  and a prior transcript to get a challenge (useful for Fiat-Shamir) -/
@[reducible, inline, specialize]
def instChallengeOracleInterfaceFiatShamir {pSpec : ProtocolSpec n} {i : pSpec.ChallengeIdx}
    {StmtIn : Type} : OracleInterface (pSpec.Challenge i) where
  Query := StmtIn × Transcript i.1.castSucc pSpec
  Response := pSpec.Challenge i
  oracle := fun c _ => c

/-- The oracle interface for Fiat-Shamir.

This is the (inefficient) version where we hash the input statement and the entire transcript up to
the point of deriving a new challenge.

Some variants of Fiat-Shamir takes in a salt each round. We assume that such salts are included in
the input statement (i.e. we can always transform a given reduction into one where every round has a
random salt). -/
def fiatShamirSpec (pSpec : ProtocolSpec n) (StmtIn : Type) : OracleSpec pSpec.ChallengeIdx :=
  fun i => (StmtIn × Transcript i.1.succ pSpec, pSpec.Challenge i)

instance {pSpec : ProtocolSpec n} {StmtIn : Type} [∀ i, VCVCompatible (pSpec.Challenge i)] :
    OracleSpec.FiniteRange (fiatShamirSpec pSpec StmtIn) where
  range_inhabited' := fun i => by simp [fiatShamirSpec, OracleSpec.range]; infer_instance
  range_fintype' := fun i => by simp [fiatShamirSpec, OracleSpec.range]; infer_instance

-- TODO: define a more efficient version where one hashes the most recent challenge along with the
-- messages since that challenge (the first challenge is obtained by hashing the statement & the
-- messages so far)

variable {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type} [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec i).2]
  (Salt : Type) [VCVCompatible Salt]

def Prover.fiatShamir (P : Prover pSpec oSpec StmtIn WitIn StmtOut WitOut) :
    NonInteractiveProver (oSpec ++ₒ fiatShamirSpec pSpec StmtIn)
      StmtIn WitIn StmtOut WitOut (∀ i, pSpec.Message i) where
  PrvState := fun i => match i with
    | 0 => P.PrvState 0
    | _ => P.PrvState (Fin.last n)
  input := P.input
  --
  sendMessage := fun idx state => by
    simp [Unique.uniq _ idx, default] at state ⊢
    sorry
  -- This function is never invoked so we apply the elimination principle
  receiveChallenge := fun idx _ _ => isEmptyElim idx
  output := P.output

def Verifier.fiatShamir (V : Verifier pSpec oSpec StmtIn StmtOut) :
    NonInteractiveVerifier (oSpec ++ₒ fiatShamirSpec pSpec StmtIn)
      StmtIn StmtOut (∀ i, pSpec.Message i) where
  verify := fun stmtIn messages =>
    let transcript := sorry
    V.verify stmtIn transcript

/-- TODO: change `unifSpec` to something more appropriate (maybe a `CryptographicSponge`) -/
def Reduction.fiatShamir (R : Reduction pSpec oSpec StmtIn WitIn StmtOut WitOut) :
    NonInteractiveReduction (oSpec ++ₒ fiatShamirSpec pSpec StmtIn)
      StmtIn WitIn StmtOut WitOut (∀ i, pSpec.Message i) :=
  ⟨R.prover.fiatShamir, R.verifier.fiatShamir⟩

section Security

noncomputable section

open scoped NNReal

variable [DecidableEq ι] [oSpec.FiniteRange] [∀ i, VCVCompatible (pSpec.Challenge i)]

theorem fiatShamir_completeness (relIn : StmtIn → WitIn → Prop) (relOut : StmtOut → WitOut → Prop)
    (completenessError : ℝ≥0) (R : Reduction pSpec oSpec StmtIn WitIn StmtOut WitOut) :
  R.completeness relIn relOut completenessError →
    (R.fiatShamir).completeness relIn relOut completenessError := sorry

-- TODO: state-restoration (knowledge) soundness implies (knowledge) soundness after Fiat-Shamir

end

end Security
