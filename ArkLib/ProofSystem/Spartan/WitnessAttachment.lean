/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Spartan.ZeroCheck.Reduction
public import ArkLib.ProofSystem.Component.SendWitness

/-!
# Spartan witness attachment

The prover sends the padded witness table. Matrix queries are forwarded to the original
instance's matrix oracles through the layout embedding. Extraction reads the sent table and
restricts it to the original witness coordinates. A `SendSingleWitness.Adapter` supplies the
one-message stage and its shared security proofs; this module supplies the layout simulation and
forward and backward relation transfers.
-/

@[expose] public section

namespace Spartan.WitnessAttachment

open OracleComp OracleSpec OracleInterface ProtocolSpec Realization
open scoped NNReal

variable {R : Type} [CommRing R] (sz : R1CS.Size)

local notation "pp" => PublicParams.forSize sz

/-- The original matrix oracle evaluates its embedded matrix at a Spartan query point. -/
@[instance_reducible]
def sourceMatrixInterface (i : R1CS.MatrixIdx) :
    OracleInterface (R1CS.OracleStatement R sz i) where
  Query := (Fin (pp).ℓ_m → R) × (Fin (pp).ℓ_n → R)
  toOC.spec := fun _ => R
  toOC.impl point := do
    return matrixEval (R1CS.embedMatrix R sz (pp).toSizeR1CS (← read)) point.1 point.2

/-- The named source interface fixes the layout used by every forwarded matrix query. -/
@[instance_reducible]
def sourceOracleInterface : ∀ i, OracleInterface (R1CS.OracleStatement R sz i) :=
  sourceMatrixInterface sz

local instance : ∀ i, OracleInterface (R1CS.OracleStatement R sz i) := sourceOracleInterface sz
local instance : OracleInterface (R1CS.Witness R (pp).toSizeR1CS) := Terminal.witnessInterface pp

/-- One prover message containing the padded witness table. -/
abbrev pSpec := SendSingleWitness.oraclePSpec (R1CS.Witness R (pp).toSizeR1CS)

/-- The retained padded matrices and the explicitly supplied padded witness table. -/
def attachedOracles (matrices : ∀ i, R1CS.OracleStatement R sz i)
    (w : R1CS.Witness R (pp).toSizeR1CS) : ∀ i, OracleStatement (R := R) pp i
  | .inl i => embedMatrices sz matrices i
  | .inr _ => w

/-- Any sent table satisfying the padded instance recovers a satisfying original witness. -/
theorem attached_relation_iff (x : R1CS.Statement R sz)
    (matrices : ∀ i, R1CS.OracleStatement R sz i)
    (w : R1CS.Witness R (pp).toSizeR1CS) :
    ZeroCheck.inputRelation pp (embedStatement sz x) (attachedOracles sz matrices w) ↔
      R1CS.relation R sz x matrices (pullbackWitness sz w) :=
  embedding_relation_iff sz x matrices w

variable {ι : Type} (oSpec : OracleSpec ι)

/-- Output matrix queries forward one scalar source query; witness queries use the sent table. -/
def outputSimulation : OracleOutputSimulation oSpec (R1CS.OracleStatement R sz)
    (OracleStatement (R := R) pp) (pSpec (R := R) sz) where
  materializeOutput _ matrices messages := attachedOracles sz matrices (messages ⟨0, rfl⟩)
  simulateOutputQuery _ q := match q with
    | ⟨.inl i, point⟩ => liftM <| OracleSpec.query
        (spec := oSpec + ([R1CS.OracleStatement R sz]ₒ + [(pSpec (R := R) sz).Message]ₒ))
        (Sum.inr (Sum.inl ⟨i, point⟩))
    | ⟨.inr _, point⟩ => liftM <| OracleSpec.query
        (spec := oSpec + ([R1CS.OracleStatement R sz]ₒ + [(pSpec (R := R) sz).Message]ₒ))
        (Sum.inr (Sum.inr ⟨⟨0, rfl⟩, point⟩))
  simulateOutputQuery_eq _ matrices messages q := by
    rcases q with ⟨i, point⟩
    cases i <;> rfl

/-- Every matrix output query makes exactly its corresponding original-matrix query. -/
theorem outputSimulation_matrixQuery
    (challenges : (pSpec (R := R) sz).Challenges) (i : R1CS.MatrixIdx)
    (point : (Fin (pp).ℓ_m → R) × (Fin (pp).ℓ_n → R)) :
    (outputSimulation sz oSpec).simulateOutputQuery challenges ⟨.inl i, point⟩ =
      liftM (OracleSpec.query
        (spec := oSpec + ([R1CS.OracleStatement R sz]ₒ + [(pSpec (R := R) sz).Message]ₒ))
        (Sum.inr (Sum.inl ⟨i, point⟩))) := rfl

/-- Pad the honest witness, restrict extracted tables, and forward matrix queries. -/
def adapter : SendSingleWitness.Adapter oSpec
    (R1CS.Statement R sz) (R1CS.OracleStatement R sz) (R1CS.Witness R sz)
    (R1CS.Statement R (pp).toSizeR1CS) (OracleStatement (R := R) pp)
    (R1CS.Witness R (pp).toSizeR1CS) where
  stmtOut := embedStatement sz
  encode := embedWitness sz
  decode := pullbackWitness sz
  outputOracle := .inr (outputSimulation sz oSpec)

/-- The honest prover pads its actual witness and sends that table. -/
def oracleProver : OracleProver oSpec (R1CS.Statement R sz) (R1CS.OracleStatement R sz)
    (R1CS.Witness R sz) (R1CS.Statement R (pp).toSizeR1CS)
    (OracleStatement (R := R) pp) Unit (pSpec (R := R) sz) :=
  (adapter sz oSpec).oracleProver

/-- The honest transcript contains precisely the embedded input witness. -/
theorem oracleProver_run (x : R1CS.Statement R sz)
    (matrices : ∀ i, R1CS.OracleStatement R sz i) (w : R1CS.Witness R sz) :
    (oracleProver sz oSpec).run (x, matrices) w =
      pure ((fun | ⟨0, _⟩ => embedWitness sz w),
        (embedStatement sz x, attachedOracles sz matrices (embedWitness sz w)), ()) :=
  (adapter sz oSpec).oracleProver_run (x, matrices) w

/-- Witness attachment has pure honest output. -/
instance : (oracleProver (R := R) sz oSpec).OutputIsPure :=
  SendSingleWitness.Adapter.instOutputIsPure _

/-- The verifier attaches the sent witness and forwards all matrix evaluations. -/
def oracleVerifier : OracleVerifier oSpec (R1CS.Statement R sz) (R1CS.OracleStatement R sz)
    (R1CS.Statement R (pp).toSizeR1CS) (OracleStatement (R := R) pp) (pSpec (R := R) sz) :=
  (adapter sz oSpec).oracleVerifier

/-- The original-instance witness attachment reduction. -/
def oracleReduction : OracleReduction oSpec (R1CS.Statement R sz) (R1CS.OracleStatement R sz)
    (R1CS.Witness R sz) (R1CS.Statement R (pp).toSizeR1CS)
    (OracleStatement (R := R) pp) Unit (pSpec (R := R) sz) :=
  (adapter sz oSpec).oracleReduction

/-- The input relation is satisfiability by the original, unpadded witness. -/
def relIn : Set ((R1CS.Statement R sz × (∀ i, R1CS.OracleStatement R sz i)) ×
    R1CS.Witness R sz) := {s | R1CS.relation R sz s.1.1 s.1.2 s.2}

/-- The output relation is exactly the next zero-check stage's input relation. -/
abbrev relOut := ZeroCheck.relIn (R := R) pp

/-- Materialization exposes precisely the embedded matrices and the table in the transcript. -/
theorem materializeOutput (challenges : (pSpec (R := R) sz).Challenges)
    (matrices : ∀ i, R1CS.OracleStatement R sz i)
    (messages : (pSpec (R := R) sz).Messages) :
    (oracleVerifier sz oSpec).materializeOutput challenges matrices messages =
      attachedOracles sz matrices (messages ⟨0, rfl⟩) := rfl

/-- The materialized verifier returns the embedded public input and attached sent table. -/
theorem verifier_run (s : R1CS.Statement R sz × (∀ i, R1CS.OracleStatement R sz i))
    (tr : (pSpec (R := R) sz).FullTranscript) :
    (oracleVerifier sz oSpec).toVerifier.run s tr =
      pure (embedStatement sz s.1, attachedOracles sz s.2 (tr 0)) := rfl

/-- Attachment has no rejecting guard and records the actual sent witness table. -/
def guardedForm : (oracleVerifier (R := R) sz oSpec).toVerifier.GuardedForm :=
  (adapter sz oSpec).guardedForm

/-- Extraction reads the sent padded table and restricts it to the original coordinates. -/
def rbrExtractor : Extractor.RoundByRound oSpec
    (R1CS.Statement R sz × (∀ i, R1CS.OracleStatement R sz i))
    (R1CS.Witness R sz) Unit (pSpec (R := R) sz)
    (fun _ => R1CS.Witness R (pp).toSizeR1CS) :=
  SendSingleWitness.transcriptExtractor oSpec (pullbackWitness sz)

omit [CommRing R] in
/-- The extracted witness is exactly the restriction of the table sent in the transcript. -/
theorem extractTranscript (s : R1CS.Statement R sz × (∀ i, R1CS.OracleStatement R sz i))
    (tr : (pSpec (R := R) sz).FullTranscript) :
    (rbrExtractor sz oSpec).extractIn s ((rbrExtractor sz oSpec).extractOut s tr ()) =
      pullbackWitness sz (tr 0) := rfl

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- A satisfying attached table decodes to an original satisfying witness. -/
theorem decode_relation (s : R1CS.Statement R sz × (∀ i, R1CS.OracleStatement R sz i))
    (w : R1CS.Witness R (pp).toSizeR1CS)
    (h : ((adapter sz oSpec).output s w, ()) ∈ relOut sz) :
    (s, (adapter sz oSpec).decode w) ∈ relIn sz :=
  (attached_relation_iff sz s.1 s.2 w).mp h

/-- Honest padding transfers the original relation to the attached output. -/
theorem encode_relation (s : R1CS.Statement R sz × (∀ i, R1CS.OracleStatement R sz i))
    (w : R1CS.Witness R sz) (h : (s, w) ∈ relIn sz) :
    ((adapter sz oSpec).output s ((adapter sz oSpec).encode w), ()) ∈ relOut sz :=
  (embedding_preserves_relation sz s.1 s.2 w).mpr h

/-- The final knowledge predicate uses the witness read from the single prover message. -/
def knowledgeStateFunction :
    (oracleVerifier (R := R) sz oSpec).toVerifier.KnowledgeStateFunction init impl
      (relIn sz) (relOut sz) (rbrExtractor sz oSpec) :=
  (adapter sz oSpec).knowledgeStateFunction init impl (relIn sz) (relOut sz)
    (decode_relation sz oSpec)

/-- The named transcript-reading extractor has zero fixed-prefix knowledge error. -/
theorem rbrKnowledgeSoundnessWith :
    (oracleVerifier (R := R) sz oSpec).toVerifier.rbrKnowledgeSoundnessWith init impl
      (relIn sz) (relOut sz) (fun _ => R1CS.Witness R (pp).toSizeR1CS)
      (rbrExtractor sz oSpec) (knowledgeStateFunction sz oSpec init impl) (fun _ => 0) :=
  (adapter sz oSpec).rbrKnowledgeSoundnessWith init impl (relIn sz) (relOut sz)
    (decode_relation sz oSpec)

/-- Honest witness padding and attachment establish the zero-check input relation. -/
theorem perfectCompleteness :
    (oracleReduction (R := R) sz oSpec).perfectCompleteness init impl (relIn sz) (relOut sz) :=
  (adapter sz oSpec).perfectCompleteness init impl (relIn sz) (relOut sz)
    (encode_relation sz oSpec)

end Spartan.WitnessAttachment
