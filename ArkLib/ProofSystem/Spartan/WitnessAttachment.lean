/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Spartan.ZeroCheck
public import ArkLib.ProofSystem.Component.SendWitness
public import ArkLib.OracleReduction.Security.GuardedRoundByRound
public import ArkLib.OracleReduction.LiftContext.Purity

/-!
# Spartan witness attachment

The prover sends the padded witness table. Matrix queries are forwarded to the original
instance's matrix oracles through the layout embedding. Extraction reads the sent table and
restricts it to the original witness coordinates.
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

/-- Layout adaptation around the existing single-witness sender. -/
def proverContextLens : Context.Lens
    (R1CS.Statement R sz × (∀ i, R1CS.OracleStatement R sz i))
    (R1CS.Statement R (pp).toSizeR1CS × (∀ i, OracleStatement (R := R) pp i))
    (R1CS.Statement R sz × (∀ i, R1CS.OracleStatement R sz i))
    (R1CS.Statement R sz ×
      (∀ i : R1CS.MatrixIdx ⊕ Fin 1,
        Sum.rec (motive := fun _ => Type) (R1CS.OracleStatement R sz)
          (fun _ : Fin 1 => R1CS.Witness R (pp).toSizeR1CS) i))
    (R1CS.Witness R sz) Unit (R1CS.Witness R (pp).toSizeR1CS) Unit where
  stmt := {
    toFunA := id
    toFunB := fun _ ⟨x, o⟩ =>
      (embedStatement sz x, attachedOracles sz (fun i => o (.inl i)) (o (.inr 0))) }
  wit := {
    toFunA := fun s => embedWitness sz s.2
    toFunB := fun _ _ => () }

variable {ι : Type} (oSpec : OracleSpec ι)

/-- The honest prover pads its actual witness and sends that table. -/
def oracleProver : OracleProver oSpec (R1CS.Statement R sz) (R1CS.OracleStatement R sz)
    (R1CS.Witness R sz) (R1CS.Statement R (pp).toSizeR1CS)
    (OracleStatement (R := R) pp) Unit (pSpec (R := R) sz) :=
  Prover.liftContext (proverContextLens sz)
    (SendSingleWitness.oracleProver oSpec (R1CS.Statement R sz) (R1CS.OracleStatement R sz)
      (R1CS.Witness R (pp).toSizeR1CS))

/-- The honest transcript contains precisely the embedded input witness. -/
theorem oracleProver_run (x : R1CS.Statement R sz)
    (matrices : ∀ i, R1CS.OracleStatement R sz i) (w : R1CS.Witness R sz) :
    (oracleProver sz oSpec).run (x, matrices) w =
      pure ((fun | ⟨0, _⟩ => embedWitness sz w),
        (embedStatement sz x, attachedOracles sz matrices (embedWitness sz w)), ()) := by
  change (pure _ : OracleComp _ _) = pure _
  congr 1
  apply Prod.ext
  · funext i
    fin_cases i
    rfl
  · rfl

/-- Witness attachment has pure honest output. -/
instance : (oracleProver (R := R) sz oSpec).OutputIsPure := by
  unfold oracleProver
  exact Prover.instOutputIsPureLiftContext _ _

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

/-- The verifier attaches the sent witness and forwards all matrix evaluations. -/
def oracleVerifier : OracleVerifier oSpec (R1CS.Statement R sz) (R1CS.OracleStatement R sz)
    (R1CS.Statement R (pp).toSizeR1CS) (OracleStatement (R := R) pp) (pSpec (R := R) sz) where
  verify x _ := pure (embedStatement sz x)
  outputOracle := .inr (outputSimulation sz oSpec)

/-- The original-instance witness attachment reduction. -/
def oracleReduction : OracleReduction oSpec (R1CS.Statement R sz) (R1CS.OracleStatement R sz)
    (R1CS.Witness R sz) (R1CS.Statement R (pp).toSizeR1CS)
    (OracleStatement (R := R) pp) Unit (pSpec (R := R) sz) where
  prover := oracleProver sz oSpec
  verifier := oracleVerifier sz oSpec

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
def guardedForm : (oracleVerifier (R := R) sz oSpec).toVerifier.GuardedForm where
  check _ _ := true
  out s tr := (embedStatement sz s.1, attachedOracles sz s.2 (tr 0))
  verify_eq _ _ := rfl

/-- Extraction reads the sent padded table and restricts it to the original coordinates. -/
def rbrExtractor : Extractor.RoundByRound oSpec
    (R1CS.Statement R sz × (∀ i, R1CS.OracleStatement R sz i))
    (R1CS.Witness R sz) Unit (pSpec (R := R) sz)
    (fun _ => R1CS.Witness R (pp).toSizeR1CS) where
  extractIn _ w := pullbackWitness sz w
  extractMid | ⟨0, _⟩ => fun _ tr _ => tr ⟨0, by simp⟩
  extractOut _ tr _ := tr 0

omit [CommRing R] in
/-- The extracted witness is exactly the restriction of the table sent in the transcript. -/
theorem extractTranscript (s : R1CS.Statement R sz × (∀ i, R1CS.OracleStatement R sz i))
    (tr : (pSpec (R := R) sz).FullTranscript) :
    (rbrExtractor sz oSpec).extractIn s ((rbrExtractor sz oSpec).extractOut s tr ()) =
      pullbackWitness sz (tr 0) := rfl

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- The final knowledge predicate uses the witness read from the single prover message. -/
def knowledgeStateFunction :
    (oracleVerifier (R := R) sz oSpec).toVerifier.KnowledgeStateFunction init impl
      (relIn sz) (relOut sz) (rbrExtractor sz oSpec) where
  toFun
    | ⟨0, _⟩ => fun s _ w => R1CS.relation R sz s.1 s.2 (pullbackWitness sz w)
    | ⟨1, _⟩ => fun s tr _ => R1CS.relation R sz s.1 s.2 (pullbackWitness sz (tr 0))
  toFun_empty _ _ h := h
  toFun_next | 0 => fun _ _ _ _ _ h => h
  toFun_full s tr _ h := by
    have hout := ((guardedForm sz oSpec).check_and_of_prEvent_pos h).2
    exact (attached_relation_iff sz s.1 s.2 (tr ⟨0, by simp⟩)).mp hout

/-- The named transcript-reading extractor has zero fixed-prefix knowledge error. -/
theorem rbrKnowledgeSoundnessWith :
    (oracleVerifier (R := R) sz oSpec).toVerifier.rbrKnowledgeSoundnessWith init impl
      (relIn sz) (relOut sz) (fun _ => R1CS.Witness R (pp).toSizeR1CS)
      (rbrExtractor sz oSpec) (knowledgeStateFunction sz oSpec init impl) (fun _ => 0) := by
  intro _ i
  exact isEmptyElim i

/-- Honest witness padding and attachment establish the zero-check input relation. -/
theorem perfectCompleteness :
    (oracleReduction (R := R) sz oSpec).perfectCompleteness init impl (relIn sz) (relOut sz) := by
  apply Reduction.perfectCompleteness_of_run_support
  rintro ⟨x, matrices⟩ w hw result hresult
  let tr : (pSpec (R := R) sz).FullTranscript := fun | ⟨0, _⟩ => embedWitness sz w
  let out := (embedStatement sz x, attachedOracles sz matrices (embedWitness sz w))
  have hrun : ((oracleReduction sz oSpec).toReduction.run (x, matrices) w).run =
      pure (some ((tr, out, ()), out)) := by
    rw [Reduction.run_run_eq_bind]
    change (do
      let p ← ((oracleProver sz oSpec).run (x, matrices) w)
      let s ← ((oracleVerifier sz oSpec).toVerifier.run (x, matrices) p.1).run
      pure (s.map (p, ·))) = _
    rw [oracleProver_run]
    simp only [pure_bind]
    rw [verifier_run]
    rfl
  rw [hrun, support_pure, Set.mem_singleton_iff] at hresult
  subst result
  exact ⟨_, rfl, (embedding_preserves_relation sz x matrices w).mpr hw, rfl⟩

end Spartan.WitnessAttachment
