/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.LiftContext.Reduction

/-!
  ## Lifting Oracle Reductions to Larger Contexts

  This file is a continuation of `LiftContext/Reduction.lean`, where we lift oracle reductions to
  larger contexts.

  The only new thing here is the definition of the oracle verifier. The rest (oracle prover +
  security properties) are just ported from `LiftContext/Reduction.lean`, with suitable conversions.
-/

open OracleSpec OracleComp ProtocolSpec

open scoped NNReal

variable {ι : Type} {oSpec : OracleSpec ι}
  {OuterStmtIn OuterWitIn OuterStmtOut OuterWitOut : Type}
  {Outer_ιₛᵢ : Type} {OuterOStmtIn : Outer_ιₛᵢ → Type} [∀ i, OracleInterface (OuterOStmtIn i)]
  {Outer_ιₛₒ : Type} {OuterOStmtOut : Outer_ιₛₒ → Type} [∀ i, OracleInterface (OuterOStmtOut i)]
  {Inner_ιₛᵢ : Type} {InnerOStmtIn : Inner_ιₛᵢ → Type} [∀ i, OracleInterface (InnerOStmtIn i)]
  {Inner_ιₛₒ : Type} {InnerOStmtOut : Inner_ιₛₒ → Type} [∀ i, OracleInterface (InnerOStmtOut i)]
  {InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}

/-- The lifting of the prover from an inner oracle reduction to an outer oracle reduction, requiring
  an associated oracle context lens -/
def OracleProver.liftContext
    (lens : OracleContext.ExecutableLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                              OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut
                              OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (P : OracleProver oSpec InnerStmtIn InnerOStmtIn InnerWitIn
                            InnerStmtOut InnerOStmtOut InnerWitOut pSpec) :
    OracleProver oSpec OuterStmtIn OuterOStmtIn OuterWitIn
                      OuterStmtOut OuterOStmtOut OuterWitOut pSpec :=
  Prover.liftContext lens.toLens.toContext P

variable [∀ i, OracleInterface (pSpec.Message i)]

private def OracleVerifier.liftContextQueryImpl
    (lens : OracleStatement.ExecutableLens
      OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut)
    (outerStmt : OuterStmtIn) :
    QueryImpl (oSpec + ([InnerOStmtIn]ₒ + [pSpec.Message]ₒ))
      (OracleComp (oSpec + ([OuterOStmtIn]ₒ + [pSpec.Message]ₒ))) :=
  QueryImpl.addLift (QueryImpl.id' oSpec)
    (QueryImpl.addLift (lens.simulateInput outerStmt) (QueryImpl.id' [pSpec.Message]ₒ) :
      QueryImpl ([InnerOStmtIn]ₒ + [pSpec.Message]ₒ)
        (OracleComp ([OuterOStmtIn]ₒ + [pSpec.Message]ₒ)))

private theorem OracleVerifier.simulateLiftContextQueryImpl
    (lens : OracleStatement.ExecutableLens
      OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut)
    (outerStmt : OuterStmtIn) (outerOStmt : ∀ i, OuterOStmtIn i)
    (messages : pSpec.Messages)
    (q : (oSpec + ([InnerOStmtIn]ₒ + [pSpec.Message]ₒ)).Domain) :
    simulateQ (OracleInterface.simOracle2 oSpec outerOStmt messages)
        (liftContextQueryImpl (oSpec := oSpec) (pSpec := pSpec) lens outerStmt q) =
      OracleInterface.simOracle2 oSpec
        (lens.materializeInput outerStmt outerOStmt) messages q := by
  rcases q with q | q
  · simp only [liftContextQueryImpl, QueryImpl.addLift_def,
      QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply]
    simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      OracleInterface.simOracle2, QueryImpl.addLift, QueryImpl.add_apply_inl,
      QueryImpl.liftTarget_apply]
    rfl
  · rcases q with q | q
    · rcases q with ⟨i, q⟩
      simp only [liftContextQueryImpl, QueryImpl.addLift_def, QueryImpl.add_apply_inr,
        QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply]
      unfold OracleInterface.simOracle2
      calc
        _ = liftM (simulateQ (OracleInterface.simOracle0 OuterOStmtIn outerOStmt)
            (lens.simulateInput outerStmt ⟨i, q⟩)) := by
            rw [QueryImpl.addLift_def]
            change simulateQ
                (QueryImpl.add
                  ((QueryImpl.id oSpec).liftTarget
                    (OracleComp oSpec))
                  ((QueryImpl.add
                    (OracleInterface.simOracle0 OuterOStmtIn outerOStmt)
                    (OracleInterface.simOracle0 pSpec.Message messages)).liftTarget
                      (OracleComp oSpec)))
                (liftM
                  (liftM (lens.simulateInput outerStmt ⟨i, q⟩) :
                    OracleComp ([OuterOStmtIn]ₒ + [pSpec.Message]ₒ) _) :
                  OracleComp (oSpec + ([OuterOStmtIn]ₒ + [pSpec.Message]ₒ)) _) = _
            rw [simulateQ_add_liftM_right, simulateQ_liftTarget,
              simulateQ_add_liftM_left]
        _ = _ := by
          rw [lens.simulateInput_eq outerStmt outerOStmt ⟨i, q⟩]
          rfl
    · rcases q with ⟨i, q⟩
      simp only [liftContextQueryImpl, QueryImpl.addLift_def,
        QueryImpl.add_apply_inr, QueryImpl.liftTarget_apply]
      unfold OracleInterface.simOracle2
      calc
        _ = liftM (simulateQ (OracleInterface.simOracle0 pSpec.Message messages)
            (QueryImpl.id' [pSpec.Message]ₒ ⟨i, q⟩)) := by
            rw [QueryImpl.addLift_def]
            change simulateQ
                (QueryImpl.add
                  ((QueryImpl.id oSpec).liftTarget
                    (OracleComp oSpec))
                  ((QueryImpl.add
                    (OracleInterface.simOracle0 OuterOStmtIn outerOStmt)
                    (OracleInterface.simOracle0 pSpec.Message messages)).liftTarget
                      (OracleComp oSpec)))
                (liftM
                  (liftM (QueryImpl.id' [pSpec.Message]ₒ ⟨i, q⟩) :
                    OracleComp ([OuterOStmtIn]ₒ + [pSpec.Message]ₒ) _) :
                  OracleComp (oSpec + ([OuterOStmtIn]ₒ + [pSpec.Message]ₒ)) _) = _
            rw [simulateQ_add_liftM_right, simulateQ_liftTarget,
              simulateQ_add_liftM_right]
        _ = _ := rfl

private theorem OracleVerifier.simulateLiftContextQueryImplComp
    (lens : OracleStatement.ExecutableLens
      OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut)
    (outerStmt : OuterStmtIn) (outerOStmt : ∀ i, OuterOStmtIn i)
    (messages : pSpec.Messages) {A : Type}
    (oa : OracleComp (oSpec + ([InnerOStmtIn]ₒ + [pSpec.Message]ₒ)) A) :
    simulateQ (OracleInterface.simOracle2 oSpec outerOStmt messages)
        (simulateQ (liftContextQueryImpl (oSpec := oSpec) (pSpec := pSpec) lens outerStmt) oa) =
      simulateQ (OracleInterface.simOracle2 oSpec
        (lens.materializeInput outerStmt outerOStmt) messages) oa := by
  rw [← QueryImpl.simulateQ_compose]
  apply congrArg (fun impl ↦ simulateQ impl oa)
  apply QueryImpl.ext
  exact simulateLiftContextQueryImpl lens outerStmt outerOStmt messages

/-- The output-oracle contract for an executable context lift.  The adapter's
public output representation must agree with applying the extensional lens to
the inner verifier's materialized output. -/
structure OracleVerifier.LiftContextOutput
    (lens : OracleStatement.ExecutableLens
      OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut)
    (V : OracleVerifier oSpec InnerStmtIn InnerOStmtIn InnerStmtOut InnerOStmtOut pSpec) where
  outputOracle :
    OracleOutputEmbedding OuterOStmtIn pSpec.Message OuterOStmtOut ⊕
      OracleOutputSimulation oSpec OuterOStmtIn OuterOStmtOut pSpec
  materialize_eq : ∀ outerStmt challenges outerOStmt messages,
    OracleVerifier.materializeOutputOracle outputOracle challenges outerOStmt messages =
      lens.materializeOutput outerOStmt
        (V.materializeOutput challenges
          (lens.materializeInput outerStmt outerOStmt) messages)

/-- The lifting of the verifier from an inner oracle reduction to an outer oracle reduction,
  requiring an associated oracle statement lens -/
def OracleVerifier.liftContext
    (lens : OracleStatement.ExecutableLens
      OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut)
    (V : OracleVerifier oSpec InnerStmtIn InnerOStmtIn InnerStmtOut InnerOStmtOut pSpec)
    (output : OracleVerifier.LiftContextOutput lens V) :
      OracleVerifier oSpec OuterStmtIn OuterOStmtIn OuterStmtOut OuterOStmtOut pSpec where
  verify := fun outerStmt challenges ↦ OptionT.mk <|
    Option.map (lens.liftStmt outerStmt) <$> simulateQ
      (liftContextQueryImpl (oSpec := oSpec) (pSpec := pSpec) lens outerStmt)
      (V.verify (lens.projStmt outerStmt) challenges).run
  outputOracle := output.outputOracle

/-- The lifting of an inner oracle reduction to an outer oracle reduction,
  requiring an associated oracle context lens -/
def OracleReduction.liftContext
    (lens : OracleContext.ExecutableLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                              OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut
                              OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (R : OracleReduction oSpec InnerStmtIn InnerOStmtIn InnerWitIn
                            InnerStmtOut InnerOStmtOut InnerWitOut pSpec)
    (output : OracleVerifier.LiftContextOutput lens.stmt R.verifier) :
      OracleReduction oSpec OuterStmtIn OuterOStmtIn OuterWitIn
                      OuterStmtOut OuterOStmtOut OuterWitOut pSpec where
  prover := R.prover.liftContext lens
  verifier := R.verifier.liftContext lens.stmt output

section Execution

/-- The lifting of the verifier commutes with the conversion from the oracle verifier to the
  verifier -/
theorem OracleVerifier.liftContext_toVerifier_comm
    (lens : OracleStatement.ExecutableLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                              OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut)
    (V : OracleVerifier oSpec InnerStmtIn InnerOStmtIn InnerStmtOut InnerOStmtOut pSpec)
    (output : OracleVerifier.LiftContextOutput lens V) :
      (V.liftContext lens output).toVerifier = V.toVerifier.liftContext lens.toLens := by
  apply Verifier.ext
  funext outerInput transcript
  rcases outerInput with ⟨outerStmt, outerOStmt⟩
  apply OptionT.ext
  simp only [OracleVerifier.toVerifier, Verifier.liftContext,
    OracleVerifier.liftContext, OptionT.run_bind, OptionT.run_pure,
    OptionT.run_mk, simulateQ_map, Functor.map_map]
  rw [simulateLiftContextQueryImplComp]
  simp only [OracleVerifier.materializeOutput]
  rw [output.materialize_eq outerStmt transcript.challenges outerOStmt transcript.messages]
  simp only [OracleVerifier.materializeOutput, Statement.Lens.lift]
  simp only [map_eq_bind_pure_comp]
  simp only [Option.elimM, bind_assoc, pure_bind, Function.comp_apply]
  apply bind_congr
  intro result
  cases result <;> rfl

/-- The lifting of the reduction commutes with the conversion from the oracle reduction to the
  reduction -/
theorem OracleReduction.liftContext_toReduction_comm
    (lens : OracleContext.ExecutableLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                              OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut
                              OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (R : OracleReduction oSpec InnerStmtIn InnerOStmtIn InnerWitIn
                            InnerStmtOut InnerOStmtOut InnerWitOut pSpec)
    (output : OracleVerifier.LiftContextOutput lens.stmt R.verifier) :
      (R.liftContext lens output).toReduction =
        R.toReduction.liftContext lens.toLens.toContext := by
  apply Reduction.ext
  · rfl
  · exact OracleVerifier.liftContext_toVerifier_comm lens.stmt R.verifier output

end Execution

section Security

variable [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {outerRelIn : Set ((OuterStmtIn × (∀ i, OuterOStmtIn i)) × OuterWitIn)}
  {outerRelOut : Set ((OuterStmtOut × (∀ i, OuterOStmtOut i)) × OuterWitOut)}
  {innerRelIn : Set ((InnerStmtIn × (∀ i, InnerOStmtIn i)) × InnerWitIn)}
  {innerRelOut : Set ((InnerStmtOut × (∀ i, InnerOStmtOut i)) × InnerWitOut)}

namespace OracleReduction

variable
  {lens : OracleContext.ExecutableLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                            OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut
                            OuterWitIn OuterWitOut InnerWitIn InnerWitOut}
  {R : OracleReduction oSpec InnerStmtIn InnerOStmtIn InnerWitIn
                          InnerStmtOut InnerOStmtOut InnerWitOut pSpec}
  {output : OracleVerifier.LiftContextOutput lens.stmt R.verifier}
  [lensComplete : lens.toLens.toContext.IsComplete outerRelIn innerRelIn outerRelOut innerRelOut
    (R.toReduction.compatContext lens.toLens.toContext)]
  {completenessError : ℝ≥0}

theorem liftContext_completeness
    (h : R.completeness init impl innerRelIn innerRelOut completenessError) :
      (R.liftContext lens output).completeness init impl outerRelIn outerRelOut
        completenessError := by
  unfold OracleReduction.completeness at h ⊢
  rw [liftContext_toReduction_comm lens R output]
  exact R.toReduction.liftContext_completeness h (lens := lens.toLens.toContext)

theorem liftContext_perfectCompleteness
    (h : R.perfectCompleteness init impl innerRelIn innerRelOut) :
      (R.liftContext lens output).perfectCompleteness init impl outerRelIn outerRelOut :=
  liftContext_completeness h

end OracleReduction

namespace OracleVerifier

variable {outerLangIn : Set (OuterStmtIn × (∀ i, OuterOStmtIn i))}
    {outerLangOut : Set (OuterStmtOut × (∀ i, OuterOStmtOut i))}
    {innerLangIn : Set (InnerStmtIn × (∀ i, InnerOStmtIn i))}
    {innerLangOut : Set (InnerStmtOut × (∀ i, InnerOStmtOut i))}
    [Inhabited InnerStmtOut] [∀ i, Inhabited (InnerOStmtOut i)]

/-- Lifting the reduction preserves soundness, assuming the lens satisfies its soundness
  conditions -/
theorem liftContext_soundness
    {soundnessError : ℝ≥0}
    {lens : OracleStatement.ExecutableLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                                OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut}
    (V : OracleVerifier oSpec InnerStmtIn InnerOStmtIn InnerStmtOut InnerOStmtOut pSpec)
    (output : OracleVerifier.LiftContextOutput lens V)
    [lensSound : lens.toLens.IsSound outerLangIn outerLangOut innerLangIn innerLangOut
      (V.toVerifier.compatStatement lens.toLens)]
    (h : V.soundness init impl innerLangIn innerLangOut soundnessError) :
      (V.liftContext lens output).soundness init impl outerLangIn outerLangOut soundnessError := by
  unfold OracleVerifier.soundness at h ⊢
  rw [liftContext_toVerifier_comm lens V output]
  exact V.toVerifier.liftContext_soundness h (lens := lens.toLens)

theorem liftContext_knowledgeSoundness [Inhabited InnerWitIn]
    {knowledgeError : ℝ≥0}
    {stmtLens : OracleStatement.ExecutableLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                                OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut}
    {witLens : Witness.InvLens (OuterStmtIn × ∀ i, OuterOStmtIn i)
                            OuterWitIn OuterWitOut InnerWitIn InnerWitOut}
    (V : OracleVerifier oSpec InnerStmtIn InnerOStmtIn InnerStmtOut InnerOStmtOut pSpec)
    (output : OracleVerifier.LiftContextOutput stmtLens V)
    [lensKS : Extractor.Lens.IsKnowledgeSound
      outerRelIn innerRelIn outerRelOut innerRelOut
      (V.toVerifier.compatStatement stmtLens.toLens) (fun _ _ => True)
      ⟨stmtLens.toLens, witLens⟩]
    (h : V.knowledgeSoundness init impl innerRelIn innerRelOut knowledgeError) :
      (V.liftContext stmtLens output).knowledgeSoundness init impl outerRelIn outerRelOut
        knowledgeError := by
  unfold OracleVerifier.knowledgeSoundness at h ⊢
  rw [liftContext_toVerifier_comm stmtLens V output]
  exact V.toVerifier.liftContext_knowledgeSoundness h
    (stmtLens := stmtLens.toLens) (witLens := witLens)

theorem liftContext_rbr_soundness
    {rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0}
    {lens : OracleStatement.ExecutableLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                                OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut}
    (V : OracleVerifier oSpec InnerStmtIn InnerOStmtIn InnerStmtOut InnerOStmtOut pSpec)
    (output : OracleVerifier.LiftContextOutput lens V)
    [lensSound : lens.toLens.IsSound
      outerLangIn outerLangOut innerLangIn innerLangOut
      (V.toVerifier.compatStatement lens.toLens)]
    (h : V.rbrSoundness init impl innerLangIn innerLangOut rbrSoundnessError) :
      (V.liftContext lens output).rbrSoundness init impl outerLangIn outerLangOut
        rbrSoundnessError := by
  unfold OracleVerifier.rbrSoundness at h ⊢
  rw [liftContext_toVerifier_comm lens V output]
  exact V.toVerifier.liftContext_rbr_soundness h (lens := lens.toLens)

theorem liftContext_rbr_knowledgeSoundness [Inhabited InnerWitIn]
    {rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0}
    {stmtLens : OracleStatement.ExecutableLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                                OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut}
    {witLens : Witness.InvLens (OuterStmtIn × ∀ i, OuterOStmtIn i)
                            OuterWitIn OuterWitOut InnerWitIn InnerWitOut}
    (V : OracleVerifier oSpec InnerStmtIn InnerOStmtIn InnerStmtOut InnerOStmtOut pSpec)
    (output : OracleVerifier.LiftContextOutput stmtLens V)
    [lensKS : Extractor.Lens.IsKnowledgeSound
      outerRelIn innerRelIn outerRelOut innerRelOut
      (V.toVerifier.compatStatement stmtLens.toLens) (fun _ _ => True)
      ⟨stmtLens.toLens, witLens⟩]
    (h : V.rbrKnowledgeSoundness init impl innerRelIn innerRelOut rbrKnowledgeError) :
      (V.liftContext stmtLens output).rbrKnowledgeSoundness init impl outerRelIn outerRelOut
        rbrKnowledgeError := by
  unfold OracleVerifier.rbrKnowledgeSoundness at h ⊢
  rw [liftContext_toVerifier_comm stmtLens V output]
  exact V.toVerifier.liftContext_rbr_knowledgeSoundness h
    (stmtLens := stmtLens.toLens) (witLens := witLens)

end OracleVerifier

end Security
