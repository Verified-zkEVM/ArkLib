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
    (lens : OracleContext.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                              OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut
                              OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (P : OracleProver oSpec InnerStmtIn InnerOStmtIn InnerWitIn
                            InnerStmtOut InnerOStmtOut InnerWitOut pSpec) :
    OracleProver oSpec OuterStmtIn OuterOStmtIn OuterWitIn
                      OuterStmtOut OuterOStmtOut OuterWitOut pSpec :=
  Prover.liftContext lens.toContext P

variable [∀ i, OracleInterface (pSpec.Message i)]

/-- The lifting of the verifier from an inner oracle reduction to an outer oracle reduction,
  requiring an associated oracle statement lens -/
def OracleVerifier.liftContext
    (lens : OracleStatement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                              OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut)
    (V : OracleVerifier oSpec InnerStmtIn InnerOStmtIn InnerStmtOut InnerOStmtOut pSpec) :
      OracleVerifier oSpec OuterStmtIn OuterOStmtIn OuterStmtOut OuterOStmtOut pSpec where
  verify := fun outerStmtIn transcript => sorry
  embed := by
    have := V.embed

    sorry
  hEq := sorry

/-- The lifting of an inner oracle reduction to an outer oracle reduction,
  requiring an associated oracle context lens -/
def OracleReduction.liftContext
    (lens : OracleContext.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                              OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut
                              OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (R : OracleReduction oSpec InnerStmtIn InnerOStmtIn InnerWitIn
                            InnerStmtOut InnerOStmtOut InnerWitOut pSpec) :
      OracleReduction oSpec OuterStmtIn OuterOStmtIn OuterWitIn
                      OuterStmtOut OuterOStmtOut OuterWitOut pSpec where
  prover := R.prover.liftContext lens
  verifier := R.verifier.liftContext lens.stmt

section Execution

/-- The lifting of the verifier commutes with the conversion from the oracle verifier to the
  verifier -/
theorem OracleVerifier.liftContext_toVerifier_comm
    {lens : OracleStatement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                              OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut}
    {V : OracleVerifier oSpec InnerStmtIn InnerOStmtIn InnerStmtOut InnerOStmtOut pSpec} :
      (V.liftContext lens).toVerifier = V.toVerifier.liftContext lens := by
  sorry

/-- The lifting of the reduction commutes with the conversion from the oracle reduction to the
  reduction -/
theorem OracleReduction.liftContext_toReduction_comm
    {lens : OracleContext.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                              OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut
                              OuterWitIn OuterWitOut InnerWitIn InnerWitOut}
    {R : OracleReduction oSpec InnerStmtIn InnerOStmtIn InnerWitIn
                            InnerStmtOut InnerOStmtOut InnerWitOut pSpec} :
      (R.liftContext lens).toReduction = R.toReduction.liftContext lens.toContext := by
  sorry

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
  {lens : OracleContext.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                            OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut
                            OuterWitIn OuterWitOut InnerWitIn InnerWitOut}
  {R : OracleReduction oSpec InnerStmtIn InnerOStmtIn InnerWitIn
                          InnerStmtOut InnerOStmtOut InnerWitOut pSpec}
  [lensComplete : lens.toContext.IsComplete outerRelIn innerRelIn outerRelOut innerRelOut
    (R.toReduction.compatContext lens.toContext)]
  {completenessError : ℝ≥0}

theorem liftContext_completeness
    (h : R.completeness init impl innerRelIn innerRelOut completenessError) :
      (R.liftContext lens).completeness init impl outerRelIn outerRelOut completenessError := by
  unfold OracleReduction.completeness at h ⊢
  rw [liftContext_toReduction_comm]
  exact R.toReduction.liftContext_completeness h (lens := lens.toContext)

theorem liftContext_perfectCompleteness
    (h : R.perfectCompleteness init impl innerRelIn innerRelOut) :
      (R.liftContext lens).perfectCompleteness init impl outerRelIn outerRelOut :=
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
    {lens : OracleStatement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                                OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut}
    (V : OracleVerifier oSpec InnerStmtIn InnerOStmtIn InnerStmtOut InnerOStmtOut pSpec)
    [lensSound : lens.IsSound outerLangIn outerLangOut innerLangIn innerLangOut
      (V.toVerifier.compatStatement lens)]
    (h : V.soundness init impl innerLangIn innerLangOut soundnessError) :
      (V.liftContext lens).soundness init impl outerLangIn outerLangOut soundnessError := by
  unfold OracleVerifier.soundness at h ⊢
  rw [liftContext_toVerifier_comm]
  exact V.toVerifier.liftContext_soundness h (lens := lens)

theorem liftContext_knowledgeSoundness [Inhabited InnerWitIn]
    {knowledgeError : ℝ≥0}
    {stmtLens : OracleStatement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                                OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut}
    {witLens : Witness.InvLens (OuterStmtIn × ∀ i, OuterOStmtIn i)
                            OuterWitIn OuterWitOut InnerWitIn InnerWitOut}
    (V : OracleVerifier oSpec InnerStmtIn InnerOStmtIn InnerStmtOut InnerOStmtOut pSpec)
    [lensKS : Extractor.Lens.IsKnowledgeSound
      outerRelIn innerRelIn outerRelOut innerRelOut
      (V.toVerifier.compatStatement stmtLens) (fun _ _ => True) ⟨stmtLens, witLens⟩]
    (h : V.knowledgeSoundness init impl innerRelIn innerRelOut knowledgeError) :
      (V.liftContext stmtLens).knowledgeSoundness init impl outerRelIn outerRelOut
        knowledgeError := by
  unfold OracleVerifier.knowledgeSoundness at h ⊢
  rw [liftContext_toVerifier_comm]
  exact V.toVerifier.liftContext_knowledgeSoundness h (stmtLens := stmtLens) (witLens := witLens)

theorem liftContext_rbr_soundness
    {rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0}
    {lens : OracleStatement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                                OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut}
    (V : OracleVerifier oSpec InnerStmtIn InnerOStmtIn InnerStmtOut InnerOStmtOut pSpec)
    [lensSound : lens.IsSound
      outerLangIn outerLangOut innerLangIn innerLangOut
      (V.toVerifier.compatStatement lens)]
    (h : V.rbrSoundness init impl innerLangIn innerLangOut rbrSoundnessError) :
      (V.liftContext lens).rbrSoundness init impl outerLangIn outerLangOut rbrSoundnessError := by
  unfold OracleVerifier.rbrSoundness at h ⊢
  rw [liftContext_toVerifier_comm]
  exact V.toVerifier.liftContext_rbr_soundness h (lens := lens)

theorem liftContext_rbr_knowledgeSoundness [Inhabited InnerWitIn]
    {rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0}
    {stmtLens : OracleStatement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                                OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut}
    {witLens : Witness.InvLens (OuterStmtIn × ∀ i, OuterOStmtIn i)
                            OuterWitIn OuterWitOut InnerWitIn InnerWitOut}
    (V : OracleVerifier oSpec InnerStmtIn InnerOStmtIn InnerStmtOut InnerOStmtOut pSpec)
    [lensKS : Extractor.Lens.IsKnowledgeSound
      outerRelIn innerRelIn outerRelOut innerRelOut
      (V.toVerifier.compatStatement stmtLens) (fun _ _ => True) ⟨stmtLens, witLens⟩]
    (h : V.rbrKnowledgeSoundness init impl innerRelIn innerRelOut rbrKnowledgeError) :
      (V.liftContext stmtLens).rbrKnowledgeSoundness init impl outerRelIn outerRelOut
        rbrKnowledgeError := by
  unfold OracleVerifier.rbrKnowledgeSoundness at h ⊢
  rw [liftContext_toVerifier_comm]
  exact V.toVerifier.liftContext_rbr_knowledgeSoundness h
    (stmtLens := stmtLens) (witLens := witLens)

end OracleVerifier

end Security
