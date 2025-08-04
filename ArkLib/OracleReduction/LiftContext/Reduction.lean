/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.LiftContext.Lens
import ArkLib.OracleReduction.Security.RoundByRound
-- import ArkLib.OracleReduction.Security.StateRestoration

/-!
  ## Lifting Reductions to Larger Contexts

  Sequential composition is usually not enough to represent oracle reductions in a modular way. We
  also need to formalize **virtual** oracle reductions, which lift reductions from one (virtual /
  inner) context into the another (real / outer) context.

  This is what is meant when we informally say "apply so-and-so protocol to this quantity (derived
  from the input statement & witness)".

  Put in other words, we define a mapping between the input-output interfaces of two (oracle)
  reductions, without changing anything about the underlying reductions.

  Recall that the input-output interface of an oracle reduction consists of:
  - Input: `OuterStmtIn : Type`, `OuterOStmtIn : ιₛᵢ → Type`, and `OuterWitIn : Type`
  - Output: `OuterStmtOut : Type`, `OuterOStmtOut : ιₛₒ → Type`, and `OuterWitOut : Type`

  The liftContext is defined as the following mappings of projections / lifts:

  - `projStmt : OuterStmtIn → InnerStmtIn`
  - `projOStmt : (simulation involving OuterOStmtIn to produce InnerOStmtIn)`
  - `projWit : OuterWitIn → InnerWitIn`
  - `liftStmt : OuterStmtIn × InnerStmtOut → OuterStmtOut`
  - `liftOStmt : (simulation involving InnerOStmtOut to produce OuterOStmtOut)`
  - `liftWit : OuterWitIn × InnerWitOut → OuterWitOut`

  Note that since completeness & soundness for oracle reductions are defined in terms of the same
  properties after converting to (non-oracle) reductions, we only need to focus our efforts on the
  non-oracle case.

  Note that this _exactly_ corresponds to lenses in programming languages / category theory. Namely,
  liftContext on the inputs correspond to a `view`/`get` operation (our "proj"), while liftContext
  on the output corresponds to a `modify`/`set` operation (our "lift").

  More precisely, the `proj/lift` operations correspond to a Lens between two monomial polyonmial
  functors: `OuterCtxIn y^ OuterCtxOut ⇆ InnerCtxIn y^ InnerCtxOut`.

  All the lens definitions are in `Lens.lean`. This file deals with the lens applied to reductions.
  See `OracleReduction.lean` for the application to oracle reduction.
-/

open OracleSpec OracleComp ProtocolSpec

open scoped NNReal

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {OuterStmtIn OuterWitIn OuterStmtOut OuterWitOut : Type}
  {InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut : Type}

/-- The outer prover after lifting invokes the inner prover on the projected input, and
  lifts the output -/
def Prover.liftContext
    (lens : Context.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (P : Prover oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut pSpec) :
      Prover oSpec OuterStmtIn OuterWitIn OuterStmtOut OuterWitOut pSpec where
  PrvState := fun i => P.PrvState i × OuterStmtIn × OuterWitIn
  input := fun ctxIn => ⟨P.input <| lens.proj ctxIn, ctxIn⟩
  sendMessage := fun i ⟨prvState, stmtIn, witIn⟩ => do
    let ⟨msg, prvState'⟩ ← P.sendMessage i prvState
    return ⟨msg, ⟨prvState', stmtIn, witIn⟩⟩
  receiveChallenge := fun i ⟨prvState, stmtIn, witIn⟩ => do
    let f ← P.receiveChallenge i prvState
    return fun chal => ⟨f chal, stmtIn, witIn⟩
  output := fun ⟨prvState, stmtIn, witIn⟩ => do
    let ⟨innerStmtOut, innerWitOut⟩ ← P.output prvState
    return lens.lift (stmtIn, witIn) (innerStmtOut, innerWitOut)

/-- The outer verifier after lifting invokes the inner verifier on the projected input, and
  lifts the output -/
def Verifier.liftContext
    (lens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut)
    (V : Verifier oSpec InnerStmtIn InnerStmtOut pSpec) :
      Verifier oSpec OuterStmtIn OuterStmtOut pSpec where
  verify := fun stmtIn transcript => do
    let innerStmtIn := lens.proj stmtIn
    let innerStmtOut ← V.verify innerStmtIn transcript
    return lens.lift stmtIn innerStmtOut

/-- The outer reduction after lifting is the combination of the lifting of the prover and
  verifier -/
def Reduction.liftContext
    (lens : Context.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (R : Reduction oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut pSpec) :
      Reduction oSpec OuterStmtIn OuterWitIn OuterStmtOut OuterWitOut pSpec where
  prover := R.prover.liftContext lens
  verifier := R.verifier.liftContext lens.stmt

open Verifier in
/-- The outer extractor after lifting invokes the inner extractor on the projected input, and
  lifts the output -/
def Extractor.Straightline.liftContext
    (lens : Extractor.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (E : Extractor.Straightline oSpec InnerStmtIn InnerWitIn InnerWitOut pSpec) :
      Extractor.Straightline oSpec OuterStmtIn OuterWitIn OuterWitOut pSpec :=
  fun outerStmtIn outerWitOut fullTranscript proveQueryLog verifyQueryLog => do
    let ⟨innerStmtIn, innerWitOut⟩ := lens.proj (outerStmtIn, outerWitOut)
    let innerWitIn ← E innerStmtIn innerWitOut fullTranscript proveQueryLog verifyQueryLog
    return lens.wit.lift (outerStmtIn, outerWitOut) innerWitIn

open Verifier in
/-- The outer round-by-round extractor after lifting invokes the inner extractor on the projected
  input, and lifts the output -/
def Extractor.RoundByRound.liftContext
    {WitMid : Fin (n + 1) → Type}
    (lens : Extractor.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                          OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (E : Extractor.RoundByRound oSpec InnerStmtIn InnerWitIn InnerWitOut pSpec WitMid) :
      Extractor.RoundByRound oSpec OuterStmtIn OuterWitIn OuterWitOut pSpec WitMid :=
  sorry
  -- fun roundIdx outerStmtIn fullTranscript proveQueryLog =>
  --   rbrLensInv.liftWit (E roundIdx (lens.projStmt outerStmtIn) fullTranscript proveQueryLog)

/-- Compatibility relation between the outer input statement and the inner output statement,
relative to a verifier.

We require that the inner output statement is a possible output of the verifier on the outer
input statement, for any given transcript. Note that we have to existentially quantify over
transcripts since we only reference the verifier, and there's no way to get the transcript without
a prover. -/
def Verifier.compatStatement
    (lens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut)
    (V : Verifier oSpec InnerStmtIn InnerStmtOut pSpec) :
      OuterStmtIn → InnerStmtOut → Prop :=
  fun outerStmtIn innerStmtOut =>
    ∃ transcript, innerStmtOut ∈ (V.run (lens.proj outerStmtIn) transcript).support

/-- Compatibility relation between the outer input context and the inner output context, relative
to a reduction.

We require that the inner output context (statement + witness) is a possible output of the reduction
on the outer input context (statement + witness). -/
def Reduction.compatContext
    (lens : Context.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (R : Reduction oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut pSpec) :
      (OuterStmtIn × OuterWitIn) → (InnerStmtOut × InnerWitOut) → Prop :=
  fun outerCtxIn innerCtxOut =>
    innerCtxOut ∈
      (Prod.snd ∘ Prod.fst) ''
        (R.run (lens.stmt.proj outerCtxIn.1) (lens.wit.proj outerCtxIn)).support

/-- Compatibility relation between the outer input witness and the inner output witness, relative to
  a straightline extractor.

We require that the inner output witness is a possible output of the straightline extractor on the
outer input witness, for a given input statement, transcript, and prover and verifier's query logs.
-/
def Extractor.Straightline.compatWit
    (lens : Extractor.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (E : Extractor.Straightline oSpec InnerStmtIn InnerWitIn InnerWitOut pSpec) :
      OuterStmtIn × OuterWitOut → InnerWitIn → Prop :=
  fun ⟨outerStmtIn, outerWitOut⟩ innerWitIn =>
    ∃ stmt tr logP logV, innerWitIn ∈
      (E stmt (lens.wit.proj (outerStmtIn, outerWitOut)) tr logP logV).support

/-- The outer state function after lifting invokes the inner state function on the projected
  input, and lifts the output -/
def Verifier.StateFunction.liftContext
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    (lens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut)
    (V : Verifier oSpec InnerStmtIn InnerStmtOut pSpec)
    (outerLangIn : Set OuterStmtIn) (outerLangOut : Set OuterStmtOut)
    (innerLangIn : Set InnerStmtIn) (innerLangOut : Set InnerStmtOut)
    [lensSound : lens.IsSound outerLangIn outerLangOut innerLangIn innerLangOut
      (V.compatStatement lens)]
    (stF : V.StateFunction init impl innerLangIn innerLangOut) :
      (V.liftContext lens).StateFunction init impl outerLangIn outerLangOut
where
  toFun := fun m outerStmtIn transcript =>
    stF m (lens.proj outerStmtIn) transcript
  toFun_empty := fun stmt => by
    have := stF.toFun_empty (lens.proj stmt)
    sorry
    -- stF.toFun_empty (lens.proj stmt) (lensSound.proj_sound stmt hStmt)
  toFun_next := fun m hDir outerStmtIn transcript hStmt msg =>
    stF.toFun_next m hDir (lens.proj outerStmtIn) transcript hStmt msg
  toFun_full := fun outerStmtIn transcript hStmt => by
    have h := stF.toFun_full (lens.proj outerStmtIn) transcript hStmt
    simp [Verifier.run, Verifier.liftContext] at h ⊢
    intro outerStmtOut s hs innerStmtOut s' h' hLens
    have := lensSound.lift_sound outerStmtIn innerStmtOut
    sorry
    -- apply lensSound.lift_sound
    -- · simp [compatStatement]; exact ⟨transcript, hSupport⟩
    -- · exact h innerStmtOut hSupport

section Theorems

/- Theorems about liftContext interacting with reduction execution and security properties -/

namespace Prover

/- Breaking down the intertwining of liftContext and prover execution -/

/-- Lifting the prover intertwines with the process round function -/
theorem liftContext_processRound
    {lens : Context.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut}
    {i : Fin n}
    {P : Prover oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut pSpec}
    {resultRound : OracleComp (oSpec ++ₒ [pSpec.Challenge]ₒ)
      (pSpec.Transcript i.castSucc × (P.liftContext lens).PrvState i.castSucc)} :
      (P.liftContext lens).processRound i resultRound
      = do
        let ⟨transcript, prvState, outerStmtIn, outerWitIn⟩ ← resultRound
        let ⟨newTranscript, newPrvState⟩ ← P.processRound i (do return ⟨transcript, prvState⟩)
        return ⟨newTranscript, ⟨newPrvState, outerStmtIn, outerWitIn⟩⟩ := by
  unfold processRound liftContext
  simp
  congr 1; funext
  split <;> simp

theorem liftContext_runToRound
    {lens : Context.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut}
    {outerStmtIn : OuterStmtIn} {outerWitIn : OuterWitIn} {i : Fin (n + 1)}
    (P : Prover oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut pSpec) :
      (P.liftContext lens).runToRound i outerStmtIn outerWitIn
      = do
        let ⟨transcript, prvState⟩ ←
          (P.runToRound i).uncurry (lens.proj (outerStmtIn, outerWitIn))
        return ⟨transcript, ⟨prvState, outerStmtIn, outerWitIn⟩⟩ := by
  unfold runToRound Function.uncurry
  dsimp
  induction i using Fin.induction with
  | zero => simp [liftContext]
  | succ i ih =>
    simp only [Fin.val_succ, Fin.induction_succ, ih, Fin.coe_castSucc, bind_pure_comp,
      liftContext_processRound, ChallengeIdx, Transcript.def_eq, bind_map_left, Prod.mk.eta]
    simp [processRound]

-- Requires more lemmas about `simulateQ` for logging oracles
theorem liftContext_runWithLogToRound
    {lens : Context.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut}
    {outerStmtIn : OuterStmtIn} {outerWitIn : OuterWitIn} {i : Fin (n + 1)}
    (P : Prover oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut pSpec) :
      (P.liftContext lens).runWithLogToRound i outerStmtIn outerWitIn
      = do
        let ⟨⟨transcript, prvState⟩, queryLog⟩ ←
          (P.runWithLogToRound i).uncurry (lens.proj (outerStmtIn, outerWitIn))
        return ⟨⟨transcript, ⟨prvState, outerStmtIn, outerWitIn⟩⟩, queryLog⟩ := by
  unfold runWithLogToRound
  induction i using Fin.induction with
  | zero => simp [liftContext, Function.uncurry]
  | succ i ih => simp [liftContext_runToRound, Function.uncurry]; congr

/-- Running the lifted outer prover is equivalent to running the inner prover on the projected
  input, and then integrating the output -/
theorem liftContext_run
    {lens : Context.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut}
    {outerStmtIn : OuterStmtIn} {outerWitIn : OuterWitIn}
    {P : Prover oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut pSpec} :
      (P.liftContext lens).run outerStmtIn outerWitIn
      = do
        let ⟨fullTranscript, innerCtxOut⟩ ←
          P.run.uncurry (lens.proj (outerStmtIn, outerWitIn))
        return ⟨fullTranscript, lens.lift (outerStmtIn, outerWitIn) innerCtxOut⟩ := by
  simp only [run, liftContext_runToRound]
  simp [liftContext, Function.uncurry]

/-- Lifting the prover intertwines with logging queries of the prover -/
theorem liftContext_runWithLog
    {lens : Context.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut}
    {outerStmtIn : OuterStmtIn} {outerWitIn : OuterWitIn}
    {P : Prover oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut pSpec} :
      (P.liftContext lens).runWithLog outerStmtIn outerWitIn
      = do
        let ⟨⟨fullTranscript, innerCtxOut⟩, queryLog⟩ ←
          P.runWithLog.uncurry (lens.proj (outerStmtIn, outerWitIn))
        return ⟨⟨fullTranscript, lens.lift (outerStmtIn, outerWitIn) innerCtxOut⟩, queryLog⟩ := by
  rw [runWithLog, liftContext_run]
  simp [Function.uncurry]
  congr

end Prover

namespace Reduction

theorem liftContext_run
    {lens : Context.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut}
    {outerStmtIn : OuterStmtIn} {outerWitIn : OuterWitIn}
    {R : Reduction oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut pSpec} :
      (R.liftContext lens).run outerStmtIn outerWitIn = do
        let ⟨⟨fullTranscript, innerCtxOut⟩, verInnerStmtOut⟩ ←
          R.run.uncurry (lens.proj (outerStmtIn, outerWitIn))
        return ⟨⟨fullTranscript, lens.lift (outerStmtIn, outerWitIn) innerCtxOut⟩ ,
                lens.stmt.lift outerStmtIn verInnerStmtOut⟩ := by
  unfold run
  simp [liftContext, Prover.liftContext_run, Verifier.liftContext, Verifier.run, Function.uncurry]

theorem liftContext_runWithLog
    {lens : Context.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut}
    {outerStmtIn : OuterStmtIn} {outerWitIn : OuterWitIn}
    {R : Reduction oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut pSpec} :
      (R.liftContext lens).runWithLog outerStmtIn outerWitIn = do
        let ⟨⟨⟨fullTranscript, innerCtxOut⟩, verInnerStmtOut⟩, queryLog⟩ ←
          R.runWithLog.uncurry (lens.proj (outerStmtIn, outerWitIn))
        return ⟨⟨⟨fullTranscript, lens.lift (outerStmtIn, outerWitIn) innerCtxOut⟩,
                lens.stmt.lift outerStmtIn verInnerStmtOut⟩, queryLog⟩ := by
  unfold runWithLog
  simp [liftContext, Prover.liftContext_runWithLog, Verifier.liftContext, Verifier.run]

end Reduction

variable [∀ i, SelectableType (pSpec.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {outerRelIn : Set (OuterStmtIn × OuterWitIn)} {outerRelOut : Set (OuterStmtOut × OuterWitOut)}
  {innerRelIn : Set (InnerStmtIn × InnerWitIn)} {innerRelOut : Set (InnerStmtOut × InnerWitOut)}

namespace Reduction

variable
    {R : Reduction oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut pSpec}
    {completenessError : ℝ≥0}
    {lens : Context.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                          OuterWitIn OuterWitOut InnerWitIn InnerWitOut}
    [lensComplete : lens.IsComplete outerRelIn innerRelIn outerRelOut innerRelOut
      (R.compatContext lens)]

/-- Lifting the reduction preserves completeness, assuming the lens satisfies its completeness
  conditions
-/
theorem liftContext_completeness
    (h : R.completeness init impl innerRelIn innerRelOut completenessError) :
      (R.liftContext lens).completeness init impl outerRelIn outerRelOut completenessError := by
  unfold completeness at h ⊢
  intro outerStmtIn outerWitIn hRelIn
  have hR := h (lens.stmt.proj outerStmtIn) (lens.wit.proj (outerStmtIn, outerWitIn))
    (lensComplete.proj_complete _ _ hRelIn)
  rw [Reduction.liftContext_run]
  refine le_trans hR ?_
  simp
  sorry
  -- refine probEvent_mono ?_
  -- intro ⟨innerContextOut, a, b⟩ hSupport ⟨hRelOut, hRelOut'⟩
  -- have : innerContextOut ∈
  --     Prod.fst <$>
  --       (R.run (lens.stmt.proj outerStmtIn)
  -- (lens.wit.proj (outerStmtIn, outerWitIn))).support := by
  --   simp
  --   exact ⟨a, b, hSupport⟩
  -- simp_all
  -- rw [← hRelOut'] at hRelOut ⊢
  -- refine lensComplete.lift_complete _ _ _ _ ?_ hRelIn hRelOut
  -- simp [compatContext]; exact this

theorem liftContext_perfectCompleteness
    (h : R.perfectCompleteness init impl innerRelIn innerRelOut) :
      (R.liftContext lens).perfectCompleteness init impl outerRelIn outerRelOut := by
  exact liftContext_completeness h

-- Can't turn the above into an instance because Lean needs to synthesize `innerRelIn` and
-- `innerRelOut` out of thin air.

-- instance [Reduction.IsComplete innerRelIn innerRelOut R completenessError] :
--     R.liftContext.IsComplete outerRelIn outerRelOut completenessError :=
--   ⟨R.liftContext.completeness⟩

-- instance [R.IsPerfectComplete relIn relOut] :
--     R.liftContext.IsPerfectComplete relIn relOut :=
--   ⟨fun _ => R.liftContext.perfectCompleteness _ _ _⟩

end Reduction

namespace Verifier

/-- Lifting the reduction preserves soundness, assuming the lens satisfies its soundness
  conditions -/
theorem liftContext_soundness [Inhabited InnerStmtOut]
    {outerLangIn : Set OuterStmtIn} {outerLangOut : Set OuterStmtOut}
    {innerLangIn : Set InnerStmtIn} {innerLangOut : Set InnerStmtOut}
    {soundnessError : ℝ≥0}
    {lens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut}
    (V : Verifier oSpec InnerStmtIn InnerStmtOut pSpec)
    -- TODO: figure out the right compatibility relation for the IsSound condition
    [lensSound : lens.IsSound outerLangIn outerLangOut innerLangIn innerLangOut
      (V.compatStatement lens)]
    (h : V.soundness init impl innerLangIn innerLangOut soundnessError) :
      (V.liftContext lens).soundness init impl outerLangIn outerLangOut soundnessError := by
  unfold soundness Reduction.run at h ⊢
  -- Note: there is no distinction between `Outer` and `Inner` here
  intro WitIn WitOut outerWitIn outerP outerStmtIn hOuterStmtIn
  simp at h ⊢
  have innerP : Prover oSpec InnerStmtIn WitIn InnerStmtOut WitOut pSpec := {
    PrvState := outerP.PrvState
    input := fun _ => outerP.input (outerStmtIn, outerWitIn)
    sendMessage := outerP.sendMessage
    receiveChallenge := outerP.receiveChallenge
    output := fun state => do
      let ⟨outerStmtOut, outerWitOut⟩ ← outerP.output state
      return ⟨default, outerWitOut⟩
  }
  have : lens.proj outerStmtIn ∉ innerLangIn := by
    apply lensSound.proj_sound
    exact hOuterStmtIn
  have hSound := h WitIn WitOut outerWitIn innerP (lens.proj outerStmtIn) this
  refine le_trans ?_ hSound
  simp [Verifier.liftContext, Verifier.run]
  -- Need to massage the two `probEvent`s so that they have the same base computation `oa`
  -- Then apply `lensSound.lift_sound`?
  sorry

/-
  Lifting the reduction preserves knowledge soundness, assuming the lens satisfies its knowledge
  soundness conditions

  Note: since knowledge soundness is defined existentially in terms of the extractor, we also cannot
  impose any meaningful compatibility conditions on the witnesses (outer output & inner input),
  hence `compatWit` field is just always true

  (future extensions may define lifting relative to a particular extractor, if needed)
-/
theorem liftContext_knowledgeSoundness [Inhabited InnerStmtOut] [Inhabited InnerWitIn]
    {outerRelIn : Set (OuterStmtIn × OuterWitIn)} {outerRelOut : Set (OuterStmtOut × OuterWitOut)}
    {innerRelIn : Set (InnerStmtIn × InnerWitIn)} {innerRelOut : Set (InnerStmtOut × InnerWitOut)}
    {knowledgeError : ℝ≥0}
    {stmtLens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut}
    {witLens : Witness.InvLens OuterStmtIn OuterWitIn OuterWitOut InnerWitIn InnerWitOut}
    (V : Verifier oSpec InnerStmtIn InnerStmtOut pSpec)
    [lensKS : Extractor.Lens.IsKnowledgeSound outerRelIn innerRelIn outerRelOut innerRelOut
      (V.compatStatement stmtLens) (fun _ _ => True) ⟨stmtLens, witLens⟩]
    (h : V.knowledgeSoundness init impl innerRelIn innerRelOut knowledgeError) :
      (V.liftContext stmtLens).knowledgeSoundness init impl outerRelIn outerRelOut
        knowledgeError := by
  unfold knowledgeSoundness at h ⊢
  obtain ⟨E, h'⟩ := h
  refine ⟨E.liftContext ⟨stmtLens, witLens⟩, ?_⟩
  intro outerStmtIn outerWitIn outerP
  simp [Extractor.Straightline.liftContext]
  let innerP : Prover oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut pSpec :=
    {
      PrvState := outerP.PrvState
      input := fun _ => outerP.input (outerStmtIn, outerWitIn)
      sendMessage := outerP.sendMessage
      receiveChallenge := outerP.receiveChallenge
      output := fun state => do
        let ⟨outerStmtOut, outerWitOut⟩ ← outerP.output state
        return ⟨default, witLens.proj (outerStmtIn, outerWitOut)⟩
    }
  have h_innerP_input {innerStmtIn} {innerWitIn} :
      innerP.input (innerStmtIn, innerWitIn) = outerP.input (outerStmtIn, outerWitIn) := rfl
  simp at h'
  have hR := h' (stmtLens.proj outerStmtIn) default innerP
  simp at hR
  simp [Reduction.runWithLog, Verifier.liftContext, Verifier.run] at hR ⊢
  have h_innerP_runWithLog {innerStmtIn} {innerWitIn} :
      innerP.runWithLog innerStmtIn innerWitIn
      = do
        let ⟨⟨transcript, ⟨_, outerWitOut⟩⟩, rest⟩ ← outerP.runWithLog outerStmtIn outerWitIn
        return ⟨⟨transcript, ⟨default, witLens.proj (outerStmtIn, outerWitOut)⟩⟩, rest⟩ := by
    sorry
  refine le_trans ?_ hR
  -- Massage the two `probEvent`s so that they have the same base computation `oa`?
  simp [h_innerP_runWithLog]
  -- apply probEvent_mono ?_
  sorry

/-
  Lifting the reduction preserves round-by-round soundness, assuming the lens satisfies its
  soundness conditions
-/
theorem liftContext_rbr_soundness [Inhabited InnerStmtOut]
    {outerLangIn : Set OuterStmtIn} {outerLangOut : Set OuterStmtOut}
    {innerLangIn : Set InnerStmtIn} {innerLangOut : Set InnerStmtOut}
    {rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0}
    {lens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut}
    (V : Verifier oSpec InnerStmtIn InnerStmtOut pSpec)
    -- TODO: figure out the right compatibility relation for the IsSound condition
    [lensSound : lens.IsSound outerLangIn outerLangOut innerLangIn innerLangOut
      (V.compatStatement lens)]
    (h : V.rbrSoundness init impl innerLangIn innerLangOut rbrSoundnessError) :
      (V.liftContext lens).rbrSoundness init impl outerLangIn outerLangOut rbrSoundnessError := by
  unfold rbrSoundness at h ⊢
  obtain ⟨stF, h⟩ := h
  simp at h ⊢
  refine ⟨stF.liftContext lens (lensSound := lensSound), ?_⟩
  intro outerStmtIn hOuterStmtIn WitIn WitOut witIn outerP roundIdx hDir
  have innerP : Prover oSpec InnerStmtIn WitIn InnerStmtOut WitOut pSpec := {
    PrvState := outerP.PrvState
    input := fun _ => outerP.input (outerStmtIn, witIn)
    sendMessage := outerP.sendMessage
    receiveChallenge := outerP.receiveChallenge
    output := fun state => do
      let ⟨outerStmtOut, outerWitOut⟩ ← outerP.output state
      pure ⟨default, outerWitOut⟩
  }
  have h' := h (lens.proj outerStmtIn) (lensSound.proj_sound _ hOuterStmtIn)
    WitIn WitOut witIn innerP roundIdx hDir
  refine le_trans ?_ h'
  sorry

/-
  Lifting the reduction preserves round-by-round knowledge soundness, assuming the lens
  satisfies its knowledge soundness conditions
-/
theorem liftContext_rbr_knowledgeSoundness [Inhabited InnerStmtOut] [Inhabited InnerWitIn]
    {outerRelIn : Set (OuterStmtIn × OuterWitIn)} {outerRelOut : Set (OuterStmtOut × OuterWitOut)}
    {innerRelIn : Set (InnerStmtIn × InnerWitIn)} {innerRelOut : Set (InnerStmtOut × InnerWitOut)}
    {rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0}
    {stmtLens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut}
    {witLens : Witness.InvLens OuterStmtIn OuterWitIn OuterWitOut InnerWitIn InnerWitOut}
    (V : Verifier oSpec InnerStmtIn InnerStmtOut pSpec)
    [lensKS : Extractor.Lens.IsKnowledgeSound outerRelIn innerRelIn outerRelOut innerRelOut
      (V.compatStatement stmtLens) (fun _ _ => True) ⟨stmtLens, witLens⟩]
    (h : V.rbrKnowledgeSoundness init impl innerRelIn innerRelOut rbrKnowledgeError) :
      (V.liftContext stmtLens).rbrKnowledgeSoundness init impl outerRelIn outerRelOut
        rbrKnowledgeError := by
  unfold rbrKnowledgeSoundness at h ⊢
  obtain ⟨stF, E, h⟩ := h
  simp at h ⊢
  -- refine ⟨stF.liftContext (lens := lens.toStatement.Lens)
  --   (lensSound := lensKnowledgeSound.toSound),
  --         ?_, ?_⟩
  sorry

end Verifier

end Theorems

section Test

open Polynomial

-- Testing out sum-check-like relations

noncomputable section

def OuterStmtIn_Test := ℤ[X] × ℤ[X] × ℤ
def InnerStmtIn_Test := ℤ[X] × ℤ

@[simp]
def outerRelIn_Test : Set (OuterStmtIn_Test × Unit) :=
  setOf (fun ⟨⟨p, q, t⟩, _⟩ => ∑ x ∈ {0, 1}, (p * q).eval x = t)
@[simp]
def innerRelIn_Test : Set (InnerStmtIn_Test × Unit) :=
  setOf (fun ⟨⟨f, t⟩, _⟩ => ∑ x ∈ {0, 1}, f.eval x = t)

def OuterStmtOut_Test := ℤ[X] × ℤ[X] × ℤ × ℤ
def InnerStmtOut_Test := ℤ[X] × ℤ × ℤ

@[simp]
def outerRelOut_Test : Set (OuterStmtOut_Test × Unit) :=
  setOf (fun ⟨⟨p, q, t, r⟩, _⟩ => (p * q).eval r = t)
@[simp]
def innerRelOut_Test : Set (InnerStmtOut_Test × Unit) :=
  setOf (fun ⟨⟨f, t, r⟩, _⟩ => f.eval r = t)

@[simp]
def testStmtLens :
    Statement.Lens OuterStmtIn_Test OuterStmtOut_Test InnerStmtIn_Test InnerStmtOut_Test :=
  ⟨fun ⟨p, q, t⟩ => ⟨p * q, t⟩, fun ⟨p, q, _⟩ ⟨_, t', u⟩ => (p, q, t', u)⟩

@[simp]
def testLens : Context.Lens OuterStmtIn_Test OuterStmtOut_Test InnerStmtIn_Test InnerStmtOut_Test
                Unit Unit Unit Unit where
  stmt := testStmtLens
  wit := Witness.Lens.id

@[simp]
def testLensE : Extractor.Lens OuterStmtIn_Test OuterStmtOut_Test InnerStmtIn_Test InnerStmtOut_Test
                Unit Unit Unit Unit where
  stmt := testStmtLens
  wit := Witness.InvLens.id

instance instTestLensComplete : testLens.IsComplete
      outerRelIn_Test innerRelIn_Test outerRelOut_Test innerRelOut_Test
      (fun ⟨⟨p, q, _⟩, _⟩ ⟨⟨f, _⟩, _⟩ => p * q = f) where
  proj_complete := fun ⟨p, q, t⟩ () hRelIn => by simp_all
  lift_complete := fun ⟨p, q, t⟩ _ ⟨f, t', r⟩ _ hCompat hRelIn hRelOut' => by
    simp_all only [outerRelIn_Test, eval_mul, Finset.mem_singleton, zero_ne_one,
      not_false_eq_true, Finset.sum_insert, Finset.sum_singleton, Set.mem_setOf_eq,
      innerRelOut_Test, outerRelOut_Test, testLens, testStmtLens]
    simp [← hRelOut', ← hCompat]

def instTestLensKnowledgeSound : testLensE.IsKnowledgeSound
      outerRelIn_Test innerRelIn_Test outerRelOut_Test innerRelOut_Test
      (fun ⟨p, q, _⟩ ⟨f, _⟩ => p * q = f) (fun _ _ => True) where
  proj_knowledgeSound := fun ⟨p, q, t⟩ ⟨f, t', r⟩ _ h h' => by
    simp_all only [outerRelOut_Test, eval_mul, Statement.Lens.lift,
      testLensE, testStmtLens, Set.mem_setOf_eq, innerRelOut_Test]
    simp [← h', ← h]
  lift_knowledgeSound := fun ⟨p, q, t⟩ _ _ _ _ => by
    simp_all

end

end Test
