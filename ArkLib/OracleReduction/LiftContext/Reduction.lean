/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.OracleReduction.LiftContext.Lens
public import ArkLib.OracleReduction.Security.RoundByRound
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

@[expose] public section

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

/-- Lifted extraction retains the outer output witness at positive rounds, so it can reconstruct
the outer input witness when it reaches round zero. -/
def Extractor.RoundByRound.LiftContextWitness
    (OuterWitIn OuterWitOut : Type) (WitMid : Fin (n + 1) → Type)
    (m : Fin (n + 1)) : Type :=
  if m = 0 then OuterWitIn else WitMid m × OuterWitOut

/-- Package an inner intermediate witness, applying the inverse witness lens at round zero. -/
def Extractor.RoundByRound.liftContextWitness
    {WitMid : Fin (n + 1) → Type}
    (lens : Extractor.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (E : Extractor.RoundByRound oSpec InnerStmtIn InnerWitIn InnerWitOut pSpec WitMid)
    (m : Fin (n + 1)) (stmt : OuterStmtIn) (wit : WitMid m) (out : OuterWitOut) :
    LiftContextWitness OuterWitIn OuterWitOut WitMid m :=
  if h : m = 0 then
    cast (by simp [LiftContextWitness, h])
      (lens.wit.lift (stmt, out) (cast ((congrArg WitMid h).trans E.eqIn) wit))
  else
    cast (by simp [LiftContextWitness, h]) (wit, out)

/-- Lift a round-by-round extractor using a new witness family with the correct input type. -/
def Extractor.RoundByRound.liftContext
    {WitMid : Fin (n + 1) → Type}
    (lens : Extractor.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                          OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (E : Extractor.RoundByRound oSpec InnerStmtIn InnerWitIn InnerWitOut pSpec WitMid) :
      Extractor.RoundByRound oSpec OuterStmtIn OuterWitIn OuterWitOut pSpec
        (LiftContextWitness OuterWitIn OuterWitOut WitMid) where
  eqIn := by simp [LiftContextWitness]
  extractMid := fun m stmt tr wit => by
    let pair : WitMid m.succ × OuterWitOut :=
      cast (by simp [LiftContextWitness]) wit
    exact E.liftContextWitness lens m.castSucc stmt
      (E.extractMid m (lens.stmt.proj stmt) tr pair.1) pair.2
  extractOut := fun stmt tr out =>
    E.liftContextWitness lens (.last n) stmt
      (E.extractOut (lens.stmt.proj stmt) tr (lens.wit.proj (stmt, out))) out

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
    ∃ transcript, innerStmtOut ∈ support (V.run (lens.proj outerStmtIn) transcript)

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
        support (R.run (lens.stmt.proj outerCtxIn.1) (lens.wit.proj outerCtxIn))

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
      support (E stmt (lens.wit.proj (outerStmtIn, outerWitOut)) tr logP logV)

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
    stop
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
    {resultRound : OracleComp (oSpec + [pSpec.Challenge]ₒ)
      (pSpec.Transcript i.castSucc × (P.liftContext lens).PrvState i.castSucc)} :
      (P.liftContext lens).processRound i resultRound
      = do
        let ⟨transcript, prvState, outerStmtIn, outerWitIn⟩ ← resultRound
        let ⟨newTranscript, newPrvState⟩ ← P.processRound i (do return ⟨transcript, prvState⟩)
        return ⟨newTranscript, ⟨newPrvState, outerStmtIn, outerWitIn⟩⟩ := by
  unfold processRound liftContext
  simp only [bind_pure_comp]
  congr 1; funext ⟨tr, ps, outerStmtIn', outerWitIn'⟩
  simp only [pure_bind]
  split <;> simp [Functor.map_map, liftM_map, map_bind]


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
    simp only [Fin.induction_succ, ih, bind_pure_comp,
      liftContext_processRound, ChallengeIdx, bind_map_left, Prod.mk.eta]
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
  | zero => simp [runToRound, liftContext, Function.uncurry, simulateQ_pure]
  | succ i ih => simp [liftContext_runToRound, Function.uncurry]

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
  simp only [ChallengeIdx, Challenge, Function.uncurry, bind_pure_comp, simulateQ_map,
    WriterT.run_map]
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
  simp only [ChallengeIdx, Challenge, liftContext, Verifier.liftContext, bind_pure_comp,
    Prover.liftContext_run, Function.uncurry, liftM_map, Verifier.run, OptionT.run_map,
    bind_map_left, map_bind, Functor.map_map]
  congr 1; funext ⟨_, _⟩; congr 1; funext a_1
  simp?
  cases a_1 <;> simp [Option.getM, map_pure]

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
  sorry

end Reduction

variable [∀ i, SampleableType (pSpec.Challenge i)]
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
  rw [OptionT.prEvent_eq_run, OptionT.prEvent_eq_run]
  simp only [OptionT.run_mk, bind_pure_comp,
    OptionT.run_map, simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map,
    Function.uncurry]
  simp only [← bind_pure_comp, bind_assoc, pure_bind]
  rw [← bind_assoc, ← bind_assoc]
  apply _root_.prEvent_mono_of_support
  intro result hSupport hGood
  rw [mem_support_bind_iff] at hSupport
  obtain ⟨s, _, hs⟩ := hSupport
  have hRaw : result.1 ∈ support
      (R.run (lens.stmt.proj outerStmtIn) (lens.wit.proj (outerStmtIn, outerWitIn))).run :=
    support_simulateQ_run'_subset (n := ProbComp) (impl.addLift challengeQueryImpl)
    (R.run (lens.stmt.proj outerStmtIn) (lens.wit.proj (outerStmtIn, outerWitIn))).run s
    (by
      rw [StateT.run'_eq, MonadAttach.support_map]
      exact Set.mem_image_of_mem Prod.fst hs)
  rcases result with ⟨result, finalState⟩
  cases result with
  | none => exact hGood.elim
  | some result =>
    rcases result with ⟨⟨tr, stmt, wit⟩, verStmt⟩
    change (verStmt, wit) ∈ innerRelOut ∧ stmt = verStmt at hGood
    rcases hGood with ⟨hOut, rfl⟩
    refine ⟨lensComplete.lift_complete _ _ _ _ ?_ hRelIn hOut, rfl⟩
    refine ⟨((tr, stmt, wit), stmt), ?_, rfl⟩
    rw [OptionT.mem_support_iff]
    exact hRaw

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
  simp only [ChallengeIdx, Challenge, QueryImpl.addLift_def,
    PFunctor.Handler.liftTarget_self, bind_pure_comp, OptionT.run_bind,
    OptionT.run_monadLift, monadLift_self, OptionT.run_map, Option.elimM_map,
    Option.elim_some, simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind,
    OptionT.mk_bind] at h ⊢
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
  -- Put the two events over the same base computation `oa`.
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
  simp only [ChallengeIdx, Challenge, QueryImpl.addLift_def,
    PFunctor.Handler.liftTarget_self, Extractor.Straightline.liftContext,
    bind_pure_comp, OptionT.run_map, liftM_map, Functor.map_map, OptionT.run_bind,
    StateT.run'_eq, OptionT.mk_bind, Option.mem_def, Prod.mk.eta]
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
  simp only [ChallengeIdx, Challenge, QueryImpl.addLift_def,
    PFunctor.Handler.liftTarget_self, bind_pure_comp, OptionT.run_bind,
    OptionT.run_map, StateT.run'_eq, OptionT.mk_bind, Option.mem_def, Prod.mk.eta] at h'
  have hR := h' (stmtLens.proj outerStmtIn) default innerP
  simp only [Reduction.runWithLog, ChallengeIdx, Challenge, run, bind_pure_comp,
    OptionT.run_bind, OptionT.run_monadLift, monadLift_self, OptionT.run_map,
    Option.elimM_map, Option.elim_some, Option.elimM_bind, simulateQ_bind,
    StateT.run_bind, map_bind, OptionT.mk_bind, liftContext, ge_iff_le] at hR ⊢
  have h_innerP_runWithLog {innerStmtIn} {innerWitIn} :
      innerP.runWithLog innerStmtIn innerWitIn
      = do
        let ⟨⟨transcript, ⟨_, outerWitOut⟩⟩, rest⟩ ← outerP.runWithLog outerStmtIn outerWitIn
        return ⟨⟨transcript, ⟨default, witLens.proj (outerStmtIn, outerWitOut)⟩⟩, rest⟩ := by
    sorry
  refine le_trans ?_ hR
  -- Put the two events over the same base computation `oa`.
  simp [h_innerP_runWithLog]
  -- Apply event monotonicity.
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
  simp only [ChallengeIdx, Challenge, QueryImpl.addLift_def,
    PFunctor.Handler.liftTarget_self, HasQuery.instOfMonadLift_query, bind_pure_comp,
    simulateQ_bind, simulateQ_map, StateT.run'_eq, StateT.run_bind, StateT.run_map,
    map_bind, Functor.map_map, Subtype.forall] at h ⊢
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

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- A related output of a lifted verifier yields a related inner output with positive probability.
The compatibility premise follows from actual execution support, not an extra assumption. -/
theorem liftContext_related_output_pos
    {lens : Extractor.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      OuterWitIn OuterWitOut InnerWitIn InnerWitOut}
    (V : Verifier oSpec InnerStmtIn InnerStmtOut pSpec)
    [lensKS : lens.IsKnowledgeSound outerRelIn innerRelIn outerRelOut innerRelOut
      (V.compatStatement lens.stmt) (fun _ _ => True)]
    (stmt : OuterStmtIn) (tr : pSpec.FullTranscript) (out : OuterWitOut)
    (h : Pr{let s ← OptionT.mk do
      (simulateQ impl
        ((V.liftContext lens.stmt).run stmt tr)).run' (← init)}[(s, out) ∈ outerRelOut] > 0) :
    Pr{let s ← OptionT.mk do
      (simulateQ impl (V.run (lens.stmt.proj stmt) tr)).run' (← init)}[
        (s, lens.wit.proj (stmt, out)) ∈ innerRelOut] > 0 := by
  change Pr{let s ← OptionT.mk do
    (simulateQ impl ((V.liftContext lens.stmt).run stmt tr).run).run'
      (← init)}[(s, out) ∈ outerRelOut] > 0 at h
  simp only [run, liftContext, bind_pure_comp, OptionT.run_map] at h
  rw [← bind_pure_comp] at h
  simp only [OptionT.prEvent_mk_pos_iff, simulateQ_map, StateT.run'_eq,
    StateT.run_map, Functor.map_map, mem_support_bind_iff,
    MonadAttach.support_map, Set.mem_image] at h ⊢
  obtain ⟨outer, ⟨s, hs, ⟨value, state⟩, hv, heq⟩, hrel⟩ := h
  cases value with
  | none => cases heq
  | some inner =>
    simp only [Option.map_some, Option.some.injEq] at heq
    subst outer
    refine ⟨inner, ⟨s, hs, (some inner, state), hv, rfl⟩,
      lensKS.proj_knowledgeSound stmt inner out ?_ hrel⟩
    refine ⟨tr, ?_⟩
    rw [OptionT.mem_support_iff]
    apply support_simulateQ_run'_subset (n := ProbComp) impl (V.run _ tr).run s
    rw [StateT.run'_eq, MonadAttach.support_map]
    exact Set.mem_image_of_mem Prod.fst hv

namespace KnowledgeStateFunction

/-- The lifted knowledge predicate uses the outer relation at zero and the inner predicate later. -/
def liftContextPredicate
    {WitMid : Fin (n + 1) → Type}
    (lens : Extractor.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (rel : Set (OuterStmtIn × OuterWitIn))
    (K : (m : Fin (n + 1)) → InnerStmtIn → Transcript m pSpec → WitMid m → Prop)
    (m : Fin (n + 1)) (stmt : OuterStmtIn) (tr : Transcript m pSpec)
    (wit : Extractor.RoundByRound.LiftContextWitness OuterWitIn OuterWitOut WitMid m) : Prop :=
  if h : m = 0 then
    (stmt, cast (by simp [Extractor.RoundByRound.LiftContextWitness, h]) wit) ∈ rel
  else
    K m (lens.stmt.proj stmt) tr
      (cast (by simp [Extractor.RoundByRound.LiftContextWitness, h]) wit : WitMid m × OuterWitOut).1

variable {WitMid : Fin (n + 1) → Type}
  {lens : Extractor.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
    OuterWitIn OuterWitOut InnerWitIn InnerWitOut}
  {V : Verifier oSpec InnerStmtIn InnerStmtOut pSpec}
  {E : Extractor.RoundByRound oSpec InnerStmtIn InnerWitIn InnerWitOut pSpec WitMid}
  [lensKS : lens.IsKnowledgeSound outerRelIn innerRelIn outerRelOut innerRelOut
    (V.compatStatement lens.stmt) (fun _ _ => True)]

include lensKS in
omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- A valid inner intermediate witness packages to a valid lifted intermediate witness. -/
theorem liftContextPredicate_pack
    (K : V.KnowledgeStateFunction init impl innerRelIn innerRelOut E)
    (m : Fin (n + 1)) (stmt : OuterStmtIn) (tr : Transcript m pSpec)
    (wit : WitMid m) (out : OuterWitOut)
    (hK : K m (lens.stmt.proj stmt) tr wit) :
    liftContextPredicate lens outerRelIn K m stmt tr
      (E.liftContextWitness lens m stmt wit out) := by
  by_cases h : m = 0
  · subst m
    have htr : tr = default := Subsingleton.elim _ _
    subst tr
    simpa [liftContextPredicate, Extractor.RoundByRound.liftContextWitness, cast_cast] using
      lensKS.lift_knowledgeSound stmt out (cast E.eqIn wit) True.intro
        ((K.toFun_empty _ _).mpr hK)
  · simpa [liftContextPredicate, Extractor.RoundByRound.liftContextWitness, h, cast_cast] using hK

/-- Transport a knowledge-state certificate using the repaired intermediate witness family. -/
def liftContext
    (K : V.KnowledgeStateFunction init impl innerRelIn innerRelOut E) :
    (V.liftContext lens.stmt).KnowledgeStateFunction init impl outerRelIn outerRelOut
      (E.liftContext lens) where
  toFun := liftContextPredicate lens outerRelIn K
  toFun_empty := by
    intro stmt wit
    simp [liftContextPredicate]
  toFun_next := by
    intro m hdir stmt tr msg wit hK
    let pair : WitMid m.succ × OuterWitOut :=
      cast (by simp [Extractor.RoundByRound.LiftContextWitness]) wit
    have hInner : K m.succ (lens.stmt.proj stmt) (tr.concat msg) pair.1 := by
      simpa [liftContextPredicate, pair, _root_.id] using hK
    simpa [Extractor.RoundByRound.liftContext, pair] using
      liftContextPredicate_pack (outerRelIn := outerRelIn) (outerRelOut := outerRelOut)
        K m.castSucc stmt tr
        (E.extractMid m (lens.stmt.proj stmt) (tr.concat msg) pair.1) pair.2
        (K.toFun_next m hdir _ tr msg pair.1 hInner)
  toFun_full := by
    intro stmt tr out h
    exact liftContextPredicate_pack (outerRelIn := outerRelIn) (outerRelOut := outerRelOut)
      K (.last n) stmt tr _ out
      (K.toFun_full _ tr _ (liftContext_related_output_pos (outerRelIn := outerRelIn)
        (innerRelIn := innerRelIn) V stmt tr out h))

include lensKS in
omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- Any bad challenge transition after lifting was already a bad inner transition. -/
theorem liftContext_badEvent
    (K : V.KnowledgeStateFunction init impl innerRelIn innerRelOut E)
    (i : pSpec.ChallengeIdx) (stmt : OuterStmtIn)
    (tr : Transcript i.1.castSucc pSpec) (challenge : pSpec.Challenge i) :
    rbrExtractionFailureEvent
        (K.liftContext (lens := lens) (outerRelIn := outerRelIn) (outerRelOut := outerRelOut))
        (E.liftContext lens) i stmt tr challenge →
      rbrExtractionFailureEvent K E i (lens.stmt.proj stmt) tr challenge := by
  rintro ⟨wit, hBad, hGood⟩
  let pair : WitMid i.1.succ × OuterWitOut :=
    cast (by simp [Extractor.RoundByRound.LiftContextWitness]) wit
  refine ⟨pair.1, ?_, ?_⟩
  · intro h
    apply hBad
    simpa [liftContext, Extractor.RoundByRound.liftContext, pair] using
      liftContextPredicate_pack (outerRelIn := outerRelIn) (outerRelOut := outerRelOut)
        K i.1.castSucc stmt tr _ pair.2 h
  · simpa [liftContext, liftContextPredicate, pair] using hGood

end KnowledgeStateFunction

/-
  Lifting the reduction preserves round-by-round knowledge soundness, assuming the lens
  satisfies its knowledge soundness conditions
-/
/-- Context lifting preserves each fixed-prefix bad-challenge bound. Unlike the averaged
proof, no simulated inner prover or inhabited inner input witness is needed. -/
theorem liftContext_rbr_knowledgeSoundness
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
  obtain ⟨W, E, K, hK⟩ := h
  refine ⟨_, E.liftContext ⟨stmtLens, witLens⟩,
    K.liftContext (lens := ⟨stmtLens, witLens⟩), ?_⟩
  intro stmt i transcript
  refine le_trans ?_ (hK (stmtLens.proj stmt) i transcript)
  apply _root_.prEvent_mono
  intro challenge hBad
  exact KnowledgeStateFunction.liftContext_badEvent
    (lens := ⟨stmtLens, witLens⟩) K i stmt transcript challenge hBad

theorem liftContext_rbr_knowledgeSoundnessAveraged [Inhabited InnerStmtOut] [Inhabited InnerWitIn]
    {outerRelIn : Set (OuterStmtIn × OuterWitIn)} {outerRelOut : Set (OuterStmtOut × OuterWitOut)}
    {innerRelIn : Set (InnerStmtIn × InnerWitIn)} {innerRelOut : Set (InnerStmtOut × InnerWitOut)}
    {rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0}
    {stmtLens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut}
    {witLens : Witness.InvLens OuterStmtIn OuterWitIn OuterWitOut InnerWitIn InnerWitOut}
    (V : Verifier oSpec InnerStmtIn InnerStmtOut pSpec)
    [lensKS : Extractor.Lens.IsKnowledgeSound outerRelIn innerRelIn outerRelOut innerRelOut
      (V.compatStatement stmtLens) (fun _ _ => True) ⟨stmtLens, witLens⟩]
    (h : V.rbrKnowledgeSoundnessAveraged init impl innerRelIn innerRelOut rbrKnowledgeError) :
      (V.liftContext stmtLens).rbrKnowledgeSoundnessAveraged init impl outerRelIn outerRelOut
        rbrKnowledgeError := by
  obtain ⟨W, E, K, hK⟩ := h
  refine ⟨_, E.liftContext ⟨stmtLens, witLens⟩,
    K.liftContext (lens := ⟨stmtLens, witLens⟩), ?_⟩
  intro stmt wit P i
  let innerP : Prover oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut pSpec := {
    PrvState := P.PrvState
    input := fun _ => P.input (stmt, wit)
    sendMessage := P.sendMessage
    receiveChallenge := P.receiveChallenge
    output := fun state => do
      let (_, out) ← P.output state
      pure (default, witLens.proj (stmt, out)) }
  have hRun : innerP.runWithLogToRound i.1.castSucc (stmtLens.proj stmt) default =
      P.runWithLogToRound i.1.castSucc stmt wit := rfl
  have hBound := hK (stmtLens.proj stmt) default innerP i
  rw [hRun] at hBound
  refine le_trans ?_ hBound
  rw [← bind_assoc, ← bind_assoc]
  apply _root_.prEvent_mono
  intro result hBad
  exact KnowledgeStateFunction.liftContext_badEvent
    (lens := ⟨stmtLens, witLens⟩) K i stmt result.1 result.2.1 hBad

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
  Set.ofPred (fun ⟨⟨p, q, t⟩, _⟩ => ∑ x ∈ {0, 1}, (p * q).eval x = t)
@[simp]
def innerRelIn_Test : Set (InnerStmtIn_Test × Unit) :=
  Set.ofPred (fun ⟨⟨f, t⟩, _⟩ => ∑ x ∈ {0, 1}, f.eval x = t)

def OuterStmtOut_Test := ℤ[X] × ℤ[X] × ℤ × ℤ
def InnerStmtOut_Test := ℤ[X] × ℤ × ℤ

@[simp]
def outerRelOut_Test : Set (OuterStmtOut_Test × Unit) :=
  Set.ofPred (fun ⟨⟨p, q, t, r⟩, _⟩ => (p * q).eval r = t)
@[simp]
def innerRelOut_Test : Set (InnerStmtOut_Test × Unit) :=
  Set.ofPred (fun ⟨⟨f, t, r⟩, _⟩ => f.eval r = t)

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
  proj_complete := fun ⟨p, q, t⟩ () hRelIn => by
    simpa [outerRelIn_Test, innerRelIn_Test, testLens, testStmtLens, eval_mul] using hRelIn
  lift_complete := fun ⟨p, q, t⟩ _ ⟨f, t', r⟩ _ hCompat hRelIn hRelOut' => by
    change (p * q).eval r = t'
    change f.eval r = t' at hRelOut'
    simpa [hCompat] using hRelOut'

theorem instTestLensKnowledgeSound : testLensE.IsKnowledgeSound
    outerRelIn_Test innerRelIn_Test outerRelOut_Test innerRelOut_Test
      (fun ⟨p, q, _⟩ ⟨f, _⟩ => p * q = f) (fun _ _ => True) where
  proj_knowledgeSound := fun ⟨p, q, t⟩ ⟨f, t', r⟩ _ h h' => by
    change f.eval r = t'
    change (p * q).eval r = t' at h'
    simpa [← h] using h'
  lift_knowledgeSound := fun ⟨p, q, t⟩ _ _ _ hInner => by
    have hInner' : (p * q).eval 0 + (p * q).eval 1 = t := by
      simpa [innerRelIn_Test, testLensE, testStmtLens] using hInner
    simpa [outerRelIn_Test] using hInner'

end

end Test
