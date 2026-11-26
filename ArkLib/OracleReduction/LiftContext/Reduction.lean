/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.OracleReduction.LiftContext.Lens
public import ArkLib.OracleReduction.Security.RoundByRound

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
/-- Lift the inner extractor's output, using a default inner witness when extraction fails.
The default lets the witness lens recover a valid outer witness in the shortcut case. -/
def Extractor.Straightline.liftContext [Inhabited InnerWitIn]
    (lens : Extractor.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (E : Extractor.Straightline oSpec InnerStmtIn InnerWitIn InnerWitOut pSpec) :
      Extractor.Straightline oSpec OuterStmtIn OuterWitIn OuterWitOut pSpec :=
  fun outerStmtIn outerWitOut fullTranscript proveQueryLog verifyQueryLog => do
    let ⟨innerStmtIn, innerWitOut⟩ := lens.proj (outerStmtIn, outerWitOut)
    let innerWitIn ← liftM (E innerStmtIn innerWitOut fullTranscript
      proveQueryLog verifyQueryLog).run
    return lens.wit.lift (outerStmtIn, outerWitOut) (innerWitIn.getD default)

open Verifier in
/-- Retain the outer output witness at every round, and lift the extracted input witness. -/
def Extractor.RoundByRound.liftContext
    {WitMid : Fin (n + 1) → Type}
    (lens : Extractor.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                          OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (E : Extractor.RoundByRound oSpec InnerStmtIn InnerWitIn InnerWitOut pSpec WitMid) :
      Extractor.RoundByRound oSpec OuterStmtIn OuterWitIn OuterWitOut pSpec
        (fun k => OuterWitOut × WitMid k) where
  extractIn := fun x w => lens.wit.lift (x, w.1) (E.extractIn (lens.stmt.proj x) w.2)
  extractMid := fun m x tr w => (w.1, E.extractMid m (lens.stmt.proj x) tr w.2)
  extractOut := fun x tr w => (w, E.extractOut (lens.stmt.proj x) tr (lens.wit.proj (x, w)))

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

/-- The lifted state holds on valid outer inputs or when the projected inner state holds. -/
def Verifier.StateFunction.liftContext
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    (lens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut)
    (V : Verifier oSpec InnerStmtIn InnerStmtOut pSpec)
    (outerLangIn : Set OuterStmtIn) (outerLangOut : Set OuterStmtOut)
    (innerLangIn : Set InnerStmtIn) (innerLangOut : Set InnerStmtOut)
    [lensSound : lens.IsSound outerLangIn outerLangOut innerLangIn innerLangOut
      (V.compatStatement lens)]
    (stF : V.StateFunction init impl innerLangIn innerLangOut) :
      (V.liftContext lens).StateFunction init impl outerLangIn outerLangOut where
  toFun := fun m x tr => x ∈ outerLangIn ∨ stF m (lens.proj x) tr
  toFun_empty := by
    rintro x (hx | hx)
    · exact hx
    · by_contra hn
      exact lensSound.proj_sound x hn (stF.toFun_empty _ hx)
  toFun_next := by
    intro m hd x tr hn msg hnext
    rcases hnext with hx | hx
    · exact hn (Or.inl hx)
    · exact stF.toFun_next m hd (lens.proj x) tr (fun h => hn (Or.inr h)) msg hx
  toFun_full := by
    intro x tr hn
    have hx : x ∉ outerLangIn := fun h => hn (Or.inl h)
    have h := stF.toFun_full (lens.proj x) tr (fun h => hn (Or.inr h))
    have hmap : ((V.liftContext lens).run x tr : OracleComp oSpec (Option OuterStmtOut)) =
        Option.map (lens.lift x) <$>
          (V.run (lens.proj x) tr : OracleComp oSpec (Option InnerStmtOut)) := by
      exact OptionT.run_map ..
    rw [OptionT.prEvent_mk_eq_zero_iff] at h ⊢
    rw [hmap]
    simp only [Fin.val_last, simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map,
      MonadAttach.support_bind, MonadAttach.mem_support, MonadAttach.support_map,
      Set.mem_iUnion, Set.mem_image,
      Option.map_eq_some_iff, Prod.exists, exists_and_right, existsAndEq, true_and,
      exists_prop, forall_exists_index, and_imp] at h ⊢
    intro oy s0 hs0 y s hy heq
    subst oy
    have hyrun : some y ∈ support ((simulateQ impl (V.run (lens.proj x) tr)).run' s0) := by
      simp only [StateT.run'_eq, support_map, Set.mem_image]
      exact ⟨(some y, s), hy, rfl⟩
    exact lensSound.lift_sound x y hx
      ⟨tr, support_simulateQ_run'_subset impl _ s0 hyrun⟩ (h y s0 hs0 s hy True.intro)

/-- The lifted knowledge state retains the inner state or the lens's input-witness shortcut.
The shortcut is unchanged by intermediate extraction. -/
def Verifier.KnowledgeStateFunction.liftContext
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {WitMid : Fin (n + 1) → Type}
    (lens : Extractor.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (V : Verifier oSpec InnerStmtIn InnerStmtOut pSpec)
    (outerRelIn : Set (OuterStmtIn × OuterWitIn)) (innerRelIn : Set (InnerStmtIn × InnerWitIn))
    (outerRelOut : Set (OuterStmtOut × OuterWitOut))
    (innerRelOut : Set (InnerStmtOut × InnerWitOut))
    [lensKS : lens.IsKnowledgeSound outerRelIn innerRelIn outerRelOut innerRelOut
      (V.compatStatement lens.stmt) (fun _ _ => True)]
    (E : Extractor.RoundByRound oSpec InnerStmtIn InnerWitIn InnerWitOut pSpec WitMid)
    (K : V.KnowledgeStateFunction init impl innerRelIn innerRelOut E) :
    (V.liftContext lens.stmt).KnowledgeStateFunction init impl outerRelIn outerRelOut
      (E.liftContext lens) where
  toFun := fun k x tr w => K k (lens.stmt.proj x) tr w.2 ∨
    ∀ v, (x, lens.wit.lift (x, w.1) v) ∈ outerRelIn
  toFun_empty := by
    rintro x w (h | h)
    · exact lensKS.lift_knowledgeSound x w.1 _ True.intro (K.toFun_empty _ _ h)
    · exact h _
  toFun_next := by
    rintro m hd x tr msg w (h | h)
    · exact Or.inl (K.toFun_next m hd (lens.stmt.proj x) tr msg w.2 h)
    · exact Or.inr h
  toFun_full := by
    intro x tr w hw
    by_cases hshortcut : ∀ v, (x, lens.wit.lift (x, w) v) ∈ outerRelIn
    · exact Or.inr hshortcut
    refine Or.inl (K.toFun_full (lens.stmt.proj x) tr (lens.wit.proj (x, w)) ?_)
    have hmap : ((V.liftContext lens.stmt).run x tr : OracleComp oSpec (Option OuterStmtOut)) =
        Option.map (lens.stmt.lift x) <$>
          (V.run (lens.stmt.proj x) tr : OracleComp oSpec (Option InnerStmtOut)) := by
      exact OptionT.run_map ..
    simp only [gt_iff_lt, OptionT.prEvent_mk_pos_iff] at hw ⊢
    rw [hmap] at hw
    simp only [simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map,
      support_bind, support_map, Set.mem_iUnion, Set.mem_image, Prod.exists,
      Option.map_eq_some_iff] at hw ⊢
    obtain ⟨oy, ⟨s0, hs0, z, s, hz, heq⟩, ho⟩ := hw
    obtain ⟨y, hy, hyout⟩ := heq
    subst oy
    have hcompat : V.compatStatement lens.stmt x y := by
      refine ⟨tr, ?_⟩
      apply support_simulateQ_run'_subset impl _ s0
      simp only [StateT.run'_eq, support_map, Set.mem_image]
      exact ⟨(z, s), hz, hy⟩
    refine ⟨y, ⟨s0, hs0, z, s, hz, hy⟩, ?_⟩
    rcases lensKS.proj_knowledgeSound x y w hcompat ho with h | h
    · exact h
    · exact (hshortcut (fun v => h v True.intro)).elim

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

section FrozenInput

variable {OS OO IS IO Aux IAux OW IW : Type}

/-- Retain the complete outer adversary. Only its public output and witness are changed. -/
def frozen (P : Prover oSpec OS Aux OO OW pSpec) (x : OS) (a : Aux)
    (dummy : IO) (project : OW → IW) : Prover oSpec IS IAux IO IW pSpec where
  PrvState := P.PrvState
  input := fun _ => P.input (x, a)
  sendMessage := P.sendMessage
  receiveChallenge := P.receiveChallenge
  output := fun s => do
    let (_, w) ← P.output s
    return (dummy, project w)

theorem frozen_processRound (P : Prover oSpec OS Aux OO OW pSpec) (x : OS) (a : Aux)
    (dummy : IO) (project : OW → IW) (i : Fin n)
    (current : OracleComp (oSpec + [pSpec.Challenge]ₒ)
      (pSpec.Transcript i.castSucc × P.PrvState i.castSucc)) :
    (frozen (IS := IS) (IAux := IAux) P x a dummy project).processRound i current =
      P.processRound i current := by
  unfold Prover.processRound frozen
  rfl

theorem frozen_runToRound (P : Prover oSpec OS Aux OO OW pSpec) (x : OS) (a : Aux)
    (dummy : IO) (project : OW → IW) (i : Fin (n + 1)) (y : IS) (b : IAux) :
    (frozen P x a dummy project).runToRound i y b = P.runToRound i x a := by
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih =>
    rw [Prover.runToRound_succ, Prover.runToRound_succ, ih]
    exact frozen_processRound P x a dummy project i _

theorem frozen_run (P : Prover oSpec OS Aux OO OW pSpec) (x : OS) (a : Aux)
    (dummy : IO) (project : OW → IW) (y : IS) (b : IAux) :
    (frozen P x a dummy project).run y b =
      (fun z => (z.1, dummy, project z.2.2)) <$> P.run x a := by
  unfold Prover.run
  rw [frozen_runToRound]
  simp [frozen]

theorem frozen_runWithLog (P : Prover oSpec OS Aux OO OW pSpec) (x : OS) (a : Aux)
    (dummy : IO) (project : OW → IW) (y : IS) (b : IAux) :
    (frozen P x a dummy project).runWithLog y b =
      (fun z => ((z.1.1, dummy, project z.1.2.2), z.2)) <$> P.runWithLog x a := by
  simp only [Prover.runWithLog, frozen_run, simulateQ_map]
  rfl

end FrozenInput

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

/-- Simulation commutes with a pure post-map on an `OptionT` computation. `OptionT.run_map` is a
theorem rather than a definitional unfolding, so `simulateQ_map` cannot fire until the
`Option.map` is exposed. The general home of this lemma is VCVio. -/
private theorem simulateQ_optionT_map
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (impl : QueryImpl oSpec m)
    {α β : Type} (f : α → β) (oa : OptionT (OracleComp oSpec) α) :
    simulateQ impl (f <$> oa : OptionT (OracleComp oSpec) β)
      = Option.map f <$> simulateQ impl (oa : OracleComp oSpec (Option α)) := by
  have h : (f <$> oa : OptionT (OracleComp oSpec) β)
      = (Option.map f <$> (oa : OracleComp oSpec (Option α)) : OracleComp oSpec (Option β)) := by
    change OptionT.run (f <$> oa) = _
    exact OptionT.run_map ..
  rw [h, simulateQ_map]

/-- A pure post-map leaves the log written by a `WriterT` simulation unchanged. -/
private theorem run_simulateQ_writerT_optionT_map
    {ω : Type} [EmptyCollection ω] [Append ω] {m : Type → Type} [Monad m]
    [LawfulMonad (WriterT ω m)]
    (impl : QueryImpl oSpec (WriterT ω m))
    {α β : Type} (f : α → β) (oa : OptionT (OracleComp oSpec) α) :
    (simulateQ impl (f <$> oa : OptionT (OracleComp oSpec) β)).run
      = (fun p => (Option.map f p.1, p.2)) <$>
          (simulateQ impl (oa : OracleComp oSpec (Option α))).run := by
  rw [simulateQ_optionT_map, WriterT.run_map]

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
  have hGet {α β : Type} (f : α → β) (x : Option α) :
      (Option.map f x).getM = f <$> (x.getM : OptionT (OracleComp (oSpec +
        [pSpec.Challenge]ₒ)) α) := by
    cases x <;> simp [Option.getM, map_pure]
  unfold runWithLog
  simp [liftContext, Prover.liftContext_runWithLog, Verifier.liftContext, Verifier.run,
    run_simulateQ_writerT_optionT_map, liftM_map, hGet]

section FrozenInput

variable {OS OO IS IO Aux IAux OW IW : Type}

/-- Run the outer prover and inner verifier on their respective inputs. -/
private def jointRun (P : Prover oSpec OS Aux OO OW pSpec)
    (V : Verifier oSpec IS IO pSpec)
    (x : OS) (a : Aux) (y : IS) :
    OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ))
      ((FullTranscript pSpec × OO × OW) × IO) := do
  let pr ← P.run x a
  let out ← liftM (V.run y pr.1).run
  return (pr, ← out.getM)

private theorem outer_jointRun (P : Prover oSpec OS Aux OO OW pSpec)
    (V : Verifier oSpec IS IO pSpec)
    (l : Statement.Lens OS OO IS IO) (x : OS) (a : Aux) :
    (Reduction.mk P (V.liftContext l)).run x a =
      (fun z => (z.1, l.lift x z.2)) <$> jointRun P V x a (l.proj x) := by
  simp only [Reduction.run, jointRun, Verifier.run, Verifier.liftContext,
    bind_pure_comp, OptionT.run_map, liftM_map, bind_map_left, map_bind, Functor.map_map]
  congr 1
  funext pr
  congr 1
  funext out
  cases out <;> rfl

private theorem inner_jointRun (P : Prover oSpec OS Aux OO OW pSpec)
    (V : Verifier oSpec IS IO pSpec)
    (dummy : IO) (project : OW → IW) (x : OS) (a : Aux) (y : IS) (b : IAux) :
    (Reduction.mk (Prover.frozen P x a dummy project) V).run y b =
      (fun z => ((z.1.1, dummy, project z.1.2.2), z.2)) <$> jointRun P V x a y := by
  simp [Reduction.run, jointRun, Prover.frozen_run, map_bind]

/-- Log the queries of the outer prover and inner verifier separately. -/
private def jointRunWithLog (P : Prover oSpec OS Aux OO OW pSpec)
    (V : Verifier oSpec IS IO pSpec)
    (x : OS) (a : Aux) (y : IS) :
    OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ))
      (((FullTranscript pSpec × OO × OW) × IO) ×
        QueryLog (oSpec + [pSpec.Challenge]ₒ) × QueryLog oSpec) := do
  let (pr, plog) ← P.runWithLog x a
  let (out, vlog) ← liftM (simulateQ loggingOracle (V.run y pr.1)).run
  return ((pr, ← out.getM), plog, vlog)

private theorem outer_jointRunWithLog (P : Prover oSpec OS Aux OO OW pSpec)
    (V : Verifier oSpec IS IO pSpec)
    (l : Statement.Lens OS OO IS IO) (x : OS) (a : Aux) :
    (Reduction.mk P (V.liftContext l)).runWithLog x a =
      (fun z => ((z.1.1, l.lift x z.1.2), z.2)) <$>
        jointRunWithLog P V x a (l.proj x) := by
  have hGet (f : IO → OO) (out : Option IO) :
      (Option.map f out).getM = f <$> (out.getM :
        OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ)) IO) := by
    cases out <;> simp [Option.getM, map_pure]
  simp [Reduction.runWithLog, jointRunWithLog, Verifier.run, Verifier.liftContext,
    Reduction.run_simulateQ_writerT_optionT_map, hGet]

private theorem inner_jointRunWithLog (P : Prover oSpec OS Aux OO OW pSpec)
    (V : Verifier oSpec IS IO pSpec)
    (dummy : IO) (project : OW → IW) (x : OS) (a : Aux) (y : IS) (b : IAux) :
    (Reduction.mk (Prover.frozen P x a dummy project) V).runWithLog y b =
      (fun z => (((z.1.1.1, dummy, project z.1.1.2.2), z.1.2), z.2)) <$>
        jointRunWithLog P V x a y := by
  simp [Reduction.runWithLog, jointRunWithLog, Prover.frozen_runWithLog, map_bind]

/-- A successful joint run returns a supported verifier output. -/
private theorem mem_support_jointRun (P : Prover oSpec OS Aux OO OW pSpec)
    (V : Verifier oSpec IS IO pSpec) (x : OS) (a : Aux) (y : IS)
    (z : (FullTranscript pSpec × OO × OW) × IO)
    (hz : z ∈ support (jointRun P V x a y)) :
    z.2 ∈ support (V.run y z.1.1) := by
  simp only [jointRun, OptionT.mem_support_iff, OptionT.run_bind,
    ← monadLift_liftM_OptionT, OptionT.run_monadLift, bind_map_left,
    Option.elimM, Option.elim_some, mem_support_bind_iff] at hz
  obtain ⟨pr, _, out, hout, hz⟩ := hz
  cases out with
  | none => simp [Option.getM] at hz
  | some v =>
    have heq : z = (pr, v) := by simpa [Option.getM] using hz
    subst z
    rw [OptionT.mem_support_iff]
    exact (mem_support_liftComp_iff _ _).mp hout

/-- A successful logged joint run returns a supported verifier output. -/
private theorem mem_support_jointRunWithLog (P : Prover oSpec OS Aux OO OW pSpec)
    (V : Verifier oSpec IS IO pSpec) (x : OS) (a : Aux) (y : IS)
    (z : ((FullTranscript pSpec × OO × OW) × IO) ×
      QueryLog (oSpec + [pSpec.Challenge]ₒ) × QueryLog oSpec)
    (hz : z ∈ support (jointRunWithLog P V x a y)) :
    z.1.2 ∈ support (V.run y z.1.1.1) := by
  simp only [jointRunWithLog, OptionT.mem_support_iff, OptionT.run_bind,
    ← monadLift_liftM_OptionT, OptionT.run_monadLift, bind_map_left,
    Option.elimM, Option.elim_some, mem_support_bind_iff] at hz
  obtain ⟨pr, _, ⟨out, log⟩, hout, hz⟩ := hz
  cases out with
  | none => simp [Option.getM] at hz
  | some v =>
    have heq : z = ((pr.1, v), pr.2, log) := by simpa [Option.getM] using hz
    subst z
    have hlog := (mem_support_liftComp_iff _ _).mp hout
    have hval : some v ∈ support
        (Prod.fst <$> (simulateQ loggingOracle (V.run y pr.1.1)).run) := by
      rw [support_map]
      exact ⟨(some v, log), hlog, rfl⟩
    rw [loggingOracle.fst_map_run_simulateQ] at hval
    exact (OptionT.mem_support_iff _ _).mpr hval

end FrozenInput

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
  -- The lifted run is a pure post-map of the inner run; move that map out of the simulation so
  -- both probability events are over the same computation.
  simp only [Function.uncurry, bind_pure_comp, OptionT.run_map, simulateQ_map, StateT.run'_map',
    Statement.Lens.proj, Witness.Lens.proj, ← map_bind]
  have hMap {α β : Type} (mx : ProbComp (Option α)) (f : α → β) (p : β → Prop) :
      Pr{let x ← OptionT.mk (Option.map f <$> mx)}[p x] =
        Pr{let x ← OptionT.mk mx}[p (f x)] := by
    rw [OptionT.prEvent_mk, prEvent_map, OptionT.prEvent_mk]
    apply prEvent_congr _ _ _
    intro o
    cases o <;> rfl
  rw [hMap]
  refine prEvent_mono_of_support _ _ _ ?_
  rintro ⟨⟨tr, innerStmtOut, innerWitOut⟩, verStmtOut⟩ hSupport ⟨hRelOut, hEq⟩
  simp only at hRelOut hEq ⊢
  subst hEq
  obtain ⟨s, -, hSupport'⟩ := OptionT.mem_support_bind_mk _ _ hSupport
  rw [OptionT.mem_support_iff] at hSupport'
  have hMem := support_simulateQ_run'_subset _ _ s hSupport'
  rw [← OptionT.mem_support_iff] at hMem
  have hCompat : R.compatContext lens (outerStmtIn, outerWitIn) (innerStmtOut, innerWitOut) :=
    ⟨((tr, innerStmtOut, innerWitOut), innerStmtOut), hMem, rfl⟩
  exact ⟨lensComplete.lift_complete _ _ _ _ hCompat hRelIn hRelOut, rfl⟩

theorem liftContext_perfectCompleteness
    (h : R.perfectCompleteness init impl innerRelIn innerRelOut) :
      (R.liftContext lens).perfectCompleteness init impl outerRelIn outerRelOut := by
  exact liftContext_completeness h

end Reduction

private theorem prEvent_simulate_map {α β : Type}
    (oa : OptionT (OracleComp oSpec) α) (f : α → β) (event : β → Prop) :
    Pr{let x ← OptionT.mk do
      (simulateQ impl (f <$> oa).run).run' (← init)}[event x] =
    Pr{let x ← OptionT.mk do
      (simulateQ impl oa.run).run' (← init)}[event (f x)] := by
  simp only [OptionT.run_map, simulateQ_map, StateT.run'_map', ← map_bind]
  rw [OptionT.prEvent_mk, prEvent_map, OptionT.prEvent_mk]
  apply prEvent_congr _ _ _
  intro o
  cases o <;> rfl

namespace Verifier

/-- Lifting the reduction preserves soundness, assuming the lens satisfies its soundness
  conditions -/
theorem liftContext_soundness [Inhabited InnerStmtOut]
    {outerLangIn : Set OuterStmtIn} {outerLangOut : Set OuterStmtOut}
    {innerLangIn : Set InnerStmtIn} {innerLangOut : Set InnerStmtOut}
    {soundnessError : ℝ≥0}
    {lens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut}
    (V : Verifier oSpec InnerStmtIn InnerStmtOut pSpec)
    [lensSound : lens.IsSound outerLangIn outerLangOut innerLangIn innerLangOut
      (V.compatStatement lens)]
    (h : V.soundness init impl innerLangIn innerLangOut soundnessError) :
      (V.liftContext lens).soundness init impl outerLangIn outerLangOut soundnessError := by
  intro Aux WitOut aux P x hx
  have hInner := h Aux WitOut aux (P.frozen x aux default id) (lens.proj x)
    (lensSound.proj_sound x hx)
  refine le_trans ?_ hInner
  change Pr{let z ← OptionT.mk do
    (simulateQ (impl.addLift challengeQueryImpl :
      QueryImpl _ (StateT σ ProbComp))
      ((Reduction.mk P (V.liftContext lens)).run x aux).run).run' (← init)}[
        z.2 ∈ outerLangOut] ≤ _
  rw [Reduction.outer_jointRun, Reduction.inner_jointRun]
  rw [prEvent_simulate_map, prEvent_simulate_map]
  refine prEvent_mono_of_support _ _ _ ?_
  intro z hz hout
  obtain ⟨s, _, hs⟩ := OptionT.mem_support_bind_mk _ _ hz
  rw [OptionT.mem_support_iff] at hs
  have hmem := support_simulateQ_run'_subset _ _ s hs
  rw [← OptionT.mem_support_iff] at hmem
  have hcompat : V.compatStatement lens x z.2 :=
    ⟨z.1.1, Reduction.mem_support_jointRun P V x aux (lens.proj x) z hmem⟩
  by_contra hbad
  exact lensSound.lift_sound x z.2 hx hcompat hbad hout

/-- Lifting preserves knowledge soundness. A default inner input witness lets the lifted
extractor use the lens shortcut even when the inner extractor fails. Witness compatibility
is unrestricted because knowledge soundness existentially quantifies over the extractor. -/
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
  obtain ⟨E, hE⟩ := h
  refine ⟨E.liftContext ⟨stmtLens, witLens⟩, ?_⟩
  intro Aux x aux P
  have hInner := hE Aux (stmtLens.proj x) aux
    (P.frozen x aux default (fun w => witLens.proj (x, w)))
  let joint := Reduction.jointRunWithLog P V x aux (stmtLens.proj x)
  let exec : OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ))
      ((((FullTranscript pSpec × OuterStmtOut × OuterWitOut) × InnerStmtOut) ×
        QueryLog (oSpec + [pSpec.Challenge]ₒ) × QueryLog oSpec) × Option InnerWitIn) := do
    let z ← joint
    let w ← liftM (E (stmtLens.proj x) (witLens.proj (x, z.1.1.2.2))
      z.1.1.1 z.2.1.fst z.2.2).run
    return (z, w)
  have hOuterRun : (do
      let z ← (Reduction.mk P (V.liftContext stmtLens)).runWithLog x aux
      let w ← liftM ((E.liftContext ⟨stmtLens, witLens⟩) x z.1.1.2.2
        z.1.1.1 z.2.1.fst z.2.2).run
      return (x, w, z.1.2, z.1.1.2.2)) =
      (fun z => (x, some (witLens.lift (x, z.1.1.1.2.2) (z.2.getD default)),
        stmtLens.lift x z.1.1.2, z.1.1.1.2.2)) <$> exec := by
    simp [exec, joint, Reduction.outer_jointRunWithLog, Extractor.Straightline.liftContext,
      OptionT.run_map, liftM_map, map_bind]
  have hInnerRun : (do
      let z ← (Reduction.mk
        (P.frozen x aux default (fun w => witLens.proj (x, w))) V).runWithLog
          (stmtLens.proj x) aux
      let w ← liftM (E (stmtLens.proj x) z.1.1.2.2 z.1.1.1 z.2.1.fst z.2.2).run
      return (stmtLens.proj x, w, z.1.2, z.1.1.2.2)) =
      (fun z => (stmtLens.proj x, z.2, z.1.1.2,
        witLens.proj (x, z.1.1.1.2.2))) <$> exec := by
    simp [exec, joint, Reduction.inner_jointRunWithLog, map_bind]
  dsimp only at hInner ⊢
  rw [hOuterRun]
  rw [hInnerRun] at hInner
  rw [prEvent_simulate_map]
  rw [prEvent_simulate_map] at hInner
  refine le_trans ?_ hInner
  refine prEvent_mono_of_support _ _ _ ?_
  intro z hz hbad
  obtain ⟨s, _, hs⟩ := OptionT.mem_support_bind_mk _ _ hz
  rw [OptionT.mem_support_iff] at hs
  have hmem := support_simulateQ_run'_subset _ _ s hs
  rw [← OptionT.mem_support_iff] at hmem
  have hjoint : z.1 ∈ support joint := by
    simp only [exec, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hmem
    obtain ⟨a, ha, b, _, hab⟩ := hmem
    cases hab
    exact ha
  have hcompat : V.compatStatement stmtLens x z.1.1.2 :=
    ⟨z.1.1.1.1, Reduction.mem_support_jointRunWithLog P V x aux (stmtLens.proj x) z.1 hjoint⟩
  rcases lensKS.proj_knowledgeSound x z.1.1.2 z.1.1.1.2.2 hcompat hbad.2 with
    hAccept | hShortcut
  · refine ⟨?_, hAccept⟩
    intro w hw hin
    have hw' : z.2 = some w := hw
    exact hbad.1 (witLens.lift (x, z.1.1.1.2.2) (z.2.getD default)) rfl (by
      simpa [hw'] using lensKS.lift_knowledgeSound x z.1.1.1.2.2 w True.intro hin)
  · exact False.elim (hbad.1 _ rfl (hShortcut (z.2.getD default) True.intro))

/-- Context lifting preserves round-by-round soundness at every fixed prefix with the same error. -/
theorem liftContext_rbrSoundness
    {outerLangIn : Set OuterStmtIn} {outerLangOut : Set OuterStmtOut}
    {innerLangIn : Set InnerStmtIn} {innerLangOut : Set InnerStmtOut}
    {rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0}
    {lens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut}
    (V : Verifier oSpec InnerStmtIn InnerStmtOut pSpec)
    [lensSound : lens.IsSound outerLangIn outerLangOut innerLangIn innerLangOut
      (V.compatStatement lens)]
    (h : V.rbrSoundness init impl innerLangIn innerLangOut rbrSoundnessError) :
      (V.liftContext lens).rbrSoundness init impl outerLangIn outerLangOut
        rbrSoundnessError := by
  obtain ⟨S, hbound⟩ := h
  refine ⟨S.liftContext lens V outerLangIn outerLangOut innerLangIn innerLangOut, ?_⟩
  intro x hx i tr
  refine le_trans (prEvent_mono _ _ _ ?_)
    (hbound (lens.proj x) (lensSound.proj_sound x hx) i tr)
  intro c hc
  simpa only [StateFunction.liftContext, hx, false_or] using hc

/-- Context lifting preserves the named extractor and knowledge state at every fixed prefix,
with the same error. -/
theorem liftContext_rbrKnowledgeSoundnessWith
    {outerRelIn : Set (OuterStmtIn × OuterWitIn)} {outerRelOut : Set (OuterStmtOut × OuterWitOut)}
    {innerRelIn : Set (InnerStmtIn × InnerWitIn)} {innerRelOut : Set (InnerStmtOut × InnerWitOut)}
    {rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0}
    {stmtLens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut}
    {witLens : Witness.InvLens OuterStmtIn OuterWitIn OuterWitOut InnerWitIn InnerWitOut}
    (V : Verifier oSpec InnerStmtIn InnerStmtOut pSpec)
    [lensKS : Extractor.Lens.IsKnowledgeSound outerRelIn innerRelIn outerRelOut innerRelOut
      (V.compatStatement stmtLens) (fun _ _ => True) ⟨stmtLens, witLens⟩]
    {WitMid : Fin (n + 1) → Type}
    (E : Extractor.RoundByRound oSpec InnerStmtIn InnerWitIn InnerWitOut pSpec WitMid)
    (K : V.KnowledgeStateFunction init impl innerRelIn innerRelOut E)
    (h : V.rbrKnowledgeSoundnessWith init impl innerRelIn innerRelOut
      WitMid E K rbrKnowledgeError) :
      (V.liftContext stmtLens).rbrKnowledgeSoundnessWith init impl outerRelIn outerRelOut
        (fun k => OuterWitOut × WitMid k) (E.liftContext ⟨stmtLens, witLens⟩)
        (K.liftContext ⟨stmtLens, witLens⟩ V outerRelIn innerRelIn outerRelOut innerRelOut E)
        rbrKnowledgeError := by
  intro x i tr
  refine le_trans (prEvent_mono _ _ _ ?_) (h (stmtLens.proj x) i tr)
  rintro c ⟨⟨w, v⟩, hprev, hnext⟩
  change ¬ (K _ _ _ _ ∨ _) at hprev
  change K _ _ _ v ∨ _ at hnext
  exact ⟨v, (fun hv => hprev (Or.inl hv)),
    hnext.resolve_right (fun hs => hprev (Or.inr hs))⟩

/-- Context lifting preserves round-by-round knowledge soundness at every fixed prefix
with the same error. -/
theorem liftContext_rbrKnowledgeSoundness
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
  obtain ⟨WitMid, E, K, hbound⟩ := h
  exact ⟨(fun k => OuterWitOut × WitMid k), E.liftContext ⟨stmtLens, witLens⟩,
    K.liftContext ⟨stmtLens, witLens⟩ V outerRelIn innerRelIn outerRelOut innerRelOut E,
    V.liftContext_rbrKnowledgeSoundnessWith E K hbound⟩

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
    left
    change f.eval r = t'
    change (p * q).eval r = t' at h'
    simpa [← h] using h'
  lift_knowledgeSound := fun ⟨p, q, t⟩ _ _ _ hInner => by
    have hInner' : (p * q).eval 0 + (p * q).eval 1 = t := by
      simpa [innerRelIn_Test, testLensE, testStmtLens] using hInner
    simpa [outerRelIn_Test] using hInner'

end

end Test
