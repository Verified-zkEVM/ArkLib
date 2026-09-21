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

section LiftRoundByRoundExtractor

namespace Extractor.RoundByRound

/-! ### Lifting a round-by-round extractor along an extractor lens

A round-by-round extractor carries a *ladder* of intermediate witness types `WitMid`, pinned at
the bottom by `eqIn : WitMid 0 = WitIn`. When the extractor is transported along an
`Extractor.Lens`, the bottom of the ladder must land in `OuterWitIn` rather than `InnerWitIn`,
so the ladder itself has to be reindexed: keeping `WitMid` fixed is not merely hard, it is
impossible (`no_liftContext_with_shared_witMid` below).

The reindexing is forced, not chosen. The witness inverse-lens supplies
`lift : OuterStmtIn × OuterWitOut → InnerWitIn → OuterWitIn`, so producing the bottom rung needs
the outer *output* witness; but only `extractOut`, at the top of the ladder, ever receives one.
Hence every positive rung must carry it, and `OuterWitOut × WitMid k` is the smallest carrier
that does. -/

/-- Any outer round-by-round extractor over the *same* mid-witness family as the inner one forces
the two input-witness types to coincide, since both are pinned to `WitMid 0` by `eqIn`. -/
theorem sharedWitMid_forces_witIn_eq {WitMid : Fin (n + 1) → Type}
    (E  : Extractor.RoundByRound oSpec InnerStmtIn InnerWitIn InnerWitOut pSpec WitMid)
    (E' : Extractor.RoundByRound oSpec OuterStmtIn OuterWitIn OuterWitOut pSpec WitMid) :
    InnerWitIn = OuterWitIn :=
  E.eqIn.symm.trans E'.eqIn

private theorem punit_ne_bool (h : PUnit = Bool) : False := by
  have h1 : (cast h.symm true : PUnit) = cast h.symm false := Subsingleton.elim _ _
  have h2 : (true : Bool) = false := by have := congrArg (cast h) h1; simp at this
  exact Bool.noConfusion h2

/-- Separating data for the no-go: a lens whose inner input witness is `PUnit` and whose outer
input witness is `Bool`. Named so that the refutation below and the inhabitation result
`reindexed_inhabited_on_refuting_data` provably speak about the *same* data. -/
def refutingLens : Extractor.Lens PUnit PUnit PUnit PUnit Bool PUnit PUnit PUnit :=
  { stmt := ⟨fun _ => .unit, fun _ _ => .unit⟩
    wit  := ⟨fun _ => .unit, fun _ _ => true⟩ }

/-- The inner extractor of the separating data. -/
def refutingInner :
    Extractor.RoundByRound oSpec PUnit PUnit PUnit pSpec (fun _ : Fin (n + 1) => PUnit) :=
  { eqIn := rfl, extractMid := fun _ _ _ _ => .unit, extractOut := fun _ _ _ => .unit }

/-- **There is no context-lifting operation for round-by-round extractors that keeps the
mid-witness family fixed.** On `refutingLens`/`refutingInner`, `sharedWitMid_forces_witIn_eq`
becomes `PUnit = Bool`. This is why `liftContext` below reindexes the family. -/
theorem no_liftContext_with_shared_witMid
    (hLift : ∀ {OWI IWI : Type} {WitMid : Fin (n + 1) → Type},
        Extractor.Lens PUnit PUnit PUnit PUnit OWI PUnit IWI PUnit →
        Extractor.RoundByRound oSpec PUnit IWI PUnit pSpec WitMid →
        Extractor.RoundByRound oSpec PUnit OWI PUnit pSpec WitMid) :
    False :=
  punit_ne_bool (hLift refutingLens (refutingInner (oSpec := oSpec) (pSpec := pSpec))).eqIn

/-- The reindexed mid-witness family: the bottom rung becomes the outer input witness, and every
positive rung additionally carries the outer output witness that the bottom rung consumes. -/
def liftWitMid (OuterWitIn OuterWitOut : Type) {n : ℕ} (WitMid : Fin (n + 1) → Type)
    (k : Fin (n + 1)) : Type :=
  match k.val with
  | 0     => OuterWitIn
  | _ + 1 => OuterWitOut × WitMid k

@[simp] theorem liftWitMid_zero (OuterWitIn OuterWitOut : Type) (WitMid : Fin (n + 1) → Type) :
    liftWitMid OuterWitIn OuterWitOut WitMid 0 = OuterWitIn := rfl

@[simp] theorem liftWitMid_succ (OuterWitIn OuterWitOut : Type) (WitMid : Fin (n + 1) → Type)
    (i : Fin n) :
    liftWitMid OuterWitIn OuterWitOut WitMid i.succ = (OuterWitOut × WitMid i.succ) := rfl

variable {WitMid : Fin (n + 1) → Type}
  (lens : Extractor.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
  (E : Extractor.RoundByRound oSpec InnerStmtIn InnerWitIn InnerWitOut pSpec WitMid)

/-- Transport an inner mid-witness at rung `k` into the lifted family. At the bottom rung this is
where the witness inverse-lens does its work; at every positive rung it threads through the outer
output witness that the bottom rung will need. -/
def rung (outerCtx : OuterStmtIn × OuterWitOut) :
    (k : Fin (n + 1)) → WitMid k → liftWitMid OuterWitIn OuterWitOut WitMid k :=
  Fin.cases
    (motive := fun k => WitMid k → liftWitMid OuterWitIn OuterWitOut WitMid k)
    (fun w => lens.wit.lift outerCtx (E.eqIn ▸ w))
    (fun _ w => (outerCtx.2, w))

@[simp] theorem rung_zero (outerCtx : OuterStmtIn × OuterWitOut) (w : WitMid 0) :
    rung lens E outerCtx 0 w = lens.wit.lift outerCtx (E.eqIn ▸ w) := rfl

@[simp] theorem rung_succ (outerCtx : OuterStmtIn × OuterWitOut) (i : Fin n)
    (w : WitMid i.succ) :
    rung lens E outerCtx i.succ w = (outerCtx.2, w) := rfl

/-- The outer round-by-round extractor after lifting invokes the inner extractor on the projected
input, and lifts the output. The mid-witness family is reindexed by `liftWitMid`; see
`no_liftContext_with_shared_witMid` for why it cannot be kept fixed. -/
def liftContext :
      Extractor.RoundByRound oSpec OuterStmtIn OuterWitIn OuterWitOut pSpec
        (liftWitMid OuterWitIn OuterWitOut WitMid) where
  eqIn := rfl
  extractMid := fun m outerStmtIn tr w =>
    rung lens E (outerStmtIn, (w : OuterWitOut × WitMid m.succ).1) m.castSucc
      (E.extractMid m (lens.stmt.proj outerStmtIn) tr (w : OuterWitOut × WitMid m.succ).2)
  extractOut := fun outerStmtIn tr outerWitOut =>
    rung lens E (outerStmtIn, outerWitOut) (.last n)
      (E.extractOut (lens.stmt.proj outerStmtIn) tr (lens.wit.proj (outerStmtIn, outerWitOut)))

/-- The lifted `extractMid` really calls `E.extractMid` on the lens-projected statement, and
really threads the carried outer output witness. -/
theorem liftContext_extractMid (m : Fin n) (s : OuterStmtIn) (tr : Transcript m.succ pSpec)
    (w : OuterWitOut × WitMid m.succ) :
    (liftContext lens E).extractMid m s tr w
      = rung lens E (s, w.1) m.castSucc (E.extractMid m (lens.stmt.proj s) tr w.2) := rfl

/-- The lifted `extractOut` really calls `E.extractOut` on the lens-projected statement and the
lens-projected output witness, and seeds the ladder with the outer output witness. -/
theorem liftContext_extractOut (s : OuterStmtIn) (tr : FullTranscript pSpec) (wo : OuterWitOut) :
    (liftContext lens E).extractOut s tr wo
      = rung lens E (s, wo) (.last n)
          (E.extractOut (lens.stmt.proj s) tr (lens.wit.proj (s, wo))) := rfl

/-- **The no-go is sharp.** On exactly the data that refutes the shared-family signature, the
reindexed signature is inhabited. So `no_liftContext_with_shared_witMid` records an obstruction
in the *indexing*, not an accidental emptiness of the surrounding types.

Since `rbrKnowledgeSoundness` quantifies existentially over the mid-witness family
(`Security/RoundByRound.lean`), reindexing costs its consumers nothing. -/
theorem reindexed_inhabited_on_refuting_data :
    Nonempty (Extractor.RoundByRound oSpec PUnit Bool PUnit pSpec
      (liftWitMid Bool PUnit (fun _ : Fin (n + 1) => PUnit))) :=
  ⟨liftContext refutingLens (refutingInner (oSpec := oSpec) (pSpec := pSpec))⟩

end Extractor.RoundByRound

end LiftRoundByRoundExtractor

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

/-- **`Statement.Lens.IsComplete` is necessary for the lifted state function, not just
sufficient.**

The lifted `toFun` is `stF ∘ lens.proj`, so its `toFun_empty` obligation reads
`stmt ∈ outerLangIn ↔ stF.toFun 0 (lens.proj stmt) default`.  Chaining with the *inner* state
function's own `toFun_empty` forces `stmt ∈ outerLangIn ↔ lens.proj stmt ∈ innerLangIn`, whose
forward half is exactly `proj_complete`.

So any state function on `V.liftContext lens` whose `toFun` is the projected inner one *exhibits*
the completeness datum: no hypothesis weaker than `Statement.Lens.IsComplete` can discharge it.
With `Statement.Lens.isSound_not_implies_isComplete` (soundness does not supply it) this makes the
instance argument on `Verifier.StateFunction.liftContext` the minimal faithful repair rather than a
convenient over-assumption. -/
theorem Verifier.StateFunction.isComplete_of_liftedToFunEmpty
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {lens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut}
    {V : Verifier oSpec InnerStmtIn InnerStmtOut pSpec}
    {outerLangIn : Set OuterStmtIn} {innerLangIn : Set InnerStmtIn}
    {innerLangOut : Set InnerStmtOut}
    (stF : V.StateFunction init impl innerLangIn innerLangOut)
    (hEmpty : ∀ stmt : OuterStmtIn,
      stmt ∈ outerLangIn ↔ stF.toFun 0 (lens.proj stmt) default) :
    lens.IsComplete outerLangIn innerLangIn :=
  ⟨fun stmt hs => (stF.toFun_empty (lens.proj stmt)).mpr ((hEmpty stmt).mp hs)⟩

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
    [lensComplete : lens.IsComplete outerLangIn innerLangIn]
    (stF : V.StateFunction init impl innerLangIn innerLangOut) :
      (V.liftContext lens).StateFunction init impl outerLangIn outerLangOut
where
  toFun := fun m outerStmtIn transcript =>
    stF m (lens.proj outerStmtIn) transcript
  toFun_empty := fun stmt =>
    (Statement.Lens.mem_iff_proj_mem lensSound.proj_sound stmt).trans
      (stF.toFun_empty (lens.proj stmt))
  toFun_next := fun m hDir outerStmtIn transcript hStmt msg =>
    stF.toFun_next m hDir (lens.proj outerStmtIn) transcript hStmt msg
  toFun_full := fun outerStmtIn transcript hStmt => by
    have h := stF.toFun_full (lens.proj outerStmtIn) transcript hStmt
    have hbridge :
        ((V.liftContext lens).verify outerStmtIn transcript :
            OracleComp oSpec (Option OuterStmtOut))
          = Option.map (lens.lift outerStmtIn) <$>
              (V.verify (lens.proj outerStmtIn) transcript :
                OracleComp oSpec (Option InnerStmtOut)) := by
      show OptionT.run ((V.liftContext lens).verify outerStmtIn transcript) = _
      rw [Verifier.liftContext]
      exact OptionT.run_map ..
    simp only [Verifier.run] at h ⊢
    rw [hbridge]
    simp at h ⊢
    intro outerStmtOut s0 hs0 innerStmtOut s hMem hEq
    subst hEq
    have hRun' : some innerStmtOut ∈ support ((simulateQ impl
        (V.verify (lens.proj outerStmtIn) transcript)).run' s0) := by
      simp only [StateT.run'_eq, support_map, Set.mem_image]
      exact ⟨(some innerStmtOut, s), hMem, rfl⟩
    have hSupp := support_simulateQ_run'_subset impl
      (V.verify (lens.proj outerStmtIn) transcript) s0 hRun'
    refine lensSound.lift_sound outerStmtIn innerStmtOut ⟨transcript, ?_⟩
      (h innerStmtOut s0 hs0 s hMem)
    exact hSupp

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

/-- **A pure post-map passes straight through any simulation.**  `simulateQ impl` is the monad
morphism induced by `impl`; the underlying natural transformation commutes with the functor
action, so mapping a function over a computation and then simulating is the same as simulating
and then mapping.

Stated for `OptionT (OracleComp spec)` because that is the monad a `Verifier` — and a whole
`Reduction` — runs in.  `OptionT`'s `<$>` is bind-based, so
`(f <$> oa).run = Option.map f <$> oa.run` is a *theorem* (`OptionT.run_map`), not definitional,
and the `Option.map` has to be exposed before the `@[simp]` lemma `simulateQ_map` can fire.  That
defeq bridge is why this cannot be discharged by `simp` alone: under `instances` transparency
`f <$> oa` does not present as an `OracleComp`.

This is the shared root of the two transport facts below: lifting along a context lens is a pure
post-map on the *output* of a reduction, hence it commutes with whatever the reduction was
simulated through — it can change neither what was queried (`WriterT`, see
`run_simulateQ_writerT_optionT_map` and `Reduction.liftContext_runWithLog`) nor what was reachable
(`StateT`, see `Reduction.liftContext_completeness`, where the same commutation is done inline:
there the `OptionT.run` is already exposed by unfolding `completeness`, so `simp only` fires on
the primitives directly and a named `StateT` corollary would be pure API noise).
Its proper long-term home is VCVio; it is kept here only so that this file's import graph is
unchanged. -/
theorem simulateQ_optionT_map
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (impl : QueryImpl oSpec m)
    {α β : Type} (f : α → β) (oa : OptionT (OracleComp oSpec) α) :
    simulateQ impl (f <$> oa : OptionT (OracleComp oSpec) β)
      = Option.map f <$> simulateQ impl (oa : OracleComp oSpec (Option α)) := by
  have h : (f <$> oa : OptionT (OracleComp oSpec) β)
      = (Option.map f <$> (oa : OracleComp oSpec (Option α)) : OracleComp oSpec (Option β)) := by
    show OptionT.run (f <$> oa) = _
    exact OptionT.run_map ..
  rw [h, simulateQ_map]

/-- **Logging is natural in the value: a pure post-map leaves the written log untouched.**
The `WriterT` instance of `simulateQ_optionT_map`.  Note the writer is the
`EmptyCollection`/`Append` one, not the `Monoid` one: VCVio deliberately declines a
`Monoid (QueryLog spec)` instance so that the `Append`-based `Monad (WriterT _ _)` is the one that
applies (`VCVio/OracleComp/QueryTracking/Structures.lean`).

This is the fact that makes `Reduction.liftContext_runWithLog` provable: lifting a verifier along
a context lens is a pure post-map on its *output*, hence cannot change what the verifier
*queried*.  It is stated for an arbitrary `QueryImpl _ (WriterT ω m)` rather than for
`loggingOracle`, because the proof never uses anything specific to logging. -/
theorem run_simulateQ_writerT_optionT_map
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
  unfold runWithLog
  simp [liftContext, Prover.liftContext_runWithLog, Verifier.liftContext, Verifier.run]
  -- The prover half is `Prover.liftContext_runWithLog`.  What remains is the *verifier* half,
  -- which `liftContext_run` never had to face: `runWithLog` wraps the verifier in
  -- `simulateQ loggingOracle`, so the lens lift is trapped *inside* the logging simulation while
  -- the right-hand side applies it *after*.  Commuting the two is exactly naturality of the
  -- monad morphism `simulateQ loggingOracle` in the value component — and it is what certifies
  -- that lifting a context does not change what the verifier queried.
  congr 1
  funext a
  rw [run_simulateQ_writerT_optionT_map loggingOracle, liftM_map]
  rw [map_eq_bind_pure_comp, bind_assoc]
  congr 1
  funext p
  simp only [Function.comp_apply, pure_bind]
  cases p.1 <;> simp [Option.getM, map_pure]

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
  -- **Reachability is natural in the value.**  `liftContext_run` exhibits the lifted run as a
  -- *pure post-map* of the inner run, but the completeness predicate is evaluated on
  -- `(simulateQ impl _).run' s`, so that post-map starts out trapped *inside* the simulation.
  -- `OptionT.run_map`/`simulateQ_map`/`StateT.run'_map'` commute it out -- the `StateT` analogue
  -- of the `WriterT` naturality used by `liftContext_runWithLog`; both are instances of
  -- `simulateQ_optionT_map`.  Only then do the two probability events share a base computation.
  simp only [Function.uncurry, bind_pure_comp, OptionT.run_map, simulateQ_map, StateT.run'_map',
    Statement.Lens.proj, Witness.Lens.proj, ← map_bind]
  refine le_trans ?_ (le_of_eq (OptionT.probEvent_eq_of_run_map_eq _ _ _ _ rfl).symm)
  refine probEvent_mono ?_
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
    -- Forced by `Verifier.StateFunction.liftContext`: constructing the lifted state function
    -- needs `outerLangIn` to be *exactly* the preimage of `innerLangIn`, which soundness alone
    -- does not give (see `Statement.Lens.eq_preimage_of_projSound_of_isComplete`).
    [lensComplete : lens.IsComplete outerLangIn innerLangIn]
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
