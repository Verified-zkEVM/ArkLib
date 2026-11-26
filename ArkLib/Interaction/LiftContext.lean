/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Security.RoundByRound

/-!
# Lifting reductions into a larger context

A context lens relates an outer reduction's inputs and outputs to an inner reduction's. Its
statement part projects the outer input statement to the inner one and lifts an inner output
statement back. Its witness part does the same for the prover's input witness and output.

* `Verifier.liftContext` decides with the inner verifier on the projected statement and lifts
  an accepted output. The decision stays passive.
* `Prover.liftContext` runs the inner prover on the projected input and maps its output. It
  changes no node slot.
* `Verifier.liftContext_run` and `Reduction.liftContext_runOutcome` state that a lifted run is a
  post-map of the inner run on the projected input. The verifier law holds for every prover.

Lens conditions are `Prop`-valued structures passed explicitly. Each is guarded by a
compatibility predicate on inner output statements, `Verifier.Compatible` for plain
verifiers, so the oracle layer reuses them with its own predicate.

* `StatementLens.IsSound` transfers soundness and round-by-round soundness.
* `ContextLens.IsComplete` transfers completeness at the same error.
* `ExtractorLens.IsKnowledgeSound` transfers round-by-round knowledge soundness.

The round-by-round transfers are first proved for the generic predicates
(`rbrSoundness_liftContext` and `rbrKnowledgeSoundness_liftContext`) from an implication
between the leaf acceptance predicates. See `docs/design/interaction-layer/lift-context.md`.
-/

@[expose] public section

universe u uA

namespace Interaction
open PFunctor FreeM TwoParty.Lens OracleComp
open scoped ENNReal

/-! ### Lenses -/

/-- Project an outer input statement to an inner one, and lift an inner output statement at a
shape path back to an outer one. Output statement types are indexed by the shape path. -/
structure StatementLens {P : PFunctor.{uA, 0}} (s : FreeM P Unit)
    (OuterIn : Type) (InnerIn : Type) (OuterOut : Path s → Type)
    (InnerOut : Path s → Type) where
  /-- The inner input statement. -/
  proj : OuterIn → InnerIn
  /-- The outer output statement from the outer input and an inner output at a path. -/
  lift : OuterIn → (p : Path s) → InnerOut p → OuterOut p

/-- Project an outer input witness to an inner one, and lift the inner prover's output on a
completed transcript back to an outer one. -/
structure WitnessLens {P : PFunctor.{uA, 0}} (l : PFunctor.Lens P rolePoly0)
    (s : FreeM P Unit) (OuterIn : Type) (OuterWit : Type) (InnerWit : Type)
    (OuterOut : Transcript l s → Type) (InnerOut : Transcript l s → Type) where
  /-- The inner input witness. -/
  proj : OuterIn → OuterWit → InnerWit
  /-- The outer prover output from the outer input and the inner prover output. -/
  lift : OuterIn → OuterWit → (tr : Transcript l s) → InnerOut tr → OuterOut tr

/-- A statement lens and a witness lens over the same outer input statement. -/
structure ContextLens {P : PFunctor.{uA, 0}} (l : PFunctor.Lens P rolePoly0)
    (s : FreeM P Unit) (OuterIn : Type) (InnerIn : Type)
    (OuterWit : Type) (InnerWit : Type)
    (OuterStmtOut InnerStmtOut : Path s → Type)
    (OuterOut InnerOut : Transcript l s → Type) where
  /-- The statement part. -/
  stmt : StatementLens s OuterIn InnerIn OuterStmtOut InnerStmtOut
  /-- The witness part. -/
  wit : WitnessLens l s OuterIn OuterWit InnerWit OuterOut InnerOut

/-- A statement lens with the maps that knowledge extraction runs backwards: an outer output
witness projects to an inner one, and an inner input witness lifts to an outer one using the
completed transcript and the outer output witness. -/
structure ExtractorLens {P : PFunctor.{uA, 0}} (l : PFunctor.Lens P rolePoly0)
    (s : FreeM P Unit) (OuterIn : Type) (InnerIn : Type)
    (OuterStmtOut InnerStmtOut : Path s → Type)
    (OuterWitIn : OuterIn → Type) (InnerWitIn : InnerIn → Type)
    (OuterWitOut : OuterIn → Transcript l s → Type)
    (InnerWitOut : InnerIn → Transcript l s → Type) where
  /-- The statement part. -/
  stmt : StatementLens s OuterIn InnerIn OuterStmtOut InnerStmtOut
  /-- The inner output witness extracted from an outer one. -/
  witOutProj : ∀ x tr, OuterWitOut x tr → InnerWitOut (stmt.proj x) tr
  /-- The outer input witness built from an inner one. -/
  witInLift : ∀ x tr, OuterWitOut x tr → InnerWitIn (stmt.proj x) → OuterWitIn x

/-! ### Lifting -/

/-- Run the inner prover on the projected input and map its output through the witness lens.
Every node slot is the inner prover's slot. -/
def Prover.liftContext {P : PFunctor.{uA, 0}} {l : PFunctor.Lens P rolePoly0}
    {ι : Type} {ambient : OracleSpec.{0, 0} ι} {s : FreeM P Unit}
    {OuterIn : Type} {InnerIn : Type} {OuterWit : Type} {InnerWit : Type}
    {OuterOut InnerOut : Transcript l s → Type}
    (proj : OuterIn → InnerIn) (lens : WitnessLens l s OuterIn OuterWit InnerWit OuterOut InnerOut)
    (prover : InnerIn → InnerWit → Prover l ambient s InnerOut)
    (stmt : OuterIn) (wit : OuterWit) : Prover l ambient s OuterOut :=
  Strategy.mapOutput (lens.lift stmt wit) (prover (proj stmt) (lens.proj stmt wit))

/-- Decide with the inner verifier on the projected statement and lift an accepted output. -/
def Verifier.liftContext {ι : Type} {ambient : OracleSpec.{0, 0} ι} {s : Protocol}
    {OuterIn : Type} {InnerIn : Type} {OuterOut InnerOut : Path s → Type}
    (lens : StatementLens s OuterIn InnerIn OuterOut InnerOut)
    (V : Verifier ambient s InnerIn InnerOut) : Verifier ambient s OuterIn OuterOut where
  decide stmt p v := lens.lift stmt p <$> V.decide (lens.proj stmt) p v

/-- Lift both parties of a reduction along a context lens. -/
def Reduction.liftContext {ι : Type} {ambient : OracleSpec.{0, 0} ι} {s : Protocol}
    {OuterIn : Type} {InnerIn : Type} {OuterWit : Type} {InnerWit : Type}
    {OuterStmtOut InnerStmtOut : Path s → Type}
    {OuterOut InnerOut : Transcript plainSig s → Type}
    (lens : ContextLens plainSig s OuterIn InnerIn OuterWit InnerWit OuterStmtOut InnerStmtOut
      OuterOut InnerOut)
    (R : Reduction ambient s InnerIn InnerWit InnerStmtOut InnerOut) :
    Reduction ambient s OuterIn OuterWit OuterStmtOut OuterOut where
  prover := Prover.liftContext lens.stmt.proj lens.wit R.prover
  verifier := R.verifier.liftContext lens.stmt

/-! ### Run laws -/

/-- Simulating a prover commutes with mapping its output. -/
theorem Prover.simulate_mapOutput {P : PFunctor.{uA, 0}} {l : PFunctor.Lens P rolePoly0}
    {ι : Type} {ambient : OracleSpec.{0, 0} ι} {m : Type → Type} [Monad m] [LawfulMonad m]
    (impl : QueryImpl ambient m) :
    (s : FreeM P Unit) → {A B : Transcript l s → Type} →
    (f : ∀ tr, A tr → B tr) → (p : Prover l ambient s A) →
    Prover.simulate impl (Strategy.mapOutput f p) = Strategy.mapOutput f (Prover.simulate impl p)
  | .pure _, _, _, f, p => by
    change simulateQ impl (f _ <$> p) = f _ <$> simulateQ impl p
    rw [simulateQ_map]
  | .liftBind a rest, _, _, f, p => by
    rw [Prover.simulate_node, Prover.simulate_node]
    change _ <$> simulateQ impl (Choice.map .focal (owner l a) _ <$> p) =
      Choice.map .focal (owner l a) _ <$> (_ <$> simulateQ impl p)
    rw [simulateQ_map, Functor.map_map, Functor.map_map]
    refine congrArg (· <$> _) (funext fun v => ?_)
    refine (congrFun (Choice.map_comp _ _ _ _) v).trans ?_
    refine Eq.trans ?_ (congrFun (Choice.map_comp _ _ _ _) v).symm
    exact congrArg (fun g => Choice.map .focal (owner l a) g v)
      (funext fun x => funext fun r => Prover.simulate_mapOutput impl _ (fun tr => f ⟨x, tr⟩) r)

/-- Running a focal strategy with a mapped output maps the focal output of the run. -/
theorem run_mapOutput_focal {P : PFunctor.{uA, u}} {l : PFunctor.Lens P rolePoly.{u}}
    {m : Type u → Type u} [Monad m] [LawfulMonad m] (s : FreeM P PUnit.{u + 1})
    {A B C : PathAlong l s → Type u} (f : ∀ tr, A tr → B tr) (p : Focal l m s A)
    (c : Counterpart l m s C) :
    TwoParty.Lens.run s (Strategy.mapOutput f p) c =
      (fun r => ⟨r.1, f r.1 r.2.1, r.2.2⟩) <$> TwoParty.Lens.run s p c := by
  have h := run_mapOutput_mapOutput s f (fun _ x => x) p c
  rw [Strategy.mapOutput_id] at h
  rw [h, map_eq_bind_pure_comp]
  refine bind_congr fun r => ?_
  obtain ⟨tr, a, b⟩ := r
  rfl

/-- Running against a prover with a mapped output maps the prover output of the outcome. -/
theorem Verifier.run_mapOutput {ι : Type} {ambient : OracleSpec.{0, 0} ι}
    {s : Protocol} {S : Type} {T : Path s → Type} {A B : Transcript plainSig s → Type}
    (V : Verifier ambient s S T) (stmt : S) (f : ∀ tr, A tr → B tr)
    (p : Prover plainSig ambient s A) :
    V.run stmt (Strategy.mapOutput f p) =
      (fun obs => ⟨obs.1, f obs.1 obs.2.1, obs.2.2⟩) <$> V.run stmt p := by
  unfold Verifier.run
  rw [Prover.simulate_mapOutput]
  have h := run_mapOutput_mapOutput s f (fun _ x => x)
    (p.simulate (QueryImpl.ofLift ambient (OracleComp (ambient + challengeSpec plainSig s))))
    (sampler plainSig s (QueryImpl.ofLift (challengeSpec plainSig s)
      (OracleComp (ambient + challengeSpec plainSig s))))
  rw [Strategy.mapOutput_id] at h
  rw [h]
  simp only [map_eq_bind_pure_comp, bind_assoc]
  refine bind_congr fun r => ?_
  obtain ⟨tr, a, b⟩ := r
  simp

/-- A lifted verifier's run against any prover is the inner run on the projected statement,
with an accepted output lifted. -/
theorem Verifier.liftContext_run {ι : Type} {ambient : OracleSpec.{0, 0} ι}
    {s : Protocol} {OuterIn : Type} {InnerIn : Type}
    {OuterOut InnerOut : Path s → Type} {Out : Transcript plainSig s → Type}
    (lens : StatementLens s OuterIn InnerIn OuterOut InnerOut)
    (V : Verifier ambient s InnerIn InnerOut) (stmt : OuterIn) (p : Prover plainSig ambient s Out) :
    (V.liftContext lens).run stmt p =
      (fun obs => ⟨obs.1, obs.2.1, obs.2.2.map (lens.lift stmt obs.1.path)⟩) <$>
        V.run (lens.proj stmt) p := by
  simp only [Verifier.run, Verifier.liftContext, map_eq_bind_pure_comp, bind_assoc]
  refine bind_congr fun r => ?_
  obtain ⟨tr, out, ⟨⟩⟩ := r
  simp only [OptionT.run_bind, Option.elimM, liftComp_bind, bind_assoc]
  refine bind_congr fun o => ?_
  cases o <;> simp

/-- A lifted reduction's run is the inner run on the projected input, with the prover output
mapped through the witness lens and an accepted output lifted. -/
theorem Reduction.liftContext_runOutcome {ι : Type} {ambient : OracleSpec.{0, 0} ι}
    {s : Protocol} {OuterIn : Type} {InnerIn : Type} {OuterWit : Type}
    {InnerWit : Type} {OuterStmtOut InnerStmtOut : Path s → Type}
    {OuterOut InnerOut : Transcript plainSig s → Type}
    (lens : ContextLens plainSig s OuterIn InnerIn OuterWit InnerWit OuterStmtOut InnerStmtOut
      OuterOut InnerOut)
    (R : Reduction ambient s InnerIn InnerWit InnerStmtOut InnerOut) (stmt : OuterIn)
    (wit : OuterWit) :
    (R.liftContext lens).runOutcome stmt wit =
      (fun obs => ⟨obs.1, lens.wit.lift stmt wit obs.1 obs.2.1,
          obs.2.2.map (lens.stmt.lift stmt obs.1.path)⟩) <$>
        R.runOutcome (lens.stmt.proj stmt) (lens.wit.proj stmt wit) := by
  simp only [Reduction.runOutcome, Reduction.liftContext, Prover.liftContext,
    Verifier.liftContext_run, Verifier.run_mapOutput, Functor.map_map]

/-! ### Compatibility -/

/-- An inner output statement is compatible with an inner input statement at a path when the
decision can return it on some view of that path. -/
def Verifier.Compatible {ι : Type} {ambient : OracleSpec.{0, 0} ι} {s : Protocol}
    {S : Type} {T : Path s → Type} (V : Verifier ambient s S T) (stmt : S) (p : Path s)
    (t : T p) : Prop :=
  ∃ v : PlainView s p, some t ∈ support (V.decide stmt p v).run

/-- Every accepted output of a run is compatible with its input statement. -/
theorem Verifier.compatible_of_mem_support_run {ι : Type} {ambient : OracleSpec.{0, 0} ι}
    {s : Protocol} {S : Type} {T : Path s → Type} {Out : Transcript plainSig s → Type}
    (V : Verifier ambient s S T) (stmt : S) (p : Prover plainSig ambient s Out)
    {obs : Outcome plainSig s Out T} (h : obs ∈ support (V.run stmt p)) {t : T obs.1.path}
    (ht : obs.2.2 = some t) : V.Compatible stmt obs.1.path t := by
  have hv := V.verdict_mem_support_run stmt p h
  rw [ht] at hv
  exact ⟨toPlainView s obs.1, hv⟩

/-- Every accepted output with positive acceptance probability is compatible with its input
statement. -/
theorem Verifier.compatible_of_mem_support_simulateQ {ι σ : Type} {ambient : OracleSpec ι}
    {s : Protocol} {S : Type} {T : Path s → Type} (V : Verifier ambient s S T)
    (impl : QueryImpl ambient (StateT σ ProbComp)) (stmt : S) (tr : Transcript plainSig s)
    {state final : σ} {t : T tr.path}
    (h : (some t, final) ∈ support
      ((simulateQ impl (V.decide stmt tr.path (toPlainView s tr)).run).run state)) :
    V.Compatible stmt tr.path t :=
  ⟨toPlainView s tr, mem_support_of_mem_support_simulateQ_run impl _ state h⟩

/-! ### Lens conditions -/

section Conditions

variable {P : PFunctor.{uA, 0}} {l : PFunctor.Lens P rolePoly0} {s : FreeM P Unit}
  {OuterIn : Type} {InnerIn : Type} {OuterWit : Type} {InnerWit : Type}
  {OuterStmtOut InnerStmtOut : Path s → Type} {OuterOut InnerOut : Transcript l s → Type}

/-- A statement lens preserves soundness: an admissible false outer input projects to an
admissible false inner input, and on such an input a compatible inner output whose lift is in
the outer output language is in the inner output language. -/
structure StatementLens.IsSound
    (lens : StatementLens s OuterIn InnerIn OuterStmtOut InnerStmtOut)
    (inputO : StatementProblem OuterIn) (inputI : StatementProblem InnerIn)
    (outputO : PathProblem s OuterStmtOut) (outputI : PathProblem s InnerStmtOut)
    (compat : InnerIn → (p : Path s) → InnerStmtOut p → Prop) : Prop where
  /-- Admissible false inputs project to admissible false inputs. -/
  proj_sound : ∀ stmt, inputO.admissible () stmt → ¬ inputO.language () stmt →
    inputI.admissible () (lens.proj stmt) ∧ ¬ inputI.language () (lens.proj stmt)
  /-- On an admissible false input, a compatible output with a true lift is true. -/
  lift_sound : ∀ stmt p t, inputO.admissible () stmt → ¬ inputO.language () stmt →
    compat (lens.proj stmt) p t → outputO.language p (lens.lift stmt p t) →
    outputI.language p t

/-- A context lens preserves completeness: a valid outer input projects to a valid inner input
with the chosen honest witnesses, and a compatible honest inner outcome lifts to an honest outer
outcome. -/
structure ContextLens.IsComplete
    (lens : ContextLens l s OuterIn InnerIn OuterWit InnerWit OuterStmtOut InnerStmtOut
      OuterOut InnerOut)
    (inputO : StatementProblem OuterIn) (inputI : StatementProblem InnerIn)
    (witnessO : ∀ stmt, inputO.Witness () stmt → OuterWit)
    (witnessI : ∀ stmt, inputI.Witness () stmt → InnerWit)
    (honestO : ((tr : Transcript l s) × OuterOut tr × Option (OuterStmtOut tr.path)) → Prop)
    (honestI : ((tr : Transcript l s) × InnerOut tr × Option (InnerStmtOut tr.path)) → Prop)
    (compat : InnerIn → (p : Path s) → InnerStmtOut p → Prop) : Prop where
  /-- A valid outer input projects to a valid inner input whose honest witness is the
  projected witness. -/
  proj_complete : ∀ stmt w, inputO.rel () stmt w →
    ∃ w', inputI.rel () (lens.stmt.proj stmt) w' ∧
      witnessI (lens.stmt.proj stmt) w' = lens.wit.proj stmt (witnessO stmt w)
  /-- A compatible honest inner outcome on a valid input lifts to an honest outer outcome. -/
  lift_complete : ∀ stmt w, inputO.rel () stmt w →
    ∀ (tr : Transcript l s) (o : InnerOut tr) (t : InnerStmtOut tr.path),
      compat (lens.stmt.proj stmt) tr.path t → honestI ⟨tr, o, some t⟩ →
      honestO ⟨tr, lens.wit.lift stmt (witnessO stmt w) tr o, some (lens.stmt.lift stmt tr.path t)⟩

end Conditions

/-- An extractor lens preserves round-by-round knowledge soundness. Admissible inputs project to
admissible inputs, and valid inner input witnesses lift to valid outer ones. A compatible
accepted outer output witness either projects to a valid inner one, or lifts every inner input
witness to a valid outer one. -/
structure ExtractorLens.IsKnowledgeSound {P : PFunctor.{uA, 0}}
    {l : PFunctor.Lens P rolePoly0} {s : FreeM P Unit}
    {OuterIn : Type} {InnerIn : Type} {OuterStmtOut InnerStmtOut : Path s → Type}
    {OuterWitIn : OuterIn → Type} {InnerWitIn : InnerIn → Type}
    {OuterWitOut : OuterIn → Transcript l s → Type}
    {InnerWitOut : InnerIn → Transcript l s → Type}
    (lens : ExtractorLens l s OuterIn InnerIn OuterStmtOut InnerStmtOut OuterWitIn InnerWitIn
      OuterWitOut InnerWitOut)
    (admissibleO : OuterIn → Prop) (admissibleI : InnerIn → Prop)
    (relInO : (stmt : OuterIn) → OuterWitIn stmt → Prop)
    (relInI : (stmt : InnerIn) → InnerWitIn stmt → Prop)
    (relOutO : (stmt : OuterIn) → (tr : Transcript l s) → OuterStmtOut tr.path →
      OuterWitOut stmt tr → Prop)
    (relOutI : (stmt : InnerIn) → (tr : Transcript l s) → InnerStmtOut tr.path →
      InnerWitOut stmt tr → Prop)
    (compat : InnerIn → (p : Path s) → InnerStmtOut p → Prop) : Prop where
  /-- Admissible inputs project to admissible inputs. -/
  proj_admissible : ∀ stmt, admissibleO stmt → admissibleI (lens.stmt.proj stmt)
  /-- A valid inner input witness lifts to a valid outer one. -/
  lift_knowledgeSound : ∀ stmt, admissibleO stmt → ∀ tr wo v,
    relInI (lens.stmt.proj stmt) v → relInO stmt (lens.witInLift stmt tr wo v)
  /-- An accepted outer output witness projects to a valid inner one, or every inner input
  witness lifts to a valid outer one. -/
  proj_knowledgeSound : ∀ stmt tr t wo,
    compat (lens.stmt.proj stmt) tr.path t →
    relOutO stmt tr (lens.stmt.lift stmt tr.path t) wo →
    relOutI (lens.stmt.proj stmt) tr t (lens.witOutProj stmt tr wo) ∨
      ∀ v, relInO stmt (lens.witInLift stmt tr wo v)

/-! ### Generic round-by-round transfers -/

section Generic

variable {P : PFunctor.{uA, 0}} {l : PFunctor.Lens P rolePoly0} {s : FreeM P Unit}
  {SO : Type} {SI : Type}

/-- Pull a state function back along a statement map. The new state is true on a statement
outside the admissible false region, and otherwise is the old state at the mapped statement. -/
def StateFunction.liftContext {admO langO : SO → Prop} {admI langI : SI → Prop}
    {accO : SO → Transcript l s → Prop} {accI : SI → Transcript l s → Prop}
    (proj : SO → SI)
    (hproj : ∀ x, admO x → ¬ langO x → admI (proj x) ∧ ¬ langI (proj x))
    (hacc : ∀ x tr, admO x → ¬ langO x → accO x tr → accI (proj x) tr)
    (F : StateFunction l s SI admI langI accI) : StateFunction l s SO admO langO accO where
  toFun sp history x := admO x → ¬ langO x → F.toFun sp history (proj x)
  root x hadm h := by
    by_contra hlang
    obtain ⟨hadmI, hlangI⟩ := hproj x hadm hlang
    exact hlangI (F.root (proj x) hadmI (h hadm hlang))
  send sp history x ho h m := by
    simp only [not_imp] at h ⊢
    exact ⟨h.1, h.2.1, F.send sp history (proj x) ho h.2.2 m⟩
  leaf sp history x h hacc' := by
    simp only [not_imp] at h
    exact F.leaf sp history (proj x) h.2.2 (hacc x _ h.1 h.2.1 hacc')

/-- Pull a knowledge state function back along an extractor lens's maps. The new intermediate
witness carries a completed transcript and an outer output witness beside the old intermediate
witness. The new state is the old state, or the shortcut that every inner input witness lifts
to a valid outer one. -/
def KnowledgeStateFunction.liftContext {WO : SO → Transcript l s → Type}
    {WI : SI → Transcript l s → Type} {WinO : SO → Type} {WinI : SI → Type}
    {admO : SO → Prop} {admI : SI → Prop}
    {relInO : (x : SO) → WinO x → Prop} {relInI : (y : SI) → WinI y → Prop}
    {validO : (x : SO) → (tr : Transcript l s) → WO x tr → Prop}
    {validI : (y : SI) → (tr : Transcript l s) → WI y tr → Prop}
    (proj : SO → SI) (witOutProj : ∀ x tr, WO x tr → WI (proj x) tr)
    (witInLift : ∀ x tr, WO x tr → WinI (proj x) → WinO x)
    (hadm : ∀ x, admO x → admI (proj x))
    (hlift : ∀ x, admO x → ∀ tr wo v, relInI (proj x) v → relInO x (witInLift x tr wo v))
    (hvalid : ∀ x tr wo, validO x tr wo →
      validI (proj x) tr (witOutProj x tr wo) ∨ ∀ v, relInO x (witInLift x tr wo v))
    (F : KnowledgeStateFunction l s SI WI WinI admI relInI validI) :
    KnowledgeStateFunction l s SO WO WinO admO relInO validO where
  Witness x _ sp history := ((tr : Transcript l s) × WO x tr) × F.Witness (proj x) sp history
  toFun x _ sp history w :=
    F.toFun (proj x) sp history w.2 ∨ ∀ v, relInO x (witInLift x w.1.1 w.1.2 v)
  extractRoot x w := witInLift x w.1.1 w.1.2 (F.extractRoot (proj x) w.2)
  extractStep x _ _ sp history m w := (w.1, F.extractStep (proj x) sp history m w.2)
  extractLeaf x sp history wo :=
    (⟨_, wo⟩, F.extractLeaf (proj x) sp history (witOutProj x _ wo))
  root x ha w h := h.elim
    (fun hF => hlift x ha _ _ _ (F.root (proj x) (hadm x ha) w.2 hF)) (fun hs => hs _)
  send sp history x ho m w h := h.imp (F.send sp history (proj x) ho m w.2) id
  leaf sp history x wo h := (hvalid x _ wo h).imp (F.leaf sp history (proj x) _) id

/-- Round-by-round soundness pulls back along a statement map that sends admissible false
statements to admissible false statements, when acceptance on such a statement implies
acceptance on its image. The draw and the error are unchanged. -/
theorem rbrSoundness_liftContext {admO langO : SO → Prop} {admI langI : SI → Prop}
    {accO : SO → Transcript l s → Prop} {accI : SI → Transcript l s → Prop}
    {draw : QueryImpl (challengeSpec l s) ProbComp} {ε : ChallengeNode l s → ℝ≥0∞}
    (proj : SO → SI)
    (hproj : ∀ x, admO x → ¬ langO x → admI (proj x) ∧ ¬ langI (proj x))
    (hacc : ∀ x tr, admO x → ¬ langO x → accO x tr → accI (proj x) tr)
    (h : rbrSoundness l s admI langI accI draw ε) :
    rbrSoundness l s admO langO accO draw ε := by
  obtain ⟨F, hF⟩ := h
  refine ⟨F.liftContext proj hproj hacc, fun x hadm hlang a next sp ho history => ?_⟩
  obtain ⟨hadmI, hlangI⟩ := hproj x hadm hlang
  simpa only [StateFunction.liftContext, hadm, hlang, not_false_eq_true, forall_const] using
    hF (proj x) hadmI hlangI a next sp ho history

/-- Round-by-round knowledge soundness pulls back along an extractor lens's maps. The draw and
the error are unchanged. -/
theorem rbrKnowledgeSoundness_liftContext {WO : SO → Transcript l s → Type}
    {WI : SI → Transcript l s → Type} {WinO : SO → Type} {WinI : SI → Type}
    {admO : SO → Prop} {admI : SI → Prop}
    {relInO : (x : SO) → WinO x → Prop} {relInI : (y : SI) → WinI y → Prop}
    {validO : (x : SO) → (tr : Transcript l s) → WO x tr → Prop}
    {validI : (y : SI) → (tr : Transcript l s) → WI y tr → Prop}
    {draw : PrefixDraw l ProbComp s} {ε : PrefixError l s}
    (proj : SO → SI) (witOutProj : ∀ x tr, WO x tr → WI (proj x) tr)
    (witInLift : ∀ x tr, WO x tr → WinI (proj x) → WinO x)
    (hadm : ∀ x, admO x → admI (proj x))
    (hlift : ∀ x, admO x → ∀ tr wo v, relInI (proj x) v → relInO x (witInLift x tr wo v))
    (hvalid : ∀ x tr wo, validO x tr wo →
      validI (proj x) tr (witOutProj x tr wo) ∨ ∀ v, relInO x (witInLift x tr wo v))
    (h : rbrKnowledgeSoundness l s admI relInI validI draw ε) :
    rbrKnowledgeSoundness l s admO relInO validO draw ε := by
  obtain ⟨F, hF⟩ := h
  refine ⟨F.liftContext proj witOutProj witInLift hadm hlift hvalid,
    fun x ha a next sp ho history => ?_⟩
  refine le_trans (MeasureTheory.measure_mono ?_) (hF (proj x) (hadm x ha) a next sp ho history)
  rintro m ⟨⟨c, wi⟩, hnot, hafter⟩
  simp only [KnowledgeStateFunction.liftContext, not_or] at hnot hafter
  exact ⟨wi, hnot.1, hafter.resolve_right hnot.2⟩

end Generic

/-! ### Probability lemmas -/

/-- The experiment's possible results are possible results of the program. -/
theorem support_experiment_subset {ι κ σ α : Type} {ambient : OracleSpec ι}
    {chal : OracleSpec κ} (init : ProbComp σ) (impl : QueryImpl ambient (StateT σ ProbComp))
    (challengeQueryImpl : QueryImpl chal ProbComp) (program : OracleComp (ambient + chal) α) :
    support (experiment init impl challengeQueryImpl program) ⊆ support program := by
  intro x hx
  simp only [experiment, mem_support_bind_iff] at hx
  obtain ⟨state, -, hx⟩ := hx
  exact support_simulateQ_run'_subset _ program state hx

/-- An event of a mapped computation is bounded by an event of the computation that holds on
every possible preimage result. -/
theorem prEvent_map_le_of_support {α β : Type} (mx : ProbComp α) (f : α → β)
    (E : β → Prop) (E' : α → Prop) (h : ∀ a ∈ support mx, E (f a) → E' a) :
    Pr{let b ← f <$> mx}[E b] ≤ Pr{let a ← mx}[E' a] := by
  rw [prEvent_map]
  exact prEvent_mono_of_support mx _ _ h

/-- An event of a computation is bounded by an event of its mapping that holds on the image of
every possible result. -/
theorem prEvent_le_map_of_support {α β : Type} (mx : ProbComp α) (f : α → β)
    (E : β → Prop) (E' : α → Prop) (h : ∀ a ∈ support mx, E' a → E (f a)) :
    Pr{let a ← mx}[E' a] ≤ Pr{let b ← f <$> mx}[E b] := by
  rw [prEvent_map]
  exact prEvent_mono_of_support mx _ _ h

/-! ### Plain transfers -/

section Plain

variable {ι σ : Type} {ambient : OracleSpec ι} {s : Protocol}
  {OuterIn : Type} {InnerIn : Type} {OuterOut InnerOut : Path s → Type}

/-- The lifted decision accepts with positive probability exactly when the inner decision
accepts, at the projected statement, an output whose lift satisfies the event. -/
theorem Verifier.validAcceptance_liftContext
    (lens : StatementLens s OuterIn InnerIn OuterOut InnerOut)
    (V : Verifier ambient s InnerIn InnerOut) (impl : QueryImpl ambient (StateT σ ProbComp))
    (stmt : OuterIn) (tr : Transcript plainSig s) (event : OuterOut tr.path → Prop) :
    (V.liftContext lens).validAcceptance impl stmt tr event ↔
      V.validAcceptance impl (lens.proj stmt) tr (fun t => event (lens.lift stmt tr.path t)) := by
  rw [Verifier.validAcceptance_iff_support, Verifier.validAcceptance_iff_support]
  simp only [Verifier.liftContext, OptionT.run_map, simulateQ_map, StateT.run_map,
    _root_.support_map, Set.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨state, t, final, ⟨⟨o, final'⟩, hmem, ho, rfl⟩, ht⟩
    obtain ⟨t', rfl, rfl⟩ := Option.map_eq_some_iff.mp ho
    exact ⟨state, t', final', hmem, ht⟩
  · rintro ⟨state, t, final, hmem, ht⟩
    exact ⟨state, _, final, ⟨⟨some t, final⟩, hmem, rfl, rfl⟩, ht⟩

/-- Soundness lifts along a sound statement lens, at the same error. -/
theorem Verifier.liftContext_soundness
    (lens : StatementLens s OuterIn InnerIn OuterOut InnerOut)
    (V : Verifier ambient s InnerIn InnerOut) (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (challenges : QueryImpl (challengeSpec plainSig s) ProbComp)
    {inputO : StatementProblem OuterIn} {inputI : StatementProblem InnerIn}
    {outputO : PathProblem s OuterOut} {outputI : PathProblem s InnerOut} {ε : ℝ≥0∞}
    (hlens : lens.IsSound inputO inputI outputO outputI V.Compatible)
    (h : V.soundness init impl challenges inputI outputI ε) :
    (V.liftContext lens).soundness init impl challenges inputO outputO ε := by
  rw [Verifier.soundness_iff_soundnessUsing] at h ⊢
  intro Out stmt hadm hlang p
  obtain ⟨hadmI, hlangI⟩ := hlens.proj_sound stmt hadm hlang
  refine le_trans ?_ (h Out (lens.proj stmt) hadmI hlangI p)
  rw [Verifier.liftContext_run]
  dsimp only
  rw [experiment_map]
  refine prEvent_map_le_of_support _ _ _ _ fun obs hobs => ?_
  rintro ⟨t, ht, hout⟩
  obtain ⟨t', ht', rfl⟩ := Option.map_eq_some_iff.mp ht
  refine ⟨t', ht', hlens.lift_sound stmt _ t' hadm hlang ?_ hout⟩
  exact V.compatible_of_mem_support_run _ p (support_experiment_subset _ _ _ _ hobs) ht'

/-- Completeness lifts along a complete context lens, at the same error. With `ε = 0` this is
the transfer of perfect completeness. -/
theorem Reduction.liftContext_completeness {OuterWit : Type} {InnerWit : Type}
    {OuterStmtOut InnerStmtOut : Path s → Type} {OuterO InnerO : Transcript plainSig s → Type}
    (lens : ContextLens plainSig s OuterIn InnerIn OuterWit InnerWit OuterStmtOut InnerStmtOut
      OuterO InnerO)
    (R : Reduction ambient s InnerIn InnerWit InnerStmtOut InnerO) (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (challenges : QueryImpl (challengeSpec plainSig s) ProbComp)
    {inputO : StatementProblem OuterIn} {inputI : StatementProblem InnerIn}
    {outputO : PathProblem s OuterStmtOut} {outputI : PathProblem s InnerStmtOut}
    {readStatementO : ∀ tr, OuterO tr → OuterStmtOut tr.path}
    {readStatementI : ∀ tr, InnerO tr → InnerStmtOut tr.path}
    {readWitnessO : ∀ obs : Outcome plainSig s OuterO OuterStmtOut, ∀ t,
      obs.2.2 = some t → outputO.Witness (Transcript.path obs.1) t}
    {readWitnessI : ∀ obs : Outcome plainSig s InnerO InnerStmtOut, ∀ t,
      obs.2.2 = some t → outputI.Witness (Transcript.path obs.1) t}
    {witnessO : ∀ stmt, inputO.Witness () stmt → OuterWit}
    {witnessI : ∀ stmt, inputI.Witness () stmt → InnerWit} {ε : ℝ≥0∞}
    (hlens : lens.IsComplete inputO inputI witnessO witnessI
      (OutputJudgement.ofOutcome outputO readStatementO readWitnessO).honest
      (OutputJudgement.ofOutcome outputI readStatementI readWitnessI).honest
      R.verifier.Compatible)
    (h : R.completeness init impl challenges inputI outputI readStatementI readWitnessI
      witnessI ε) :
    (R.liftContext lens).completeness init impl challenges inputO outputO readStatementO
      readWitnessO witnessO ε := by
  let : MeasurableSpace (Outcome plainSig s OuterO OuterStmtOut) := ⊤
  let : MeasurableSpace (Outcome plainSig s InnerO InnerStmtOut) := ⊤
  refine ⟨MeasurableSpace.measurableSet_top, fun stmt w hrel => ?_⟩
  obtain ⟨w', hrel', hw'⟩ := hlens.proj_complete stmt w hrel
  have hI := h.2 _ w' hrel'
  change 1 - ε ≤ 𝒟[experiment init impl challenges
    ((R.liftContext lens).runOutcome stmt (witnessO stmt w))] _
  change 1 - ε ≤ 𝒟[experiment init impl challenges
    (R.runOutcome (lens.stmt.proj stmt) (witnessI _ w'))] _ at hI
  rw [hw'] at hI
  rw [Reduction.liftContext_runOutcome, experiment_map]
  rw [← prEvent_eq_evalDist_of_discrete] at hI ⊢
  refine le_trans hI (prEvent_le_map_of_support _ _ _ _ fun obs hobs hhon => ?_)
  obtain ⟨tr, o, verdict⟩ := obs
  cases verdict with
  | none =>
    obtain ⟨t, ht, _⟩ := hhon
    exact absurd ht (by simp [OutputJudgement.ofOutcome])
  | some t =>
    exact hlens.lift_complete stmt w hrel tr o t
      (R.verifier.compatible_of_mem_support_run _ _ (support_experiment_subset _ _ _ _ hobs) rfl)
      hhon

/-- Round-by-round soundness lifts along a sound statement lens, with the same draw and
error. -/
theorem Verifier.liftContext_rbrSoundness
    (lens : StatementLens s OuterIn InnerIn OuterOut InnerOut)
    (V : Verifier ambient s InnerIn InnerOut) (impl : QueryImpl ambient (StateT σ ProbComp))
    {inputO : StatementProblem OuterIn} {inputI : StatementProblem InnerIn}
    {outputO : PathProblem s OuterOut} {outputI : PathProblem s InnerOut}
    {draw : QueryImpl (challengeSpec plainSig s) ProbComp}
    {ε : ChallengeNode plainSig s → ℝ≥0∞}
    (hlens : lens.IsSound inputO inputI outputO outputI V.Compatible)
    (h : V.rbrSoundness impl inputI outputI draw ε) :
    (V.liftContext lens).rbrSoundness impl inputO outputO draw ε := by
  refine rbrSoundness_liftContext lens.proj hlens.proj_sound (fun x tr hadm hlang hacc => ?_) h
  rw [Verifier.validAcceptance_liftContext, Verifier.validAcceptance_iff_support] at hacc
  rw [Verifier.validAcceptance_iff_support]
  obtain ⟨state, t, final, hmem, hout⟩ := hacc
  exact ⟨state, t, final, hmem, hlens.lift_sound x _ t hadm hlang
    (V.compatible_of_mem_support_simulateQ impl _ tr hmem) hout⟩

/-- Round-by-round knowledge soundness lifts along a knowledge-sound extractor lens, with the
same draw and error. -/
theorem Verifier.liftContext_rbrKnowledgeSoundness
    {OuterWitIn : OuterIn → Type} {InnerWitIn : InnerIn → Type}
    {OuterWitOut : OuterIn → Transcript plainSig s → Type}
    {InnerWitOut : InnerIn → Transcript plainSig s → Type}
    (lens : ExtractorLens plainSig s OuterIn InnerIn OuterOut InnerOut OuterWitIn InnerWitIn
      OuterWitOut InnerWitOut)
    (V : Verifier ambient s InnerIn InnerOut) (impl : QueryImpl ambient (StateT σ ProbComp))
    {admissibleO : OuterIn → Prop} {admissibleI : InnerIn → Prop}
    {relInO : (stmt : OuterIn) → OuterWitIn stmt → Prop}
    {relInI : (stmt : InnerIn) → InnerWitIn stmt → Prop}
    {relOutO : (stmt : OuterIn) → (tr : Transcript plainSig s) → OuterOut tr.path →
      OuterWitOut stmt tr → Prop}
    {relOutI : (stmt : InnerIn) → (tr : Transcript plainSig s) → InnerOut tr.path →
      InnerWitOut stmt tr → Prop}
    {draw : PrefixDraw plainSig ProbComp s} {ε : PrefixError plainSig s}
    (hlens : lens.IsKnowledgeSound admissibleO admissibleI relInO relInI relOutO relOutI
      V.Compatible)
    (h : V.rbrKnowledgeSoundness impl admissibleI relInI relOutI draw ε) :
    (V.liftContext lens.stmt).rbrKnowledgeSoundness impl admissibleO relInO relOutO draw ε := by
  refine rbrKnowledgeSoundness_liftContext lens.stmt.proj lens.witOutProj lens.witInLift
    hlens.proj_admissible hlens.lift_knowledgeSound (fun x tr wo hacc => ?_) h
  rw [Verifier.validAcceptance_liftContext, Verifier.validAcceptance_iff_support] at hacc
  obtain ⟨state, t, final, hmem, hout⟩ := hacc
  refine (hlens.proj_knowledgeSound x tr t wo
    (V.compatible_of_mem_support_simulateQ impl _ tr hmem) hout).imp (fun hI => ?_) id
  rw [Verifier.validAcceptance_iff_support]
  exact ⟨state, t, final, hmem, hI⟩

end Plain

end Interaction
