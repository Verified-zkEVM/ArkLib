/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Security.RoundByRound

/-!
# Agreeing oracle verifiers

Two oracle verifiers on the same tree agree (`OracleVerifier.Agrees`) when, on every completed
run, their decisions are the same program in every lawful monad and their output data agree. The
input and path oracles are answered from the actual data; ambient queries are answered by any
implementation. Agreeing verifiers have equal runs against every prover, equal extraction games,
and the same valid-acceptance predicate, so every security notion of the classical model holds for
one exactly when it holds for the other. Verifiers whose decisions are equal programs agree
(`Agrees.of_decide_eq`).

The second part transports oracle verifiers, challenge oracles, errors and witness families
along an equality of oracle trees, and shows that the transport preserves the run and the security
notions.

Agreement compares results, not query traces: two agreeing decisions may make different queries
to the input and path oracles. Equality of the decision programs, as in `Agrees.of_decide_eq`,
also gives equal decision logs (`runWithLog_eq_of_decide_eq`).
-/

@[expose] public section

universe vDraw

namespace Interaction.OracleVerifier
open scoped ENNReal
open PFunctor FreeM TwoParty.Lens Oracle OracleComp OracleSpec

/-! ## Agreement -/

section Agree
variable {ι : Type} {S : Type} {ambient : OracleSpec.{0, 0} ι}
  {s : OracleProtocol.{0, 0}}
  {T : Path s → Type} {inputs : OracleBundle}
  {outputs : Path s → OracleBundle}

/-- Two oracle verifiers on the same tree agree on every completed run: their decisions, with the
input and path oracles answered from the actual data and ambient queries answered in any lawful
monad, are the same program, and their output data agree. -/
def Agrees (V V' : OracleVerifier ambient s S T inputs outputs) : Prop :=
  ∀ (stmt : S) (data : inputs.Data) (tr : Transcript oracleSig s),
    (∀ (m : Type → Type) [Monad m] [LawfulMonad m] (amb : QueryImpl ambient m),
      simulateQ (QueryImpl.addLift (r := m) amb ((pathBundle inputs s tr.path).answer
          (data, oracleMessages s tr)))
          (V.decide stmt _ (toView s tr)).run =
        simulateQ (QueryImpl.addLift (r := m) amb ((pathBundle inputs s tr.path).answer
          (data, oracleMessages s tr)))
          (V'.decide stmt _ (toView s tr)).run) ∧
    (V.outputMap stmt _ (toView s tr)).f (data, oracleMessages s tr) =
      (V'.outputMap stmt _ (toView s tr)).f (data, oracleMessages s tr)

variable {V V' : OracleVerifier ambient s S T inputs outputs}

/-- Verifiers whose decisions on every completed run are the same program, and whose output data
agree, agree. -/
theorem Agrees.of_decide_eq
    (hd : ∀ (stmt : S) (tr : Transcript oracleSig s),
      V.decide stmt _ (toView s tr) = V'.decide stmt _ (toView s tr))
    (ho : ∀ (stmt : S) (data : inputs.Data) (tr : Transcript oracleSig s),
      (V.outputMap stmt _ (toView s tr)).f (data, oracleMessages s tr) =
        (V'.outputMap stmt _ (toView s tr)).f (data, oracleMessages s tr)) :
    Agrees V V' := fun stmt data tr =>
  ⟨fun _ _ _ _ => by rw [hd], ho stmt data tr⟩

end Agree

section Run
variable {ι : Type} {S : Type} {ambient : OracleSpec ι} {s : OracleProtocol.{0, 0}}
  {T : Path s → Type} {inputs : OracleBundle}
  {outputs : Path s → OracleBundle}
  {V V' : OracleVerifier ambient s S T inputs outputs}

/-- Agreeing verifiers have equal runs against every prover. -/
theorem Agrees.run_eq (h : Agrees V V') (stmt : S) (data : inputs.Data)
    {Out : Transcript oracleSig s → Type} (p : Prover oracleSig ambient s Out) :
    V.run stmt data p = V'.run stmt data p := by
  simp only [OracleVerifier.run_eq]
  refine bind_congr fun r => ?_
  obtain ⟨d, o⟩ := h stmt data r.1
  rw [d, o]

end Run

section Classical
variable {ι σ : Type} {S : Type} {ambient : OracleSpec ι} {s : OracleProtocol.{0, 0}}
  {T : Path s → Type} {inputs : OracleBundle}
  {outputs : Path s → OracleBundle}
  {V V' : OracleVerifier ambient s S T inputs outputs}

/-- Verifiers whose decisions on every completed run are the same program, and whose output data
agree, have equal logged runs: the same outcome, prover log and decision log before
routing. `OracleVerifier.runWithLog` in `Security/Knowledge.lean` requires small input
indices and input queries because its full decision log is a run output. -/
theorem runWithLog_eq_of_decide_eq {s : OracleProtocol.{0, 0}}
    {T : Path s → Type} {outputs : Path s → OracleBundle}
    {inputs : OracleBundle}
    {V V' : OracleVerifier ambient s S T inputs outputs}
    (hd : ∀ (stmt : S) (tr : Transcript oracleSig s),
      V.decide stmt _ (toView s tr) = V'.decide stmt _ (toView s tr))
    (ho : ∀ (stmt : S) (data : inputs.Data) (tr : Transcript oracleSig s),
      (V.outputMap stmt _ (toView s tr)).f (data, oracleMessages s tr) =
        (V'.outputMap stmt _ (toView s tr)).f (data, oracleMessages s tr))
    (stmt : S) (data : inputs.Data) {Out : Transcript oracleSig s → Type}
    (p : Prover oracleSig ambient s Out) :
    V.runWithLog stmt data p = V'.runWithLog stmt data p := by
  simp only [runWithLog_eq]
  refine bind_congr fun r => ?_
  rw [hd, ho]

/-- Agreeing verifiers accept validly at the same statements and transcripts. -/
theorem Agrees.validAcceptance_iff (h : Agrees V V')
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (stmt : S × inputs.Data) (tr : Transcript oracleSig s)
    (langOut : OracleVerifier.Output T outputs tr.path → Prop) :
    V.validAcceptance impl stmt tr langOut ↔ V'.validAcceptance impl stmt tr langOut := by
  obtain ⟨d, o⟩ := h stmt.1 stmt.2 tr
  simp only [OracleVerifier.validAcceptance, d, o]

/-- Agreeing verifiers have equal extraction games, for every extractor, prover and family of
output witnesses. -/
theorem Agrees.extractionGame_eq (h : Agrees V V') {Out Wout : Transcript oracleSig s → Type}
    {Witness : (S × inputs.Data) → Type} (readOut : ∀ tr, Out tr → Wout tr)
    (E : Extractor.OracleStraightLine ambient s Witness Wout)
    (stmt : S × inputs.Data) (p : Prover oracleSig ambient s Out) :
    V.extractionGame readOut E stmt p = V'.extractionGame readOut E stmt p := by
  simp only [OracleVerifier.extractionGame, runWithAmbientLog_eq, bind_assoc]
  refine bind_congr (m := OracleComp (ambient + challengeSpec oracleSig s)) fun x => ?_
  obtain ⟨d, o⟩ := h stmt.1 stmt.2 x.1.1
  rw [d, o]

variable {σ : Type}

/-- Agreeing verifiers have the same classical model. -/
theorem Agrees.classicalModel_eq (h : Agrees V V') {Out : Transcript oracleSig s → Type}
    [MeasurableSpace (Outcome oracleSig s Out (OracleVerifier.Output T outputs))]
    (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (draw : QueryImpl (challengeSpec oracleSig s) ProbComp) :
    V.classicalModel (Out := Out) init impl draw = V'.classicalModel init impl draw := by
  simp only [OracleVerifier.classicalModel, h.run_eq]

/-- Agreeing verifiers are knowledge sound together in the classical straight-line interface, for
every family of output witnesses. -/
theorem Agrees.knowledgeSoundness_iff (h : Agrees V V') {Out Wout : Transcript oracleSig s → Type}
    [mObs : MeasurableSpace (Outcome oracleSig s Out (OracleVerifier.Output T outputs))]
    (init : ProbComp σ) (impl : QueryImpl ambient (StateT σ ProbComp))
    (draw : QueryImpl (challengeSpec oracleSig s) ProbComp) (readOut : ∀ tr, Out tr → Wout tr)
    (input : StatementProblem (S × inputs.Data))
    (output : PathProblem s (OracleVerifier.Output T outputs))
    [mWit : ∀ stmt, MeasurableSpace (input.Witness () stmt)]
    (J : OutputJudgement (Outcome oracleSig s Out (OracleVerifier.Output T outputs)) output)
    (ε : ℝ≥0∞) :
    knowledgeSoundness (V.classicalModel init impl draw) input output J
        (V.classicalStraightLine (input.Witness ()) init impl draw readOut) ε ↔
      knowledgeSoundness (V'.classicalModel init impl draw) input output J
        (V'.classicalStraightLine (input.Witness ()) init impl draw readOut) ε := by
  simp only [knowledgeSoundness, knowledgeSoundnessWith, OracleVerifier.classicalStraightLine,
    OracleVerifier.classicalModel, h.run_eq, h.extractionGame_eq]

/-- Agreeing verifiers are sound together. -/
theorem Agrees.soundness_iff (h : Agrees V V') {Out : Transcript oracleSig s → Type}
    [mObs : MeasurableSpace (Outcome oracleSig s Out (OracleVerifier.Output T outputs))]
    (init : ProbComp σ) (impl : QueryImpl ambient (StateT σ ProbComp))
    (draw : QueryImpl (challengeSpec oracleSig s) ProbComp)
    (input : StatementProblem (S × inputs.Data))
    (output : PathProblem s (OracleVerifier.Output T outputs))
    (verdict : (obs : Outcome oracleSig s Out (OracleVerifier.Output T outputs)) →
      Option (OracleVerifier.Output T outputs (Transcript.path obs.1)))
    (ε : ℝ≥0∞) :
    Interaction.soundness (V.classicalModel init impl draw) input output
        (fun obs => Transcript.path obs.1) verdict ε ↔
      Interaction.soundness (V'.classicalModel init impl draw) input output
        (fun obs => Transcript.path obs.1) verdict ε := by
  rw [h.classicalModel_eq]

/-- Agreeing verifiers are complete together, for the same honest prover. -/
theorem Agrees.completeness_iff (h : Agrees V V') {Out : Transcript oracleSig s → Type}
    [mObs : MeasurableSpace (Outcome oracleSig s Out (OracleVerifier.Output T outputs))]
    (init : ProbComp σ) (impl : QueryImpl ambient (StateT σ ProbComp))
    (draw : QueryImpl (challengeSpec oracleSig s) ProbComp)
    (input : StatementProblem (S × inputs.Data))
    (output : PathProblem s (OracleVerifier.Output T outputs))
    (J : OutputJudgement (Outcome oracleSig s Out (OracleVerifier.Output T outputs)) output)
    (honest : ∀ stmt, input.Witness () stmt → Prover oracleSig ambient s Out)
    (ε : ℝ≥0∞) :
    completeness (V.classicalModel init impl draw) input output J honest ε ↔
      completeness (V'.classicalModel init impl draw) input output J honest ε := by
  simp only [completeness, OracleVerifier.classicalModel, h.run_eq]

/-- Agreeing verifiers have the same valid-acceptance predicate. -/
theorem Agrees.validAcceptance_eq (h : Agrees V V')
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (langOut : (stmt : S × inputs.Data) → (tr : Transcript oracleSig s) →
      OracleVerifier.Output T outputs tr.path → Prop) :
    (fun stmt tr => V.validAcceptance impl stmt tr (langOut stmt tr)) =
      (fun stmt tr => V'.validAcceptance impl stmt tr (langOut stmt tr)) := by
  funext stmt tr
  exact propext (h.validAcceptance_iff impl stmt tr _)

/-- Agreeing verifiers are round-by-round sound together. -/
theorem Agrees.rbrSoundness_iff (h : Agrees V V') (impl : QueryImpl ambient (StateT σ ProbComp))
    (input : StatementProblem (S × inputs.Data))
    (output : PathProblem s (OracleVerifier.Output T outputs))
    (draw : QueryImpl (challengeSpec oracleSig s) ProbComp)
    (ε : ChallengeNode oracleSig s → ℝ≥0∞) :
    V.rbrSoundness impl input output draw ε ↔ V'.rbrSoundness impl input output draw ε := by
  have eq : (fun stmt tr => V.validAcceptance impl stmt tr
      (output.language tr.path)) =
      (fun stmt tr => V'.validAcceptance impl stmt tr
        (output.language tr.path)) :=
    funext fun stmt => funext fun tr =>
      propext (h.validAcceptance_iff impl stmt tr _)
  unfold OracleVerifier.rbrSoundness
  rw [eq]

/-- Agreeing verifiers are round-by-round knowledge sound together, for every family of output
witnesses and every statement-and-transcript-indexed output relation. -/
theorem Agrees.rbrKnowledgeSoundness_iff (h : Agrees V V')
    {Win : (S × inputs.Data) → Type}
    {W : (S × inputs.Data) → Transcript oracleSig s → Type}
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (admissible : S × inputs.Data → Prop)
    (relIn : (stmt : S × inputs.Data) → Win stmt → Prop)
    (relOut : (stmt : S × inputs.Data) → (tr : Transcript oracleSig s) →
      OracleVerifier.Output T outputs tr.path → W stmt tr → Prop)
    (draw : PrefixDraw viewSig ProbComp s) (ε : PrefixError oracleSig s) :
    V.rbrKnowledgeSoundness impl admissible relIn relOut draw ε ↔
      V'.rbrKnowledgeSoundness impl admissible relIn relOut draw ε := by
  have eq : (fun stmt tr wit => V.validAcceptance impl stmt tr (fun t => relOut stmt tr t wit)) =
      (fun stmt tr wit => V'.validAcceptance impl stmt tr (fun t => relOut stmt tr t wit)) :=
    funext fun stmt => funext fun tr => funext fun _ =>
      propext (h.validAcceptance_iff impl stmt tr _)
  unfold OracleVerifier.rbrKnowledgeSoundness
  rw [eq]

end Classical

/-! ## Transport along a tree equality -/

section Cast
variable {ι : Type} {S : Type} {ambient : OracleSpec.{0, 0} ι}
  {s s' : OracleProtocol.{0, 0}} {T : Path s → Type}
  {inputs : OracleBundle}
  {outputs : Path s → OracleBundle}

/-- Transport a verifier to an equal tree, reindexing its output statements, oracle indices,
carriers and interfaces along the same path equality. -/
def cast (e : s' = s)
    (V : OracleVerifier ambient s' S (fun p => T (e ▸ p)) inputs (fun p => outputs (e ▸ p))) :
    OracleVerifier ambient s S T inputs outputs :=
  _root_.cast (by subst e; rfl) V

/-- With constant output statements and bundles, verifier transport is ordinary equality
substitution.
The constant specialization is needed because ordinary substitution keeps the output carriers
fixed while changing the tree. -/
theorem cast_const {T : Type} {outputs : OracleBundle} (e : s' = s)
    (V : OracleVerifier ambient s' S (fun _ => T) inputs (fun _ => outputs)) :
    V.cast (T := fun _ => T) (outputs := fun _ => outputs) e = e ▸ V := by
  subst e; rfl

/-- Transporting a verifier along a tree equality does not change its decision on corresponding
transcripts. -/
theorem decide_cast (e : s' = s)
    (V : OracleVerifier ambient s' S (fun p => T (e ▸ p)) inputs (fun p => outputs (e ▸ p)))
    (stmt : S)
    (tr : Transcript oracleSig s) (tr' : Transcript oracleSig s') (htr : HEq tr tr') :
    HEq ((V.cast e).decide stmt _ (toView s tr))
      (V.decide stmt _ (toView s' tr')) := by
  subst e; cases eq_of_heq htr; rfl

/-- Transporting a verifier along a tree equality does not change its interpreted decision on
corresponding transcripts. -/
theorem simulateQ_decide_cast (e : s' = s)
    (V : OracleVerifier ambient s' S (fun p => T (e ▸ p)) inputs (fun p => outputs (e ▸ p)))
    (stmt : S) (data : inputs.Data) (tr : Transcript oracleSig s) (tr' : Transcript oracleSig s')
    (htr : HEq tr tr') (m : Type → Type) [Monad m] [LawfulMonad m]
    (amb : QueryImpl ambient m) :
    HEq (simulateQ (QueryImpl.addLift (r := m) amb
      ((pathBundle inputs s tr.path).answer (data, oracleMessages s tr)))
        ((V.cast e).decide stmt _ (toView s tr)).run)
      (simulateQ (QueryImpl.addLift (r := m) amb
        ((pathBundle inputs s' tr'.path).answer (data, oracleMessages s' tr')))
        (V.decide stmt _ (toView s' tr')).run) := by
  subst e; cases eq_of_heq htr; rfl

/-- Transporting a verifier along a tree equality preserves its output data. Heterogeneous
equality compares the data in the corresponding path-dependent output carriers. -/
theorem outputMap_cast (e : s' = s)
    (V : OracleVerifier ambient s' S (fun p => T (e ▸ p)) inputs (fun p => outputs (e ▸ p)))
    (stmt : S)
    (data : inputs.Data) (tr : Transcript oracleSig s) (tr' : Transcript oracleSig s')
    (htr : HEq tr tr') :
    HEq (((V.cast e).outputMap stmt _
      (toView s tr)).f (data, oracleMessages s tr))
      ((V.outputMap stmt _ (toView s' tr')).f (data, oracleMessages s' tr')) := by
  subst e; cases eq_of_heq htr; rfl

/-- A constant error is unchanged by transport along a tree equality. -/
theorem eqRec_const (e : s' = s) (x : ℝ≥0∞) :
    (e ▸ fun _ : ChallengeNode oracleSig s' => x) = fun _ : ChallengeNode oracleSig s => x := by
  subst e; rfl

/-- Lifting a node-indexed draw to full prefixes commutes with tree transport. -/
theorem prefixDraw_ofNodes_cast {m : Type → Type vDraw} [Functor m] (e : s' = s)
    (draw : QueryImpl (challengeSpec oracleSig s') m) :
    @Eq (PrefixDraw oracleSig m s)
      (fun {a next} => e ▸ (@PrefixDraw.ofNodes _ oracleSig m _ s' draw a next))
      (@PrefixDraw.ofNodes _ oracleSig m _ s (e ▸ draw)) := by
  subst e; rfl

/-- Reading a node-indexed draw through the verifier's view commutes with tree transport. -/
theorem prefixDraw_ofNodesView_cast {m : Type → Type vDraw} [Functor m] (e : s' = s)
    (draw : QueryImpl (challengeSpec oracleSig s') m) :
    @Eq (PrefixDraw viewSig m s)
      (fun {a next} => e ▸ (PrefixDraw.ofNodesView (s := s') draw (a := a) (next := next)))
      (PrefixDraw.ofNodesView (s := s) (e ▸ draw)) := by
  subst e; rfl

/-- Lifting a node-indexed error to full prefixes commutes with tree transport. -/
theorem prefixError_ofNodes_cast (e : s' = s) (ε : ChallengeNode oracleSig s' → ℝ≥0∞) :
    @Eq (PrefixError oracleSig s)
      (fun {a next} => e ▸ (@PrefixError.ofNodes _ oracleSig s' ε a next))
      (@PrefixError.ofNodes _ oracleSig s (e ▸ ε)) := by
  subst e; rfl

end Cast

section RunCast
variable {ι : Type} {S : Type} {ambient : OracleSpec ι}
  {s s' : OracleProtocol.{0, 0}} {T : Path s → Type}
  {inputs : OracleBundle}
  {outputs : Path s → OracleBundle}

/-- Transporting a verifier and a challenge reindexing along a tree equality, and the prover back,
gives the same finalized program when the two finalizations agree on corresponding outcomes.
The prover's output family may also depend on its transcript. -/
theorem run_cast {κ X : Type} {spec : OracleSpec κ} (e : s' = s)
    (V : OracleVerifier ambient s' S (fun p => T (e ▸ p)) inputs (fun p => outputs (e ▸ p)))
    (impl : QueryImpl (ambient + challengeSpec oracleSig s') (OracleComp spec))
    {Out : Transcript oracleSig s → Type}
    (f : Outcome oracleSig s Out (OracleVerifier.Output T outputs) → X)
    (g : Outcome oracleSig s' (fun tr => Out (e ▸ tr))
      (fun p => OracleVerifier.Output T outputs (e ▸ p)) → X)
    (hfg : ∀ tr out verdict,
      f ⟨e ▸ tr, out, _root_.cast (by subst e; rfl) verdict⟩ = g ⟨tr, out, verdict⟩)
    (stmt : S) (data : inputs.Data) (p : Prover oracleSig ambient s Out) :
    simulateQ (e ▸ impl) (f <$> (V.cast e).run stmt data p) =
      simulateQ impl (g <$> V.run stmt data (_root_.cast (by subst e; rfl) p)) := by
  subst e
  have : f = g := funext fun ⟨tr, out, verdict⟩ => hfg tr out verdict
  subst this; rfl

end RunCast

section ClassicalCast
variable {ι σ : Type} {S : Type} {ambient : OracleSpec ι}
  {s s' : OracleProtocol.{0, 0}} {T : Path s → Type}
  {inputs : OracleBundle}
  {outputs : Path s → OracleBundle}

/-- Challenge oracles on equal trees are equal when they agree on corresponding nodes. -/
theorem queryImpl_eq_cast (e : s' = s) (f : QueryImpl (challengeSpec oracleSig s) ProbComp)
    (g : QueryImpl (challengeSpec oracleSig s') ProbComp)
    (h : ∀ c c', HEq c c' → HEq (f c) (g c')) : f = e ▸ g := by
  subst e; exact funext fun c => eq_of_heq (h c c HEq.rfl)

/-- Transporting a verifier and its challenge oracle along a tree equality preserves soundness,
for every prover output family. -/
theorem soundness_cast (e : s' = s)
    (V : OracleVerifier ambient s' S (fun p => T (e ▸ p)) inputs (fun p => outputs (e ▸ p)))
    (init : ProbComp σ) (impl : QueryImpl ambient (StateT σ ProbComp))
    (draw : QueryImpl (challengeSpec oracleSig s') ProbComp)
    (input : StatementProblem (S × inputs.Data))
    (output : PathProblem s (OracleVerifier.Output T outputs))
    (ε : ℝ≥0∞) :
    (∀ Out : Transcript oracleSig s → Type,
      letI : MeasurableSpace (Outcome oracleSig s Out (OracleVerifier.Output T outputs)) := ⊤
      Interaction.soundness ((V.cast e).classicalModel (Out := Out) init impl (e ▸ draw))
        input output (fun obs => Transcript.path obs.1) (fun obs => obs.2.2) ε) ↔
    (∀ Out : Transcript oracleSig s' → Type,
      letI : MeasurableSpace (Outcome oracleSig s' Out
        (fun p => OracleVerifier.Output T outputs (e ▸ p))) := ⊤
      Interaction.soundness (V.classicalModel (Out := Out) init impl draw) input
        (_root_.cast (by subst e; rfl) output :
        PathProblem s' (fun p => OracleVerifier.Output T outputs (e ▸ p)))
        (fun obs => Transcript.path obs.1) (fun obs => obs.2.2) ε) := by
  subst e; exact Iff.rfl

/-- Transporting a verifier, its challenge oracle and its error along a tree equality preserves
round-by-round soundness. -/
theorem rbrSoundness_cast (e : s' = s)
    (V : OracleVerifier ambient s' S (fun p => T (e ▸ p)) inputs (fun p => outputs (e ▸ p)))
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (input : StatementProblem (S × inputs.Data))
    (output : PathProblem s (OracleVerifier.Output T outputs))
    (draw : QueryImpl (challengeSpec oracleSig s') ProbComp)
    (ε : ChallengeNode oracleSig s' → ℝ≥0∞) :
    (V.cast e).rbrSoundness impl input output (e ▸ draw) (e ▸ ε) ↔
      V.rbrSoundness impl input (_root_.cast (by subst e; rfl) output :
        PathProblem s' (fun p => OracleVerifier.Output T outputs (e ▸ p))) draw ε := by
  subst e; exact Iff.rfl

/-- Transporting a verifier, its prefix-dependent challenge sampler and its error along a tree
equality preserves round-by-round knowledge soundness. Input witnesses depend on statements;
output witnesses and their relations depend on statements and completed transcripts. -/
theorem rbrKnowledgeSoundness_cast (e : s' = s)
    (V : OracleVerifier ambient s' S (fun p => T (e ▸ p)) inputs (fun p => outputs (e ▸ p)))
    {Win : (S × inputs.Data) → Type}
    {W : (S × inputs.Data) → Transcript oracleSig s → Type}
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (admissible : S × inputs.Data → Prop)
    (relIn : (stmt : S × inputs.Data) → Win stmt → Prop)
    (relOut : (stmt : S × inputs.Data) → (tr : Transcript oracleSig s) →
      OracleVerifier.Output T outputs tr.path → W stmt tr → Prop)
    (draw : PrefixDraw viewSig ProbComp s') (ε : PrefixError oracleSig s') :
    (V.cast e).rbrKnowledgeSoundness
        impl admissible relIn relOut (e ▸ draw) (e ▸ ε) ↔
      V.rbrKnowledgeSoundness
        impl admissible relIn (W := fun stmt tr => W stmt (e ▸ tr))
        (fun stmt tr out wit =>
          relOut stmt (e ▸ tr) (_root_.cast (by subst e; rfl) out) wit) draw ε := by
  subst e; rfl

end ClassicalCast

end Interaction.OracleVerifier
