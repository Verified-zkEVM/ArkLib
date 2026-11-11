/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Core.Security.RoundByRound

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

universe uK

namespace Interaction.Core.OracleVerifier
open scoped ENNReal
open PFunctor FreeM TwoParty.Lens Oracle OracleComp OracleSpec

/-! ## Agreement -/

section Agree
variable {ι I J S T : Type} {ambient : OracleSpec ι} {s : OracleProtocol}
  {A : I → Type} {B : J → Type} {inputs : OracleFamily.{0, 0, 0} I A} {outputs : OracleFamily J B}

/-- Two oracle verifiers on the same tree agree on every completed run: their decisions, with the
input and path oracles answered from the actual data and ambient queries answered in any lawful
monad, are the same program, and their output data agree. -/
def Agrees (V V' : OracleVerifier ambient s S (fun _ => T) inputs (fun _ => outputs)) : Prop :=
  ∀ (stmt : S) (data : ∀ i, A i) (tr : PathAlong oracleSig s),
    (∀ (m : Type → Type) [Monad m] [LawfulMonad m] (amb : QueryImpl ambient m),
      simulateQ (QueryImpl.addLift (r := m) amb ((pathResources inputs s (projectPathAlong
        oracleSig s tr)).answer
          (data, payloads s tr)))
          (V.decide stmt _ (toView s tr)).run =
        simulateQ (QueryImpl.addLift (r := m) amb ((pathResources inputs s (projectPathAlong
          oracleSig s tr)).answer
          (data, payloads s tr)))
          (V'.decide stmt _ (toView s tr)).run) ∧
    (V.outputMap stmt _ (toView s tr)).f (data, payloads s tr) =
      (V'.outputMap stmt _ (toView s tr)).f (data, payloads s tr)

variable {V V' : OracleVerifier ambient s S (fun _ => T) inputs (fun _ => outputs)}

/-- Verifiers whose decisions on every completed run are the same program, and whose output data
agree, agree. -/
theorem Agrees.of_decide_eq
    (hd : ∀ (stmt : S) (tr : PathAlong oracleSig s),
      V.decide stmt _ (toView s tr) = V'.decide stmt _ (toView s tr))
    (ho : ∀ (stmt : S) (data : ∀ i, A i) (tr : PathAlong oracleSig s),
      (V.outputMap stmt _ (toView s tr)).f (data, payloads s tr) =
        (V'.outputMap stmt _ (toView s tr)).f (data, payloads s tr)) :
    Agrees V V' := fun stmt data tr =>
  ⟨fun _ _ _ _ => by rw [hd], ho stmt data tr⟩

/-- Agreeing verifiers have equal runs against every prover. -/
theorem Agrees.run_eq (h : Agrees V V') (stmt : S) (data : ∀ i, A i)
    {Out : PathAlong oracleSig s → Type} (p : Prover oracleSig ambient s Out) :
    V.run stmt data p = V'.run stmt data p := by
  simp only [OracleVerifier.run]
  refine bind_congr fun r => ?_
  obtain ⟨d, o⟩ := h stmt data r.1
  rw [d, o]

/-- Verifiers whose decisions on every completed run are the same program, and whose output data
agree, have equal logged runs: the same observation, prover log and decision log before
routing. -/
theorem runWithLog_eq_of_decide_eq
    (hd : ∀ (stmt : S) (tr : PathAlong oracleSig s),
      V.decide stmt _ (toView s tr) = V'.decide stmt _ (toView s tr))
    (ho : ∀ (stmt : S) (data : ∀ i, A i) (tr : PathAlong oracleSig s),
      (V.outputMap stmt _ (toView s tr)).f (data, payloads s tr) =
        (V'.outputMap stmt _ (toView s tr)).f (data, payloads s tr))
    (stmt : S) (data : ∀ i, A i) {Out : PathAlong oracleSig s → Type}
    (p : Prover oracleSig ambient s Out) :
    V.runWithLog stmt data p = V'.runWithLog stmt data p := by
  simp only [runWithLog]
  refine bind_congr fun r => ?_
  rw [hd, ho]

/-- Agreeing verifiers accept validly at the same statements and transcripts. -/
theorem Agrees.validAcceptance_iff (h : Agrees V V') {σ : Type}
    (impl : QueryImpl ambient (StateT σ ProbComp)) (langOut : T × (∀ j, B j) → Prop)
    (stmt : S × (∀ i, A i)) (tr : PathAlong oracleSig s) :
    V.validAcceptance impl stmt tr langOut ↔ V'.validAcceptance impl stmt tr langOut := by
  obtain ⟨d, o⟩ := h stmt.1 stmt.2 tr
  simp only [OracleVerifier.validAcceptance, d, o]

/-- Agreeing verifiers have equal extraction games, for every extractor, prover and family of
output witnesses. -/
theorem Agrees.extractionGame_eq (h : Agrees V V') {Out Wout : PathAlong oracleSig s → Type}
    {Witness : (S × (∀ i, A i)) → Type} (readOut : ∀ tr, Out tr → Wout tr)
    (E : Extractor.OracleStraightline ambient s Witness Wout)
    (stmt : S × (∀ i, A i)) (p : Prover oracleSig ambient s Out) :
    V.extractionGame readOut E stmt p = V'.extractionGame readOut E stmt p := by
  simp only [OracleVerifier.extractionGame, runWithAmbientLog, bind_assoc]
  refine bind_congr (m := OracleComp (ambient + challengeSpec oracleSig s)) fun x => ?_
  obtain ⟨d, o⟩ := h stmt.1 stmt.2 x.1.1
  rw [d, o]

variable {σ : Type}

/-- Agreeing verifiers have the same classical model. -/
theorem Agrees.classicalModel_eq (h : Agrees V V') {Out : PathAlong oracleSig s → Type}
    [MeasurableSpace (Observation oracleSig s Out (fun _ => T × (∀ j, B j)))] (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (draw : QueryImpl (challengeSpec oracleSig s) ProbComp) :
    V.classicalModel (Out := Out) init impl draw = V'.classicalModel init impl draw := by
  simp only [OracleVerifier.classicalModel, h.run_eq]

/-- Agreeing verifiers are knowledge sound together in the classical straight-line interface, for
every family of output witnesses. -/
theorem Agrees.knowledgeSoundness_iff (h : Agrees V V') {Out Wout : PathAlong oracleSig s → Type}
    [mObs : MeasurableSpace (Observation oracleSig s Out (fun _ => T × (∀ j, B j)))]
    (init : ProbComp σ) (impl : QueryImpl ambient (StateT σ ProbComp))
    (draw : QueryImpl (challengeSpec oracleSig s) ProbComp) (readOut : ∀ tr, Out tr → Wout tr)
    (input : StatementProblem (S × (∀ i, A i))) (output : PathProblem s (fun _ => T × (∀ j, B j)))
    [mWit : ∀ stmt, MeasurableSpace (input.Witness () stmt)]
    (J : OutputJudgement (Observation oracleSig s Out (fun _ => T × (∀ j, B j))) output) (ε : ℝ≥0∞)
      :
    knowledgeSoundness (V.classicalModel init impl draw) input output J
        (V.classicalStraightline (input.Witness ()) init impl draw readOut) ε ↔
      knowledgeSoundness (V'.classicalModel init impl draw) input output J
        (V'.classicalStraightline (input.Witness ()) init impl draw readOut) ε := by
  simp only [knowledgeSoundness, knowledgeSoundnessWith, OracleVerifier.classicalStraightline,
    OracleVerifier.classicalModel, h.run_eq, h.extractionGame_eq]

/-- Agreeing verifiers are sound together. -/
theorem Agrees.soundness_iff (h : Agrees V V') {Out : PathAlong oracleSig s → Type}
    [mObs : MeasurableSpace (Observation oracleSig s Out (fun _ => T × (∀ j, B j)))]
    (init : ProbComp σ) (impl : QueryImpl ambient (StateT σ ProbComp))
    (draw : QueryImpl (challengeSpec oracleSig s) ProbComp)
    (input : StatementProblem (S × (∀ i, A i))) (output : PathProblem s (fun _ => T × (∀ j, B j)))
    (verdict : Observation oracleSig s Out (fun _ => T × (∀ j, B j)) → Option (T × (∀ j, B j)))
    (ε : ℝ≥0∞) :
    Core.soundness (V.classicalModel init impl draw) input output
        (fun obs => projectPathAlong oracleSig s obs.1) verdict ε ↔
      Core.soundness (V'.classicalModel init impl draw) input output
        (fun obs => projectPathAlong oracleSig s obs.1) verdict ε := by
  rw [h.classicalModel_eq]

/-- Agreeing verifiers are complete together, for the same honest prover. -/
theorem Agrees.completeness_iff (h : Agrees V V') {Out : PathAlong oracleSig s → Type}
    [mObs : MeasurableSpace (Observation oracleSig s Out (fun _ => T × (∀ j, B j)))]
    (init : ProbComp σ) (impl : QueryImpl ambient (StateT σ ProbComp))
    (draw : QueryImpl (challengeSpec oracleSig s) ProbComp)
    (input : StatementProblem (S × (∀ i, A i))) (output : PathProblem s (fun _ => T × (∀ j, B j)))
    (J : OutputJudgement (Observation oracleSig s Out (fun _ => T × (∀ j, B j))) output)
    (honest : ∀ stmt, input.Witness () stmt → Prover oracleSig ambient s Out) (ε : ℝ≥0∞) :
    completeness (V.classicalModel init impl draw) input output J honest ε ↔
      completeness (V'.classicalModel init impl draw) input output J honest ε := by
  simp only [completeness, OracleVerifier.classicalModel, h.run_eq]

/-- Agreeing verifiers have the same valid-acceptance predicate. -/
theorem Agrees.validAcceptance_eq (h : Agrees V V')
    (impl : QueryImpl ambient (StateT σ ProbComp)) (langOut : T × (∀ j, B j) → Prop) :
    (fun stmt tr => V.validAcceptance impl stmt tr langOut) =
      (fun stmt tr => V'.validAcceptance impl stmt tr langOut) := by
  funext stmt tr
  exact propext (h.validAcceptance_iff impl langOut stmt tr)

/-- Agreeing verifiers are round-by-round sound together. -/
theorem Agrees.rbrSoundness_iff (h : Agrees V V') (impl : QueryImpl ambient (StateT σ ProbComp))
    (input : StatementProblem (S × (∀ i, A i))) (output : PathProblem s (fun _ => T × (∀ j, B j)))
    (draw : QueryImpl (challengeSpec oracleSig s) ProbComp) (ε : ChallengeNode oracleSig s → ℝ≥0∞) :
    V.rbrSoundness impl input output draw ε ↔ V'.rbrSoundness impl input output draw ε := by
  have eq : (fun stmt tr => V.validAcceptance impl stmt tr
      (output.language (projectPathAlong oracleSig s tr))) =
      (fun stmt tr => V'.validAcceptance impl stmt tr
        (output.language (projectPathAlong oracleSig s tr))) :=
    funext fun stmt => funext fun tr => propext (h.validAcceptance_iff impl _ stmt tr)
  unfold OracleVerifier.rbrSoundness
  rw [eq]

/-- Agreeing verifiers are round-by-round knowledge sound together, for every family of output
witnesses and every transcript-indexed output relation. -/
theorem Agrees.rbrKnowledgeSoundness_iff (h : Agrees V V') {Win : Type}
    {W : PathAlong oracleSig s → Type} (impl : QueryImpl ambient (StateT σ ProbComp))
    (admissible : S × (∀ i, A i) → Prop) (relIn : (S × (∀ i, A i)) → Win → Prop)
    (relOut : (tr : PathAlong oracleSig s) → (T × (∀ j, B j)) → W tr → Prop)
    (draw : QueryImpl (challengeSpec oracleSig s) ProbComp) (ε : ChallengeNode oracleSig s → ℝ≥0∞) :
    V.rbrKnowledgeSoundness.{0, 0, uK} impl admissible relIn relOut draw ε ↔
      V'.rbrKnowledgeSoundness.{0, 0, uK} impl admissible relIn relOut draw ε := by
  have eq : (fun stmt tr wit => V.validAcceptance impl stmt tr (fun t => relOut tr t wit)) =
      (fun stmt tr wit => V'.validAcceptance impl stmt tr (fun t => relOut tr t wit)) :=
    funext fun stmt => funext fun tr => funext fun _ =>
      propext (h.validAcceptance_iff impl _ stmt tr)
  unfold OracleVerifier.rbrKnowledgeSoundness
  rw [eq]

end Agree

/-! ## Transport along a tree equality -/

section Cast
variable {ι I J S T σ : Type} {ambient : OracleSpec ι} {s s' : OracleProtocol}
  {A : I → Type} {B : J → Type} {inputs : OracleFamily.{0, 0, 0} I A} {outputs : OracleFamily J B}

/-- Transporting a verifier along a tree equality does not change its decision on corresponding
transcripts. -/
theorem decide_cast (e : s' = s) (V : OracleVerifier ambient s' S (fun _ => T) inputs (fun _ =>
  outputs)) (stmt : S)
    (tr : PathAlong oracleSig s) (tr' : PathAlong oracleSig s') (htr : HEq tr tr') :
    HEq ((e ▸ V : OracleVerifier ambient s S (fun _ => T) inputs (fun _ => outputs)).decide stmt _
      (toView s tr))
      (V.decide stmt _ (toView s' tr')) := by
  subst e; cases eq_of_heq htr; rfl

/-- Transporting a verifier along a tree equality does not change its interpreted decision on
corresponding transcripts. -/
theorem simulateQ_decide_cast (e : s' = s) (V : OracleVerifier ambient s' S (fun _ => T) inputs
  (fun _ => outputs))
    (stmt : S) (data : ∀ i, A i) (tr : PathAlong oracleSig s) (tr' : PathAlong oracleSig s')
    (htr : HEq tr tr') (m : Type → Type) [Monad m] [LawfulMonad m] (amb : QueryImpl ambient m) :
    simulateQ (QueryImpl.addLift (r := m) amb ((pathResources inputs s (projectPathAlong oracleSig
      s tr)).answer
          (data, payloads s tr)))
        ((e ▸ V : OracleVerifier ambient s S (fun _ => T) inputs (fun _ => outputs)).decide stmt _
          (toView s tr)).run =
      simulateQ (QueryImpl.addLift (r := m) amb ((pathResources inputs s' (projectPathAlong
        oracleSig s' tr')).answer
          (data, payloads s' tr')))
        (V.decide stmt _ (toView s' tr')).run := by
  subst e; cases eq_of_heq htr; rfl

/-- Transporting a verifier along a tree equality does not change its output data on
corresponding transcripts. -/
theorem outputMap_cast (e : s' = s) (V : OracleVerifier ambient s' S (fun _ => T) inputs (fun _ =>
  outputs)) (stmt : S)
    (data : ∀ i, A i) (tr : PathAlong oracleSig s) (tr' : PathAlong oracleSig s')
    (htr : HEq tr tr') :
    ((e ▸ V : OracleVerifier ambient s S (fun _ => T) inputs (fun _ => outputs)).outputMap stmt _
      (toView s tr)).f
        (data, payloads s tr) =
      (V.outputMap stmt _ (toView s' tr')).f (data, payloads s' tr') := by
  subst e; cases eq_of_heq htr; rfl

/-- Challenge oracles on equal trees are equal when they agree on corresponding nodes. -/
theorem queryImpl_eq_cast (e : s' = s) (f : QueryImpl (challengeSpec oracleSig s) ProbComp)
    (g : QueryImpl (challengeSpec oracleSig s') ProbComp)
    (h : ∀ c c', HEq c c' → HEq (f c) (g c')) : f = e ▸ g := by
  subst e; exact funext fun c => eq_of_heq (h c c HEq.rfl)

/-- A constant error is unchanged by transport along a tree equality. -/
theorem eqRec_const (e : s' = s) (x : ℝ≥0∞) :
    (e ▸ fun _ : ChallengeNode oracleSig s' => x) = fun _ : ChallengeNode oracleSig s => x := by
  subst e; rfl

/-- Transporting a verifier and its challenge oracle along a tree equality preserves soundness,
for every prover output family. -/
theorem soundness_cast (e : s' = s) (V : OracleVerifier ambient s' S (fun _ => T) inputs (fun _ =>
  outputs))
    (init : ProbComp σ) (impl : QueryImpl ambient (StateT σ ProbComp))
    (draw : QueryImpl (challengeSpec oracleSig s') ProbComp)
    (input : StatementProblem (S × (∀ i, A i))) (output : PathProblem s (fun _ => T × (∀ j, B j)))
    (ε : ℝ≥0∞) :
    (∀ Out : PathAlong oracleSig s → Type,
      letI : MeasurableSpace (Observation oracleSig s Out (fun _ => T × (∀ j, B j))) := ⊤
      Core.soundness ((e ▸ V).classicalModel (Out := Out) init impl (e ▸ draw)) input output
        (fun obs => projectPathAlong oracleSig _ obs.1) (fun obs => obs.2.2) ε) ↔
    (∀ Out : PathAlong oracleSig s' → Type,
      letI : MeasurableSpace (Observation oracleSig s' Out (fun _ => T × (∀ j, B j))) := ⊤
      Core.soundness (V.classicalModel (Out := Out) init impl draw) input (e.symm ▸ output)
        (fun obs => projectPathAlong oracleSig _ obs.1) (fun obs => obs.2.2) ε) := by
  subst e; exact Iff.rfl

/-- Transporting a verifier, its challenge oracle and its error along a tree equality preserves
round-by-round soundness. -/
theorem rbrSoundness_cast (e : s' = s) (V : OracleVerifier ambient s' S (fun _ => T) inputs (fun _
  => outputs))
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (input : StatementProblem (S × (∀ i, A i))) (output : PathProblem s (fun _ => T × (∀ j, B j)))
    (draw : QueryImpl (challengeSpec oracleSig s') ProbComp)
    (ε : ChallengeNode oracleSig s' → ℝ≥0∞) :
    (e ▸ V).rbrSoundness impl input output (e ▸ draw) (e ▸ ε) ↔
      V.rbrSoundness impl input (e.symm ▸ output) draw ε := by
  subst e; exact Iff.rfl

/-- Transporting a verifier, its challenge oracle and its error along a tree equality preserves
round-by-round knowledge soundness. The output witness family and the output relation, indexed
by transcripts of the target tree, are read on the source tree through the transport of
transcripts. -/
theorem rbrKnowledgeSoundness_cast (e : s' = s) (V : OracleVerifier ambient s' S (fun _ => T)
  inputs (fun _ => outputs))
    {Win : Type} {W : PathAlong oracleSig s → Type} (impl : QueryImpl ambient (StateT σ ProbComp))
    (admissible : S × (∀ i, A i) → Prop) (relIn : (S × (∀ i, A i)) → Win → Prop)
    (relOut : (tr : PathAlong oracleSig s) → (T × (∀ j, B j)) → W tr → Prop)
    (draw : QueryImpl (challengeSpec oracleSig s') ProbComp)
    (ε : ChallengeNode oracleSig s' → ℝ≥0∞) :
    (e ▸ V).rbrKnowledgeSoundness.{0, 0, uK} impl admissible relIn relOut (e ▸ draw) (e ▸ ε) ↔
      V.rbrKnowledgeSoundness.{0, 0, uK} impl admissible relIn (W := fun tr => W (e ▸ tr))
        (fun tr => relOut (e ▸ tr)) draw ε := by
  subst e
  rfl

/-- Transporting a verifier and a challenge reindexing along a tree equality, and the prover back,
gives the same finalized program when the two finalizations agree on corresponding transcripts. -/
theorem run_cast {X κ Y : Type} {spec : OracleSpec κ} (e : s' = s)
    (V : OracleVerifier ambient s' S (fun _ => T) inputs (fun _ => outputs))
    (impl : QueryImpl (ambient + challengeSpec oracleSig s') (OracleComp spec))
    (f : Observation oracleSig s (fun _ => X) (fun _ => T × (∀ j, B j)) → Y)
    (g : Observation oracleSig s' (fun _ => X) (fun _ => T × (∀ j, B j)) → Y)
    (hfg : ∀ tr out v, f ⟨e ▸ tr, out, v⟩ = g ⟨tr, out, v⟩)
    (stmt : S) (data : ∀ i, A i) (p : Prover oracleSig ambient s (fun _ => X)) :
    simulateQ (e ▸ impl) (f <$> (e ▸ V).run stmt data p) =
      simulateQ impl (g <$> V.run stmt data (e.symm ▸ p)) := by
  subst e
  have : f = g := funext fun ⟨tr, out, v⟩ => hfg tr out v
  subst this; rfl

end Cast

end Interaction.Core.OracleVerifier
