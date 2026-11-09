/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Core.Legacy.Execution
public import ArkLib.Interaction.Core.Security.Soundness
public import ArkLib.OracleReduction.Security.Basic

/-!
# Security transfers for embedded legacy reductions

Legacy relations and languages become statement problems with trivial admissibility. Under the
reindexed legacy challenge implementation `plainChallengeImpl challengeQueryImpl`, the classical
interaction-layer notions of the embedded reduction are equivalent to the legacy notions.

* Completeness: the embedded honest parties are judged by the honest-output judgement whose
  prover statement and witness are the honest prover's outputs. An accepted observation is
  honest exactly when the legacy result is accepted with agreeing statements in the output
  relation.
* Soundness: every interaction-layer prover is translated into a legacy prover with the same
  output measure on verdicts, and every legacy prover embeds as an interaction-layer prover with
  the same measure. The two notions are therefore equivalent.

Both transfers go through the execution correspondence in distribution, so they hold for every
prover and need only that the legacy challenge implementation is stateless, as it is.

The legacy experiment reads its result through `OptionT`, where rejection is missing mass. The
interaction-layer experiment keeps rejection as the outcome `none` of the verdict. The transfers
compare the legacy probability of an event with the interaction-layer measure of the event
"accepted, and the legacy event holds", so rejection is never identified with missing mass.
-/

@[expose] public section

namespace Interaction.Core.Legacy
open PFunctor FreeM TwoParty.Lens OracleComp OracleSpec ProtocolSpec MeasureTheory
open scoped ENNReal NNReal

variable {ι : Type} {oSpec : OracleSpec ι} {n : ℕ} {pSpec : ProtocolSpec n}

/-! ### Statement problems of legacy relations and languages -/

/-- The statement problem of a legacy relation. Every statement is admissible. -/
def relProblem {S W : Type} (rel : Set (S × W)) : StatementProblem S where
  Witness _ _ := W
  admissible _ _ := True
  rel _ s w := (s, w) ∈ rel
  rel_admissible _ _ _ _ := trivial

/-- The statement problem of a legacy language, with trivial witnesses. -/
def langProblem {S : Type} (lang : Set S) : StatementProblem S where
  Witness _ _ := Unit
  admissible _ _ := True
  rel _ s _ := s ∈ lang
  rel_admissible _ _ _ _ := trivial

@[simp] theorem langProblem_language {S : Type} (lang : Set S) (s : S) :
    (langProblem lang).language () s ↔ s ∈ lang :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨⟨⟩, h⟩⟩

/-! ### Events of the legacy result -/

section Events

variable {StmtOut WitOut σ : Type}

theorem experiment_map {κ α β : Type} {ambient : OracleSpec ι} {chal : OracleSpec κ}
    (init : ProbComp σ) (impl : QueryImpl ambient (StateT σ ProbComp))
    (chImpl : QueryImpl chal ProbComp) (f : α → β) (x : OracleComp (ambient + chal) α) :
    experiment init impl chImpl (f <$> x) = f <$> experiment init impl chImpl x := by
  simp only [experiment, simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map,
    _root_.map_bind]

/-- An event of the legacy result, read through `OptionT`, has the probability of the event
"accepted, and the legacy event holds" on the finalized observation. -/
theorem prEvent_mk_finalize
    (x : ProbComp (Observation plainSig (protocol pSpec) (fun _ => StmtOut × WitOut) StmtOut))
    (q : (FullTranscript pSpec × StmtOut × WitOut) × StmtOut → Prop) :
    Pr{let r ← OptionT.mk (finalize <$> x)}[q r] =
      letI : MeasurableSpace
        (Observation plainSig (protocol pSpec) (fun _ => StmtOut × WitOut) StmtOut) := ⊤
      𝒟[x] {obs | (finalize obs).elim False q} := by
  let : MeasurableSpace
    (Observation plainSig (protocol pSpec) (fun _ => StmtOut × WitOut) StmtOut) := ⊤
  rw [OptionT.prEvent_mk, prEvent_map]
  exact prEvent_eq_evalDist x _ measurable_from_top

/-- An event of the legacy run, read through `OptionT`, has the interaction-layer measure of
the event "accepted, and the legacy event holds" on the embedded reduction's observation. -/
theorem prEvent_legacy_run {StmtIn WitIn : Type} (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (chImpl : QueryImpl [pSpec.Challenge]ₒ ProbComp)
    (R : _root_.Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) (stmt : StmtIn) (wit : WitIn)
    (q : (FullTranscript pSpec × StmtOut × WitOut) × StmtOut → Prop) :
    Pr{let r ← OptionT.mk (experiment init impl chImpl (R.run stmt wit).run)}[q r] =
      letI : MeasurableSpace
        (Observation plainSig (protocol pSpec) (fun _ => StmtOut × WitOut) StmtOut) := ⊤
      𝒟[experiment init impl (plainChallengeImpl chImpl)
        ((embedReduction R).observe stmt wit)] {obs | (finalize obs).elim False q} := by
  rw [← prEvent_mk_finalize, ← experiment_map, OptionT.prEvent_mk, OptionT.prEvent_mk]
  exact ((experiment_finalize_observe_evalDistEq init impl chImpl R stmt wit).prEvent_eq _).symm

end Events

/-! ### Completeness -/

section Completeness

variable {StmtIn WitIn StmtOut WitOut σ : Type} [∀ i, SampleableType (pSpec.Challenge i)]

/-- **Completeness transfer.** The embedded reduction is complete for the honest-output
judgement, under the reindexed legacy challenge implementation, exactly when the legacy
reduction is complete, with the same relations and error. -/
theorem completeness_iff (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (R : _root_.Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut)) (ε : ℝ≥0) :
    (embedReduction R).completeness init impl (plainChallengeImpl ProtocolSpec.challengeQueryImpl)
        (relProblem relIn) (relProblem relOut) (fun _ o => o.1) (fun obs _ _ => obs.2.1.2)
        (fun _ w => w) ε ↔
      R.completeness init impl relIn relOut ε := by
  have hset : {obs : Observation plainSig (protocol pSpec) (fun _ => StmtOut × WitOut) StmtOut |
      (OutputJudgement.ofObservation (relProblem relOut) (fun _ o => o.1)
        (fun obs _ _ => obs.2.1.2)).honest obs} =
      {obs | (finalize obs).elim False fun r => (r.2, r.1.2.2) ∈ relOut ∧ r.1.2.1 = r.2} := by
    ext ⟨tr, out, v⟩
    cases v with
    | none => simp [OutputJudgement.honest, OutputJudgement.ofObservation, finalize]
    | some t =>
      simp only [OutputJudgement.honest, OutputJudgement.ofObservation, finalize, relProblem,
        Option.some.injEq, exists_prop, exists_eq_left', Set.mem_ofPred_eq, Option.map_some,
        Option.elim_some]
      exact and_comm
  constructor
  · rintro ⟨-, h⟩ stmt wit hrel
    have h' := h stmt wit hrel
    rw [hset] at h'
    refine le_of_le_of_eq h' ?_
    exact (prEvent_legacy_run init impl ProtocolSpec.challengeQueryImpl R stmt wit _).symm
  · intro h
    refine ⟨MeasurableSpace.measurableSet_top, fun stmt wit hrel => ?_⟩
    have h' := h stmt wit hrel
    rw [hset]
    refine le_of_le_of_eq h' ?_
    exact prEvent_legacy_run init impl ProtocolSpec.challengeQueryImpl R stmt wit _

end Completeness

/-! ### Mapping the outputs of a plain-tree strategy -/

section MapOut

/-- Map the leaf outputs of a focal strategy on a plain tree, keeping every slot. -/
def mapOut {M : Type → Type} [Functor M] : (s : Protocol.{0}) →
    {Out Out' : PathAlong plainSig s → Type} → (∀ tr, Out tr → Out' tr) →
    Focal plainSig M s Out → Focal plainSig M s Out'
  | .pure ⟨⟩, _, _, f, p => f ⟨⟩ <$> p
  | .liftBind a rest, _, _, f, p =>
    Choice.map .focal (owner plainSig a)
      (fun x next => mapOut (rest (plainSig.toFunB a x)) (fun tr o => f ⟨x, tr⟩ o) next) <$> p

/-- Interpreting the slots commutes with mapping the outputs. -/
theorem simulate_mapOut {κ : Type} {spec : OracleSpec κ} {M : Type → Type} [Monad M]
    [LawfulMonad M] (F : QueryImpl spec M) : (s : Protocol.{0}) →
    {Out Out' : PathAlong plainSig s → Type} → (f : ∀ tr, Out tr → Out' tr) →
    (p : Core.Prover plainSig spec s Out) →
    Prover.simulate F (mapOut s f p) = mapOut s f (Prover.simulate F p)
  | .pure ⟨⟩, _, _, f, p => by
    change simulateQ F (_ <$> p) = _ <$> simulateQ F p
    exact simulateQ_map F p _
  | .liftBind a rest, _, _, f, p => by
    change _ <$> simulateQ F (_ <$> p) = _ <$> (_ <$> simulateQ F p)
    rw [simulateQ_map, Functor.map_map, Functor.map_map]
    refine congrArg (· <$> simulateQ F p) (funext fun c => ?_)
    refine (congrFun (Choice.map_comp _ _ _ _) c).trans ?_
    refine Eq.trans ?_ (congrFun (Choice.map_comp _ _ _ _) c).symm
    exact congrArg (fun g => Choice.map .focal (owner plainSig a) g c)
      (funext fun x => funext fun q => simulate_mapOut F _ _ q)

/-- Running a strategy with mapped outputs maps the outputs of the run. -/
theorem runWith_mapOut {M : Type → Type} [Monad M] [LawfulMonad M] (order : Schedule) :
    (s : Protocol.{0}) → {Out Out' OutC : PathAlong plainSig s → Type} →
    (f : ∀ tr, Out tr → Out' tr) → (p : Focal plainSig M s Out) →
    (c : Counterpart plainSig M s OutC) →
    runWith order s (mapOut s f p) c =
      (fun r => ⟨r.1, f r.1 r.2.1, r.2.2⟩) <$> runWith order s p c
  | .pure ⟨⟩, _, _, _, f, p, c => by
    erw [runWith_done, runWith_done]
    cases order <;> simp [Schedule.seq, _root_.map_bind, mapOut]
  | .liftBind a rest, _, _, _, f, p, c => by
    rw [runWith_liftBind, runWith_liftBind]
    change step _ _ (_ <$> p) c _ = _
    rw [step_map_left, map_eq_bind_pure_comp, step_bind]
    refine congrArg (step _ order p c) (funext fun x => funext fun q => funext fun c' => ?_)
    rw [runWith_mapOut order _ _ q c', bind_map_left]
    simp only [bind_assoc, LawfulMonad.pure_bind, Function.comp_apply]

/-- The verifier's run of a strategy with mapped outputs maps the outputs of its observation. -/
theorem verifier_run_mapOut {S T : Type} {s : Protocol.{0}}
    (V : Core.Verifier oSpec s S T) (stmt : S) {Out Out' : PathAlong plainSig s → Type}
    (f : ∀ tr, Out tr → Out' tr) (p : Core.Prover plainSig oSpec s Out) :
    V.run stmt (mapOut s f p) =
      (fun obs => ⟨obs.1, f obs.1 obs.2.1, obs.2.2⟩) <$> V.run stmt p := by
  simp only [Core.Verifier.run, simulate_mapOut, TwoParty.Lens.run, runWith_mapOut,
    bind_map_left, _root_.map_bind]
  refine bind_congr fun r => ?_
  rcases r with ⟨tr, out, ⟨⟩⟩
  simp

end MapOut

/-! ### Translating interaction-layer provers into legacy provers -/

section Translate

variable (oSpec pSpec) in
/-- The state of a translated prover before round `i`: the remaining strategy on the suffix
tree. -/
def TranslState (i : Fin (n + 1)) : Type :=
  Σ' (m : ℕ) (h : i.1 + m = n),
    Core.Prover plainSig oSpec (suffix pSpec i.1 m h) (fun _ => PUnit)

/-- View the slot of round `j` at the node of direction `D`. -/
def toSlot (j : Fin n) {A : Type} : (D : Direction) → pSpec.dir j = D →
    OracleComp oSpec (Choice .focal (owner plainSig (plainRound pSpec j))
      (Move plainSig (plainRound pSpec j)) (fun _ => A)) →
    OracleComp oSpec (Choice .focal (owner plainSig (plainPos D (pSpec.«Type» j)))
      (Move plainSig (plainPos D (pSpec.«Type» j))) (fun _ => A))
  | _, rfl, x => x

/-- The first slot of a remaining strategy, continuing in the translated state. -/
def nextSlot (j : Fin n) (m : ℕ) (h : j.1 + (m + 1) = n)
    (q : Core.Prover plainSig oSpec (suffix pSpec j.1 (m + 1) h) (fun _ => PUnit)) :
    OracleComp oSpec (Choice .focal (owner plainSig (plainRound pSpec j))
      (Move plainSig (plainRound pSpec j)) (fun _ => TranslState oSpec pSpec j.succ)) :=
  Choice.map .focal _ (fun _ next => ⟨m, by simp only [Fin.val_succ]; omega, next⟩) <$> q

/-- The legacy prover that plays a plain-tree strategy slot for slot. Its statement output is
the fixed value `t₀`, and its witnesses are trivial. -/
def translate {StmtIn StmtOut : Type}
    (p : Core.Prover plainSig oSpec (protocol pSpec) (fun _ => PUnit)) (t₀ : StmtOut) :
    _root_.Prover oSpec StmtIn PUnit StmtOut PUnit pSpec where
  PrvState := TranslState oSpec pSpec
  input _ := ⟨n, Nat.zero_add n, p⟩
  sendMessage
    | ⟨j, _⟩, ⟨0, h, _⟩ => False.elim (by simp only [Fin.val_castSucc] at h; omega)
    | ⟨j, hj⟩, ⟨m + 1, h, q⟩ => (fun c => (c.1, c.2)) <$> toSlot j .P_to_V hj (nextSlot j m h q)
  receiveChallenge
    | ⟨j, _⟩, ⟨0, h, _⟩ => False.elim (by simp only [Fin.val_castSucc] at h; omega)
    | ⟨j, hj⟩, ⟨m + 1, h, q⟩ => toSlot j .V_to_P hj (nextSlot j m h q)
  output
    | ⟨0, _, q⟩ => (fun _ => (t₀, ⟨⟩)) <$> q
    | ⟨_ + 1, h, _⟩ => False.elim (by simp only [Fin.val_last] at h; omega)

variable {StmtIn StmtOut : Type}

theorem roundSlot_translate (p : Core.Prover plainSig oSpec (protocol pSpec) (fun _ => PUnit))
    (t₀ : StmtOut) (j : Fin n) (D : Direction) (hD : pSpec.dir j = D) (m : ℕ)
    (h : j.1 + (m + 1) = n)
    (q : Core.Prover plainSig oSpec (suffix pSpec j.1 (m + 1) h) (fun _ => PUnit)) :
    roundSlot (translate (StmtIn := StmtIn) p t₀) j D hD ⟨m + 1, h, q⟩ =
      toSlot j D hD (nextSlot j m h q) := by
  cases D with
  | P_to_V =>
    unfold roundSlot
    dsimp only [translate]
    erw [Functor.map_map]
    exact LawfulFunctor.id_map _
  | V_to_P => rfl

/-- The embedded translated prover from round `k` maps the outputs of the remaining strategy to
`(t₀, ⟨⟩)`. -/
theorem embedFrom_translate (p : Core.Prover plainSig oSpec (protocol pSpec) (fun _ => PUnit))
    (t₀ : StmtOut) : (m k : ℕ) → (h : k + m = n) →
    (q : Core.Prover plainSig oSpec (suffix pSpec k m h) (fun _ => PUnit)) →
    embedFrom (translate (StmtIn := StmtIn) p t₀) k m h ⟨m, h, q⟩ =
      mapOut _ (fun _ _ => (t₀, ⟨⟩)) q
  | 0, k, h, q => by
    subst h
    rfl
  | m + 1, k, h, q => by
    change Choice.map .focal _ _ <$> roundSlot (translate (StmtIn := StmtIn) p t₀)
      ⟨k, by omega⟩ _ rfl ⟨m + 1, h, q⟩ = _
    rw [roundSlot_translate]
    change _ <$> (_ <$> q) = _
    erw [Functor.map_map]
    refine congrArg (· <$> q) (funext fun c => ?_)
    refine (congrFun (Choice.map_comp _ _ _ _) c).trans ?_
    exact congrArg (fun g => Choice.map .focal _ g c)
      (funext fun x => funext fun q' => embedFrom_translate p t₀ m (k + 1) (by omega) q')

theorem embedProver_translate
    (p : Core.Prover plainSig oSpec (protocol pSpec) (fun _ => PUnit)) (t₀ : StmtOut)
    (stmt : StmtIn) :
    embedProver (translate p t₀) stmt ⟨⟩ = mapOut _ (fun _ _ => (t₀, ⟨⟩)) p :=
  embedFrom_translate p t₀ n 0 (Nat.zero_add n) p

end Translate

/-! ### Soundness -/

section Soundness

variable {StmtIn StmtOut σ : Type}

/-- The accepted-in-language event is the legacy event on the finalized observation. -/
theorem setOf_accept_eq {Out : PathAlong plainSig (protocol pSpec) → Type} {WitOut : Type}
    (langOut : Set StmtOut) (g : ∀ tr, Out tr → StmtOut × WitOut) :
    {obs : Observation plainSig (protocol pSpec) Out StmtOut |
        ∃ t, obs.2.2 = some t ∧ (langProblem langOut).language () t} =
      (fun obs => (⟨obs.1, g obs.1 obs.2.1, obs.2.2⟩ :
        Observation plainSig (protocol pSpec) (fun _ => StmtOut × WitOut) StmtOut)) ⁻¹'
        {obs | (finalize obs).elim False fun r => r.2 ∈ langOut} := by
  ext ⟨tr, out, v⟩
  cases v <;> simp [finalize]

/-- **Soundness transfer.** The embedded verifier is sound against every interaction-layer
prover, under the reindexed legacy challenge implementation, exactly when the legacy verifier is
sound against every legacy prover, with the same languages and error.

A legacy prover is embedded slot for slot. An interaction-layer prover is translated into a
legacy prover by `translate`, after its outputs are forgotten; when `StmtOut` is empty, no
verdict is accepted and the bound holds trivially. -/
theorem soundness_iff [∀ i, SampleableType (pSpec.Challenge i)] (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (V : _root_.Verifier oSpec StmtIn StmtOut pSpec) (langIn : Set StmtIn)
    (langOut : Set StmtOut) (ε : ℝ≥0) :
    (embedVerifier V).soundness init impl (plainChallengeImpl ProtocolSpec.challengeQueryImpl)
        (langProblem langIn) (langProblem langOut) ε ↔
      V.soundness init impl langIn langOut ε := by
  constructor
  · intro h WitIn WitOut witIn P stmt hstmt
    have h' := h (fun _ => StmtOut × WitOut) stmt trivial
      (fun hl => hstmt ((langProblem_language langIn stmt).mp hl)) (embedProver P stmt witIn)
    refine le_of_eq_of_le
      (prEvent_legacy_run init impl ProtocolSpec.challengeQueryImpl ⟨P, V⟩ stmt witIn _) ?_
    refine le_of_eq_of_le ?_ h'
    rw [setOf_accept_eq langOut (fun _ o => o)]
    rfl
  · intro h Out stmt _ hstmt adv
    rcases isEmpty_or_nonempty StmtOut with hT | hT
    · refine le_of_eq_of_le (b := 0) ?_ zero_le
      simp only [IsEmpty.exists_iff, Set.ofPred_false, measure_empty]
    · obtain ⟨t₀⟩ := hT
      let p' := mapOut _ (fun _ _ => (⟨⟩ : PUnit)) adv
      have hl := h PUnit PUnit ⟨⟩ (translate p' t₀) stmt
        (fun hl => hstmt ((langProblem_language langIn stmt).mpr hl))
      refine le_of_eq_of_le (Eq.symm ?_) hl
      refine (prEvent_legacy_run init impl ProtocolSpec.challengeQueryImpl
        ⟨translate p' t₀, V⟩ stmt ⟨⟩ _).trans ?_
      let : MeasurableSpace
        (Observation plainSig (protocol pSpec) (fun _ => PUnit) StmtOut) := ⊤
      let : MeasurableSpace
        (Observation plainSig (protocol pSpec) (fun _ => StmtOut × PUnit) StmtOut) := ⊤
      let : MeasurableSpace (Observation plainSig (protocol pSpec) Out StmtOut) := ⊤
      change 𝒟[experiment init impl (plainChallengeImpl ProtocolSpec.challengeQueryImpl)
        ((embedVerifier V).run stmt (embedProver (translate p' t₀) stmt ⟨⟩))] _ = _
      rw [embedProver_translate, verifier_run_mapOut]
      simp only [p']
      erw [verifier_run_mapOut]
      rw [experiment_map,
        experiment_map, evalDist_map _ measurable_from_top, evalDist_map _ measurable_from_top,
        Measure.map_apply measurable_from_top MeasurableSpace.measurableSet_top,
        Measure.map_apply measurable_from_top MeasurableSpace.measurableSet_top,
        setOf_accept_eq langOut (fun _ _ => ((t₀, ⟨⟩) : StmtOut × PUnit))]
      rfl

end Soundness

end Interaction.Core.Legacy
