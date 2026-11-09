/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Core.Legacy.Execution
public import ArkLib.Interaction.Core.Security.Knowledge
public import ArkLib.Interaction.Core.Security.RoundByRound
public import ArkLib.OracleReduction.Security.Implications

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
* Knowledge soundness: a legacy straight-line extractor, run on the decoded transcript, certifies
  the classical straight-line notion of the embedded verifier exactly when it certifies the
  legacy notion. Both games hand the extractor the shared-oracle part of the prover's log, so no
  invariance premise on the extractor is needed.
* Round-by-round soundness and knowledge soundness: a full prefix of the plain tree corresponds
  to the legacy transcript prefix `legacyPrefix` it decodes to, and the challenge drawn at a
  node is the legacy challenge of its round. State functions transfer along this
  correspondence in both directions, as do legacy knowledge state functions and extractors.
  The error at a challenge node is the legacy error of its round. Two departures from the
  legacy statements are explicit hypotheses: the transfers into the interaction layer assume
  that `init` can produce every ambient state, and the knowledge transfer out of the
  interaction layer assumes an inhabited input witness type and yields a chosen extractor.

The transfers go through the execution correspondence in distribution, and its logged form for
knowledge soundness. They hold for every prover and need only that the legacy challenge
implementation is stateless, as it is.

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
abbrev relProblem {S W : Type} (rel : Set (S × W)) : StatementProblem S where
  Witness _ _ := W
  admissible _ _ := True
  rel _ s w := (s, w) ∈ rel
  rel_admissible _ _ _ _ := trivial

/-- The statement problem of a legacy language, with trivial witnesses. -/
abbrev langProblem {S : Type} (lang : Set S) : StatementProblem S where
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

/-! ### Mapping the outputs of a strategy -/

section MapOutput

/-- Interpreting the slots commutes with PolyFun's `Strategy.mapOutput`. -/
theorem simulate_mapOutput {P : PFunctor.{1, 0}} {l : PFunctor.Lens P rolePoly.{0}} {κ : Type}
    {spec : OracleSpec κ} {M : Type → Type} [Monad M] [LawfulMonad M] (F : QueryImpl spec M) :
    (s : FreeM P PUnit.{1}) → {Out Out' : PathAlong l s → Type} → (f : ∀ tr, Out tr → Out' tr) →
    (p : Core.Prover l spec s Out) →
    Prover.simulate F (Strategy.mapOutput f p) = Strategy.mapOutput f (Prover.simulate F p)
  | .pure _, _, _, f, p => simulateQ_map F p (f ⟨⟩)
  | .liftBind a rest, _, _, f, p => by
    rw [Prover.simulate_node, Prover.simulate_node]
    change _ <$> simulateQ F (_ <$> p) = _ <$> (_ <$> simulateQ F p)
    rw [simulateQ_map, Functor.map_map, Functor.map_map]
    refine congrArg (· <$> simulateQ F p) (funext fun c => ?_)
    refine (congrFun (Choice.map_comp _ _ _ _) c).trans ?_
    refine Eq.trans ?_ (congrFun (Choice.map_comp _ _ _ _) c).symm
    exact congrArg (fun g => Choice.map .focal (owner l a) g c)
      (funext fun x => funext fun q => simulate_mapOutput F _ (fun tr => f ⟨x, tr⟩) q)

/-- The verifier's run of a strategy with mapped outputs maps the outputs of its observation. It
is PolyFun's `runWith_mapOutput_mapOutput` with the identity map on the sampler. -/
theorem verifier_run_mapOutput {S T : Type} {s : Protocol.{0}}
    (V : Core.Verifier oSpec s S T) (stmt : S) {Out Out' : PathAlong plainSig s → Type}
    (f : ∀ tr, Out tr → Out' tr) (p : Core.Prover plainSig oSpec s Out) :
    V.run stmt (Strategy.mapOutput f p) =
      (fun obs => ⟨obs.1, f obs.1 obs.2.1, obs.2.2⟩) <$> V.run stmt p := by
  have h := runWith_mapOutput_mapOutput (m := OracleComp (oSpec + challengeSpec plainSig s))
    .focalFirst s f (fun _ x => x)
    (p.simulate (fun q => liftM ((oSpec + challengeSpec plainSig s).query (.inl q))))
    (sampler plainSig s (fun c => liftM ((oSpec + challengeSpec plainSig s).query (.inr c))))
  rw [Strategy.mapOutput_id] at h
  simp only [Core.Verifier.run, simulate_mapOutput, TwoParty.Lens.run, h, bind_assoc,
    LawfulMonad.pure_bind, _root_.map_bind]
  refine bind_congr fun r => ?_
  simp

end MapOutput

/-! ### Translating interaction-layer provers into legacy provers -/

section Translate

variable (oSpec pSpec) in
/-- The state of a translated prover before round `i`: the remaining strategy on the suffix
tree. -/
def TranslState (Out : Type) (i : Fin (n + 1)) : Type :=
  Σ' (m : ℕ) (h : i.1 + m = n),
    Core.Prover plainSig oSpec (suffix pSpec i.1 m h) (fun _ => Out)

/-- View the slot of round `j` at the node of direction `D`. -/
def toSlot (j : Fin n) {A : Type} : (D : Direction) → pSpec.dir j = D →
    OracleComp oSpec (Choice .focal (owner plainSig (plainRound pSpec j))
      (Move plainSig (plainRound pSpec j)) (fun _ => A)) →
    OracleComp oSpec (Choice .focal (owner plainSig (plainPos D (pSpec.«Type» j)))
      (Move plainSig (plainPos D (pSpec.«Type» j))) (fun _ => A))
  | _, rfl, x => x

/-- The first slot of a remaining strategy, continuing in the translated state. -/
def nextSlot {Out : Type} (j : Fin n) (m : ℕ) (h : j.1 + (m + 1) = n)
    (q : Core.Prover plainSig oSpec (suffix pSpec j.1 (m + 1) h) (fun _ => Out)) :
    OracleComp oSpec (Choice .focal (owner plainSig (plainRound pSpec j))
      (Move plainSig (plainRound pSpec j)) (fun _ => TranslState oSpec pSpec Out j.succ)) :=
  Choice.map .focal _ (fun _ next => ⟨m, by simp only [Fin.val_succ]; omega, next⟩) <$> q

/-- The legacy prover that plays a plain-tree strategy slot for slot and outputs the strategy's
output. Its private input is trivial. -/
def translate {StmtIn StmtOut WitOut : Type}
    (p : Core.Prover plainSig oSpec (protocol pSpec) (fun _ => StmtOut × WitOut)) :
    _root_.Prover oSpec StmtIn PUnit StmtOut WitOut pSpec where
  PrvState := TranslState oSpec pSpec (StmtOut × WitOut)
  input _ := ⟨n, Nat.zero_add n, p⟩
  sendMessage
    | ⟨j, _⟩, ⟨0, h, _⟩ => False.elim (by simp only [Fin.val_castSucc] at h; omega)
    | ⟨j, hj⟩, ⟨m + 1, h, q⟩ => (fun c => (c.1, c.2)) <$> toSlot j .P_to_V hj (nextSlot j m h q)
  receiveChallenge
    | ⟨j, _⟩, ⟨0, h, _⟩ => False.elim (by simp only [Fin.val_castSucc] at h; omega)
    | ⟨j, hj⟩, ⟨m + 1, h, q⟩ => toSlot j .V_to_P hj (nextSlot j m h q)
  output
    | ⟨0, _, q⟩ => q
    | ⟨_ + 1, h, _⟩ => False.elim (by simp only [Fin.val_last] at h; omega)

variable {StmtIn StmtOut WitOut : Type}

theorem roundSlot_translate
    (p : Core.Prover plainSig oSpec (protocol pSpec) (fun _ => StmtOut × WitOut))
    (j : Fin n) (D : Direction) (hD : pSpec.dir j = D) (m : ℕ) (h : j.1 + (m + 1) = n)
    (q : Core.Prover plainSig oSpec (suffix pSpec j.1 (m + 1) h) (fun _ => StmtOut × WitOut)) :
    roundSlot (translate (StmtIn := StmtIn) p) j D hD ⟨m + 1, h, q⟩ =
      toSlot j D hD (nextSlot j m h q) := by
  cases D with
  | P_to_V =>
    unfold roundSlot
    dsimp only [translate]
    erw [Functor.map_map]
    exact LawfulFunctor.id_map _
  | V_to_P => rfl

/-- The embedded translated prover from round `k` is the remaining strategy. -/
theorem embedFrom_translate
    (p : Core.Prover plainSig oSpec (protocol pSpec) (fun _ => StmtOut × WitOut)) :
    (m k : ℕ) → (h : k + m = n) →
    (q : Core.Prover plainSig oSpec (suffix pSpec k m h) (fun _ => StmtOut × WitOut)) →
    embedFrom (translate (StmtIn := StmtIn) p) k m h ⟨m, h, q⟩ = q
  | 0, k, h, q => by
    subst h
    rfl
  | m + 1, k, h, q => by
    change Choice.map .focal _ _ <$> roundSlot (translate (StmtIn := StmtIn) p)
      ⟨k, by omega⟩ _ rfl ⟨m + 1, h, q⟩ = _
    rw [roundSlot_translate]
    change _ <$> (_ <$> q) = _
    erw [Functor.map_map]
    refine Eq.trans (congrArg (· <$> q) (funext fun c => ?_)) (LawfulFunctor.id_map q)
    refine (congrFun (Choice.map_comp _ _ _ _) c).trans ?_
    refine Eq.trans ?_ (congrFun (Choice.map_id (A := fun _ => _) .focal _) c)
    exact congrArg (fun g => Choice.map .focal _ g c)
      (funext fun x => funext fun q' => embedFrom_translate p m (k + 1) (by omega) q')

/-- Translating an interaction-layer prover and embedding it back gives the same prover. -/
theorem embedProver_translate
    (p : Core.Prover plainSig oSpec (protocol pSpec) (fun _ => StmtOut × WitOut))
    (stmt : StmtIn) : embedProver (translate p) stmt ⟨⟩ = p :=
  embedFrom_translate p n 0 (Nat.zero_add n) p

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
legacy prover by `translate`, after its outputs are replaced by a fixed statement and the trivial
witness; when `StmtOut` is empty, no verdict is accepted and the bound holds trivially. -/
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
      let p' := Strategy.mapOutput (fun _ _ => ((t₀, ⟨⟩) : StmtOut × PUnit)) adv
      have hl := h PUnit PUnit ⟨⟩ (translate p') stmt
        (fun hl => hstmt ((langProblem_language langIn stmt).mpr hl))
      refine le_of_eq_of_le (Eq.symm ?_) hl
      refine (prEvent_legacy_run init impl ProtocolSpec.challengeQueryImpl
        ⟨translate p', V⟩ stmt ⟨⟩ _).trans ?_
      let : MeasurableSpace
        (Observation plainSig (protocol pSpec) (fun _ => StmtOut × PUnit) StmtOut) := ⊤
      let : MeasurableSpace (Observation plainSig (protocol pSpec) Out StmtOut) := ⊤
      change 𝒟[experiment init impl (plainChallengeImpl ProtocolSpec.challengeQueryImpl)
        ((embedVerifier V).run stmt (embedProver (translate p') stmt ⟨⟩))] _ = _
      rw [embedProver_translate]
      simp only [p']
      erw [verifier_run_mapOutput]
      rw [experiment_map, evalDist_map _ measurable_from_top,
        Measure.map_apply measurable_from_top MeasurableSpace.measurableSet_top,
        setOf_accept_eq langOut (fun _ _ => ((t₀, ⟨⟩) : StmtOut × PUnit))]
      rfl

end Soundness

/-! ### Knowledge soundness -/

section Knowledge

variable {StmtIn WitIn StmtOut WitOut Aux σ : Type}

/-- The verifier and extractor phase of the legacy knowledge game, after the logged prover run:
run the logged verifier, and on acceptance run the extractor on the decoded transcript, the
prover's output witness and the two shared-oracle logs. Both layers' games end with this phase,
over their own challenge oracles. -/
def knowledgeTail {κ : Type} (chal : OracleSpec κ)
    (V : _root_.Verifier oSpec StmtIn StmtOut pSpec)
    (E : _root_.Extractor.Straightline oSpec StmtIn WitIn WitOut pSpec) (stmt : StmtIn)
    (z : (FullTranscript pSpec × StmtOut × WitOut) × QueryLog oSpec) :
    OracleComp (oSpec + chal) (Option (StmtIn × Option WitIn × StmtOut × WitOut)) := do
  let r ← liftComp (simulateQ loggingOracle (V.verify stmt z.1.1)).run (oSpec + chal)
  match r.1 with
  | none => pure none
  | some so => do
    let ex ← liftComp (E stmt z.1.2.2 z.1.1 z.2 r.2).run (oSpec + chal)
    pure (some (stmt, ex, so, z.1.2.2))

/-- The legacy logging oracle is the logging identity implementation. -/
theorem loggingOracle_eq_id' {κ : Type} (spec : OracleSpec κ) :
    (loggingOracle : QueryImpl spec _) = (QueryImpl.id' spec).withLogging := rfl

/-- Lifting a shared-oracle program into `OptionT` over a larger specification succeeds with
its lifted result. -/
theorem run_liftM_optionT {κ : Type} {chal : OracleSpec κ} {α : Type} (y : OracleComp oSpec α) :
    (liftM y : OptionT (OracleComp (oSpec + chal)) α).run =
      some <$> (liftM y : OracleComp (oSpec + chal) α) := by
  simp only [liftM, monadLift, MonadLift.monadLift, OptionT.run_lift, OptionT.run_mk]
  rw [simulateQ_bind]
  simp only [simulateQ_pure]
  rw [map_eq_bind_pure_comp]
  rfl

/-- **Legacy knowledge program.** The legacy knowledge game is the logged prover run followed by
`knowledgeTail`. -/
theorem legacy_exec_run (V : _root_.Verifier oSpec StmtIn StmtOut pSpec)
    (E : _root_.Extractor.Straightline oSpec StmtIn WitIn WitOut pSpec) (stmtIn : StmtIn)
    (aux : Aux) (prover : _root_.Prover oSpec StmtIn Aux StmtOut WitOut pSpec) :
    (do
      let ⟨⟨⟨transcript, ⟨_, witOut⟩⟩, stmtOut⟩, proveQueryLog, verifyQueryLog⟩
        ← (_root_.Reduction.mk prover V).runWithLog stmtIn aux
      let extractedWitIn? ←
        liftM (E stmtIn witOut transcript proveQueryLog.fst verifyQueryLog).run
      return (stmtIn, extractedWitIn?, stmtOut, witOut) :
        OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ)) _).run =
      ambientLogged (prover.run stmtIn aux) >>= knowledgeTail [pSpec.Challenge]ₒ V E stmtIn := by
  simp only [ChallengeIdx, Challenge, _root_.Reduction.runWithLog, _root_.Prover.runWithLog,
    loggingOracle_eq_id', _root_.Verifier.run, LawfulMonad.bind_pure_comp, bind_assoc,
    bind_map_left, OptionT.run_bind, OptionT.run_monadLift, monadLift_self, OptionT.run_map,
    Option.elimM_map, Option.elim_some, ambientLogged, knowledgeTail, liftComp_eq_liftM]
  refine bind_congr fun a => ?_
  simp only [Option.elimM, run_liftM_optionT, Functor.map_map, Option.map_some, bind_map_left,
    Option.elim_some]
  refine bind_congr fun r => ?_
  rcases r with ⟨_ | so, vl⟩ <;> simp [Option.getM]

/-- A legacy extractor reads the prover's full log only through its shared-oracle part, so it is
invariant under moving challenge entries relative to shared-oracle entries. The transfer
therefore needs no invariance premise. -/
theorem challengeMoveInvariant_extractor {κ : Type} {chal : OracleSpec κ}
    (E : _root_.Extractor.Straightline oSpec StmtIn WitIn WitOut pSpec) (stmt : StmtIn)
    (w : WitOut) (tr : FullTranscript pSpec) (verifyLog : QueryLog oSpec) :
    ChallengeMoveInvariant (chal := chal)
      (fun log : QueryLog (oSpec + chal) => E stmt w tr log.fst verifyLog) :=
  challengeMoveInvariant_comp_fst (fun log => E stmt w tr log verifyLog)

/-- The interaction-layer view of a legacy straight-line extractor. -/
def liftExtractor (E : _root_.Extractor.Straightline oSpec StmtIn WitIn WitOut pSpec) :
    Core.Extractor.Straightline oSpec (protocol pSpec) (fun _ : StmtIn => WitIn) WitOut :=
  fun stmt w tr pl vl => E stmt w (decode pSpec tr) pl vl

/-- The legacy view of an interaction-layer straight-line extractor on the plain tree. -/
def lowerExtractor
    (E : Core.Extractor.Straightline oSpec (protocol pSpec) (fun _ : StmtIn => WitIn) WitOut) :
    _root_.Extractor.Straightline oSpec StmtIn WitIn WitOut pSpec :=
  fun stmt w tr pl vl => E stmt w ((transcriptEquiv pSpec).symm tr) pl vl

@[simp] theorem liftExtractor_lowerExtractor
    (E : Core.Extractor.Straightline oSpec (protocol pSpec) (fun _ : StmtIn => WitIn) WitOut) :
    liftExtractor (lowerExtractor E) = E := by
  funext stmt w tr pl vl
  simp [liftExtractor, lowerExtractor, decode]

/-- **Interaction-layer knowledge program.** The extraction game of the embedded verifier with a
lifted legacy extractor, read as a legacy result, is the decoded logged prover-sampler run
followed by `knowledgeTail`. -/
theorem extractionGame_embed (V : _root_.Verifier oSpec StmtIn StmtOut pSpec)
    (E : _root_.Extractor.Straightline oSpec StmtIn WitIn WitOut pSpec) (stmt : StmtIn)
    (adv : Core.Prover plainSig oSpec (protocol pSpec) (fun _ => StmtOut × WitOut)) :
    (fun z => z.1.2.2.map fun t => (stmt, z.2, t, z.1.2.1.2)) <$>
        extractionGame (embedVerifier V) (fun _ o => o.2) (liftExtractor E) stmt adv =
      ((fun z => ((decode pSpec z.1.1, z.1.2.1), z.2)) <$> ambientLogged
        (TwoParty.Lens.run (protocol pSpec)
          (adv.simulate (fun q =>
            liftM ((oSpec + challengeSpec plainSig (protocol pSpec)).query (.inl q))))
          (sampler plainSig (protocol pSpec) (fun c =>
            liftM ((oSpec + challengeSpec plainSig (protocol pSpec)).query (.inr c)))))) >>=
        knowledgeTail (challengeSpec plainSig (protocol pSpec)) V E stmt := by
  simp only [extractionGame, Core.Verifier.runWithLog, ambientLogged, _root_.map_bind,
    bind_map_left, bind_assoc]
  refine bind_congr fun a => ?_
  rcases a with ⟨⟨tr, out, ⟨⟩⟩, pl⟩
  simp only [knowledgeTail, run_withLogging_inl, embedVerifier_decide,
    LawfulMonad.pure_bind]
  refine bind_congr fun r => ?_
  rcases r with ⟨_ | so, vl⟩
  · simp
  · simp [liftExtractor]

/-- The verifier and extractor phase has the same run under either challenge oracle: it makes no
challenge queries. -/
theorem runEq_knowledgeTail {σ κ₁ κ₂ : Type} {chal₁ : OracleSpec κ₁} {chal₂ : OracleSpec κ₂}
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (ch₁ : QueryImpl chal₁ ProbComp)
    (ch₂ : QueryImpl chal₂ ProbComp) (V : _root_.Verifier oSpec StmtIn StmtOut pSpec)
    (E : _root_.Extractor.Straightline oSpec StmtIn WitIn WitOut pSpec) (stmt : StmtIn)
    (z : (FullTranscript pSpec × StmtOut × WitOut) × QueryLog oSpec) :
    RunEq (expHandler impl ch₁) (expHandler impl ch₂) (knowledgeTail chal₁ V E stmt z)
      (knowledgeTail chal₂ V E stmt z) := by
  refine RunEq.bind (runEq_liftComp impl ch₁ ch₂ _) fun r => ?_
  rcases r with ⟨_ | so, vl⟩
  · exact RunEq.pure _
  · exact RunEq.bind (runEq_liftComp impl ch₁ ch₂ _) fun _ => RunEq.pure _

/-- The output judgement of a legacy relation: the verifier's verdict with the prover's output
witness. -/
def knowledgeJudgement (relOut : Set (StmtOut × WitOut)) :
    OutputJudgement (Observation plainSig (protocol pSpec) (fun _ => StmtOut × WitOut) StmtOut)
      StmtOut (relProblem relOut) :=
  OutputJudgement.ofObservation (relProblem relOut) (fun _ o => o.1) (fun obs _ _ => obs.2.1.2)

variable [∀ i, SampleableType (pSpec.Challenge i)]

/-- The legacy knowledge event, read through `OptionT`, has the interaction-layer measure of the
knowledge bad event on the embedded prover's extraction game. -/
theorem prEvent_legacy_knowledge [MeasurableSpace WitIn] (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (V : _root_.Verifier oSpec StmtIn StmtOut pSpec)
    (E : _root_.Extractor.Straightline oSpec StmtIn WitIn WitOut pSpec)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut)) (stmt : StmtIn) (aux : Aux)
    (P : _root_.Prover oSpec StmtIn Aux StmtOut WitOut pSpec)
    (hW : ∀ s : Set WitIn, MeasurableSet s) :
    Pr{let r ← OptionT.mk (experiment init impl ProtocolSpec.challengeQueryImpl
        (ambientLogged (P.run stmt aux) >>= knowledgeTail [pSpec.Challenge]ₒ V E stmt))}[
        (∀ w ∈ r.2.1, (r.1, w) ∉ relIn) ∧ (r.2.2.1, r.2.2.2) ∈ relOut] =
      letI : MeasurableSpace
        (Observation plainSig (protocol pSpec) (fun _ => StmtOut × WitOut) StmtOut) := ⊤
      𝒟[experiment init impl (plainChallengeImpl ProtocolSpec.challengeQueryImpl)
        (extractionGame (embedVerifier V) (fun _ o => o.2) (liftExtractor E) stmt
          (embedProver P stmt aux))]
        {z | (knowledgeJudgement relOut).valid z.1 ∧
          ∀ wit ∈ z.2, ¬ (relProblem relIn).rel () stmt wit} := by
  let : MeasurableSpace
    (Observation plainSig (protocol pSpec) (fun _ => StmtOut × WitOut) StmtOut) := ⊤
  have hrun : experiment init impl (plainChallengeImpl ProtocolSpec.challengeQueryImpl)
      ((fun z => z.1.2.2.map fun t => (stmt, z.2, t, z.1.2.1.2)) <$>
        extractionGame (embedVerifier V) (fun _ o => o.2) (liftExtractor E) stmt
          (embedProver P stmt aux)) =ᵈ
      experiment init impl ProtocolSpec.challengeQueryImpl
        (ambientLogged (P.run stmt aux) >>= knowledgeTail [pSpec.Challenge]ₒ V E stmt) := by
    refine experiment_evalDistEq_of_runEq init impl _ _ ?_
    rw [extractionGame_embed]
    exact RunEq.bind (runEq_ambientLogged_prover impl _ P stmt aux)
      (runEq_knowledgeTail impl _ _ V E stmt)
  have hmeas : MeasurableSet {z : Observation plainSig (protocol pSpec)
      (fun _ => StmtOut × WitOut) StmtOut × Option WitIn |
      (knowledgeJudgement relOut).valid z.1 ∧
        ∀ wit ∈ z.2, ¬ (relProblem relIn).rel () stmt wit} :=
    show MeasurableSet (Prod.fst ⁻¹' {obs | (knowledgeJudgement relOut).valid obs} ∩
      Prod.snd ⁻¹' {o : Option WitIn | ∀ wit ∈ o, ¬ (relProblem relIn).rel () stmt wit}) from
    (measurable_fst MeasurableSpace.measurableSet_top).inter
      (measurable_snd (Option.measurableSet_option_iff.mpr (hW _)))
  rw [OptionT.prEvent_mk, ← hrun.prEvent_eq, experiment_map, prEvent_map]
  refine Eq.trans ?_ (prEvent_eq_evalDist _ _ (measurableSet_setOfPred.mp hmeas))
  congr 1
  congr 1
  funext ⟨⟨tr, out, v⟩, ex⟩
  cases v <;> simp [knowledgeJudgement, OutputJudgement.valid, OutputJudgement.ofObservation,
    relProblem, and_comm]

/-- **Knowledge-soundness transfer.** A legacy straight-line extractor certifies knowledge
soundness of the embedded verifier, in the classical straight-line interface under the reindexed
legacy challenge implementation, exactly when it certifies legacy knowledge soundness, with the
same relations and error.

The extractor is lifted by decoding the transcript, and reads the same two shared-oracle logs:
the prover's log with challenge queries removed, and the verifier's log. A legacy prover is
embedded slot for slot. An interaction-layer prover is translated into a legacy prover by
`translate`, which keeps its outputs. The extractor's output witness is the prover's output
witness, and the output relation is judged on the verifier's statement with that witness. -/
theorem knowledgeSoundnessWith_iff (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (V : _root_.Verifier oSpec StmtIn StmtOut pSpec)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (E : _root_.Extractor.Straightline oSpec StmtIn WitIn WitOut pSpec) (ε : ℝ≥0) :
    letI : MeasurableSpace
      (Observation plainSig (protocol pSpec) (fun _ => StmtOut × WitOut) StmtOut) := ⊤
    letI : MeasurableSpace WitIn := ⊤
    knowledgeSoundnessWith
        ((embedVerifier V).classicalModel init impl
          (plainChallengeImpl ProtocolSpec.challengeQueryImpl))
        (relProblem relIn) (relProblem relOut) (knowledgeJudgement relOut)
        (classicalStraightline (fun _ => WitIn) (embedVerifier V) init impl
          (plainChallengeImpl ProtocolSpec.challengeQueryImpl) (fun _ o => o.2))
        (liftExtractor E) ε ↔
      V.knowledgeSoundnessWith init impl relIn relOut E ε := by
  let : MeasurableSpace
    (Observation plainSig (protocol pSpec) (fun _ => StmtOut × WitOut) StmtOut) := ⊤
  let : MeasurableSpace WitIn := ⊤
  have hW : ∀ s : Set WitIn, MeasurableSet s := fun _ => MeasurableSpace.measurableSet_top
  constructor
  · intro h Aux stmt aux P
    dsimp only
    rw [legacy_exec_run]
    exact le_of_eq_of_le (prEvent_legacy_knowledge init impl V E relIn relOut stmt aux P hW)
      (h stmt trivial (embedProver P stmt aux)).2.2
  · intro h stmt _ adv
    refine ⟨classicalStraightline_marginal _ _ _ _ _ _ _ stmt adv, le_rfl, ?_⟩
    have h' := h PUnit stmt ⟨⟩ (translate adv)
    dsimp only at h'
    rw [legacy_exec_run] at h'
    have hp := prEvent_legacy_knowledge init impl V E relIn relOut stmt ⟨⟩ (translate adv) hW
    rw [embedProver_translate adv stmt] at hp
    exact le_of_eq_of_le hp.symm h'

/-- **Existential knowledge-soundness transfer.** The embedded verifier has a straight-line
extractor in the classical interface, under the reindexed legacy challenge implementation,
exactly when the legacy verifier has a legacy straight-line extractor, with the same relations
and error. Extractors correspond by decoding transcripts (`liftExtractor`, `lowerExtractor`). -/
theorem knowledgeSoundness_iff (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (V : _root_.Verifier oSpec StmtIn StmtOut pSpec)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut)) (ε : ℝ≥0) :
    letI : MeasurableSpace
      (Observation plainSig (protocol pSpec) (fun _ => StmtOut × WitOut) StmtOut) := ⊤
    letI : MeasurableSpace WitIn := ⊤
    knowledgeSoundness
        ((embedVerifier V).classicalModel init impl
          (plainChallengeImpl ProtocolSpec.challengeQueryImpl))
        (relProblem relIn) (relProblem relOut) (knowledgeJudgement relOut)
        (classicalStraightline (fun _ => WitIn) (embedVerifier V) init impl
          (plainChallengeImpl ProtocolSpec.challengeQueryImpl) (fun _ o => o.2)) ε ↔
      V.knowledgeSoundness init impl relIn relOut ε := by
  constructor
  · rintro ⟨E, h⟩
    refine ⟨lowerExtractor E, (knowledgeSoundnessWith_iff init impl V relIn relOut _ ε).mp ?_⟩
    exact (liftExtractor_lowerExtractor E).symm ▸ h
  · rintro ⟨E, h⟩
    exact ⟨liftExtractor E, (knowledgeSoundnessWith_iff init impl V relIn relOut E ε).mpr h⟩

end Knowledge

/-! ### Full prefixes as legacy transcript prefixes -/

namespace Layout

variable (L : Layout pSpec)

/-- The legacy transcript prefix of a full prefix of a layout's tree from round `k`, after the
transcript `pre` of the rounds before `k`. Each recorded move is the legacy payload of its
round. -/
def prefixFrom : (k m : ℕ) → (h : k + m = n) → Transcript ⟨k, by omega⟩ pSpec →
    {t : FreeM L.P PUnit.{1}} → (sp : Cursor.Spine (L.tree k m h) t) →
    PrefixMoves L.l sp → (j : Fin (n + 1)) × Transcript j pSpec
  | k, 0, _, pre, _, .root _, _ => ⟨⟨k, by omega⟩, pre⟩
  | k, _ + 1, _, pre, _, .root _, _ => ⟨⟨k, by omega⟩, pre⟩
  | k, m + 1, _, pre, _, .down _ tail, hist =>
    prefixFrom (k + 1) m (by omega)
      (Transcript.concat (m := ⟨k, by omega⟩) (L.move _ hist.1.1) pre) tail hist.2

/-- A terminal full prefix is the decoded completed transcript. -/
theorem prefixFrom_complete : (k m : ℕ) → (h : k + m = n) →
    (pre : Transcript ⟨k, by omega⟩ pSpec) →
    (sp : Cursor.Spine (L.tree k m h) (.pure ⟨⟩)) → (hist : PrefixMoves L.l sp) →
    L.prefixFrom k m h pre sp hist =
      ⟨Fin.last n, decodeFrom L.l L.pos L.move k m h pre (PrefixMoves.complete L.l sp hist)⟩
  | k, 0, h, pre, .root _, _ => by
    change (⟨⟨k, by omega⟩, pre⟩ : (j : Fin (n + 1)) × Transcript j pSpec) = _
    refine Sigma.ext (Fin.ext (by simp; omega)) (Transcript.heq_ext (by simp; omega) ?_)
    intro i _ _
    rfl
  | k, m + 1, h, pre, .down _ tail, hist => by
    obtain ⟨⟨x, hx⟩, rest⟩ := hist
    subst hx
    exact prefixFrom_complete (k + 1) m (by omega) _ tail rest

/-- At the first node of the chain from round `k`, the challenge draw is the legacy draw of
round `k`. -/
theorem draw_root (src : (i : pSpec.ChallengeIdx) → ProbComp (pSpec.Challenge i))
    (k m : ℕ) (h : k + (m + 1) = n) (hc : owner L.l (L.pos ⟨k, by omega⟩) = .receiver) :
    (fun x => L.move _ x) <$> L.draw src k (m + 1) h ⟨.inl ⟨⟩, hc⟩ =
      src ⟨⟨k, by omega⟩, (L.owner_iff _).mp hc⟩ := by
  change (fun x => L.move _ x) <$> ((L.move ⟨k, by omega⟩).symm <$>
    src ⟨⟨k, by omega⟩, (L.owner_iff _).mp hc⟩) = _
  rw [Functor.map_map]
  simp

/-- One step of a full prefix ending at a node: the node is round `j`, the prefix is a legacy
prefix `tr` before round `j`, and a move `x` extends it by the payload of `x`. At a challenge
node, the node's legacy challenge index is `j`, and the node's draw is the legacy draw of round
`j` up to the payload equivalence. -/
theorem prefixFrom_step : (k m : ℕ) → (h : k + m = n) → (pre : Transcript ⟨k, by omega⟩ pSpec) →
    {a : L.P.A} → {next : L.P.B a → FreeM L.P PUnit.{1}} →
    (sp : Cursor.Spine (L.tree k m h) (.liftBind a next)) →
    (hist : PrefixMoves L.l sp) →
    ∃ (j : Fin n) (ha : a = L.pos j) (tr : Transcript j.castSucc pSpec),
      L.prefixFrom k m h pre sp hist = ⟨j.castSucc, tr⟩ ∧
      (∀ x, L.prefixFrom k m h pre (sp.comp (.down (L.l.toFunB a x) (.root _)))
          (PrefixMoves.snoc L.l sp hist x) =
        ⟨j.succ, tr.concat (L.move j (cast (congrArg (Move L.l) ha) x))⟩) ∧
      ∀ hc : owner L.l a = .receiver, ∃ hd : pSpec.dir j = .V_to_P,
        L.challengeRound k m h (spineChallenge L.l sp hc) = ⟨j, hd⟩ ∧
        ∀ src : (i : pSpec.ChallengeIdx) → ProbComp (pSpec.Challenge i),
          (fun x => L.move j (cast (congrArg (Move L.l) ha)
            (Eq.mp (congrArg (Move L.l) (spineNode_position sp)) x))) <$>
              L.draw src k m h (spineChallenge L.l sp hc) = src ⟨j, hd⟩
  | k, 1, h, pre, _, _, .root _, _ => ⟨⟨k, by omega⟩, rfl, pre, rfl, fun _ => rfl,
      fun hc => ⟨(L.owner_iff _).mp hc, rfl, fun src => by exact L.draw_root src k 0 h hc⟩⟩
  | k, _ + 2, h, pre, _, _, .root _, _ => ⟨⟨k, by omega⟩, rfl, pre, rfl, fun _ => rfl,
      fun hc => ⟨(L.owner_iff _).mp hc, rfl, fun src => by exact L.draw_root src k _ h hc⟩⟩
  | k, m + 1, h, pre, _, _, .down _ tail, hist =>
    prefixFrom_step (k + 1) m (by omega) _ tail hist.2

/-- The legacy transcript prefix of a full prefix of a layout's tree, with its round. -/
def legacyPrefix {t : FreeM L.P PUnit.{1}} (sp : Cursor.Spine L.protocol t)
    (hist : PrefixMoves L.l sp) : (j : Fin (n + 1)) × Transcript j pSpec :=
  L.prefixFrom 0 n (Nat.zero_add n) default sp hist

/-- The empty full prefix is the empty legacy transcript. -/
theorem legacyPrefix_root : L.legacyPrefix (.root _) ⟨⟩ = ⟨0, default⟩ := by
  cases n <;> rfl

theorem legacyPrefix_root_fst : (L.legacyPrefix (.root _) ⟨⟩).1 = 0 := by
  rw [legacyPrefix_root]

/-- A terminal full prefix is the decoded full transcript. -/
theorem legacyPrefix_complete (sp : Cursor.Spine L.protocol (.pure ⟨⟩))
    (hist : PrefixMoves L.l sp) :
    L.legacyPrefix sp hist = ⟨Fin.last n, L.decode (PrefixMoves.complete L.l sp hist)⟩ :=
  L.prefixFrom_complete 0 n _ default sp hist

/-- A full prefix ending at a node is a legacy prefix before the last round. -/
theorem legacyPrefix_val_lt {a : L.P.A} {next : L.P.B a → FreeM L.P PUnit.{1}}
    (sp : Cursor.Spine L.protocol (.liftBind a next)) (hist : PrefixMoves L.l sp) :
    (L.legacyPrefix sp hist).1.val < n := by
  obtain ⟨j, -, tr, h1, -⟩ := L.prefixFrom_step 0 n _ default sp hist
  unfold legacyPrefix
  rw [h1]
  exact j.isLt

/-- One move advances the legacy round by one. -/
theorem legacyPrefix_snoc_fst {a : L.P.A} {next : L.P.B a → FreeM L.P PUnit.{1}}
    (sp : Cursor.Spine L.protocol (.liftBind a next)) (hist : PrefixMoves L.l sp)
    (x : Move L.l a) :
    (L.legacyPrefix (sp.comp (.down (L.l.toFunB a x) (.root _)))
      (PrefixMoves.snoc L.l sp hist x)).1 =
        (⟨(L.legacyPrefix sp hist).1.val, L.legacyPrefix_val_lt sp hist⟩ : Fin n).succ := by
  obtain ⟨j, rfl, tr, h1, h2, -⟩ := L.prefixFrom_step 0 n _ default sp hist
  apply Fin.ext
  simp only [Fin.val_succ]
  unfold legacyPrefix
  rw [h1, h2]
  rfl

/-- A terminal full prefix is not a legacy prefix before the last round. -/
theorem legacyPrefix_complete_ne (sp : Cursor.Spine L.protocol (.pure ⟨⟩))
    (hist : PrefixMoves L.l sp) {j : Fin n} {tr : Transcript j.castSucc pSpec} :
    L.legacyPrefix sp hist ≠ ⟨j.castSucc, tr⟩ := fun hpre => by
  have := congrArg (fun p => p.1.val) hpre
  rw [legacyPrefix_complete] at this
  simp at this
  omega

/-- The challenge draw at a node under the reindexed legacy challenge implementation. -/
theorem sampleAt_challengeImpl (chImpl : QueryImpl [pSpec.Challenge]ₒ ProbComp)
    {a : L.P.A} {next : L.P.B a → FreeM L.P PUnit.{1}}
    (sp : Cursor.Spine L.protocol (.liftBind a next)) (hc : owner L.l a = .receiver) :
    sampleAt L.l (L.challengeImpl chImpl) sp hc =
      (fun x => Eq.mp (congrArg (Move L.l) (spineNode_position sp)) x) <$>
        L.draw (fun i => chImpl ⟨i, ()⟩) 0 n (Nat.zero_add n) (spineChallenge L.l sp hc) :=
  rfl

end Layout

/-- Legacy backwards extraction respects equal rounds, transcripts and witnesses. -/
theorem extractMid_heq {StmtIn WitIn WitOut : Type} {WitMid : Fin (n + 1) → Type}
    (E : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid)
    (stmt : StmtIn) {j j' : Fin n} (hj : j = j') {T : Transcript j.succ pSpec}
    {T' : Transcript j'.succ pSpec} (hT : HEq T T') {w : WitMid j.succ} {w' : WitMid j'.succ}
    (hw : HEq w w') : HEq (E.extractMid j stmt T w) (E.extractMid j' stmt T' w') := by
  subst hj
  obtain rfl := eq_of_heq hT
  obtain rfl := eq_of_heq hw
  rfl

theorem heq_snd_of_eq {p : (j : Fin (n + 1)) × Transcript j pSpec} {j : Fin (n + 1)}
    {tr : Transcript j pSpec} (h : p = ⟨j, tr⟩) : HEq p.2 tr := by
  subst h
  rfl

/-- The legacy transcript prefix of a full prefix of the plain tree. -/
abbrev legacyPrefix {t : Protocol.{0}} (sp : Cursor.Spine (protocol pSpec) t)
    (hist : PrefixMoves plainSig sp) : (j : Fin (n + 1)) × Transcript j pSpec :=
  (plainLayout pSpec).legacyPrefix sp hist

/-- The empty full prefix of the plain tree is the empty legacy transcript. -/
theorem legacyPrefix_root (pSpec : ProtocolSpec n) :
    legacyPrefix (pSpec := pSpec) (.root _) ⟨⟩ = ⟨0, default⟩ :=
  (plainLayout pSpec).legacyPrefix_root

/-! ### Terminal acceptance -/

section Acceptance

variable {StmtIn StmtOut σ : Type}

/-- An acceptance predicate on the completed runs of a layout's tree agrees with the legacy
verifier when, for every output predicate, it holds exactly when some ambient state gives a
possible accepted output of legacy `verify` on the decoded transcript satisfying the
predicate. The plain verifier's and the oracle verifier's valid acceptance both agree with their
legacy verifiers. -/
def Layout.AcceptanceAgrees (L : Layout pSpec) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (V : _root_.Verifier oSpec StmtIn StmtOut pSpec)
    (acc : (StmtOut → Prop) → StmtIn → PathAlong L.l L.protocol → Prop) : Prop :=
  ∀ p stmt tr, acc p stmt tr ↔
    ∃ st t, some t ∈ support ((simulateQ impl (V.verify stmt (L.decode tr)).run).run' st) ∧ p t

/-- Valid acceptance of the embedded verifier from some state is a possible accepted output of
the legacy verifier, run from that state on the decoded transcript. -/
theorem validAcceptance_embed_iff (V : _root_.Verifier oSpec StmtIn StmtOut pSpec)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) :
    (plainLayout pSpec).AcceptanceAgrees impl V
      (fun p => (embedVerifier V).validAcceptance impl p) := by
  intro p stmt tr
  let : MeasurableSpace (Option StmtOut) := ⊤
  refine exists_congr fun st => ?_
  rw [← prEvent_eq_evalDist _ _ measurable_from_top, prEvent_pos_iff]
  constructor
  · rintro ⟨_, hx, t, rfl, hp⟩
    exact ⟨t, hx, hp⟩
  · rintro ⟨t, ht, hp⟩
    exact ⟨_, ht, t, rfl, hp⟩

/-- The legacy terminal event from a fresh `init` state has probability zero exactly when no
state that `init` can produce gives a possible accepted output satisfying it. -/
theorem prEvent_legacy_fresh_eq_zero_iff (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (V : _root_.Verifier oSpec StmtIn StmtOut pSpec)
    (stmt : StmtIn) (tr : FullTranscript pSpec) (p : StmtOut → Prop) :
    Pr{let t ← (OptionT.mk do (simulateQ impl (V.run stmt tr)).run' (← init))}[p t] = 0 ↔
      ∀ st ∈ support init, ∀ t,
        some t ∈ support ((simulateQ impl (V.verify stmt tr).run).run' st) → ¬ p t := by
  rw [OptionT.prEvent_mk_eq_zero_iff]
  simp only [mem_support_bind_iff]
  constructor
  · intro h st hst t ht
    exact h t ⟨st, hst, ht⟩
  · rintro h t ⟨st, hst, ht⟩
    exact h st hst t ht

/-- The legacy terminal event from a fresh `init` state has positive probability exactly when
some state that `init` can produce gives a possible accepted output satisfying it. -/
theorem prEvent_legacy_fresh_pos_iff (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (V : _root_.Verifier oSpec StmtIn StmtOut pSpec)
    (stmt : StmtIn) (tr : FullTranscript pSpec) (p : StmtOut → Prop) :
    0 < Pr{let t ← (OptionT.mk do (simulateQ impl (V.run stmt tr)).run' (← init))}[p t] ↔
      ∃ st ∈ support init, ∃ t,
        some t ∈ support ((simulateQ impl (V.verify stmt tr).run).run' st) ∧ p t := by
  rw [OptionT.prEvent_mk_pos_iff]
  simp only [mem_support_bind_iff]
  constructor
  · rintro ⟨t, ⟨st, hst, ht⟩, hp⟩
    exact ⟨st, hst, t, ht, hp⟩
  · rintro ⟨st, hst, t, ht, hp⟩
    exact ⟨t, ⟨st, hst, ht⟩, hp⟩

end Acceptance

/-! ### Round-by-round soundness -/

namespace Layout

section RoundByRound

variable (L : Layout pSpec) {StmtIn StmtOut σ : Type} {init : ProbComp σ}
  {impl : QueryImpl oSpec (StateT σ ProbComp)} {V : _root_.Verifier oSpec StmtIn StmtOut pSpec}
  {acc : (StmtOut → Prop) → StmtIn → PathAlong L.l L.protocol → Prop}

/-- The interaction-layer state function of a legacy state function: a full prefix is in the
state when its legacy transcript prefix is.

The terminal obligation of the interaction layer quantifies over every ambient state, while the
legacy one constrains only states drawn by `init`; `hinit` closes that gap. -/
def embedStateFunction (hacc : L.AcceptanceAgrees impl V acc) {langIn : Set StmtIn}
    {langOut : Set StmtOut} (hinit : ∀ st, st ∈ support init)
    (S : V.StateFunction init impl langIn langOut) :
    StateFunction L.l L.protocol StmtIn ((langProblem langIn).admissible ())
      ((langProblem langIn).language ()) (acc ((langProblem langOut).language ())) where
  toFun sp hist stmt := Sigma.uncurry (fun j tr => S.toFun j stmt tr) (L.legacyPrefix sp hist)
  root stmt _ hS := by
    rw [legacyPrefix_root] at hS
    exact (langProblem_language _ _).mpr (S.toFun_empty stmt hS)
  send sp hist stmt hown hnot x := by
    obtain ⟨j, rfl, tr, h1, h2, -⟩ := L.prefixFrom_step 0 n _ default sp hist
    unfold legacyPrefix at hnot ⊢
    rw [h1] at hnot
    rw [h2]
    exact S.toFun_next j (L.dir_eq_of_sender hown) stmt tr hnot _
  leaf sp hist stmt hnot := by
    rw [legacyPrefix_complete] at hnot
    have hzero := (prEvent_legacy_fresh_eq_zero_iff init impl V stmt _ _).mp
      (S.toFun_full stmt _ hnot)
    rw [hacc]
    rintro ⟨st, t, ht, hp⟩
    exact hzero st (hinit st) t ht ((langProblem_language _ _).mp hp)

/-- The legacy state function of an interaction-layer state function: a legacy prefix is in the
state when every full prefix with that legacy transcript prefix is. -/
def legacyStateFunction (hacc : L.AcceptanceAgrees impl V acc) {langIn : Set StmtIn}
    {langOut : Set StmtOut}
    (F : StateFunction L.l L.protocol StmtIn ((langProblem langIn).admissible ())
      ((langProblem langIn).language ()) (acc ((langProblem langOut).language ()))) :
    V.StateFunction init impl langIn langOut where
  toFun j stmt tr := ∀ (t : FreeM L.P PUnit.{1}) (sp : Cursor.Spine L.protocol t)
    (hist : PrefixMoves L.l sp), L.legacyPrefix sp hist = ⟨j, tr⟩ → F.toFun sp hist stmt
  toFun_empty stmt h :=
    (langProblem_language _ _).mp (F.root stmt trivial (h _ (.root _) ⟨⟩ L.legacyPrefix_root))
  toFun_next m hdir stmt tr hnot msg hyp := by
    refine hnot fun t sp hist hpre => by_contra fun hF => ?_
    rcases t with ⟨⟨⟩⟩ | ⟨a, next⟩
    · exact L.legacyPrefix_complete_ne sp hist hpre
    · obtain ⟨j, rfl, tr', h1, h2, -⟩ := L.prefixFrom_step 0 n _ default sp hist
      unfold legacyPrefix at hpre
      rw [h1] at hpre
      obtain ⟨hj, htr⟩ := Sigma.mk.inj_iff.mp hpre
      obtain rfl : j = m := Fin.castSucc_injective _ hj
      obtain rfl := eq_of_heq htr
      refine F.send sp hist stmt (L.owner_eq_sender hdir) hF ((L.move j).symm msg)
        (hyp _ _ _ ?_)
      unfold legacyPrefix
      rw [h2]
      simp
  toFun_full stmt tr hnot := by
    refine (prEvent_legacy_fresh_eq_zero_iff init impl V stmt tr _).mpr fun st _ t ht hp => ?_
    refine hnot fun u sp hist hpre => by_contra fun hF => ?_
    rcases u with ⟨⟨⟩⟩ | ⟨a, next⟩
    · rw [legacyPrefix_complete] at hpre
      obtain ⟨-, htr⟩ := Sigma.mk.inj_iff.mp hpre
      refine F.leaf sp hist stmt hF ((hacc _ stmt _).mpr
        ⟨st, t, ?_, (langProblem_language _ _).mpr hp⟩)
      rw [eq_of_heq htr]
      exact ht
    · have := L.legacyPrefix_val_lt sp hist
      rw [hpre] at this
      simp at this

variable [∀ i, SampleableType (pSpec.Challenge i)]

/-- **Round-by-round soundness, legacy to interaction layer**, on any layout whose acceptance
agrees with the legacy verifier. The error at a challenge node is the legacy error of its
round. -/
theorem rbrSoundness_of_legacy (hacc : L.AcceptanceAgrees impl V acc) (langIn : Set StmtIn)
    (langOut : Set StmtOut) (ε : pSpec.ChallengeIdx → ℝ≥0) (hinit : ∀ st, st ∈ support init)
    (h : V.rbrSoundness init impl langIn langOut ε) :
    Core.rbrSoundness L.l L.protocol ((langProblem langIn).admissible ())
      ((langProblem langIn).language ()) (acc ((langProblem langOut).language ()))
      (L.challengeImpl ProtocolSpec.challengeQueryImpl)
      (fun c => ε (L.challengeRound 0 n (Nat.zero_add n) c)) := by
  obtain ⟨S, hS⟩ := h
  refine ⟨L.embedStateFunction hacc hinit S, fun stmt _ hlang a next sp hc hist => ?_⟩
  obtain ⟨j, rfl, tr, h1, h2, hch⟩ := L.prefixFrom_step 0 n _ default sp hist
  obtain ⟨hd, hcr, hmap⟩ := hch hc
  have hbound := hS stmt (fun hm => hlang ((langProblem_language _ _).mpr hm)) ⟨j, hd⟩ tr
  let : MeasurableSpace (Move L.l (L.pos j)) := ⊤
  change _ ≤ ((ε (L.challengeRound 0 n _ (spineChallenge L.l sp hc)) : ℝ≥0) : ℝ≥0∞)
  rw [hcr]
  refine le_of_eq_of_le ?_ hbound
  have hm := hmap (fun i => $ᵗ (pSpec.Challenge i))
  beta_reduce at hm
  rw [← prEvent_eq_evalDist _ _ measurable_from_top, sampleAt_challengeImpl, ← hm]
  simp only [embedStateFunction, legacyPrefix]
  rw [h1]
  simp only [h2]
  exact (prEvent_map _ _ _).trans (prEvent_map _
    (fun x => L.move j (Eq.mp (congrArg (Move L.l) (spineNode_position sp)) x))
    (fun c => ¬ S.toFun j.castSucc stmt tr ∧ S.toFun j.succ stmt (tr.concat c))).symm

/-- **Round-by-round soundness, interaction layer to legacy**, on any layout whose acceptance
agrees with the legacy verifier. No hypothesis on `init` is needed: an interaction-layer
terminal obligation covers every ambient state, hence every state drawn by `init`. -/
theorem legacy_rbrSoundness (hacc : L.AcceptanceAgrees impl V acc) (langIn : Set StmtIn)
    (langOut : Set StmtOut) (ε : pSpec.ChallengeIdx → ℝ≥0)
    (h : Core.rbrSoundness L.l L.protocol ((langProblem langIn).admissible ())
      ((langProblem langIn).language ()) (acc ((langProblem langOut).language ()))
      (L.challengeImpl ProtocolSpec.challengeQueryImpl)
      (fun c => ε (L.challengeRound 0 n (Nat.zero_add n) c))) :
    V.rbrSoundness init impl langIn langOut ε := by
  obtain ⟨F, hF⟩ := h
  refine ⟨L.legacyStateFunction hacc F, fun stmt hstmt ⟨i, hi⟩ tr => ?_⟩
  by_cases hpre : (L.legacyStateFunction (init := init) hacc F).toFun i.castSucc stmt tr
  · refine le_trans (le_of_eq ?_) zero_le
    exact prEvent_eq_zero_of_forall_not _ _ fun _ hc => hc.1 hpre
  simp only [legacyStateFunction, not_forall] at hpre
  obtain ⟨t, sp, hist, hp, hFn⟩ := hpre
  rcases t with ⟨⟨⟩⟩ | ⟨a, next⟩
  · exact absurd hp (L.legacyPrefix_complete_ne sp hist)
  obtain ⟨j, rfl, tr', h1, h2, hch⟩ := L.prefixFrom_step 0 n _ default sp hist
  unfold legacyPrefix at hp
  rw [h1] at hp
  obtain ⟨hj, htr⟩ := Sigma.mk.inj_iff.mp hp
  obtain rfl : j = i := Fin.castSucc_injective _ hj
  obtain rfl := eq_of_heq htr
  obtain ⟨hd, hcr, hmap⟩ := hch ((L.owner_iff j).mpr hi)
  have hb := hF stmt trivial (fun hl => hstmt ((langProblem_language _ _).mp hl)) _ _ sp
    ((L.owner_iff j).mpr hi) hist
  simp only [hcr] at hb
  refine le_trans ?_ hb
  let : MeasurableSpace (Move L.l (L.pos j)) := ⊤
  have hm := hmap (fun i => $ᵗ (pSpec.Challenge i))
  beta_reduce at hm
  rw [← prEvent_eq_evalDist _ _ measurable_from_top, sampleAt_challengeImpl, ← hm]
  refine le_of_eq_of_le (prEvent_map _
    (fun x => L.move j (Eq.mp (congrArg (Move L.l) (spineNode_position sp)) x))
    (fun c => ¬ (L.legacyStateFunction (init := init) hacc F).toFun j.castSucc stmt tr' ∧
      (L.legacyStateFunction (init := init) hacc F).toFun j.succ stmt (tr'.concat c))) ?_
  refine le_of_le_of_eq ?_ (prEvent_map _ _ _).symm
  refine prEvent_mono _ _ _ fun x hx => ⟨hFn, hx.2 _ _ _ ?_⟩
  unfold legacyPrefix
  rw [h2]
  rfl

end RoundByRound

/-! ### Round-by-round knowledge soundness -/

section RoundByRoundKnowledge

variable (L : Layout pSpec) {StmtIn WitIn StmtOut WitOut σ : Type} {WitMid : Fin (n + 1) → Type}
  {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {V : _root_.Verifier oSpec StmtIn StmtOut pSpec}
  {acc : (StmtOut → Prop) → StmtIn → PathAlong L.l L.protocol → Prop}

/-- The legacy backwards extraction across the move `x` after the full prefix `sp`. -/
def embedExtractStep (E : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid)
    {a : L.P.A} {next : L.P.B a → FreeM L.P PUnit.{1}}
    (sp : Cursor.Spine L.protocol (.liftBind a next)) (hist : PrefixMoves L.l sp)
    (stmt : StmtIn) (x : Move L.l a)
    (w : WitMid (L.legacyPrefix (sp.comp (.down (L.l.toFunB a x) (.root _)))
      (PrefixMoves.snoc L.l sp hist x)).1) : WitMid (L.legacyPrefix sp hist).1 :=
  cast (congrArg WitMid (Fin.ext rfl))
    (E.extractMid ⟨_, L.legacyPrefix_val_lt sp hist⟩ stmt
      (cast (congrArg (fun j => Transcript j pSpec) (L.legacyPrefix_snoc_fst sp hist x))
        (L.legacyPrefix _ _).2)
      (cast (congrArg WitMid (L.legacyPrefix_snoc_fst sp hist x)) w))

/-- Along a full prefix at round `j` with legacy transcript `tr`, the legacy state after a move
and the extracted state before it are the legacy states at `tr.concat`. -/
theorem embedExtractStep_congr {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {E : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid}
    (K : V.KnowledgeStateFunction init impl relIn relOut E) (j : Fin n)
    {next : L.P.B (L.pos j) → FreeM L.P PUnit.{1}}
    (sp : Cursor.Spine L.protocol (.liftBind (L.pos j) next))
    (hist : PrefixMoves L.l sp) (tr : Transcript j.castSucc pSpec)
    (h1 : L.legacyPrefix sp hist = ⟨j.castSucc, tr⟩)
    (h2 : ∀ x, L.legacyPrefix (sp.comp (.down (L.l.toFunB _ x) (.root _)))
      (PrefixMoves.snoc L.l sp hist x) = ⟨j.succ, tr.concat (L.move j x)⟩)
    (stmt : StmtIn) (x : Move L.l (L.pos j)) (w) :
    (K.toFun _ stmt (L.legacyPrefix _ _).2 w ↔
      K.toFun j.succ stmt (tr.concat (L.move j x))
        (cast (congrArg WitMid (congrArg Sigma.fst (h2 x))) w)) ∧
    (K.toFun _ stmt (L.legacyPrefix sp hist).2 (L.embedExtractStep E sp hist stmt x w) ↔
      K.toFun j.castSucc stmt tr (E.extractMid j stmt (tr.concat (L.move j x))
        (cast (congrArg WitMid (congrArg Sigma.fst (h2 x))) w))) := by
  have hj : (⟨(L.legacyPrefix sp hist).1.val, L.legacyPrefix_val_lt sp hist⟩ : Fin n) = j :=
    Fin.ext (show (L.legacyPrefix sp hist).1.val = j.val by rw [h1]; rfl)
  refine ⟨K.toFun_congr (congrArg Sigma.fst (h2 x)) stmt (heq_snd_of_eq (h2 x))
      (cast_heq _ _).symm,
    K.toFun_congr (by rw [h1]) stmt (heq_snd_of_eq h1) ?_⟩
  refine (cast_heq _ _).trans (extractMid_heq E stmt hj ?_ ?_)
  · exact (cast_heq _ _).trans (heq_snd_of_eq (h2 x))
  · exact (cast_heq _ _).trans (cast_heq _ _).symm

/-- The interaction-layer knowledge state function of a legacy knowledge state function: the
witness at a full prefix is the legacy intermediate witness at its legacy transcript prefix, and
extraction is the legacy extractor's. The hypothesis `hinit` plays the role it plays in
`embedStateFunction`. -/
def embedKnowledgeStateFunction (hacc : L.AcceptanceAgrees impl V acc)
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {E : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid}
    (hinit : ∀ st, st ∈ support init) (K : V.KnowledgeStateFunction init impl relIn relOut E) :
    KnowledgeStateFunction L.l L.protocol StmtIn WitOut WitIn (fun _ => True)
      (fun stmt w => (stmt, w) ∈ relIn)
      (fun stmt tr wit => acc (fun t => (t, wit) ∈ relOut) stmt tr) where
  Witness sp hist := WitMid (L.legacyPrefix sp hist).1
  toFun sp hist stmt w := K.toFun (L.legacyPrefix sp hist).1 stmt (L.legacyPrefix sp hist).2 w
  extractRoot stmt w := E.extractIn stmt (cast (congrArg WitMid L.legacyPrefix_root_fst) w)
  extractStep sp hist stmt x w := L.embedExtractStep E sp hist stmt x w
  extractLeaf sp hist stmt wo :=
    cast (congrArg WitMid (congrArg Sigma.fst (L.legacyPrefix_complete sp hist)).symm)
      (E.extractOut stmt (L.decode (PrefixMoves.complete L.l sp hist)) wo)
  root stmt _ wit h := K.toFun_empty stmt _ ((K.toFun_congr L.legacyPrefix_root_fst stmt
    (heq_snd_of_eq L.legacyPrefix_root) (cast_heq _ _).symm).mp h)
  send sp hist stmt hown x wit h := by
    obtain ⟨j, rfl, tr, h1, h2, -⟩ := L.prefixFrom_step 0 n _ default sp hist
    have hc := L.embedExtractStep_congr K j sp hist tr h1 h2 stmt x wit
    exact hc.2.mpr (K.toFun_next j (L.dir_eq_of_sender hown) stmt tr _ _ (hc.1.mp h))
  leaf sp hist stmt wo hvalid := by
    have hpos := (prEvent_legacy_fresh_pos_iff init impl V stmt
      (L.decode (PrefixMoves.complete L.l sp hist)) (fun t => (t, wo) ∈ relOut)).mpr (by
        obtain ⟨st, t, ht, hp⟩ := (hacc _ stmt _).mp hvalid
        exact ⟨st, hinit st, t, ht, hp⟩)
    exact (K.toFun_congr (congrArg Sigma.fst (L.legacyPrefix_complete sp hist)).symm stmt
      (heq_snd_of_eq (L.legacyPrefix_complete sp hist)).symm (cast_heq _ _).symm).mp
        (K.toFun_full stmt _ wo hpos)

/-- The interaction-layer state function of the induced languages: some intermediate witness
makes the knowledge state true. -/
def languageStateFunction (hacc : L.AcceptanceAgrees impl V acc) {relIn : Set (StmtIn × WitIn)}
    {relOut : Set (StmtOut × WitOut)}
    (F : KnowledgeStateFunction L.l L.protocol StmtIn WitOut WitIn (fun _ => True)
      (fun stmt w => (stmt, w) ∈ relIn)
      (fun stmt tr wit => acc (fun t => (t, wit) ∈ relOut) stmt tr)) :
    StateFunction L.l L.protocol StmtIn
      ((langProblem relIn.language).admissible ()) ((langProblem relIn.language).language ())
      (acc ((langProblem relOut.language).language ())) where
  toFun sp hist stmt := ∃ w, F.toFun sp hist stmt w
  root stmt _ := fun ⟨w, hw⟩ => (langProblem_language _ _).mpr
    ((Set.mem_language_iff _ _).mpr ⟨_, F.root stmt trivial w hw⟩)
  send sp hist stmt hown hnot x := fun ⟨w, hw⟩ => hnot ⟨_, F.send sp hist stmt hown x w hw⟩
  leaf sp hist stmt hnot hacc' := by
    obtain ⟨st, t, ht, hl⟩ := (hacc _ stmt _).mp hacc'
    obtain ⟨wo, hwo⟩ := (Set.mem_language_iff _ _).mp ((langProblem_language _ _).mp hl)
    exact hnot ⟨_, F.leaf sp hist stmt wo ((hacc _ stmt _).mpr ⟨st, t, ht, hwo⟩)⟩

variable [∀ i, SampleableType (pSpec.Challenge i)]

/-- **Round-by-round knowledge soundness, legacy to interaction layer**, on any layout whose
acceptance agrees with the legacy verifier. The witness at a full prefix is the legacy
intermediate witness at its legacy transcript prefix, and the extraction functions are the
legacy extractor's, reindexed. -/
theorem rbrKnowledgeSoundness_of_legacy (hacc : L.AcceptanceAgrees impl V acc)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (ε : pSpec.ChallengeIdx → ℝ≥0) (hinit : ∀ st, st ∈ support init)
    (h : V.rbrKnowledgeSoundness init impl relIn relOut ε) :
    Core.rbrKnowledgeSoundness L.l L.protocol (fun _ => True) (fun stmt w => (stmt, w) ∈ relIn)
      (fun stmt tr wit => acc (fun t => (t, wit) ∈ relOut) stmt tr)
      (L.challengeImpl ProtocolSpec.challengeQueryImpl)
      (fun c => ε (L.challengeRound 0 n (Nat.zero_add n) c)) := by
  obtain ⟨WitMid, E, K, hK⟩ := h
  refine ⟨L.embedKnowledgeStateFunction hacc hinit K, fun stmt _ a next sp hc hist => ?_⟩
  obtain ⟨j, rfl, tr, h1, h2, hch⟩ := L.prefixFrom_step 0 n _ default sp hist
  obtain ⟨hd, hcr, hmap⟩ := hch hc
  have hbound := hK stmt ⟨j, hd⟩ tr
  let : MeasurableSpace (Move L.l (L.pos j)) := ⊤
  change _ ≤ ((ε (L.challengeRound 0 n _ (spineChallenge L.l sp hc)) : ℝ≥0) : ℝ≥0∞)
  rw [hcr]
  refine le_trans ?_ hbound
  have hm := hmap (fun i => $ᵗ (pSpec.Challenge i))
  beta_reduce at hm
  rw [← prEvent_eq_evalDist _ _ measurable_from_top, sampleAt_challengeImpl, ← hm]
  refine le_of_eq_of_le (prEvent_map _ _ _) (le_of_le_of_eq ?_ (prEvent_map _
    (fun x => L.move j (Eq.mp (congrArg (Move L.l) (spineNode_position sp)) x))
    (fun c => ∃ witMid, ¬ K.toFun j.castSucc stmt tr (E.extractMid j stmt (tr.concat c) witMid) ∧
      K.toFun j.succ stmt (tr.concat c) witMid)).symm)
  refine prEvent_mono _ _ _ fun y ⟨wit, hnot, hyes⟩ => ?_
  have hc := L.embedExtractStep_congr K j sp hist tr h1 h2 stmt
    (Eq.mp (congrArg (Move L.l) (spineNode_position sp)) y) wit
  exact ⟨_, fun h => hnot (hc.2.mpr h), hc.1.mp hyes⟩

/-- **Round-by-round knowledge soundness, interaction layer to legacy**, on any layout whose
acceptance agrees with the legacy verifier.

The interaction-layer witnesses are indexed by full prefixes, which the legacy intermediate
witness type cannot quantify over. The proof therefore drops the witnesses: the knowledge state
function induces a state function for the induced languages, whose soundness transfers by
`legacy_rbrSoundness`, and legacy round-by-round soundness for the induced languages gives
knowledge soundness with a chosen extractor. That last step needs `Nonempty WitIn`. -/
theorem legacy_rbrKnowledgeSoundness [Nonempty WitIn] (hacc : L.AcceptanceAgrees impl V acc)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (ε : pSpec.ChallengeIdx → ℝ≥0)
    (h : Core.rbrKnowledgeSoundness L.l L.protocol (fun _ => True)
      (fun stmt w => (stmt, w) ∈ relIn)
      (fun stmt tr wit => acc (fun t => (t, wit) ∈ relOut) stmt tr)
      (L.challengeImpl ProtocolSpec.challengeQueryImpl)
      (fun c => ε (L.challengeRound 0 n (Nat.zero_add n) c))) :
    V.rbrKnowledgeSoundness init impl relIn relOut ε := by
  obtain ⟨F, hF⟩ := h
  refine Verifier.rbrSoundness_implies_rbrKnowledgeSoundness init impl
    (L.legacy_rbrSoundness hacc _ _ ε ⟨L.languageStateFunction hacc F,
      fun stmt _ _ a next sp hc hist =>
        le_trans (measure_mono ?_) (hF stmt trivial a next sp hc hist)⟩)
  rintro x ⟨hn, hw⟩
  obtain ⟨w, hw⟩ := hw
  exact ⟨w, fun h => hn ⟨_, h⟩, hw⟩

end RoundByRoundKnowledge

end Layout

/-! ### The plain tree -/

section Plain

variable {StmtIn WitIn StmtOut WitOut σ : Type} [∀ i, SampleableType (pSpec.Challenge i)]

/-- **Round-by-round soundness, legacy to interaction layer.** A legacy round-by-round sound
verifier embeds as a round-by-round sound verifier under the reindexed legacy challenge
implementation, with the legacy error of each challenge node's round.

The state at a full prefix is the legacy state at its legacy transcript prefix, and the fresh
challenge at a node is the legacy challenge of its round, so each per-prefix bound is a legacy
per-prefix bound. The hypothesis `hinit` says that `init` can produce every ambient state. It is
needed because the interaction layer's terminal obligation quantifies over every ambient state,
while the legacy one is stated for a fresh `init` state. -/
theorem embedVerifier_rbrSoundness (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (V : _root_.Verifier oSpec StmtIn StmtOut pSpec) (langIn : Set StmtIn) (langOut : Set StmtOut)
    (ε : pSpec.ChallengeIdx → ℝ≥0) (hinit : ∀ st, st ∈ support init)
    (h : V.rbrSoundness init impl langIn langOut ε) :
    (embedVerifier V).rbrSoundness impl (langProblem langIn) (langProblem langOut)
      (plainChallengeImpl ProtocolSpec.challengeQueryImpl)
      (fun c => ε (challengeRound 0 n (Nat.zero_add n) c)) :=
  (plainLayout pSpec).rbrSoundness_of_legacy (validAcceptance_embed_iff V impl) langIn langOut ε
    hinit h

/-- **Round-by-round soundness, interaction layer to legacy.** If the embedded verifier is
round-by-round sound under the reindexed legacy challenge implementation, with the legacy error
of each node's round, then the legacy verifier is round-by-round sound, for every `init`. -/
theorem rbrSoundness_of_embedVerifier (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (V : _root_.Verifier oSpec StmtIn StmtOut pSpec)
    (langIn : Set StmtIn) (langOut : Set StmtOut) (ε : pSpec.ChallengeIdx → ℝ≥0)
    (h : (embedVerifier V).rbrSoundness impl (langProblem langIn) (langProblem langOut)
      (plainChallengeImpl ProtocolSpec.challengeQueryImpl)
      (fun c => ε (challengeRound 0 n (Nat.zero_add n) c))) :
    V.rbrSoundness init impl langIn langOut ε :=
  (plainLayout pSpec).legacy_rbrSoundness (validAcceptance_embed_iff V impl) langIn langOut ε h

/-- Round-by-round soundness of the embedded verifier, under the reindexed legacy challenge
implementation and with the legacy error of each node's round, is legacy round-by-round
soundness, when `init` can produce every ambient state. -/
theorem rbrSoundness_iff (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (V : _root_.Verifier oSpec StmtIn StmtOut pSpec) (langIn : Set StmtIn) (langOut : Set StmtOut)
    (ε : pSpec.ChallengeIdx → ℝ≥0) (hinit : ∀ st, st ∈ support init) :
    (embedVerifier V).rbrSoundness impl (langProblem langIn) (langProblem langOut)
        (plainChallengeImpl ProtocolSpec.challengeQueryImpl)
        (fun c => ε (challengeRound 0 n (Nat.zero_add n) c)) ↔
      V.rbrSoundness init impl langIn langOut ε :=
  ⟨rbrSoundness_of_embedVerifier init impl V langIn langOut ε,
    embedVerifier_rbrSoundness init impl V langIn langOut ε hinit⟩

/-- **Round-by-round knowledge soundness, legacy to interaction layer.** A legacy round-by-round
knowledge sound verifier embeds as a round-by-round knowledge sound verifier under the
reindexed legacy challenge implementation, with the legacy error of each challenge node's round.
The supplied extraction functions are kept, reindexed by legacy transcript prefixes. The
hypothesis `hinit` plays the role it plays in `embedVerifier_rbrSoundness`. -/
theorem embedVerifier_rbrKnowledgeSoundness (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (V : _root_.Verifier oSpec StmtIn StmtOut pSpec)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (ε : pSpec.ChallengeIdx → ℝ≥0) (hinit : ∀ st, st ∈ support init)
    (h : V.rbrKnowledgeSoundness init impl relIn relOut ε) :
    (embedVerifier V).rbrKnowledgeSoundness impl (fun _ => True) (fun stmt w => (stmt, w) ∈ relIn)
      (fun t w => (t, w) ∈ relOut) (plainChallengeImpl ProtocolSpec.challengeQueryImpl)
      (fun c => ε (challengeRound 0 n (Nat.zero_add n) c)) :=
  (plainLayout pSpec).rbrKnowledgeSoundness_of_legacy (validAcceptance_embed_iff V impl) relIn
    relOut ε hinit h

/-- **Round-by-round knowledge soundness, interaction layer to legacy.** If the embedded
verifier is round-by-round knowledge sound, then the legacy verifier is round-by-round knowledge
sound, with a chosen extractor; see `Layout.legacy_rbrKnowledgeSoundness`. -/
theorem rbrKnowledgeSoundness_of_embedVerifier [Nonempty WitIn] (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (V : _root_.Verifier oSpec StmtIn StmtOut pSpec)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (ε : pSpec.ChallengeIdx → ℝ≥0)
    (h : (embedVerifier V).rbrKnowledgeSoundness impl (fun _ => True)
      (fun stmt w => (stmt, w) ∈ relIn) (fun t w => (t, w) ∈ relOut)
      (plainChallengeImpl ProtocolSpec.challengeQueryImpl)
      (fun c => ε (challengeRound 0 n (Nat.zero_add n) c))) :
    V.rbrKnowledgeSoundness init impl relIn relOut ε :=
  (plainLayout pSpec).legacy_rbrKnowledgeSoundness (validAcceptance_embed_iff V impl) relIn relOut
    ε h

/-- Round-by-round knowledge soundness of the embedded verifier, under the reindexed legacy
challenge implementation and with the legacy error of each node's round, is legacy
round-by-round knowledge soundness, when `init` can produce every ambient state and the input
witness type is inhabited. -/
theorem rbrKnowledgeSoundness_iff [Nonempty WitIn] (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (V : _root_.Verifier oSpec StmtIn StmtOut pSpec)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (ε : pSpec.ChallengeIdx → ℝ≥0) (hinit : ∀ st, st ∈ support init) :
    (embedVerifier V).rbrKnowledgeSoundness impl (fun _ => True)
        (fun stmt w => (stmt, w) ∈ relIn) (fun t w => (t, w) ∈ relOut)
        (plainChallengeImpl ProtocolSpec.challengeQueryImpl)
        (fun c => ε (challengeRound 0 n (Nat.zero_add n) c)) ↔
      V.rbrKnowledgeSoundness init impl relIn relOut ε :=
  ⟨rbrKnowledgeSoundness_of_embedVerifier init impl V relIn relOut ε,
    embedVerifier_rbrKnowledgeSoundness init impl V relIn relOut ε hinit⟩

end Plain

end Interaction.Core.Legacy
