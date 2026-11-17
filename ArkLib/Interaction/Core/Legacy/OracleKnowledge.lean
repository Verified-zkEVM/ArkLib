/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Core.Legacy.OracleExecution
public import ArkLib.Interaction.Core.Legacy.Security

/-!
# Straight-line knowledge soundness for embedded legacy oracle verifiers

Legacy knowledge soundness of an oracle verifier `V` is knowledge soundness of the induced plain
verifier `V.toVerifier`. This file transfers it to the embedded oracle verifier
`embedOracleVerifier V` on the oracle tree, in the classical straight-line oracle interface
`OracleVerifier.classicalStraightline`, with challenges drawn by the reindexed legacy challenge
implementation `oracleChallengeImpl challengeQueryImpl`.

* The logged prover-sampler run of the oracle tree is the logged run of the transported prover on
  the plain tree (`runEq_ambientLogged_oracleProver`): the same decoded transcript, outputs,
  shared-oracle log and final shared state.
* The decision's ambient log is the legacy decision's log (`oracleExtractionGame_embed`). The
  oracle decision is logged before its input-oracle and message queries are answered; the legacy
  decision answers them by `simOracle2`, without ambient queries.
* Extractors correspond through the oracle transcript equivalence (`liftOracleExtractor`,
  `lowerOracleExtractor`). The transfers `oracleKnowledgeSoundnessWith_iff` and
  `oracleKnowledgeSoundness_iff` keep the relations, the error, the rejection semantics and
  explicit extraction failure.
* Along an equality of oracle trees, transporting a verifier, its challenge oracle and its honest
  prover preserves knowledge soundness and completeness for legacy relations
  (`knowledgeSoundness_cast`, `completeness_cast`), with the output judgement
  `knowledgeJudgementOn` read on either tree.
-/

@[expose] public section

noncomputable section

universe uS uI wI wJ

namespace Interaction.Core.Legacy
open PFunctor FreeM TwoParty.Lens OracleComp OracleSpec ProtocolSpec Oracle MeasureTheory
open scoped ENNReal NNReal

variable {n : ℕ} {pSpec : ProtocolSpec n} [Oₘ : ∀ i, OracleInterface.{0, 0} (pSpec.Message i)]
  {ι : Type} {oSpec : OracleSpec ι} [∀ t, Inhabited (oSpec.Range t)]
  {StmtIn WitIn StmtOut WitOut : Type}
  {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [Oₛᵢ : ∀ i, OracleInterface.{0, 0} (OStmtIn i)]
  {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} [Oₛₒ : ∀ i, OracleInterface.{0, 0} (OStmtOut i)]
  {σ : Type}

/-! ### Extractors -/

/-- The interaction-layer view of a legacy straight-line extractor of an oracle verifier: it reads
the transcript decoded from the oracle tree, and the same two shared-oracle logs. -/
def liftOracleExtractor
    (E : _root_.Extractor.Straightline oSpec (StmtIn × ∀ i, OStmtIn i) WitIn WitOut pSpec) :
    Core.Extractor.OracleStraightline oSpec (oracleProtocol pSpec)
      (fun _ : StmtIn × (∀ i, OStmtIn i) => WitIn) (fun _ => WitOut) :=
  fun stmt tr w pl vl => E stmt w (oracleDecode pSpec tr) pl vl

/-- The legacy view of an interaction-layer straight-line extractor on the oracle tree. -/
def lowerOracleExtractor
    (E : Core.Extractor.OracleStraightline oSpec (oracleProtocol pSpec)
      (fun _ : StmtIn × (∀ i, OStmtIn i) => WitIn) (fun _ => WitOut)) :
    _root_.Extractor.Straightline oSpec (StmtIn × ∀ i, OStmtIn i) WitIn WitOut pSpec :=
  fun stmt w T pl vl => E stmt ((oracleTranscriptEquiv pSpec).symm T) w pl vl

omit [∀ t, Inhabited (oSpec.Range t)] Oₛᵢ Oₛₒ in
@[simp] theorem liftOracleExtractor_lowerOracleExtractor
    (E : Core.Extractor.OracleStraightline oSpec (oracleProtocol pSpec)
      (fun _ : StmtIn × (∀ i, OStmtIn i) => WitIn) (fun _ => WitOut)) :
    liftOracleExtractor (lowerOracleExtractor E) = E := by
  funext stmt tr w pl vl
  simp only [liftOracleExtractor, lowerOracleExtractor, oracleDecode]
  rw [Equiv.symm_apply_apply]

/-! ### The oracle knowledge program -/

/-- **Oracle knowledge program.** The extraction game of the embedded oracle verifier with a lifted
legacy extractor, read as a legacy result, is the decoded logged prover-sampler run of the oracle
tree followed by `knowledgeTail` for the induced plain verifier `V.toVerifier`.

The decision's ambient log, recorded before its input-oracle and message queries are answered, is
the log of the legacy decision, in which `simOracle2` answers those queries without ambient
queries. -/
theorem oracleExtractionGame_embed
    (V : _root_.OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec)
    (E : _root_.Extractor.Straightline oSpec (StmtIn × ∀ i, OStmtIn i) WitIn WitOut pSpec)
    (stmt : StmtIn) (oStmt : ∀ i, OStmtIn i)
    (adv : Core.Prover oracleSig oSpec (oracleProtocol pSpec)
      (fun _ => (StmtOut × (∀ i, OStmtOut i)) × WitOut)) :
    (fun z => z.1.2.2.map fun t => ((stmt, oStmt), z.2, t, z.1.2.1.2)) <$>
        (embedOracleVerifier V).extractionGame (fun _ o => o.2) (liftOracleExtractor E)
          (stmt, oStmt) adv =
      ((fun z => ((oracleDecode pSpec z.1.1, z.1.2.1), z.2)) <$> ambientLogged
        (TwoParty.Lens.run (oracleProtocol pSpec)
          (adv.simulate (fun q =>
            liftM ((oSpec + challengeSpec oracleSig (oracleProtocol pSpec)).query (.inl q))))
          (sampler oracleSig (oracleProtocol pSpec) (fun c =>
            liftM ((oSpec + challengeSpec oracleSig (oracleProtocol pSpec)).query
              (.inr c)))))) >>=
        knowledgeTail (challengeSpec oracleSig (oracleProtocol pSpec)) V.toVerifier E
          (stmt, oStmt) := by
  have hF : (fun z => z.1.2.2.map fun t => ((stmt, oStmt), z.2, t, z.1.2.1.2)) <$>
        (embedOracleVerifier V).extractionGame (fun _ o => o.2) (liftOracleExtractor E)
          (stmt, oStmt) adv =
      (embedOracleVerifier V).runWithAmbientLog stmt oStmt adv >>= fun y =>
        match y.1.2.2 with
        | none => pure none
        | some t => (fun ex => some ((stmt, oStmt), ex, t, y.1.2.1.2)) <$>
            liftComp (E (stmt, oStmt) y.1.2.1.2 (oracleDecode pSpec y.1.1) y.2.1 y.2.2).run
              (oSpec + challengeSpec oracleSig (oracleProtocol pSpec)) := by
    rw [Core.OracleVerifier.extractionGame]
    refine (_root_.map_bind _ _ _).trans (bind_congr fun x => ?_)
    rcases x with ⟨⟨tr, out, _ | v⟩, pl, vl⟩ <;> simp [liftOracleExtractor]
  have hlog := Core.OracleVerifier.runWithLog_fst (embedOracleVerifier V) stmt oStmt adv
  dsimp only at hlog
  rw [hF, ← Core.OracleVerifier.map_runWithLog_eq_runWithAmbientLog, hlog]
  simp only [ambientLogged, bind_map_left, bind_assoc]
  refine bind_congr fun x => ?_
  rw [simulateQ_embedOracleVerifier_decide, run_withLogging_inl, embedOracleVerifier_outputMap_f]
  simp only [knowledgeTail, _root_.OracleVerifier.toVerifier, OptionT.mk, simulateQ_map,
    WriterT.run_map, liftComp_map, bind_map_left, LawfulMonad.pure_bind]
  refine bind_congr fun r => ?_
  rcases r with ⟨_ | so, vl⟩
  · simp
  · simp

omit [∀ t, Inhabited (oSpec.Range t)] in
/-- **Logged prover phase on the oracle tree.** For every starting state, the decoded logged
prover-sampler run on the oracle tree agrees in distribution with the decoded logged run of the
transported prover on the plain tree, including the transcript, prover output, shared-oracle log and
final shared state. -/
theorem runEq_ambientLogged_oracleProver (impl : QueryImpl oSpec (StateT σ ProbComp))
    (chImpl : QueryImpl [pSpec.Challenge]ₒ ProbComp) {X : Type}
    (p : Core.Prover oracleSig oSpec (oracleProtocol pSpec) (fun _ => X)) :
    RunEq (expHandler impl (oracleChallengeImpl chImpl))
      (expHandler impl (plainChallengeImpl chImpl))
      ((fun z : ((_ : PathAlong oracleSig (oracleProtocol pSpec)) × X × PUnit) × QueryLog oSpec =>
          ((oracleDecode pSpec z.1.1, z.1.2.1), z.2)) <$> ambientLogged
        (TwoParty.Lens.run (oracleProtocol pSpec)
          (p.simulate (fun q =>
            liftM ((oSpec + challengeSpec oracleSig (oracleProtocol pSpec)).query (.inl q))))
          (sampler oracleSig (oracleProtocol pSpec) (fun c =>
            liftM ((oSpec + challengeSpec oracleSig (oracleProtocol pSpec)).query
              (.inr c))))))
      ((fun z : ((_ : PathAlong plainSig (protocol pSpec)) × X × PUnit) × QueryLog oSpec =>
          ((decode pSpec z.1.1, z.1.2.1), z.2)) <$> ambientLogged
        (TwoParty.Lens.run (protocol pSpec)
          (Core.Prover.simulate (fun q =>
              liftM ((oSpec + challengeSpec plainSig (protocol pSpec)).query (.inl q)))
            (toPlainFrom .focal 0 n (Nat.zero_add n) p :
              Core.Prover plainSig oSpec (protocol pSpec) (fun _ => X)))
          (sampler plainSig (protocol pSpec) (fun c =>
            liftM ((oSpec + challengeSpec plainSig (protocol pSpec)).query (.inr c)))))) :=
  RunEq.of_eq fun st => by
    rw [simulateQ_map, StateT.run_map, run_ambientLogged_nil, simulateQ_map, StateT.run_map,
      run_ambientLogged_nil, Functor.map_map, Functor.map_map,
      (oracleLayout pSpec).simulateQ_expHandler_challengeReindex (logImpl impl) chImpl,
      simulateQ_expHandler_challengeReindex (logImpl impl) chImpl]
    erw [simulateQ_oracleChallengeReindex_run, simulateQ_challengeReindex_run]
    rw [runWith_oracleLegacySampler, simulateQ_map, StateT.run_map, Functor.map_map]
    simp only [oracleDecode_toOraclePath]

/-! ### Transfers -/

/-- The output judgement of a legacy relation on the oracle tree: the verifier's output statement
and output oracle data, with the prover's output witness. -/
def oracleKnowledgeJudgement (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut)) :
    OutputJudgement (Observation oracleSig (oracleProtocol pSpec)
      (fun _ => (StmtOut × (∀ i, OStmtOut i)) × WitOut) (fun _ => StmtOut × (∀ i, OStmtOut i)))
      (relProblem relOut :
        PathProblem (oracleProtocol pSpec) (fun _ => StmtOut × (∀ i, OStmtOut i))) :=
  OutputJudgement.ofObservation (relProblem relOut) (fun _ o => o.1) (fun obs _ _ => obs.2.1.2)

variable [∀ i, SampleableType (pSpec.Challenge i)]

/-- The legacy knowledge event of a legacy prover, read through `OptionT`, has the
interaction-layer measure of the knowledge bad event on the extraction game of any oracle-tree
prover whose transport is the legacy prover's plain embedding. -/
theorem prEvent_legacy_oracleKnowledge [MeasurableSpace WitIn] {Aux : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (V : _root_.OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec)
    (E : _root_.Extractor.Straightline oSpec (StmtIn × ∀ i, OStmtIn i) WitIn WitOut pSpec)
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut))
    (stmt : StmtIn) (oStmt : ∀ i, OStmtIn i) (aux : Aux)
    (P : _root_.Prover oSpec (StmtIn × ∀ i, OStmtIn i) Aux (StmtOut × ∀ i, OStmtOut i) WitOut
      pSpec)
    (adv : Core.Prover oracleSig oSpec (oracleProtocol pSpec)
      (fun _ => (StmtOut × (∀ i, OStmtOut i)) × WitOut))
    (hadv : toPlainFrom .focal 0 n (Nat.zero_add n) adv = embedProver P (stmt, oStmt) aux)
    (hW : ∀ s : Set WitIn, MeasurableSet s) :
    Pr{let r ← OptionT.mk (experiment init impl ProtocolSpec.challengeQueryImpl
        (ambientLogged (P.run (stmt, oStmt) aux) >>=
          knowledgeTail [pSpec.Challenge]ₒ V.toVerifier E (stmt, oStmt)))}[
        (∀ w ∈ r.2.1, (r.1, w) ∉ relIn) ∧ (r.2.2.1, r.2.2.2) ∈ relOut] =
      letI : MeasurableSpace (Observation oracleSig (oracleProtocol pSpec)
        (fun _ => (StmtOut × (∀ i, OStmtOut i)) × WitOut)
        (fun _ => StmtOut × (∀ i, OStmtOut i))) := ⊤
      𝒟[experiment init impl (oracleChallengeImpl ProtocolSpec.challengeQueryImpl)
        ((embedOracleVerifier V).extractionGame (fun _ o => o.2) (liftOracleExtractor E)
          (stmt, oStmt) adv)]
        {z | (oracleKnowledgeJudgement relOut).valid z.1 ∧
          ∀ wit ∈ z.2, ¬ (relProblem relIn).rel () (stmt, oStmt) wit} := by
  let : MeasurableSpace (Observation oracleSig (oracleProtocol pSpec)
    (fun _ => (StmtOut × (∀ i, OStmtOut i)) × WitOut) (fun _ => StmtOut × (∀ i, OStmtOut i))) := ⊤
  have hprover := runEq_ambientLogged_oracleProver impl ProtocolSpec.challengeQueryImpl adv
  rw [hadv] at hprover
  have hrun : experiment init impl (oracleChallengeImpl ProtocolSpec.challengeQueryImpl)
      ((fun z => z.1.2.2.map fun t => ((stmt, oStmt), z.2, t, z.1.2.1.2)) <$>
        (embedOracleVerifier V).extractionGame (fun _ o => o.2) (liftOracleExtractor E)
          (stmt, oStmt) adv) =ᵈ
      experiment init impl ProtocolSpec.challengeQueryImpl
        (ambientLogged (P.run (stmt, oStmt) aux) >>=
          knowledgeTail [pSpec.Challenge]ₒ V.toVerifier E (stmt, oStmt)) := by
    refine experiment_evalDistEq_of_runEq init impl _ _ ?_
    rw [oracleExtractionGame_embed]
    exact RunEq.bind (fun st => (hprover st).trans
        (runEq_ambientLogged_prover impl _ P (stmt, oStmt) aux st))
      (runEq_knowledgeTail impl _ _ V.toVerifier E (stmt, oStmt))
  have hmeas : MeasurableSet {z : Observation oracleSig (oracleProtocol pSpec)
      (fun _ => (StmtOut × (∀ i, OStmtOut i)) × WitOut) (fun _ => StmtOut × (∀ i, OStmtOut i)) ×
        Option WitIn |
      (oracleKnowledgeJudgement relOut).valid z.1 ∧
        ∀ wit ∈ z.2, ¬ (relProblem relIn).rel () (stmt, oStmt) wit} :=
    show MeasurableSet (Prod.fst ⁻¹' {obs | (oracleKnowledgeJudgement relOut).valid obs} ∩
      Prod.snd ⁻¹' {o : Option WitIn | ∀ wit ∈ o, ¬ (relProblem relIn).rel () (stmt, oStmt) wit})
      from (measurable_fst MeasurableSpace.measurableSet_top).inter
        (measurable_snd (Option.measurableSet_option_iff.mpr (hW _)))
  rw [OptionT.prEvent_mk, ← hrun.prEvent_eq, experiment_map, prEvent_map]
  refine Eq.trans ?_ (prEvent_eq_evalDist _ _ (measurableSet_setOfPred.mp hmeas))
  congr 1
  congr 1
  funext ⟨⟨tr, out, v⟩, ex⟩
  cases v <;> simp [oracleKnowledgeJudgement, OutputJudgement.valid,
    OutputJudgement.ofObservation, relProblem, and_comm]

/-- **Knowledge-soundness transfer for oracle verifiers.** A legacy straight-line extractor
certifies knowledge soundness of the embedded oracle verifier, in the classical straight-line
oracle interface under the reindexed legacy challenge implementation, exactly when it certifies
legacy knowledge soundness of the oracle verifier, with the same relations and error.

The extractor is lifted by decoding the oracle transcript, and reads the same two shared-oracle
logs: the prover's log without challenge entries, and the decision's log without input-oracle and
message entries. A rejected run yields no witness, and an explicit extraction failure stays in the
bad event. A legacy prover is embedded on the oracle tree. An oracle-tree prover is transported to
the plain tree and translated into a legacy prover, which keeps its outputs. -/
theorem oracleKnowledgeSoundnessWith_iff (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (V : _root_.OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec)
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut))
    (E : _root_.Extractor.Straightline oSpec (StmtIn × ∀ i, OStmtIn i) WitIn WitOut pSpec)
    (ε : ℝ≥0) :
    letI : MeasurableSpace (Observation oracleSig (oracleProtocol pSpec)
      (fun _ => (StmtOut × (∀ i, OStmtOut i)) × WitOut) (fun _ => StmtOut × (∀ i, OStmtOut i))) := ⊤
    letI : MeasurableSpace WitIn := ⊤
    knowledgeSoundnessWith
        ((embedOracleVerifier V).classicalModel init impl
          (oracleChallengeImpl ProtocolSpec.challengeQueryImpl))
        (relProblem relIn) (relProblem relOut) (oracleKnowledgeJudgement relOut)
        ((embedOracleVerifier V).classicalStraightline (fun _ => WitIn) init impl
          (oracleChallengeImpl ProtocolSpec.challengeQueryImpl) (fun _ o => o.2))
        (liftOracleExtractor E) ε ↔
      V.knowledgeSoundnessWith init impl relIn relOut E ε := by
  let : MeasurableSpace (Observation oracleSig (oracleProtocol pSpec)
    (fun _ => (StmtOut × (∀ i, OStmtOut i)) × WitOut) (fun _ => StmtOut × (∀ i, OStmtOut i))) := ⊤
  let : MeasurableSpace WitIn := ⊤
  have hW : ∀ s : Set WitIn, MeasurableSet s := fun _ => MeasurableSpace.measurableSet_top
  constructor
  · intro h Aux stmt aux P
    dsimp only
    rw [legacy_exec_run]
    exact le_of_eq_of_le (prEvent_legacy_oracleKnowledge init impl V E relIn relOut stmt.1 stmt.2
        aux P (embedOracleProver P stmt.1 stmt.2 aux)
        (toPlainFrom_embedOracleProver P stmt.1 stmt.2 aux) hW)
      (h stmt trivial (embedOracleProver P stmt.1 stmt.2 aux)).2.2
  · intro h stmt _ adv
    refine ⟨Core.OracleVerifier.classicalStraightline_marginal _ _ _ _ _ _ _ stmt adv, le_rfl, ?_⟩
    have h' := h PUnit stmt ⟨⟩ (translate (toPlainFrom .focal 0 n (Nat.zero_add n) adv))
    dsimp only at h'
    rw [legacy_exec_run] at h'
    have hp := prEvent_legacy_oracleKnowledge init impl V E relIn relOut stmt.1 stmt.2 ⟨⟩
      (translate (toPlainFrom .focal 0 n (Nat.zero_add n) adv)) adv
      (embedProver_translate (toPlainFrom .focal 0 n (Nat.zero_add n) adv) (stmt.1, stmt.2)).symm hW
    exact le_of_eq_of_le hp.symm h'

/-- **Existential knowledge-soundness transfer for oracle verifiers.** The embedded oracle
verifier has a straight-line extractor in the classical oracle interface, under the reindexed
legacy challenge implementation, exactly when the legacy oracle verifier has a legacy
straight-line extractor, with the same relations and error. Extractors correspond through the
oracle transcript equivalence (`liftOracleExtractor`, `lowerOracleExtractor`). -/
theorem oracleKnowledgeSoundness_iff (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (V : _root_.OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec)
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut)) (ε : ℝ≥0) :
    letI : MeasurableSpace (Observation oracleSig (oracleProtocol pSpec)
      (fun _ => (StmtOut × (∀ i, OStmtOut i)) × WitOut) (fun _ => StmtOut × (∀ i, OStmtOut i))) := ⊤
    letI : MeasurableSpace WitIn := ⊤
    knowledgeSoundness
        ((embedOracleVerifier V).classicalModel init impl
          (oracleChallengeImpl ProtocolSpec.challengeQueryImpl))
        (relProblem relIn) (relProblem relOut) (oracleKnowledgeJudgement relOut)
        ((embedOracleVerifier V).classicalStraightline (fun _ => WitIn) init impl
          (oracleChallengeImpl ProtocolSpec.challengeQueryImpl) (fun _ o => o.2)) ε ↔
      V.knowledgeSoundness init impl relIn relOut ε := by
  constructor
  · rintro ⟨E, h⟩
    refine ⟨lowerOracleExtractor E,
      (oracleKnowledgeSoundnessWith_iff init impl V relIn relOut _ ε).mp ?_⟩
    exact (liftOracleExtractor_lowerOracleExtractor E).symm ▸ h
  · rintro ⟨E, h⟩
    exact ⟨liftOracleExtractor E,
      (oracleKnowledgeSoundnessWith_iff init impl V relIn relOut E ε).mpr h⟩

/-! ### Transport along a tree equality -/

section TreeTransport
variable {κ J T WIn WOut : Type} {S : Type uS} {I : Type uI}
  {ambient : OracleSpec κ} {s s' : OracleProtocol} {A : I → Type} {B : J → Type}
  {inputs : OracleFamily.{uI, 0, wI} I A} {outputs : OracleFamily.{0, 0, wJ} J B}

/-- A relation adapter with an independent claim universe, for tree transport. The legacy
`relProblem` adapter fixes its claim universe to zero. -/
abbrev treeRelationProblem {Ctx : Type} {X : Type uS} {W : Type}
    (rel : Set (X × W)) : Problem (⟨fun _ : Ctx => X⟩ : ClaimFamily Ctx) where
  Witness _ _ := W
  admissible _ _ := True
  rel _ x w := (x, w) ∈ rel
  rel_admissible _ _ _ _ := trivial

/-- The output judgement of a legacy relation on any oracle tree: the output statement and its
output witness are read from the prover's output, and the verdict from the verifier's output.
On the oracle tree of a legacy specification it is `oracleKnowledgeJudgement`. -/
abbrev knowledgeJudgementOn (s : OracleProtocol) (relOut : Set ((T × ∀ j, B j) × WOut)) :
    OutputJudgement (Observation oracleSig s (fun _ => (T × (∀ j, B j)) × WOut)
      (fun _ => T × (∀ j, B j))) (relProblem (Ctx := Path s) relOut) :=
  OutputJudgement.ofObservation (relProblem relOut) (fun _ o => o.1) (fun obs _ _ => obs.2.1.2)

/-- Transporting a verifier and its challenge oracle along a tree equality preserves knowledge
soundness for legacy relations. -/
theorem knowledgeSoundness_cast (e : s' = s) (V : OracleVerifier ambient s' S (fun _ => T) inputs
    (fun _ => outputs))
    (init : ProbComp σ) (impl : QueryImpl ambient (StateT σ ProbComp))
    (draw : QueryImpl (challengeSpec oracleSig s') ProbComp)
    (relIn : Set ((S × ∀ i, A i) × WIn)) (relOut : Set ((T × ∀ j, B j) × WOut))
    (ε : ℝ≥0∞) :
    (letI : MeasurableSpace (Observation oracleSig s (fun _ => (T × (∀ j, B j)) × WOut)
      (fun _ => T × (∀ j, B j))) := ⊤
    letI : MeasurableSpace WIn := ⊤
    knowledgeSoundness ((e ▸ V).classicalModel init impl (e ▸ draw))
      (treeRelationProblem relIn) (relProblem relOut) (knowledgeJudgementOn s relOut)
      ((e ▸ V).classicalStraightline (fun _ => WIn) init impl (e ▸ draw)
        (fun _ (o : (T × (∀ j, B j)) × WOut) => o.2))
      ε) ↔
    (letI : MeasurableSpace (Observation oracleSig s' (fun _ => (T × (∀ j, B j)) × WOut)
      (fun _ => T × (∀ j, B j))) := ⊤
    letI : MeasurableSpace WIn := ⊤
    knowledgeSoundness (V.classicalModel init impl draw)
      (treeRelationProblem relIn) (relProblem relOut) (knowledgeJudgementOn s' relOut)
      (V.classicalStraightline (fun _ => WIn) init impl draw
        (fun _ (o : (T × (∀ j, B j)) × WOut) => o.2)) ε) := by
  subst e; exact Iff.rfl

/-- Transporting a verifier, its challenge oracle and its honest prover along a tree equality
preserves completeness for legacy relations. -/
theorem completeness_cast (e : s' = s) (V : OracleVerifier ambient s' S (fun _ => T) inputs (fun _
    => outputs))
    (init : ProbComp σ) (impl : QueryImpl ambient (StateT σ ProbComp))
    (draw : QueryImpl (challengeSpec oracleSig s') ProbComp)
    (relIn : Set ((S × ∀ i, A i) × WIn)) (relOut : Set ((T × ∀ j, B j) × WOut))
    (honest : ∀ (_ : S × ∀ i, A i) (_ : WIn),
      Prover oracleSig ambient s' (fun _ => (T × (∀ j, B j)) × WOut))
    (ε : ℝ≥0∞) :
    (letI : MeasurableSpace (Observation oracleSig s (fun _ => (T × (∀ j, B j)) × WOut)
      (fun _ => T × (∀ j, B j))) := ⊤
    completeness ((e ▸ V).classicalModel init impl (e ▸ draw))
      (treeRelationProblem relIn) (relProblem relOut) (knowledgeJudgementOn s relOut)
      (fun stmt wit => e ▸ honest stmt wit) ε) ↔
    (letI : MeasurableSpace (Observation oracleSig s' (fun _ => (T × (∀ j, B j)) × WOut)
      (fun _ => T × (∀ j, B j))) := ⊤
    completeness (V.classicalModel init impl draw)
      (treeRelationProblem relIn) (relProblem relOut) (knowledgeJudgementOn s' relOut)
        honest ε) := by
  subst e; exact Iff.rfl

end TreeTransport

end Interaction.Core.Legacy
