/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Core.Legacy.OracleExecution
public import ArkLib.Interaction.Core.Legacy.Security

/-!
# Security transfers for embedded legacy oracle reductions

The notions here are stated on the oracle tree, for the embedded oracle verifier
`embedOracleVerifier V` under `OracleVerifier.classicalModel`, with challenges drawn by the
reindexed legacy challenge implementation `oracleChallengeImpl challengeQueryImpl`. Legacy
oracle notions are defined through the induced plain verifier `OracleVerifier.toVerifier`.

* Every oracle experiment is a plain experiment: the run of the embedded oracle verifier
  against an oracle-tree prover has the statistics of the run of the embedded plain verifier of
  `V.toVerifier` against the transported prover (`experiment_embedOracleVerifier_run`). The
  event "accepted in the output language" reads only the verdict, which the transport keeps.
* Completeness and soundness of the embedded oracle verifier are equivalent to the legacy
  oracle notions, with the same relations, languages and error.
* The oracle verifier's valid acceptance agrees with legacy `verify` on the decoded transcript
  (`oracleAcceptanceAgrees`), so the round-by-round transfers of `Layout` apply to the oracle
  layout.
-/

@[expose] public section

noncomputable section

namespace Interaction.Core.Legacy
open PFunctor FreeM TwoParty.Lens OracleComp OracleSpec ProtocolSpec Oracle MeasureTheory
open scoped ENNReal NNReal

variable {n : ℕ} {pSpec : ProtocolSpec n} [Oₘ : ∀ i, OracleInterface.{0, 0} (pSpec.Message i)]
  {ι : Type} {oSpec : OracleSpec ι} [∀ t, Inhabited (oSpec.Range t)]
  {StmtIn StmtOut : Type}
  {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [Oₛᵢ : ∀ i, OracleInterface.{0, 0} (OStmtIn i)]
  {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} [Oₛₒ : ∀ i, OracleInterface.{0, 0} (OStmtOut i)]
  {σ : Type}

/-! ### The oracle decision under a stateful ambient implementation -/

section Acceptance

omit [∀ t, Inhabited (oSpec.Range t)] in
/-- A stateful ambient implementation next to pure behaviors factors through the identity on the
ambient queries. -/
theorem simulateQ_addLift_id' {κ : Type} {R : OracleSpec κ} {α : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (beh : QueryImpl R Id)
    (oa : OracleComp (oSpec + R) α) :
    simulateQ (QueryImpl.addLift impl beh) oa =
      simulateQ impl (simulateQ (QueryImpl.addLift (QueryImpl.id' oSpec) beh) oa) := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
    simp only [QueryImpl.addLift_def, QueryImpl.liftTarget_self] at ih
    rcases t with q | r
    · simp [QueryImpl.addLift_def, ih]
    · have h1 : (liftM (beh r) : StateT σ ProbComp _) = pure (beh r) := rfl
      have h2 : (liftM (beh r) : OracleComp oSpec _) = pure (beh r) := rfl
      simp [QueryImpl.addLift_def, h1, h2, ih]

/-- The decision of the embedded oracle verifier on the actual payloads of a run, under a
stateful ambient implementation, is legacy `verify` on the decoded challenges with message and
input-oracle queries answered from the decoded messages and the input data. -/
theorem simulateQ_embedOracleVerifier_decide_impl (impl : QueryImpl oSpec (StateT σ ProbComp))
    (V : _root_.OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec) (stmt : StmtIn)
    (oStmt : ∀ i, OStmtIn i) (tr : PathAlong oracleSig (oracleProtocol pSpec)) :
    simulateQ (QueryImpl.addLift impl
        ((sumFamily (family OStmtIn)
          (pathFamily _ (projectPathAlong oracleSig _ tr))).behaviorOfRealizations
            (sumData oStmt (payloads _ tr))))
        ((embedOracleVerifier V).decide stmt (projectPathAlong oracleSig _ tr)
          (toView _ tr)).run =
      simulateQ impl
        (simulateQ (OracleInterface.simOracle2 oSpec oStmt (oracleDecode pSpec tr).messages)
          (V.verify stmt (oracleDecode pSpec tr).challenges).run) := by
  rw [simulateQ_addLift_id', simulateQ_embedOracleVerifier_decide, simulateQ_id']

/-- **Oracle acceptance agrees with the legacy verifier.** Valid acceptance of the embedded
oracle verifier from some ambient state is a possible accepted output of the induced legacy
verifier, run from that state on the decoded transcript. -/
theorem oracleAcceptanceAgrees (impl : QueryImpl oSpec (StateT σ ProbComp))
    (V : _root_.OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec) :
    (oracleLayout pSpec).AcceptanceAgrees impl V.toVerifier
      (fun p => (embedOracleVerifier V).validAcceptance impl p) := by
  rintro p ⟨stmt, oStmt⟩ tr
  let : MeasurableSpace (Option StmtOut) := ⊤
  refine exists_congr fun st => ?_
  change 0 < 𝒟[StateT.run' (simulateQ (QueryImpl.addLift impl
      ((sumFamily (family OStmtIn)
        (pathFamily _ (projectPathAlong oracleSig _ tr))).behaviorOfRealizations
          (sumData oStmt (payloads _ tr))))
      ((embedOracleVerifier V).decide stmt (projectPathAlong oracleSig _ tr)
        (toView _ tr)).run) st]
      {v | ∃ t, v = some t ∧ p (t, ((embedOracleVerifier V).outputMap stmt
        (projectPathAlong oracleSig _ tr) (toView _ tr)).f (sumData oStmt (payloads _ tr)))} ↔
    ∃ t, some t ∈ support (StateT.run' (simulateQ impl
      (Option.map (fun s => (s, V.materializeOutput (oracleDecode pSpec tr).challenges oStmt
        (oracleDecode pSpec tr).messages)) <$>
        simulateQ (OracleInterface.simOracle2 oSpec oStmt (oracleDecode pSpec tr).messages)
          (V.verify stmt (oracleDecode pSpec tr).challenges).run)) st) ∧ p t
  rw [simulateQ_embedOracleVerifier_decide_impl, embedOracleVerifier_outputMap_f,
    ← prEvent_eq_evalDist _ _ measurable_from_top, prEvent_pos_iff, simulateQ_map,
    StateT.run'_map', _root_.support_map]
  constructor
  · rintro ⟨_, hv, t, rfl, hp⟩
    exact ⟨_, ⟨_, hv, rfl⟩, hp⟩
  · rintro ⟨_, ⟨v, hv, hmap⟩, hp⟩
    obtain ⟨s, rfl, rfl⟩ := Option.map_eq_some_iff.mp hmap
    exact ⟨_, hv, s, rfl, hp⟩

end Acceptance

/-! ### Oracle experiments -/

section Experiments

/-- **Oracle outcomes are plain outcomes.** The measure of an event on the oracle observation of
the embedded oracle verifier is the measure of its preimage on the plain observation of the
induced legacy verifier, against the transported prover. -/
theorem evalDist_experiment_embedOracleVerifier_run (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (chImpl : QueryImpl [pSpec.Challenge]ₒ ProbComp)
    (V : _root_.OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec) (stmt : StmtIn)
    (oStmt : ∀ i, OStmtIn i) {Out : PathAlong oracleSig (oracleProtocol pSpec) → Type}
    (p : Core.Prover oracleSig oSpec (oracleProtocol pSpec) Out)
    (E : Set (Observation oracleSig (oracleProtocol pSpec) Out (StmtOut × (∀ i, OStmtOut i)))) :
    letI : MeasurableSpace
      (Observation oracleSig (oracleProtocol pSpec) Out (StmtOut × (∀ i, OStmtOut i))) := ⊤
    letI : MeasurableSpace (Observation plainSig (protocol pSpec)
      (fun tr => Out (toOraclePath 0 n (Nat.zero_add n) tr)) (StmtOut × (∀ i, OStmtOut i))) := ⊤
    𝒟[experiment init impl (oracleChallengeImpl chImpl)
        ((embedOracleVerifier V).run stmt oStmt p)] E =
      𝒟[experiment init impl (plainChallengeImpl chImpl)
        ((embedVerifier V.toVerifier).run (stmt, oStmt)
          (toPlainFrom .focal 0 n (Nat.zero_add n) p))] (toOracleObservation ⁻¹' E) := by
  let : MeasurableSpace
    (Observation oracleSig (oracleProtocol pSpec) Out (StmtOut × (∀ i, OStmtOut i))) := ⊤
  let : MeasurableSpace (Observation plainSig (protocol pSpec)
    (fun tr => Out (toOraclePath 0 n (Nat.zero_add n) tr)) (StmtOut × (∀ i, OStmtOut i))) := ⊤
  have h := experiment_embedOracleVerifier_run init impl chImpl V stmt oStmt p id
  have h0 : id <$> (embedOracleVerifier V).run stmt oStmt p =
      (embedOracleVerifier V).run stmt oStmt p := LawfulFunctor.id_map _
  rw [Function.id_comp, h0] at h
  rw [h, experiment_map, evalDist_map _ measurable_from_top,
    Measure.map_apply measurable_from_top MeasurableSpace.measurableSet_top]

end Experiments

/-! ### Completeness -/

section Completeness

variable {WitIn WitOut : Type} [∀ i, SampleableType (pSpec.Challenge i)]

/-- **Completeness transfer for oracle reductions.** The embedded oracle reduction is complete
for the honest-output judgement, under the reindexed legacy challenge implementation, exactly
when the legacy oracle reduction is complete, with the same relations and error. -/
theorem oracleCompleteness_iff (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (R : _root_.OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec)
    (relIn : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn))
    (relOut : Set ((StmtOut × (∀ i, OStmtOut i)) × WitOut)) (ε : ℝ≥0) :
    letI : MeasurableSpace (Observation oracleSig (oracleProtocol pSpec)
      (fun _ => (StmtOut × (∀ i, OStmtOut i)) × WitOut) (StmtOut × (∀ i, OStmtOut i))) := ⊤
    Core.completeness ((embedOracleVerifier R.verifier).classicalModel init impl
          (oracleChallengeImpl ProtocolSpec.challengeQueryImpl))
        (relProblem relIn) (relProblem relOut)
        (OutputJudgement.ofObservation (relProblem relOut) (fun _ o => o.1)
          (fun obs _ _ => obs.2.1.2))
        (fun stmt wit => embedOracleProver R.prover stmt.1 stmt.2 wit) ε ↔
      R.completeness init impl relIn relOut ε := by
  refine Iff.trans ?_ (completeness_iff init impl R.toReduction relIn relOut ε)
  let : MeasurableSpace (Observation oracleSig (oracleProtocol pSpec)
    (fun _ => (StmtOut × (∀ i, OStmtOut i)) × WitOut) (StmtOut × (∀ i, OStmtOut i))) := ⊤
  let : MeasurableSpace (Observation plainSig (protocol pSpec)
    (fun _ => (StmtOut × (∀ i, OStmtOut i)) × WitOut) (StmtOut × (∀ i, OStmtOut i))) := ⊤
  have hout : ∀ (stmt : StmtIn × (∀ i, OStmtIn i)) (wit : WitIn),
      ((embedOracleVerifier R.verifier).classicalModel init impl
          (oracleChallengeImpl ProtocolSpec.challengeQueryImpl)).outcome stmt
          (embedOracleProver R.prover stmt.1 stmt.2 wit)
        {obs | (OutputJudgement.ofObservation (relProblem relOut) (fun _ o => o.1)
          (fun obs _ _ => obs.2.1.2)).honest obs} =
      ((embedVerifier R.verifier.toVerifier).classicalModel init impl
          (plainChallengeImpl ProtocolSpec.challengeQueryImpl)).outcome stmt
          (embedProver R.prover stmt wit)
        {obs | (OutputJudgement.ofObservation (relProblem relOut) (fun _ o => o.1)
          (fun obs _ _ => obs.2.1.2)).honest obs} := by
    intro stmt wit
    refine (evalDist_experiment_embedOracleVerifier_run init impl _ R.verifier stmt.1 stmt.2
      _ _).trans ?_
    rw [toPlainFrom_embedOracleProver]
    rfl
  constructor
  · rintro ⟨-, h⟩
    refine ⟨MeasurableSpace.measurableSet_top, fun stmt wit hrel => ?_⟩
    exact (h stmt wit hrel).trans_eq (hout stmt wit)
  · rintro ⟨-, h⟩
    refine ⟨MeasurableSpace.measurableSet_top, fun stmt wit hrel => ?_⟩
    exact (h stmt wit hrel).trans_eq (hout stmt wit).symm

end Completeness

/-! ### Soundness -/

section Soundness

/-- **Soundness transfer for oracle reductions.** The embedded oracle verifier is sound against
every oracle-tree prover, under the reindexed legacy challenge implementation, exactly when the
legacy oracle verifier is sound, with the same languages and error.

An oracle-tree prover is transported to the plain tree, where the plain transfer
`soundness_iff` applies; a legacy prover embeds as an oracle-tree prover whose transport is its
plain embedding. -/
theorem oracleSoundness_iff [∀ i, SampleableType (pSpec.Challenge i)] (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (V : _root_.OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec)
    (langIn : Set (StmtIn × (∀ i, OStmtIn i))) (langOut : Set (StmtOut × (∀ i, OStmtOut i)))
    (ε : ℝ≥0) :
    (∀ Out : PathAlong oracleSig (oracleProtocol pSpec) → Type,
      letI : MeasurableSpace (Observation oracleSig (oracleProtocol pSpec) Out
        (StmtOut × (∀ i, OStmtOut i))) := ⊤
      Core.soundness ((embedOracleVerifier V).classicalModel (Out := Out) init impl
          (oracleChallengeImpl ProtocolSpec.challengeQueryImpl))
        (langProblem langIn) (langProblem langOut) (fun obs => obs.2.2) ε) ↔
      V.soundness init impl langIn langOut ε := by
  constructor
  · intro h WitIn WitOut witIn P stmt hstmt
    have h' := h (fun _ => (StmtOut × (∀ i, OStmtOut i)) × WitOut) stmt trivial
      (fun hl => hstmt ((langProblem_language langIn stmt).mp hl))
      (embedOracleProver P stmt.1 stmt.2 witIn)
    refine le_of_eq_of_le
      (prEvent_legacy_run init impl ProtocolSpec.challengeQueryImpl ⟨P, V.toVerifier⟩ stmt
        witIn _) ?_
    refine le_of_eq_of_le ?_ h'
    refine Eq.trans ?_ (evalDist_experiment_embedOracleVerifier_run init impl _ V stmt.1 stmt.2
      _ _).symm
    rw [toPlainFrom_embedOracleProver]
    let : MeasurableSpace (Observation plainSig (protocol pSpec)
      (fun _ => (StmtOut × (∀ i, OStmtOut i)) × WitOut) (StmtOut × (∀ i, OStmtOut i))) := ⊤
    exact congrArg (fun S => 𝒟[experiment init impl
      (plainChallengeImpl ProtocolSpec.challengeQueryImpl)
      ((embedVerifier V.toVerifier).run stmt (embedProver P stmt witIn))] S)
      (setOf_accept_eq langOut (fun _ o => o)).symm
  · intro h Out stmt _ hstmt adv
    refine le_of_eq_of_le (evalDist_experiment_embedOracleVerifier_run init impl _ V stmt.1
      stmt.2 adv _) ?_
    exact ((soundness_iff init impl V.toVerifier langIn langOut ε).mpr h)
      (fun tr => Out (toOraclePath 0 n (Nat.zero_add n) tr)) stmt trivial hstmt
      (toPlainFrom .focal 0 n (Nat.zero_add n) adv)

end Soundness

/-! ### Round-by-round soundness -/

section RoundByRound

variable {WitIn WitOut : Type} [∀ i, SampleableType (pSpec.Challenge i)]

/-- **Round-by-round soundness of an oracle verifier, legacy to interaction layer.** A legacy
round-by-round sound oracle verifier embeds as a round-by-round sound oracle verifier on the
oracle tree, under the reindexed legacy challenge implementation, with the legacy error of each
challenge node's round. The hypothesis `hcert` plays the role it plays in
`embedVerifier_rbrSoundness`: every legacy state function of `V.toVerifier` has an all-state
terminal certificate. -/
theorem embedOracleVerifier_rbrSoundness (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (V : _root_.OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec)
    (langIn : Set (StmtIn × (∀ i, OStmtIn i))) (langOut : Set (StmtOut × (∀ i, OStmtOut i)))
    (ε : pSpec.ChallengeIdx → ℝ≥0)
    (hcert : ∀ S : V.toVerifier.StateFunction init impl langIn langOut,
      StateTerminalCertificate S)
    (h : V.rbrSoundness init impl langIn langOut ε) :
    (embedOracleVerifier V).rbrSoundness impl (langProblem langIn) (langProblem langOut)
      (oracleChallengeImpl ProtocolSpec.challengeQueryImpl)
      (fun c => ε (oracleChallengeRound 0 n (Nat.zero_add n) c)) :=
  (oracleLayout pSpec).rbrSoundness_of_legacy (oracleAcceptanceAgrees impl V) langIn langOut ε
    hcert h

/-- **Round-by-round soundness of an oracle verifier, interaction layer to legacy**, for every
`init`. -/
theorem rbrSoundness_of_embedOracleVerifier (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (V : _root_.OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec)
    (langIn : Set (StmtIn × (∀ i, OStmtIn i))) (langOut : Set (StmtOut × (∀ i, OStmtOut i)))
    (ε : pSpec.ChallengeIdx → ℝ≥0)
    (h : (embedOracleVerifier V).rbrSoundness impl (langProblem langIn) (langProblem langOut)
      (oracleChallengeImpl ProtocolSpec.challengeQueryImpl)
      (fun c => ε (oracleChallengeRound 0 n (Nat.zero_add n) c))) :
    V.rbrSoundness init impl langIn langOut ε :=
  (oracleLayout pSpec).legacy_rbrSoundness (oracleAcceptanceAgrees impl V) langIn langOut ε h

/-- **Round-by-round knowledge soundness of an oracle verifier, legacy to interaction layer.**
The supplied extraction functions are kept, reindexed by legacy transcript prefixes. The
hypothesis `hcert` gives every legacy knowledge state function of `V.toVerifier` an all-state
terminal certificate. -/
theorem embedOracleVerifier_rbrKnowledgeSoundness (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (V : _root_.OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec)
    (relIn : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn))
    (relOut : Set ((StmtOut × (∀ i, OStmtOut i)) × WitOut))
    (ε : pSpec.ChallengeIdx → ℝ≥0)
    (hcert : ∀ (M : Fin (n + 1) → Type)
      (E : Extractor.RoundByRound oSpec (StmtIn × (∀ i, OStmtIn i)) WitIn WitOut pSpec M)
      (K : V.toVerifier.KnowledgeStateFunction init impl relIn relOut E),
      KnowledgeTerminalCertificate K)
    (h : V.rbrKnowledgeSoundness init impl relIn relOut ε) :
    (embedOracleVerifier V).rbrKnowledgeSoundness impl (fun _ => True)
      (fun stmt w => (stmt, w) ∈ relIn) (fun t w => (t, w) ∈ relOut)
      (oracleChallengeImpl ProtocolSpec.challengeQueryImpl)
      (fun c => ε (oracleChallengeRound 0 n (Nat.zero_add n) c)) :=
  (oracleLayout pSpec).rbrKnowledgeSoundness_of_legacy (oracleAcceptanceAgrees impl V) relIn
    relOut ε hcert h

/-- **Round-by-round knowledge soundness of an oracle verifier, interaction layer to legacy**,
with a chosen extractor; see `Layout.legacy_rbrKnowledgeSoundness`. -/
theorem rbrKnowledgeSoundness_of_embedOracleVerifier [Nonempty WitIn] (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (V : _root_.OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec)
    (relIn : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn))
    (relOut : Set ((StmtOut × (∀ i, OStmtOut i)) × WitOut))
    (ε : pSpec.ChallengeIdx → ℝ≥0)
    (h : (embedOracleVerifier V).rbrKnowledgeSoundness impl (fun _ => True)
      (fun stmt w => (stmt, w) ∈ relIn) (fun t w => (t, w) ∈ relOut)
      (oracleChallengeImpl ProtocolSpec.challengeQueryImpl)
      (fun c => ε (oracleChallengeRound 0 n (Nat.zero_add n) c))) :
    V.rbrKnowledgeSoundness init impl relIn relOut ε :=
  (oracleLayout pSpec).legacy_rbrKnowledgeSoundness (oracleAcceptanceAgrees impl V) relIn relOut
    ε h

end RoundByRound

end Interaction.Core.Legacy
