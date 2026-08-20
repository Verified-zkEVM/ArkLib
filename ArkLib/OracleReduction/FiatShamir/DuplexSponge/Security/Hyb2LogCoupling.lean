/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.RevisedHybridGame
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.DecodedFibreCoupling
import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-!
# Logged fixed-table H₂ refinement

This module isolates the trace re-expression needed by Claim 5.22.  A fixed H₂ decoded-table
query is logged as its corresponding H₁ encoded-table query.  Decoding that synthetic H₁ log
recovers the ordinary H₂ log exactly, including repeated occurrences.  The construction is only
a change of log representation: it does not suppress an H₂ `eᵢ` query or sample a new encoded
representative.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec

namespace DuplexSpongeFS.KeyLemma

open DuplexSpongeFS.ProverTransform DuplexSpongeFS.TraceTransform

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn U : Type}
  [SpongeUnit U] [SpongeSize] [VCVCompatible U] [VCVCompatible StmtIn]
  [codec : CodecCore pSpec U] {δ : Nat}
  [DecidableEq StmtIn] [DecidableEq U] [Fintype U] [Nonempty U]

/-- Re-express one H₂ outer-oracle occurrence as the H₁ occurrence that carries the encoded
representative selected by `table`.  The non-challenge arms are carried verbatim. -/
def hyb2OuterEntryAsHyb1
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :
    (q : (oSpec + D2SChallengePlusUnitOracle
      (U := U) (eSpec (U := U) StmtIn pSpec δ)).Domain) →
      (oSpec + D2SChallengePlusUnitOracle
        (U := U) (eSpec (U := U) StmtIn pSpec δ)).Range q →
        QueryLog (oSpec + D2SChallengePlusUnitOracle
          (U := U) (gSpec (U := U) StmtIn pSpec δ))
  | .inl q, answer => [⟨.inl q, answer⟩]
  | .inr (.inl q), _ => [⟨.inr (.inl q), table q⟩]
  | .inr (.inr (.inl q)), answer => [⟨.inr (.inr (.inl q)), answer⟩]
  | .inr (.inr (.inr q)), answer => [⟨.inr (.inr (.inr q)), answer⟩]

/-- Decode the encoded challenge entries of an H₁-shaped outer log.  Unit, uniform, and ambient
occurrences are untouched. -/
def decodeHyb1OuterLog
    (log : QueryLog (oSpec + D2SChallengePlusUnitOracle
      (U := U) (gSpec (U := U) StmtIn pSpec δ))) :
    QueryLog (oSpec + D2SChallengePlusUnitOracle
      (U := U) (eSpec (U := U) StmtIn pSpec δ)) :=
  log.map fun entry =>
    match entry with
    | ⟨.inl q, answer⟩ => ⟨.inl q, answer⟩
    | ⟨.inr (.inl q), answer⟩ => ⟨.inr (.inl q), codec.decode q.1 answer⟩
    | ⟨.inr (.inr (.inl q)), answer⟩ => ⟨.inr (.inr (.inl q)), answer⟩
    | ⟨.inr (.inr (.inr q)), answer⟩ => ⟨.inr (.inr (.inr q)), answer⟩

/-- Decode the synthetic H₁-shaped logs of one H₂ prover--verifier phase without changing its
control-flow result, inherited normal state, or memo.  This is the phase-level counterpart of
`decodeHyb1OuterLog`: it is deliberately defined before the game-level coupling so the latter
must prove only the outer-handler simulation, not rebuild the absorbing-stop case split. -/
def decodeHyb1StylePhase
    {StmtOut : Type} {T_H T_P M : Type}
    [DSTraceStorage.LawfulTraceNablaImpl T_H T_P StmtIn U]
    (phase : HybridGameRevisedPhaseWithLog
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) (δ := δ)
      oSpec (eSpec (U := U) StmtIn pSpec δ) T_H T_P M
      (QueryLog (oSpec + D2SChallengePlusUnitOracle
        (U := U) (gSpec (U := U) StmtIn pSpec δ)))) :
    HybridGameRevisedPhaseWithLog
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) (δ := δ)
      oSpec (eSpec (U := U) StmtIn pSpec δ) T_H T_P M
      (QueryLog (oSpec + D2SChallengePlusUnitOracle
        (U := U) (eSpec (U := U) StmtIn pSpec δ))) :=
  match phase with
  | .proverStopped reason proverLog =>
      .proverStopped reason
        (decodeHyb1OuterLog (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
          proverLog)
  | .verifier proverRun verifierResult proverLog verifierLog =>
      .verifier proverRun verifierResult
        (decodeHyb1OuterLog (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
          proverLog)
        (decodeHyb1OuterLog (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
          verifierLog)

/-- The synthetic H₁ entry for a fixed-table H₂ challenge decodes to the response that the H₂
outer handler returns. -/
theorem decode_hyb2OuterEntryAsHyb1_challenge
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))
    (q : (gSpec (U := U) StmtIn pSpec δ).Domain) :
    decodeHyb1OuterLog (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
      (hyb2OuterEntryAsHyb1 (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) (δ := δ) table (.inr (.inl q)) (codec.decode q.1 (table q))) =
      [⟨.inr (.inl q), codec.decode q.1 (table q)⟩] := by
  rfl

/-- The synthetic log of each non-challenge outer occurrence decodes to that occurrence itself. -/
theorem decode_hyb2OuterEntryAsHyb1_nonChallenge
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))
    (q : (oSpec + D2SChallengePlusUnitOracle
      (U := U) (eSpec (U := U) StmtIn pSpec δ)).Domain)
    (hChallenge : ¬ ∃ key, q = .inr (.inl key))
    (answer : (oSpec + D2SChallengePlusUnitOracle
      (U := U) (eSpec (U := U) StmtIn pSpec δ)).Range q) :
    decodeHyb1OuterLog (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
      (hyb2OuterEntryAsHyb1 (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) (δ := δ) table q answer) = [⟨q, answer⟩] := by
  rcases q with q | q
  · rfl
  · rcases q with q | q
    · exact False.elim (hChallenge ⟨q, rfl⟩)
    · rcases q with q | q <;> rfl

/-- The fixed-table H₂ handler equipped with an H₁-shaped raw log.  It still answers every H₂
`eᵢ` request through `hyb2AmbientOuterImpl`; only the appended witness records the matching
encoded-table request. -/
noncomputable def hyb2Hyb1StyleLoggingImpl
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :
    QueryImpl
      (oSpec + D2SChallengePlusUnitOracle
        (U := U) (eSpec (U := U) StmtIn pSpec δ))
      (WriterT
        (QueryLog (oSpec + D2SChallengePlusUnitOracle
          (U := U) (gSpec (U := U) StmtIn pSpec δ))) ProbComp) :=
  (hyb2AmbientOuterImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
    oSpecImpl table).withTraceAppend
      (hyb2OuterEntryAsHyb1 (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) (δ := δ) table)

/-- Stateful form of `hyb2Hyb1StyleLoggingImpl`.  The outer table is sampled once by the hybrid
game and is read, but never changed, by every outer query.  Keeping that invariant in the
handler type is the bridge from the fixed-table log coupling to the actual `StateT` game
executor. -/
noncomputable def hyb2Hyb1StyleLoggingStatefulImpl
    (oSpecImpl : QueryImpl oSpec ProbComp) :
    QueryImpl
      (oSpec + D2SChallengePlusUnitOracle
        (U := U) (eSpec (U := U) StmtIn pSpec δ))
      (WriterT
        (QueryLog (oSpec + D2SChallengePlusUnitOracle
          (U := U) (gSpec (U := U) StmtIn pSpec δ)))
        (StateT (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier ProbComp)) :=
  fun q => WriterT.mk fun table =>
    (fun output => (output, table)) <$>
      (hyb2Hyb1StyleLoggingImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) (δ := δ) oSpecImpl table q).run

/-- The complete H₂ phase with its ordinary decoded oracle answers but an H₁-shaped log.  The
outer table is the genuine `D_e` carrier (definitionally an encoded table), sampled once and
threaded unchanged through the prover and verifier. -/
noncomputable def hyb2Hyb1StylePhase
    {StmtOut : Type} {T_H T_P : Type}
    [DSTraceStorage.LawfulTraceNablaImpl T_H T_P StmtIn U]
    [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : MaliciousProver oSpec pSpec StmtIn U δ) :
    StateT (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier ProbComp
      (HybridGameRevisedPhaseWithLog
        (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) (δ := δ)
        oSpec (eSpec (U := U) StmtIn pSpec δ) T_H T_P
        (gSpec (U := U) StmtIn pSpec δ).QueryCache
        (QueryLog (oSpec + D2SChallengePlusUnitOracle
          (U := U) (gSpec (U := U) StmtIn pSpec δ)))) := by
  letI : Inhabited (gSpec (U := U) StmtIn pSpec δ).QueryCache := ⟨∅⟩
  exact hybridGameRevisedPhaseWithLoggerFrom
    (T_H := T_H) (T_P := T_P)
    (logger := hyb2Hyb1StyleLoggingStatefulImpl (oSpec := oSpec) (StmtIn := StmtIn)
      (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl)
    (d2sDecodedBridgeImplCacheOfImage
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)) V P ∅

/-- The same complete H₂ phase with the ordinary decoded `e` log.  This is a named normal form
for the real H₂ game rather than a second game: the next theorem identifies it with
`decodeHyb1StylePhase` applied to `hyb2Hyb1StylePhase`. -/
noncomputable def hyb2OrdinaryLoggedPhase
    {StmtOut : Type} {T_H T_P : Type}
    [DSTraceStorage.LawfulTraceNablaImpl T_H T_P StmtIn U]
    [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : MaliciousProver oSpec pSpec StmtIn U δ) :
    StateT (D_e (U := U) StmtIn pSpec δ).Carrier ProbComp
      (HybridGameRevisedPhaseWithLog
        (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) (δ := δ)
        oSpec (eSpec (U := U) StmtIn pSpec δ) T_H T_P
        (gSpec (U := U) StmtIn pSpec δ).QueryCache
        (QueryLog (oSpec + D2SChallengePlusUnitOracle
          (U := U) (eSpec (U := U) StmtIn pSpec δ)))) := by
  letI : Inhabited (gSpec (U := U) StmtIn pSpec δ).QueryCache := ⟨∅⟩
  exact hybridGameRevisedPhaseWithLoggerFrom
    (T_H := T_H) (T_P := T_P)
    (logger := (hybChallengeImpl oSpecImpl (D_e (U := U) StmtIn pSpec δ)).withLogging)
    (d2sDecodedBridgeImplCacheOfImage
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)) V P ∅

/-- The lossless, line-4-mapped observed form of the actual revised H₂ game.  This is the
public H₂ endpoint with the pre-projection phase and its ordinary decoded log retained, so the
Claim-5.22 coupling can be proved before erasing the evidence that its line-4 maps agree. -/
noncomputable def hyb2RevisedObserved
    {StmtOut Salt : Type} [VCVCompatible Salt] [SaltCodec U δ Salt]
    {T_H T_P : Type} [DSTraceStorage.LawfulTraceNablaImpl T_H T_P StmtIn U]
    [∀ i, VCVCompatible (pSpec.Message i)] [∀ i, VCVCompatible (pSpec.Challenge i)]
    [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : MaliciousProver oSpec pSpec StmtIn U δ) :
    ProbComp (HybridGameRevisedMappedObservation
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt)
      (eSpec (U := U) StmtIn pSpec δ) T_H T_P
      (gSpec (U := U) StmtIn pSpec δ).QueryCache) := by
  let challengeSpec := eSpec (U := U) StmtIn pSpec δ
  let D_e := D_e (U := U) StmtIn pSpec δ
  letI : Inhabited (gSpec (U := U) StmtIn pSpec δ).QueryCache := ⟨∅⟩
  let gImpl := d2sDecodedBridgeImplCacheOfImage
    (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
  exact hybridGameDistRevisedObserved
    (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P)
    (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (U := U)
    (init := hybChallengeInit (challengeSpec := challengeSpec) D_e)
    (impl := hybChallengeImpl
      (oSpec := oSpec) (U := U) (challengeSpec := challengeSpec) oSpecImpl D_e)
    gImpl V P
    (TraceTransform.hyb2Line4Trace
      (δ := δ) (Salt := Salt)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))

/-- Expose the concrete lossless H₂ observation without repeatedly unfolding its image-fibre
bridge in endpoint transports. -/
theorem hyb2RevisedObserved_eq_hybridGameDistRevisedObserved
    {StmtOut Salt : Type} [VCVCompatible Salt] [SaltCodec U δ Salt]
    {T_H T_P : Type} [DSTraceStorage.LawfulTraceNablaImpl T_H T_P StmtIn U]
    [∀ i, VCVCompatible (pSpec.Message i)] [∀ i, VCVCompatible (pSpec.Challenge i)]
    [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : MaliciousProver oSpec pSpec StmtIn U δ) :
    hyb2RevisedObserved (T_H := T_H) (T_P := T_P) (δ := δ) (Salt := Salt)
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
      oSpecImpl V P =
      letI : Inhabited (gSpec (U := U) StmtIn pSpec δ).QueryCache := ⟨∅⟩
      hybridGameDistRevisedObserved
        (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P)
        (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
        (init := hybChallengeInit
          (challengeSpec := eSpec (U := U) StmtIn pSpec δ)
          (D_e (U := U) StmtIn pSpec δ))
        (impl := hybChallengeImpl
          (oSpec := oSpec) (U := U) (challengeSpec := eSpec (U := U) StmtIn pSpec δ)
          oSpecImpl (D_e (U := U) StmtIn pSpec δ))
        (d2sDecodedBridgeImplCacheOfImage
          (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
        V P
        (TraceTransform.hyb2Line4Trace
          (δ := δ) (Salt := Salt)
          (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) := by
  rfl

/-- Mapping a lifted probabilistic computation preserves the state supplied to `StateT`.
This small normalization is kept explicit because the ordinary H₂ logger is stateful only to
hold its fixed decoded table. -/
private theorem map_run_stateT_lift
    {S α β : Type}
    (f : α → β)
    (computation : ProbComp α)
    (state : S) :
    (f <$> (StateT.lift computation : StateT S ProbComp α)).run state =
      (fun output => (f output, state)) <$> computation := by
  change (fun pair => (f pair.1, pair.2)) <$>
      (StateT.lift computation : StateT S ProbComp α).run state = _
  rw [StateT.run_lift]
  simp only [bind_pure_comp]
  rw [← LawfulFunctor.comp_map]
  rfl

/-- Transport a sequential probabilistic computation through a map on its first result.
The phase-level H₂ log theorem uses this once for the prover and once for the verifier. -/
private theorem map_bind_through
    {α β γ ξ : Type}
    (computation : ProbComp α)
    (pre : α → β)
    (post : γ → ξ)
    (contA : α → ProbComp γ)
    (contB : β → ProbComp ξ)
    (h : ∀ value, post <$> contA value = contB (pre value)) :
    post <$> (computation >>= contA) = (pre <$> computation) >>= contB := by
  rw [map_bind, bind_map_left]
  apply bind_congr
  exact h

/-- Running H₂'s ordinary stateful logger at a fixed decoded-table carrier is the corresponding
fixed-table logger paired with that unchanged carrier.  This is the ordinary-side analogue of
the table-preservation theorem for the synthetic logger below. -/
theorem run_hyb2OrdinaryLogger_eq_fixed
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (table : (D_e (U := U) StmtIn pSpec δ).Carrier)
    (q : (oSpec + D2SChallengePlusUnitOracle
      (U := U) (eSpec (U := U) StmtIn pSpec δ)).Domain) :
    (((hybChallengeImpl oSpecImpl (D_e (U := U) StmtIn pSpec δ)).withLogging q).run table) =
      (fun output => (output, table)) <$>
        ((hyb2AmbientOuterImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
          oSpecImpl table).withLogging q).run := by
  rcases q with q | q
  · simp [hybChallengeImpl, QueryImpl.withLogging_apply, hyb2AmbientOuterImpl,
      bind_pure]
    change ((fun answer => (answer, QueryLog.singleton
      (spec := oSpec + D2SChallengePlusUnitOracle
        (U := U) (eSpec (U := U) StmtIn pSpec δ))
      (Sum.inl q) answer)) <$>
        (StateT.lift (oSpecImpl q) : StateT (D_e (U := U) StmtIn pSpec δ).Carrier ProbComp _)).run
          table = _
    simpa only [QueryLog.singleton] using
      map_run_stateT_lift
        (S := (D_e (U := U) StmtIn pSpec δ).Carrier)
        (f := fun answer => (answer, QueryLog.singleton
          (spec := oSpec + D2SChallengePlusUnitOracle
            (U := U) (eSpec (U := U) StmtIn pSpec δ))
          (Sum.inl q) answer))
        (oSpecImpl q) table
  · rcases q with q | q
    · simp [hybChallengeImpl, QueryImpl.withLogging_apply, hyb2AmbientOuterImpl,
        decodedBridgeOuterImpl]
      rw [D_e_toImpl_apply (U := U) StmtIn pSpec δ table q.1 q.2]
      rfl
    · rcases q with q | q
      · simp [hybChallengeImpl, QueryImpl.withLogging_apply, hyb2AmbientOuterImpl,
          decodedBridgeOuterImpl, bind_pure]
        change ((fun answer => (answer, QueryLog.singleton
          (spec := oSpec + D2SChallengePlusUnitOracle
            (U := U) (eSpec (U := U) StmtIn pSpec δ))
          (Sum.inr (Sum.inr (Sum.inl q))) answer)) <$>
            (StateT.lift (d2sUnitSampleImpl (U := U) q) :
              StateT (D_e (U := U) StmtIn pSpec δ).Carrier ProbComp _)).run table = _
        simpa only [QueryLog.singleton] using
          map_run_stateT_lift
            (S := (D_e (U := U) StmtIn pSpec δ).Carrier)
            (f := fun answer => (answer, QueryLog.singleton
              (spec := oSpec + D2SChallengePlusUnitOracle
                (U := U) (eSpec (U := U) StmtIn pSpec δ))
              (Sum.inr (Sum.inr (Sum.inl q))) answer))
            (d2sUnitSampleImpl (U := U) q) table
      · simp [hybChallengeImpl, QueryImpl.withLogging_apply, hyb2AmbientOuterImpl,
          decodedBridgeOuterImpl, bind_pure]
        change ((fun answer => (answer, QueryLog.singleton
          (spec := oSpec + D2SChallengePlusUnitOracle
            (U := U) (eSpec (U := U) StmtIn pSpec δ))
          (Sum.inr (Sum.inr (Sum.inr q))) answer)) <$>
            (StateT.lift (liftM (OracleSpec.query q) : ProbComp (unifSpec.Range q)) :
              StateT (D_e (U := U) StmtIn pSpec δ).Carrier ProbComp _)).run table = _
        simpa only [QueryLog.singleton] using
          map_run_stateT_lift
            (S := (D_e (U := U) StmtIn pSpec δ).Carrier)
            (f := fun answer => (answer, QueryLog.singleton
              (spec := oSpec + D2SChallengePlusUnitOracle
                (U := U) (eSpec (U := U) StmtIn pSpec δ))
              (Sum.inr (Sum.inr (Sum.inr q))) answer))
            (liftM (OracleSpec.query q) : ProbComp (unifSpec.Range q)) table

/-- Decoding the synthetic H₁-style record emitted by the fixed H₂ handler gives the ordinary
H₂ logging record at every outer query.  In particular, a repeat is retained as a second log
entry: this lemma is deliberately about a one-occurrence list, not a cache lookup. -/
theorem map_run_hyb2Hyb1StyleLoggingImpl_eq_hyb2Logging
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))
    (q : (oSpec + D2SChallengePlusUnitOracle
      (U := U) (eSpec (U := U) StmtIn pSpec δ)).Domain) :
    (fun output => (output.1,
      decodeHyb1OuterLog (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) output.2)) <$>
      (hyb2Hyb1StyleLoggingImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) (δ := δ) oSpecImpl table q).run =
      ((hyb2AmbientOuterImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
        oSpecImpl table).withLogging q).run := by
  rcases q with q | q
  · simp [hyb2Hyb1StyleLoggingImpl, QueryImpl.withTraceAppend_apply,
      QueryImpl.withLogging_apply, hyb2AmbientOuterImpl, decodeHyb1OuterLog,
      hyb2OuterEntryAsHyb1]
  · rcases q with q | q
    · simp [hyb2Hyb1StyleLoggingImpl, QueryImpl.withTraceAppend_apply,
        QueryImpl.withLogging_apply, hyb2AmbientOuterImpl, decodedBridgeOuterImpl,
        decodeHyb1OuterLog, hyb2OuterEntryAsHyb1]
      rw [D_e_toImpl_apply (U := U) StmtIn pSpec δ table q.1 q.2]
      rfl
    · rcases q with q | q <;>
        simp [hyb2Hyb1StyleLoggingImpl, QueryImpl.withTraceAppend_apply,
          QueryImpl.withLogging_apply, hyb2AmbientOuterImpl, decodedBridgeOuterImpl,
          decodeHyb1OuterLog, hyb2OuterEntryAsHyb1]

/-- At a fixed stateful outer table, decoding the synthetic stateful H₂ record is exactly the
ordinary H₂ logging record, and the table is preserved. -/
theorem map_run_hyb2Hyb1StyleLoggingStatefulImpl_eq_hyb2Logging
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (table : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier)
    (q : (oSpec + D2SChallengePlusUnitOracle
      (U := U) (eSpec (U := U) StmtIn pSpec δ)).Domain) :
    (fun output => ((output.1.1,
      decodeHyb1OuterLog (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
        output.1.2), output.2)) <$>
      (hyb2Hyb1StyleLoggingStatefulImpl (oSpec := oSpec) (StmtIn := StmtIn)
        (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl q).run table =
      (fun output => (output, table)) <$>
        ((hyb2AmbientOuterImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
          oSpecImpl table).withLogging q).run := by
  simp only [hyb2Hyb1StyleLoggingStatefulImpl, WriterT.run_mk]
  rw [← LawfulFunctor.comp_map]
  change (fun output => ((output.1,
      decodeHyb1OuterLog (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
        output.2), table)) <$>
      (hyb2Hyb1StyleLoggingImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) (δ := δ) oSpecImpl table q).run = _
  simpa only [Functor.map_map] using congrArg
    (fun computation => (fun output => (output, table)) <$> computation)
    (map_run_hyb2Hyb1StyleLoggingImpl_eq_hyb2Logging
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
      oSpecImpl table q)

/-- The stateful synthetic H₂ logger leaves its sampled outer table unchanged.  Consequently,
for any finite adaptive outer computation, running it at a fixed table is exactly the fixed-table
synthetic logger paired with that same table. -/
theorem run_simulateQ_hyb2Hyb1StyleLoggingStatefulImpl_eq_fixed
    {α : Type}
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (table : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier)
    (oa : OracleComp (oSpec + D2SChallengePlusUnitOracle
      (U := U) (eSpec (U := U) StmtIn pSpec δ)) α) :
    (simulateQ
      (hyb2Hyb1StyleLoggingStatefulImpl (oSpec := oSpec) (StmtIn := StmtIn)
        (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl) oa).run table =
      (fun output => (output, table)) <$>
        (simulateQ
          (hyb2Hyb1StyleLoggingImpl (oSpec := oSpec) (StmtIn := StmtIn)
            (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl table) oa).run := by
  induction oa using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind q continuation ih =>
      simp only [simulateQ_bind, WriterT.run_bind', map_bind]
      rw [simulateQ_spec_query, simulateQ_spec_query]
      simp only [hyb2Hyb1StyleLoggingStatefulImpl, WriterT.run_mk]
      change (do
        let x ← (fun output => (output, table)) <$>
          (hyb2Hyb1StyleLoggingImpl (oSpec := oSpec) (StmtIn := StmtIn)
            (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl table q).run
        (fun output : (α × QueryLog (oSpec + D2SChallengePlusUnitOracle
              (U := U) (gSpec (U := U) StmtIn pSpec δ))) ×
              (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier =>
            ((output.1.1, x.1.2 ++ output.1.2), output.2)) <$>
          (simulateQ
            (hyb2Hyb1StyleLoggingStatefulImpl (oSpec := oSpec) (StmtIn := StmtIn)
              (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl)
            (continuation x.1.1)).run x.2) = _
      simp_rw [map_eq_bind_pure_comp]
      rw [bind_assoc]
      apply bind_congr
      intro a
      simp only [ChallengeIdx, Challenge, Function.comp_apply, pure_bind, bind_assoc,
        bind_pure_comp]
      rw [ih a.1]
      simp only [map_eq_bind_pure_comp, bind_assoc]
      apply bind_congr
      intro x
      rfl

/-- The ordinary H₂ logger also preserves its once-sampled decoded table over every finite
adaptive computation.  This is deliberately separate from the synthetic-log statement above:
it identifies the actual stateful implementation with the common fixed-table execution. -/
theorem run_simulateQ_hyb2OrdinaryLogger_eq_fixed
    {α : Type}
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (table : (D_e (U := U) StmtIn pSpec δ).Carrier)
    (oa : OracleComp (oSpec + D2SChallengePlusUnitOracle
      (U := U) (eSpec (U := U) StmtIn pSpec δ)) α) :
    (simulateQ ((hybChallengeImpl oSpecImpl (D_e (U := U) StmtIn pSpec δ)).withLogging) oa).run
        table =
      (fun output => (output, table)) <$>
        (simulateQ
          ((hyb2AmbientOuterImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
            oSpecImpl table).withLogging) oa).run := by
  induction oa using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind q continuation ih =>
      simp only [simulateQ_bind, WriterT.run_bind', map_bind]
      rw [simulateQ_spec_query, simulateQ_spec_query]
      change (do
        let x ←
          ((hybChallengeImpl oSpecImpl (D_e (U := U) StmtIn pSpec δ)).withLogging q).run table
        (fun output : (α × QueryLog (oSpec + D2SChallengePlusUnitOracle
              (U := U) (eSpec (U := U) StmtIn pSpec δ))) ×
              (D_e (U := U) StmtIn pSpec δ).Carrier =>
            ((output.1.1, x.1.2 ++ output.1.2), output.2)) <$>
          (simulateQ ((hybChallengeImpl oSpecImpl
            (D_e (U := U) StmtIn pSpec δ)).withLogging)
            (continuation x.1.1)).run x.2) = _
      rw [run_hyb2OrdinaryLogger_eq_fixed]
      simp_rw [map_eq_bind_pure_comp]
      rw [bind_assoc]
      apply bind_congr
      intro a
      simp only [ChallengeIdx, Challenge, Function.comp_apply, pure_bind, bind_assoc,
        bind_pure_comp]
      rw [ih a.1]
      simp only [map_eq_bind_pure_comp, bind_assoc]
      apply bind_congr
      intro x
      rfl

/-- The one-occurrence re-expression commutes with every finite outer-oracle computation.  Hence
the synthetic log has exactly the ordinary H₂ log after decoding, with the same order and
multiplicity. -/
theorem map_run_simulateQ_hyb2Hyb1StyleLoggingImpl_eq_hyb2Logging
    {α : Type}
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))
    (oa : OracleComp (oSpec + D2SChallengePlusUnitOracle
      (U := U) (eSpec (U := U) StmtIn pSpec δ)) α) :
    (fun output => (output.1,
      decodeHyb1OuterLog (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) output.2)) <$>
      (simulateQ
        (hyb2Hyb1StyleLoggingImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
          (U := U) (δ := δ) oSpecImpl table) oa).run =
      (simulateQ
        ((hyb2AmbientOuterImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
          oSpecImpl table).withLogging) oa).run := by
  induction oa using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind q continuation ih =>
      simp only [simulateQ_bind, WriterT.run_bind', map_bind]
      let decodeOutput : ∀ {β : Type},
          β × QueryLog (oSpec + D2SChallengePlusUnitOracle
            (U := U) (gSpec (U := U) StmtIn pSpec δ)) →
            β × QueryLog (oSpec + D2SChallengePlusUnitOracle
              (U := U) (eSpec (U := U) StmtIn pSpec δ)) := fun {β} output =>
        (output.1, decodeHyb1OuterLog (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
          output.2)
      have htail : ∀ output :
          (oSpec + D2SChallengePlusUnitOracle
            (U := U) (eSpec (U := U) StmtIn pSpec δ)).Range q ×
              QueryLog (oSpec + D2SChallengePlusUnitOracle
                (U := U) (gSpec (U := U) StmtIn pSpec δ)),
          decodeOutput <$>
              (Prod.map id (fun suffix => output.2 ++ suffix) <$>
                (simulateQ
                  (hyb2Hyb1StyleLoggingImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
                    (U := U) (δ := δ) oSpecImpl table)
                  (continuation output.1)).run) =
            Prod.map id (fun suffix => (decodeOutput output).2 ++ suffix) <$>
              (decodeOutput <$>
                (simulateQ
                  (hyb2Hyb1StyleLoggingImpl (oSpec := oSpec) (StmtIn := StmtIn)
                    (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl table)
                  (continuation output.1)).run) := by
        intro output
        rw [← LawfulFunctor.comp_map, ← LawfulFunctor.comp_map]
        congr 1
        funext result
        rcases output with ⟨answer, pref⟩
        rcases result with ⟨value, suffix⟩
        simp [decodeOutput, decodeHyb1OuterLog, List.map_append]
      calc
        (do
          let output ←
            (simulateQ
              (hyb2Hyb1StyleLoggingImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
                (U := U) (δ := δ) oSpecImpl table)
              (liftM (OracleSpec.query q))).run
          decodeOutput <$>
            (Prod.map id (fun suffix => output.2 ++ suffix) <$>
              (simulateQ
                (hyb2Hyb1StyleLoggingImpl (oSpec := oSpec) (StmtIn := StmtIn)
                  (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl table)
                (continuation output.1)).run)) =
            (do
              let output ←
                (simulateQ
                  (hyb2Hyb1StyleLoggingImpl (oSpec := oSpec) (StmtIn := StmtIn)
                    (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl table)
                  (liftM (OracleSpec.query q))).run
              Prod.map id (fun suffix => (decodeOutput output).2 ++ suffix) <$>
                (decodeOutput <$>
                  (simulateQ
                    (hyb2Hyb1StyleLoggingImpl (oSpec := oSpec) (StmtIn := StmtIn)
                      (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl table)
                    (continuation output.1)).run)) := by
              apply bind_congr
              intro output
              exact htail output
        _ = (do
              let output ←
                (simulateQ
                  (hyb2Hyb1StyleLoggingImpl (oSpec := oSpec) (StmtIn := StmtIn)
                    (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl table)
                  (liftM (OracleSpec.query q))).run
              Prod.map id (fun suffix => (decodeOutput output).2 ++ suffix) <$>
                (simulateQ
                  ((hyb2AmbientOuterImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
                    (δ := δ) oSpecImpl table).withLogging)
                  (continuation output.1)).run) := by
              apply bind_congr
              intro output
              rw [← ih output.1]
        _ = (do
              let output ← decodeOutput <$>
                (simulateQ
                  (hyb2Hyb1StyleLoggingImpl (oSpec := oSpec) (StmtIn := StmtIn)
                    (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl table)
                  (liftM (OracleSpec.query q))).run
              Prod.map id (fun suffix => output.2 ++ suffix) <$>
                (simulateQ
                  ((hyb2AmbientOuterImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
                    (δ := δ) oSpecImpl table).withLogging)
                  (continuation output.1)).run) := by
              rw [bind_map_left]
        _ = (do
              let output ←
                (simulateQ
                  ((hyb2AmbientOuterImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
                    (δ := δ) oSpecImpl table).withLogging)
                  (liftM (OracleSpec.query q))).run
              Prod.map id (fun suffix => output.2 ++ suffix) <$>
                (simulateQ
                  ((hyb2AmbientOuterImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
                    (δ := δ) oSpecImpl table).withLogging)
                  (continuation output.1)).run) := by
              have hquery := map_run_hyb2Hyb1StyleLoggingImpl_eq_hyb2Logging
                (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
                oSpecImpl table q
              simpa only [decodeOutput, simulateQ_query, OracleQuery.cont_query, id_map,
                OracleQuery.input_query] using congrArg
                (fun run => do
                  let output ← run
                  Prod.map id (fun suffix => output.2 ++ suffix) <$>
                    (simulateQ
                      ((hyb2AmbientOuterImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
                        (δ := δ) oSpecImpl table).withLogging)
                      (continuation output.1)).run) hquery

/-- At a fixed sampled H₂ table, the stateful synthetic H₁-shaped log decodes to the ordinary
stateful H₂ log for every finite adaptive outer computation.  Both the order and multiplicity
of outer requests are preserved, and the sampled table is returned unchanged. -/
theorem map_run_simulateQ_hyb2Hyb1StyleLoggingStatefulImpl_eq_hyb2Logging
    {α : Type}
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (table : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier)
    (oa : OracleComp (oSpec + D2SChallengePlusUnitOracle
      (U := U) (eSpec (U := U) StmtIn pSpec δ)) α) :
    (fun output => ((output.1.1,
      decodeHyb1OuterLog (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
        output.1.2), output.2)) <$>
      (simulateQ
        (hyb2Hyb1StyleLoggingStatefulImpl (oSpec := oSpec) (StmtIn := StmtIn)
          (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl) oa).run table =
      (fun output => (output, table)) <$>
        (simulateQ
          ((hyb2AmbientOuterImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
            oSpecImpl table).withLogging) oa).run := by
  rw [run_simulateQ_hyb2Hyb1StyleLoggingStatefulImpl_eq_fixed]
  calc
    _ = (fun output => (output, table)) <$>
        ((fun output => (output.1,
          decodeHyb1OuterLog (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
            output.2)) <$>
          (simulateQ
            (hyb2Hyb1StyleLoggingImpl (oSpec := oSpec) (StmtIn := StmtIn)
              (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl table) oa).run) := by
          rw [← LawfulFunctor.comp_map, ← LawfulFunctor.comp_map]
          congr 1
    _ = _ := by
      rw [map_run_simulateQ_hyb2Hyb1StyleLoggingImpl_eq_hyb2Logging]

/-- Decoding the H₁-shaped log of the actual stateful H₂ handler gives the ordinary stateful H₂
logger for every finite outer computation.  Both executions carry the same fixed table, so this
is an equality of stateful runs—not merely equality after dropping the table. -/
theorem map_run_simulateQ_hyb2Hyb1StyleLoggingStatefulImpl_eq_hyb2OrdinaryLogger
    {α : Type}
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (table : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier)
    (oa : OracleComp (oSpec + D2SChallengePlusUnitOracle
      (U := U) (eSpec (U := U) StmtIn pSpec δ)) α) :
    (fun output => ((output.1.1,
      decodeHyb1OuterLog (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
        output.1.2), output.2)) <$>
      (simulateQ
        (hyb2Hyb1StyleLoggingStatefulImpl (oSpec := oSpec) (StmtIn := StmtIn)
          (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl) oa).run table =
      (simulateQ ((hybChallengeImpl oSpecImpl (D_e (U := U) StmtIn pSpec δ)).withLogging)
        oa).run table := by
  calc
    _ = (fun output => (output, table)) <$>
        (simulateQ
          ((hyb2AmbientOuterImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
            oSpecImpl table).withLogging) oa).run :=
      map_run_simulateQ_hyb2Hyb1StyleLoggingStatefulImpl_eq_hyb2Logging
        (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
        oSpecImpl table oa
    _ = _ := (run_simulateQ_hyb2OrdinaryLogger_eq_fixed
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
      oSpecImpl table oa).symm

/-- `WriterT.run` followed by the outer-table `StateT.run` form of the preceding simulation
lemma.  The explicit form is convenient inside the two-phase game executor. -/
theorem map_run_run_simulateQ_hyb2Hyb1StyleLoggingStatefulImpl_eq_hyb2OrdinaryLogger
    {α : Type}
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (table : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier)
    (oa : OracleComp (oSpec + D2SChallengePlusUnitOracle
      (U := U) (eSpec (U := U) StmtIn pSpec δ)) α) :
    (fun output => ((output.1.1,
      decodeHyb1OuterLog (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
        output.1.2), output.2)) <$>
      ((simulateQ
        (hyb2Hyb1StyleLoggingStatefulImpl (oSpec := oSpec) (StmtIn := StmtIn)
          (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl) oa).run).run table =
      ((simulateQ ((hybChallengeImpl oSpecImpl (D_e (U := U) StmtIn pSpec δ)).withLogging)
        oa).run).run table := by
  exact map_run_simulateQ_hyb2Hyb1StyleLoggingStatefulImpl_eq_hyb2OrdinaryLogger
    (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
    oSpecImpl table oa

/-- The complete H₂ prover--verifier phase is unchanged when its synthetic H₁-shaped outer log
is decoded.  The theorem includes the absorbing prover-stop case and the successful handoff of
the exact normal state and memo to the verifier. -/
theorem map_run_hyb2Hyb1StylePhase_eq_hyb2OrdinaryLoggedPhase
    {StmtOut : Type} {T_H T_P : Type}
    [DSTraceStorage.LawfulTraceNablaImpl T_H T_P StmtIn U]
    [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : MaliciousProver oSpec pSpec StmtIn U δ)
    (table : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier) :
    (fun output => (decodeHyb1StylePhase
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (T_H := T_H) (T_P := T_P)
      output.1, output.2)) <$>
      (hyb2Hyb1StylePhase (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) (δ := δ) oSpecImpl V P).run table =
      (hyb2OrdinaryLoggedPhase (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) (δ := δ) oSpecImpl V P).run table := by
  simp only [hyb2Hyb1StylePhase, hyb2OrdinaryLoggedPhase,
    hybridGameRevisedPhaseWithLoggerFrom, StateT.run_bind]
  letI : Inhabited (gSpec (U := U) StmtIn pSpec δ).QueryCache := ⟨∅⟩
  let proverComp := d2fRawRevisedStopping (T_H := T_H) (T_P := T_P)
    (d2sDecodedBridgeImplCacheOfImage
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)) P ∅
  have hProver :=
    map_run_run_simulateQ_hyb2Hyb1StyleLoggingStatefulImpl_eq_hyb2OrdinaryLogger
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
      oSpecImpl table proverComp
  dsimp [proverComp] at hProver
  rw [← hProver]
  apply map_bind_through
  rintro ⟨⟨proverResult, proverLog⟩, state⟩
  cases proverResult with
  | error reason => rfl
  | ok proverRun =>
      simp only [bind_pure_comp]
      let verifierComp := d2fRawRevisedStoppingFrom (T_H := T_H) (T_P := T_P)
        (d2sDecodedBridgeImplCacheOfImage
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
        (runForwardVerifierWide δ V proverRun.1.1.1 proverRun.1.1.2) proverRun.1.2 proverRun.2
      have hVerifier :=
        map_run_run_simulateQ_hyb2Hyb1StyleLoggingStatefulImpl_eq_hyb2OrdinaryLogger
          (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
          oSpecImpl state verifierComp
      dsimp [verifierComp] at hVerifier
      simp only [StateT.run_map]
      rw [← LawfulFunctor.comp_map]
      change (fun output =>
        (HybridGameRevisedPhaseWithLog.verifier proverRun output.1.1
          (decodeHyb1OuterLog (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
            proverLog)
          (decodeHyb1OuterLog (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
            output.1.2), output.2)) <$>
          ((simulateQ
            (hyb2Hyb1StyleLoggingStatefulImpl (oSpec := oSpec) (StmtIn := StmtIn)
              (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl)
            (d2fRawRevisedStoppingFrom (T_H := T_H) (T_P := T_P)
              (d2sDecodedBridgeImplCacheOfImage
                (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
                (δ := δ))
              (runForwardVerifierWide δ V proverRun.1.1.1 proverRun.1.1.2)
              proverRun.1.2 proverRun.2)).run).run state =
        (fun output =>
          (HybridGameRevisedPhaseWithLog.verifier proverRun output.1.1
            (decodeHyb1OuterLog (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
              proverLog) output.1.2, output.2)) <$>
          ((simulateQ
            ((hybChallengeImpl oSpecImpl (D_e (U := U) StmtIn pSpec δ)).withLogging)
            (d2fRawRevisedStoppingFrom (T_H := T_H) (T_P := T_P)
              (d2sDecodedBridgeImplCacheOfImage
                (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
                (δ := δ))
              (runForwardVerifierWide δ V proverRun.1.1.1 proverRun.1.1.2)
              proverRun.1.2 proverRun.2)).run).run state
      simpa only [Functor.map_map] using congrArg
        (fun computation =>
          (fun output =>
            (HybridGameRevisedPhaseWithLog.verifier proverRun output.1.1
              (decodeHyb1OuterLog (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
              proverLog) output.1.2, output.2)) <$> computation)
        hVerifier

end DuplexSpongeFS.KeyLemma
