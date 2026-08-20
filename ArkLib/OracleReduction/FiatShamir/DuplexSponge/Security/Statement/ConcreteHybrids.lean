/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.D2SAmbientLazySampling
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.D2SRevisedForward
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.RevisedHybridGame
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Section5Nonempty
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Statement.EventsAndAnalysis

/-!
# Concrete Section 5 hybrid endpoints

This module closes the statement-layer gap deliberately left by
`Statement.EventsAndAnalysis`: its generic `ProbComp` parameters are useful for local probability
arguments, but they are not themselves the five experiments of CO25 Section 5.8.  Here each
endpoint is a live game: Hyb₀ retains the existing duplex-sponge game with the revised trace
transformer, Hyb₁--Hyb₃ use `KeyLemma.hybridGameRevised`, and Hyb₄ uses the live revised
`ProverTransform.d2sAlgoRevised` transform.  Thus every duplex execution in the public hybrid
chain takes the stateful `Install → append → Monitor` path.

The declarations below are proposition specifications, not proofs of the four hybrid claims.  In
particular, their use does not hide the existing probability holes in `KeyLemma`; it only ensures
that every updated Section 5 claim and Lemma 5.1 names its actual game endpoints.
-/

noncomputable section

namespace DuplexSpongeFS

namespace Statement

open OracleComp OracleSpec ProtocolSpec DSTraceStorage

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn StmtOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  {U : Type} [SpongeUnit U] [SpongeSize] [VCVCompatible U]
  [∀ i, VCVCompatible (pSpec.Message i)] [codec : CodecCore pSpec U]
  {δ : Nat} {Salt : Type} [VCVCompatible Salt] [SaltCodec U δ Salt]
  [DecidableEq StmtIn] [DecidableEq U]
  {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]

/-- The genuine Section 5.8 game result: statement, verifier result, salted proof, and the full
tagged query log.  This is intentionally the real game output rather than only its trace
projection; the paper's Lemma 5.1 preserves the complete output distribution. -/
abbrev ConcreteHybridOutput : Type :=
  Option (KeyLemma.BasicFiatShamirGameOutput (oSpec := oSpec) (StmtIn := StmtIn)
    (StmtOut := StmtOut) (pSpec := pSpec) (Salt := Salt))

/-- CO25 Hyb0, definitionally the real duplex-sponge experiment with the revised `D2STrace`
witness. -/
noncomputable def Hyb0
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    ProbComp (ConcreteHybridOutput (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (Salt := Salt)) :=
  KeyLemma.hyb_0 (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
    (StmtOut := StmtOut) (pSpec := pSpec) (U := U) oSpecImpl V maliciousProver
    (TraceTransform.d2sTraceSalted (T_H := T_H) (T_P := T_P) (δ := δ) (Salt := Salt)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))

/-- The observed form of the concrete Hyb₀ game.  Its `publicOutput` follows exactly the Hyb₀
line-4 `D2STrace` convention, while `sourceOutput` and `traceObservation` retain the actual
duplex base trace and exact encoded StdTrace entries.  This is the H₀ input of the lossless
Hyb₀↔Hyb₁ lazy-sampling coupling; it is not a second or resampled H₀ experiment. -/
noncomputable def Hyb0Observed
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    ProbComp (KeyLemma.MappedDSFSGameD2STraceObservation
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt)) :=
  KeyLemma.mappedDSFSGameDistD2STraceObserved
    (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P)
    (init := KeyLemma.hyb0Init (StmtIn := StmtIn) (U := U))
    (impl := KeyLemma.hyb0Impl (oSpec := oSpec) (StmtIn := StmtIn) (U := U) oSpecImpl)
    V maliciousProver

omit [∀ i, VCVCompatible (pSpec.Challenge i)] [VCVCompatible Salt] in
/-- The retained Hyb₀ observation is lossless: its public-output projection is exactly the
concrete public Hyb₀ experiment. -/
lemma Hyb0Observed_map_publicOutput_eq_Hyb0
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    (fun observation => observation.publicOutput) <$>
        Hyb0Observed (Salt := Salt) (T_H := T_H) (T_P := T_P)
          oSpecImpl V maliciousProver =
      Hyb0 (Salt := Salt) (T_H := T_H) (T_P := T_P) oSpecImpl V maliciousProver := by
  simpa only [Hyb0, Hyb0Observed, KeyLemma.hyb_0] using
    (KeyLemma.mappedDSFSGameDistD2STraceObserved_map_publicOutput_eq
      (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P)
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U)
      (init := KeyLemma.hyb0Init (StmtIn := StmtIn) (U := U))
      (impl := KeyLemma.hyb0Impl (oSpec := oSpec) (StmtIn := StmtIn) (U := U) oSpecImpl)
      V maliciousProver)

/-- CO25 Hyb1, definitionally the real encoded-challenge game. -/
noncomputable def Hyb1
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    ProbComp (ConcreteHybridOutput (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (Salt := Salt)) :=
  KeyLemma.hyb1Revised (T_H := T_H) (T_P := T_P) (δ := δ) (Salt := Salt) (oSpec := oSpec)
    (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) oSpecImpl V maliciousProver

/-- The observed form of the concrete Hyb₁ game.  It uses the same `D_Σ` sampling, `gᵢ`
implementation, revised D2SQuery executor, and line-4 trace map as `Hyb1`; in addition it keeps
the actual raw prover/verifier D2S logs and the structured first-stop result.  Those are the
direct online counterparts of the raw DSFS trace retained by `Hyb0Observed`. -/
noncomputable def Hyb1Observed
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    ProbComp (KeyLemma.HybridGameRevisedMappedObservation
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt)
      (gSpec (U := U) StmtIn pSpec δ) T_H T_P PUnit) := by
  let challengeSpec := gSpec (U := U) StmtIn pSpec δ
  -- Keep the observed endpoint on the same explicit finite `D_Σ` realization as
  -- `KeyLemma.hyb1Revised`; otherwise the proof-facing observation and public
  -- endpoint would unnecessarily differ only by a legacy sampler wrapper.
  let D_g := D_SigmaFinite (U := U) StmtIn pSpec δ
  exact
    KeyLemma.hybridGameDistRevisedObserved
      (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P)
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U)
      (init := KeyLemma.hybChallengeInit (challengeSpec := challengeSpec) D_g)
      (impl := KeyLemma.hybChallengeImpl
        (oSpec := oSpec) (U := U) (challengeSpec := challengeSpec) oSpecImpl D_g)
      (gImpl := KeyLemma.hyb1GImpl
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)) V maliciousProver
      (TraceTransform.hyb1Line4Trace
        (δ := δ) (Salt := Salt)
        (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))

omit [∀ i, VCVCompatible (pSpec.Challenge i)] [VCVCompatible Salt] in
/-- The retained Hyb₁ observation is a lossless instrumentation: forgetting its extra history
recovers the concrete public Hyb₁ endpoint exactly. -/
lemma Hyb1Observed_map_publicOutput_eq_Hyb1
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    (fun observation => observation.publicOutput) <$>
        Hyb1Observed (Salt := Salt) (T_H := T_H) (T_P := T_P)
          oSpecImpl V maliciousProver =
      Hyb1 (Salt := Salt) (T_H := T_H) (T_P := T_P) oSpecImpl V maliciousProver := by
  simpa only [Hyb1, Hyb1Observed, KeyLemma.hyb1Revised] using
    (KeyLemma.hybridGameDistRevisedObserved_map_publicOutput_eq
      (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P)
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U)
      (init := KeyLemma.hybChallengeInit
        (challengeSpec := gSpec (U := U) StmtIn pSpec δ)
        (D_SigmaFinite (U := U) StmtIn pSpec δ))
      (impl := KeyLemma.hybChallengeImpl
        (oSpec := oSpec) (U := U) (challengeSpec := gSpec (U := U) StmtIn pSpec δ)
        oSpecImpl (D_SigmaFinite (U := U) StmtIn pSpec δ))
      (gImpl := KeyLemma.hyb1GImpl
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
      V maliciousProver
      (TraceTransform.hyb1Line4Trace
        (δ := δ) (Salt := Salt)
        (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))

/-- CO25 Hyb2, definitionally the real decoded-challenge game. -/
noncomputable def Hyb2
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    ProbComp (ConcreteHybridOutput (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (Salt := Salt)) :=
  KeyLemma.hyb2Revised (T_H := T_H) (T_P := T_P) (δ := δ) (Salt := Salt) (oSpec := oSpec)
    (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) oSpecImpl V maliciousProver

/-- CO25 Hyb3, definitionally the real salted-FS / revised-D2SQuery game. -/
noncomputable def Hyb3
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    ProbComp (ConcreteHybridOutput (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (Salt := Salt)) :=
  KeyLemma.hyb3Revised (T_H := T_H) (T_P := T_P) (δ := δ) (Salt := Salt) (oSpec := oSpec)
    (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) oSpecImpl V maliciousProver

/-- The lossless Hyb₃ execution.  In contrast to the public endpoint, this retains the revised
prover/verifier phase and hence distinguishes a partial codec-lift `oracleAbort` from an
underlying stateful D2S failure.  Claim 5.23 uses exactly that distinction to charge an
out-of-image `fᵢ` value to `Bad_cdc`, rather than silently assuming a total decoder fibre. -/
noncomputable def Hyb3Observed
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    ProbComp (KeyLemma.HybridGameRevisedMappedObservation
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt)
      (fsChallengeOracle (StmtIn × Salt) pSpec) T_H T_P
      (ProverTransform.D2SAlgoMemo StmtIn U δ Salt pSpec)) := by
  let challengeSpec := fsChallengeOracle (StmtIn × Salt) pSpec
  let D_IP_salted := D_IP_salted (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec)
  let gImpl := ProverTransform.d2sCodecBridgeImplMemo (δ := δ) (Salt := Salt)
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
  exact KeyLemma.hybridGameDistRevisedObserved
    (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P)
    (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (U := U)
    (init := KeyLemma.hybChallengeInit (challengeSpec := challengeSpec) D_IP_salted)
    (impl := KeyLemma.hybChallengeImpl
      (oSpec := oSpec) (U := U) (challengeSpec := challengeSpec) oSpecImpl D_IP_salted)
    gImpl V maliciousProver
    (TraceTransform.hyb3Line4Trace (Salt := Salt) (oSpec := oSpec)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))

/-- Forgetting Hyb₃'s retained phase/log data is exactly the public revised Hyb₃ experiment. -/
lemma Hyb3Observed_map_publicOutput_eq_Hyb3
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    (fun observation => observation.publicOutput) <$>
        Hyb3Observed (Salt := Salt) (T_H := T_H) (T_P := T_P)
          oSpecImpl V maliciousProver =
      Hyb3 (Salt := Salt) (T_H := T_H) (T_P := T_P) oSpecImpl V maliciousProver := by
  simpa only [Hyb3, Hyb3Observed, KeyLemma.hyb3Revised,
    KeyLemma.hybridGameDistRevisedObserved_map_publicOutput_eq]

/-- The explicit out-of-image branch of the partial Hyb₃ codec bridge.  The `fᵢ` table and all
other outer components are total; therefore an `oracleAbort` of this revised execution is the
branch where the queried standard challenge did not have an encoded decoder preimage. -/
def Hyb3CodecImageFailure
    (observation : KeyLemma.HybridGameRevisedMappedObservation
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt)
      (fsChallengeOracle (StmtIn × Salt) pSpec) T_H T_P
      (ProverTransform.D2SAlgoMemo StmtIn U δ Salt pSpec)) : Prop :=
  match observation.game.phase with
  | .proverStopped (.oracleAbort _) _ => True
  | .verifier _ (.error (.oracleAbort _)) _ _ => True
  | _ => False

/-- CO25 Hyb4, definitionally the real **absorbing** basic-FS experiment with the live revised
`D2SAlgo` executor.  A source-side failure returns `⊥` before invoking the standard verifier,
as required by revised Claims 5.23--5.24. -/
noncomputable def Hyb4
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    ProbComp (ConcreteHybridOutput (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (Salt := Salt)) :=
  KeyLemma.hyb4Absorbing (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
    (StmtOut := StmtOut) (pSpec := pSpec) (U := U) oSpecImpl V maliciousProver
    (ProverTransform.d2sAlgoRevised (T_H := T_H) (T_P := T_P) (δ := δ) (Salt := Salt)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))

/-- The lossless Hyb4 endpoint used by the codec/private-shadow argument.  The sampled table is
retained with the output, so a later joint simulation can state that its shadow consults the
*same* salted FS table as the real basic-FS game. -/
structure Hyb4ObservedSample where
  table : (D_IP_salted (StmtIn := StmtIn) (Salt := Salt) pSpec).Carrier
  output : ConcreteHybridOutput (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (Salt := Salt)

/-- Run the actual Hyb4 game from an explicitly retained eager `D_IP_salted` table. -/
noncomputable def Hyb4Observed
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    ProbComp (Hyb4ObservedSample (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (Salt := Salt)) := do
  let table ← (D_IP_salted (StmtIn := StmtIn) (Salt := Salt) pSpec).sample
  let output ← KeyLemma.basicFiatShamirGameAbsorbingDist
    (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
    (Salt := Salt)
    (init := pure table)
    (impl := KeyLemma.hybChallengeImpl
      (oSpec := oSpec) (U := U)
      (challengeSpec := fsChallengeOracle (StmtIn × Salt) pSpec)
      oSpecImpl (D_IP_salted (StmtIn := StmtIn) (Salt := Salt) pSpec))
    V (ProverTransform.d2sAlgoRevised (T_H := T_H) (T_P := T_P) (δ := δ) (Salt := Salt)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) maliciousProver)
  pure ⟨table, output⟩

/-- Forgetting the retained table recovers exactly the public Hyb4 endpoint. -/
lemma Hyb4Observed_map_output_eq_Hyb4
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    (fun sample => sample.output) <$> Hyb4Observed (Salt := Salt) (T_H := T_H) (T_P := T_P)
      oSpecImpl V maliciousProver =
      Hyb4 (Salt := Salt) (T_H := T_H) (T_P := T_P) oSpecImpl V maliciousProver := by
  simp [Hyb4Observed, Hyb4, KeyLemma.hyb4Absorbing,
    KeyLemma.basicFiatShamirGameAbsorbingDist,
    KeyLemma.hybChallengeInit]

/-- The complete, concrete Hyb0--Hyb4 family.  Unlike the previous generic family, this is a
computed family of actual `ProbComp` games and cannot be populated by arbitrary distributions. -/
noncomputable def concreteHybs
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    HybridIndex → ProbComp (ConcreteHybridOutput (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (Salt := Salt)) := fun i =>
  if i.1 = 0 then Hyb0 (Salt := Salt) (T_H := T_H) (T_P := T_P) oSpecImpl V maliciousProver
  else if i.1 = 1 then Hyb1 (Salt := Salt) (T_H := T_H) (T_P := T_P) oSpecImpl V maliciousProver
  else if i.1 = 2 then Hyb2 (Salt := Salt) (T_H := T_H) (T_P := T_P) oSpecImpl V maliciousProver
  else if i.1 = 3 then Hyb3 (Salt := Salt) (T_H := T_H) (T_P := T_P) oSpecImpl V maliciousProver
  else Hyb4 (Salt := Salt) (T_H := T_H) (T_P := T_P) oSpecImpl V maliciousProver

/-! ## The instrumented Hyb₀--Hyb₁ lazy-sampling coupling (paper (44c)--(44e)) -/

/-- The lossless value produced by the concrete observed Hyb₀ game.  This abbreviation is only a
name for the existing live observation carrier; it does not resample or project its source trace. -/
abbrev Hyb0Observation : Type :=
  KeyLemma.MappedDSFSGameD2STraceObservation
    (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt)

/-- The lossless value produced by the concrete observed Hyb₁ game.  Its `game` field contains the
real revised-D2SQuery runs and their structured stopping reasons. -/
abbrev Hyb1Observation : Type :=
  KeyLemma.HybridGameRevisedMappedObservation
    (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt)
    (gSpec (U := U) StmtIn pSpec δ) T_H T_P PUnit

/-- Convert one real `StdTrace` entry to the corresponding encoded `gᵢ` occurrence.  This is the
same complete round-tagged key that direct D2SQuery issues: the BackTrack output supplies the
statement, salt, and encoded prover prefix, while the StdTrace response supplies the answer. -/
noncomputable def stdTraceEntryToEncodedOccurrence
    (entry : TraceTransform.StdTraceEntry (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      (δ := δ)) : Sigma (gSpec (U := U) StmtIn pSpec δ) :=
  ⟨⟨entry.query.roundIdx,
    (entry.query.stmt, entry.query.salt, entry.query.encodedMessages)⟩, entry.response⟩

/-- The actual insertion-ordered encoded `gᵢ` trace retained by an observed Hyb₀ run.  A failed
offline transform has no encoded entries; the raw source trace remains separately available in
`observation.baseTrace`. -/
noncomputable def Hyb0Observation.encodedTrace (observation : Hyb0Observation
    (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt)) :
    D2SAlgo.EncodedTrace StmtIn pSpec U δ :=
  match observation.traceObservation with
  | none => []
  | some traceObservation => traceObservation.encodedTrace.map
      (stdTraceEntryToEncodedOccurrence (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))

/-- The actual insertion-ordered direct `gᵢ` trace of an observed Hyb₁ run.  This extracts only
the `gSpec` component of the legal raw phase log, retaining repeated keys and their order; it
discards neither a duplicate query nor a pre-existing memo hit.  A stopped prover has no verifier
log, by construction. -/
noncomputable def Hyb1Observation.encodedTrace (observation : Hyb1Observation
    (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P)) :
    D2SAlgo.EncodedTrace StmtIn pSpec U δ :=
  observation.game.rawQueryLog.filterMap fun entry =>
    match entry with
    | ⟨.inr (.inl query), answer⟩ => some ⟨query, answer⟩
    | _ => none

/-- The earliest point at which the actual observed Hyb₀ execution is no longer live.  A source
abort is before its first duplex occurrence; a `D2STrace` abort is after the retained source
trace has been obtained.  This is derived from the lossless observation, not supplied by a
caller. -/
noncomputable def Hyb0Observation.abortIndex? (observation : Hyb0Observation
    (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt)) : Option ℕ :=
  match observation.sourceOutput, observation.traceObservation with
  | none, _ => some 0
  | some _, none => some observation.baseTrace.length
  | some _, some _ => none

/-- The earliest point at which the actual observed Hyb₁ execution stopped.  Every stopping
reason carries the full global D2S trace at its exact attempted occurrence: this is the prover
trace on a prover stop and the common prover--verifier trace on a verifier stop.  A normal
verifier rejection is *not* an abort and therefore yields `none`. -/
noncomputable def Hyb1Observation.abortIndex? (observation : Hyb1Observation
    (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P)) : Option ℕ :=
  match observation.game.phase with
  | .proverStopped reason _ => some reason.trace.length
  | .verifier _ (.error reason) _ _ => some reason.trace.length
  | .verifier _ (.ok _) _ _ => none

/-! ## Concrete Lemma 5.8 verifier-extension endpoints -/

/-- One observed live game result together with the completed stateful verifier extension that
realizes its base trace.  The extension contains the complete stateful replay, its good prior
prefix, the exact `N_𝒱` count, and the separate absorb/squeeze frame obligations.  Consequently,
the equality below is the precise bridge needed to apply Lemma 5.8 to an *actual* game endpoint,
rather than to an unrelated `ProbComp` of completed-extension witnesses. -/
structure CompletedExtensionSample (Observation : Type)
    (traceOf : Observation → Trace StmtIn U) (T : ℕ) where
  observation : Observation
  extension : CompletedVerifierExtension StmtIn pSpec U δ T
  trace_agrees : extension.history.trace = traceOf observation

/-- An instrumentation of one concrete endpoint by completed verifier-extension witnesses.  Its
first marginal is definitionally the live endpoint distribution, while its second projection is
the exact experiment to which Lemma 5.8 applies.  This is deliberately a coupling/refinement
*obligation*: constructing it from the live verifier is a theorem, but the statement no longer
permits an arbitrary completed-extension experiment to stand in for Hyb₀ or Hyb₁. -/
structure CompletedExtensionInstrumentation (Observation : Type)
    (endpoint : ProbComp Observation) (traceOf : Observation → Trace StmtIn U) (T : ℕ) where
  joint : ProbComp (CompletedExtensionSample (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
    (δ := δ) Observation traceOf T)
  endpoint_marginal : (fun sample => sample.observation) <$> joint = endpoint

/-- The completed-extension experiment projected from an endpoint instrumentation.  Every output
is a genuine stateful extension; this is the sole value fed to `Lemma58` and
`Lemma58Stopped`. -/
noncomputable def CompletedExtensionInstrumentation.extensionRun
    {Observation : Type} {endpoint : ProbComp Observation} {traceOf : Observation → Trace StmtIn U}
    {T : ℕ}
    (instrument : CompletedExtensionInstrumentation (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      (δ := δ) Observation endpoint traceOf T) :
    ProbComp (CompletedVerifierTrace StmtIn pSpec U δ T) :=
  (fun sample => sample.extension) <$> instrument.joint

/-- The ideal-permutation endpoint instrumentation for Lemma 5.8: the observation marginal is
exactly the concrete Hyb₀ game, and its completed replay trace is the observed DSFS base trace. -/
abbrev Hyb0CompletedExtensionInstrumentation (T : ℕ)
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) : Type :=
  CompletedExtensionInstrumentation (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
    (Hyb0Observation (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt))
    (Hyb0Observed (Salt := Salt) (T_H := T_H) (T_P := T_P) oSpecImpl V maliciousProver)
    (fun observation => observation.baseTrace) T

/-- The direct revised-D2SQuery endpoint instrumentation for Lemma 5.8: its observation marginal
is exactly Hyb₁ and each extension trace is the actual revised game base trace. -/
abbrev Hyb1CompletedExtensionInstrumentation (T : ℕ)
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) : Type :=
  CompletedExtensionInstrumentation (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
    (Hyb1Observation (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P))
    (Hyb1Observed (Salt := Salt) (T_H := T_H) (T_P := T_P) oSpecImpl V maliciousProver)
    (fun observation => observation.game.baseTrace) T

/-- Lemma 5.8 at the genuine ideal-permutation endpoint.  The endpoint is fixed by the
instrumentation's marginal; the statement cannot be instantiated with an arbitrary experiment. -/
noncomputable def Hyb0Lemma58 (T : ℕ)
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (instrument : Hyb0CompletedExtensionInstrumentation (StmtIn := StmtIn) (StmtOut := StmtOut)
      (oSpec := oSpec) (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt) (T_H := T_H)
      (T_P := T_P) T oSpecImpl V maliciousProver) : Prop :=
  Lemma58 (U := U) (pSpec := pSpec) (δ := δ) (T := T) instrument.extensionRun

/-- The stopped/first-new-bad-event clause of Lemma 5.8 at Hyb₀'s actual endpoint. -/
noncomputable def Hyb0Lemma58Stopped (T : ℕ)
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (instrument : Hyb0CompletedExtensionInstrumentation (StmtIn := StmtIn) (StmtOut := StmtOut)
      (oSpec := oSpec) (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt) (T_H := T_H)
      (T_P := T_P) T oSpecImpl V maliciousProver) : Prop :=
  Lemma58Stopped (U := U) (pSpec := pSpec) (δ := δ) (T := T) instrument.extensionRun

/-- Lemma 5.8 at the genuine revised-D2SQuery endpoint, with the exact same stateful count and
completed-extension representation as the ideal endpoint. -/
noncomputable def Hyb1Lemma58 (T : ℕ)
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (instrument : Hyb1CompletedExtensionInstrumentation (StmtIn := StmtIn) (StmtOut := StmtOut)
      (oSpec := oSpec) (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt) (T_H := T_H)
      (T_P := T_P) T oSpecImpl V maliciousProver) : Prop :=
  Lemma58 (U := U) (pSpec := pSpec) (δ := δ) (T := T) instrument.extensionRun

/-- The stopped/first-new-bad-event clause of Lemma 5.8 at Hyb₁'s actual endpoint. -/
noncomputable def Hyb1Lemma58Stopped (T : ℕ)
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (instrument : Hyb1CompletedExtensionInstrumentation (StmtIn := StmtIn) (StmtOut := StmtOut)
      (oSpec := oSpec) (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt) (T_H := T_H)
      (T_P := T_P) T oSpecImpl V maliciousProver) : Prop :=
  Lemma58Stopped (U := U) (pSpec := pSpec) (δ := δ) (T := T) instrument.extensionRun

/-- A coupling-register entry for one **fresh complete encoded marker key**.  Its key, marker
input, encoded answer, padded rate blocks, first output capacity, and residual tail all use the
same types as the actual revised `Program` transition.  `padded_rates` records the operational
relationship: the first materialized output supplies the first rate block and a residual
`RateOnlyTail`, when present, supplies exactly the remaining blocks. -/
structure Hyb01MarkerRegister (j : pSpec.ChallengeIdx) where
  key : (gSpecInterface (U := U) StmtIn pSpec δ j).Query
  markerInput : CanonicalSpongeState U
  encodedAnswer : Vector U (challengeSize j)
  paddedRates : List (Vector U SpongeSize.R)
  firstOutput : CanonicalSpongeState U
  firstCapacity : Vector U SpongeSize.C
  residualTail : Option (ProverTransform.RateOnlyTail (U := U))
  first_capacity : firstOutput.capacitySegment = firstCapacity
  padded_rates : paddedRates = firstOutput.rateSegment ::
    match residualTail with
    | none => []
    | some tail => tail.blocks

/-- A coupling-register entry for an **already materialized** lazy cache tail.  The cache stores
no latent output capacity: this record is created only once the common forward mapping is
installed, and carries at most the actual residual rate-only tail. -/
structure Hyb01MaterializedTail where
  stateIn : CanonicalSpongeState U
  stateOut : CanonicalSpongeState U
  residualTail : Option (ProverTransform.RateOnlyTail (U := U))

/-- One side's coupling-only M/C register snapshot after a base-oracle prefix.  `programmed` is
M: complete encoded marker keys with their programming data.  `materializedTails` is C: precisely
the cache-tail inputs which have become real forward mappings.  The latter has unique input keys,
matching the executable rate-only-cache invariant. -/
structure Hyb01Registers where
  programmed : List (Sigma fun j : pSpec.ChallengeIdx => Hyb01MarkerRegister
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) j)
  materializedTails : List (Hyb01MaterializedTail (U := U))
  materialized_inputs_nodup :
    (materializedTails.map Hyb01MaterializedTail.stateIn).Nodup

/-- The M/C register histories of the two sides of the coupling.  They remain separate so (44d)
is an equality to prove before stopping, rather than being hidden by a single shared mutable
object. -/
structure Hyb01RegisterHistory where
  side0 : ℕ → Hyb01Registers (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
  side1 : ℕ → Hyb01Registers (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)

/-- An actual endpoint abort has occurred by a prefix of `j` base-oracle occurrences. -/
def AbortedBy (abortIndex? : Option ℕ) (j : ℕ) : Prop :=
  ∃ i, abortIndex? = some i ∧ i ≤ j

/-- The exact common base-oracle budget in the Hyb₀/Hyb₁ coupling: the malicious prover's
`T = tₕ+tₚ+tₚ⁻¹` calls, the verifier's one `DS.Start` hash call, and the statefully replayed
`N_𝒱` forward permutation calls.  This is a definition, rather than a default-valued structure
field, so a coupling witness cannot be formed at a caller-selected count. -/
noncomputable def Hyb01BoundCount (tₕ tₚ tₚᵢ : ℕ) : ℕ :=
  tₕ + tₚ + tₚᵢ + 1 +
    DuplexSpongeFS.verifierPermCallCount (pSpec := pSpec) (δ := δ)

/-- The stop certificate for paper (44c)--(44e), over the two **actual** lossless observations.
`τ = N + 1` is the no-stop value.  Before `τ`, the direct base traces agree, neither prefix is
bad, and direct Hyb₁ has not aborted.  Hyb₀'s offline `D2STrace` postprocessing is deliberately
not a base-oracle stopping event; its no-stop totality is supplied separately by Lemma 5.17.
At a genuine stop, either trace has a bad prefix or Hyb₁ has actually aborted by `τ`.  On no
stop, exact encoded-trace equality and equality of the complete public outputs give (44e).
`trace_bound` is the paper's common `N`-entry budget, so the sentinel `N + 1` never conceals an
unbounded completed trace. -/
structure Hyb01StopCertificate
    (h0 : Hyb0Observation (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt))
    (h1 : Hyb1Observation (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P))
    (registers : Hyb01RegisterHistory (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
    (N : ℕ) where
  τ : ℕ
  bounded : τ ≤ N + 1
  trace_bound : h0.baseTrace.length ≤ N ∧ h1.game.baseTrace.length ≤ N
  before_stop : ∀ j, j < τ →
    h0.baseTrace.take j = h1.game.baseTrace.take j ∧
      ¬ BadEvent (h0.baseTrace.take j) ∧
      ¬ BadEvent (h1.game.baseTrace.take j) ∧
      ¬ AbortedBy h1.abortIndex? j ∧
      registers.side0 j = registers.side1 j
  terminal : τ = N + 1 ∨
    τ ≤ N ∧
      (BadEvent (h0.baseTrace.take τ) ∨
        BadEvent (h1.game.baseTrace.take τ) ∨
        AbortedBy h1.abortIndex? τ)
  no_stop : τ = N + 1 →
    h0.baseTrace = h1.game.baseTrace ∧
      h0.encodedTrace = h1.encodedTrace ∧
      h0.publicOutput = h1.publicOutput

/-- One sample of the instrumented Hyb₀↔Hyb₁ coupling.  The two observations are each produced
by their live experiment; the only extra data are the proof-only register histories and exact
stop certificate required by (44c)--(44e). -/
structure Hyb01CouplingSample (N : ℕ) where
  h0 : Hyb0Observation (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt)
  h1 : Hyb1Observation (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P)
  registers : Hyb01RegisterHistory (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
  stop : Hyb01StopCertificate (StmtIn := StmtIn) (StmtOut := StmtOut) (oSpec := oSpec)
    (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P)
    h0 h1 registers N

/-- A concrete coupling witness for the revised Hyb₀/Hyb₁ games.  The projections of `joint`
are required to be the actual `Hyb0Observed` and `Hyb1Observed` distributions; consequently this
is a genuine coupling construction obligation, not a relation over caller-provided observations
or a freely chosen sampler.  The last field is the Lemma 5.8 first-stop charge in (44f). -/
structure Hyb01CouplingWitness
    [SampleableType U]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (tₕ tₚ tₚᵢ : ℕ) where
  joint : ProbComp (Hyb01CouplingSample (StmtIn := StmtIn) (StmtOut := StmtOut)
    (oSpec := oSpec) (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt) (T_H := T_H)
    (T_P := T_P) (Hyb01BoundCount (U := U) (pSpec := pSpec) (δ := δ) tₕ tₚ tₚᵢ))
  h0_marginal : (fun sample => sample.h0) <$> joint =
    Hyb0Observed (Salt := Salt) (T_H := T_H) (T_P := T_P) oSpecImpl V maliciousProver
  h1_marginal : (fun sample => sample.h1) <$> joint =
    Hyb1Observed (Salt := Salt) (T_H := T_H) (T_P := T_P) oSpecImpl V maliciousProver
  first_stop_bound :
    (Pr[ fun sample => sample.stop.τ ≤
      Hyb01BoundCount (U := U) (pSpec := pSpec) (δ := δ) tₕ tₚ tₚᵢ | joint ]).toReal ≤
        badEventBound U (Hyb01BoundCount (U := U) (pSpec := pSpec) (δ := δ) tₕ tₚ tₚᵢ)

/-- The exact missing statement of the revised paper's lazy-sampling coupling lemma.  It asserts
existence of a joint execution with the concrete Hyb₀/Hyb₁ marginals, typed M/C registers, the
first-stop invariant (44c)--(44e), and the stateful Lemma 5.8 charge (44f).  Construction and
proof of this witness are deliberately separate; this declaration introduces neither a new paper
premise nor an arbitrary sampler parameter. -/
noncomputable def Hyb01LazySamplingCoupling
    [SampleableType U] [DecidableEq ι] [Section5Nonempty pSpec]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (tₕ tₚ tₚᵢ : ℕ) : Prop :=
  KeyLemma.IsLemma5_1QueryBound maliciousProver tₕ tₚ tₚᵢ →
    Nonempty (Hyb01CouplingWitness (StmtIn := StmtIn) (StmtOut := StmtOut) (oSpec := oSpec)
      (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P)
      oSpecImpl V maliciousProver tₕ tₚ tₚᵢ)

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)] [VCVCompatible U]
  [∀ i, VCVCompatible (pSpec.Message i)] [VCVCompatible Salt] [SaltCodec U δ Salt] in
/-- The purely probabilistic last step of the Hyb₀--Hyb₁ first-stop argument.  A joint
execution whose two public projections agree unless its stop index is at most `N` has
statistical distance at most the probability of that stop.  This is intentionally stated over
the already-constructed joint execution: the substantive cryptographic work is constructing the
joint execution and charging its first stop, while this lemma is just the standard
identical-until-bad consequence. -/
private lemma tvDist_map_publicOutput_le_stop
    [SampleableType U]
    (N : ℕ)
    (joint : ProbComp (Hyb01CouplingSample (StmtIn := StmtIn) (StmtOut := StmtOut)
      (oSpec := oSpec) (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt) (T_H := T_H)
      (T_P := T_P) N)) :
    tvDist
        ((fun sample => sample.h0.publicOutput) <$> joint)
        ((fun sample => sample.h1.publicOutput) <$> joint) ≤
      (Pr[ fun sample => sample.stop.τ ≤ N | joint ]).toReal := by
  simpa only [map_eq_bind_pure_comp, Function.comp_apply] using
    (tvDist_bind_left_event_le joint
      (fun sample => pure sample.h0.publicOutput)
      (fun sample => pure sample.h1.publicOutput)
      (fun sample => sample.stop.τ ≤ N)
      (fun sample hnot => by
        have hbounded := sample.stop.bounded
        have hterminal : sample.stop.τ = N + 1 := by
          omega
        have houtput : sample.h0.publicOutput = sample.h1.publicOutput :=
          (sample.stop.no_stop hterminal).2.2
        simp [houtput]))

/-- The updated Claim 5.21 endpoint statement over the computed Hyb0/Hyb1 games.  The revised
Section 5 scope `Section5Nonempty` entails `N_𝒱 > 0`, so its paper statement has one direct
`B(T + 1 + N_𝒱)` branch; the generic `(0,0)` split remains only in the trace-level Lemma 5.8
core, where empty schedules are still meaningful. -/
noncomputable def Claim521
    [DecidableEq ι] [Section5Nonempty pSpec]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (tₕ tₚ tₚᵢ : ℕ) : Prop :=
  KeyLemma.IsLemma5_1QueryBound maliciousProver tₕ tₚ tₚᵢ →
    let T := tₕ + tₚ + tₚᵢ
    let nV := DuplexSpongeFS.verifierPermCallCount (pSpec := pSpec) (δ := δ)
    HybridTVDist
      (Hyb0 (Salt := Salt) (T_H := T_H) (T_P := T_P) oSpecImpl V maliciousProver)
      (Hyb1 (Salt := Salt) (T_H := T_H) (T_P := T_P) oSpecImpl V maliciousProver) ≤
        badEventBound U (T + 1 + nV)

/-- The concrete first-stop coupling implies the revised Claim 5.21 bound.  This packages only
the **last** probability-theoretic step: the witness supplies the actual Hyb₀/Hyb₁ marginals and
the `first_stop_bound`; `tvDist_map_publicOutput_le_stop` turns equality off the stop event into
the displayed total-variation bound.  Thus Claim 5.21 is no longer left as an unconnected
statement-layer promise once the lazy-sampling coupling has been constructed. -/
lemma claim521_of_hyb01LazySamplingCoupling
    [SampleableType U] [DecidableEq ι] [Section5Nonempty pSpec]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (tₕ tₚ tₚᵢ : ℕ)
    (hCoupling : Hyb01LazySamplingCoupling (StmtIn := StmtIn) (StmtOut := StmtOut)
      (oSpec := oSpec) (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt) (T_H := T_H)
      (T_P := T_P) oSpecImpl V maliciousProver tₕ tₚ tₚᵢ) :
    Claim521 (StmtIn := StmtIn) (StmtOut := StmtOut) (oSpec := oSpec) (pSpec := pSpec)
      (U := U) (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P)
      oSpecImpl V maliciousProver tₕ tₚ tₚᵢ := by
  intro hQueryBound
  rcases hCoupling hQueryBound with ⟨witness⟩
  let N := Hyb01BoundCount (U := U) (pSpec := pSpec) (δ := δ) tₕ tₚ tₚᵢ
  have htv :
      tvDist
          ((fun sample => sample.h0.publicOutput) <$> witness.joint)
          ((fun sample => sample.h1.publicOutput) <$> witness.joint) ≤
        (Pr[ fun sample => sample.stop.τ ≤ N | witness.joint ]).toReal :=
    tvDist_map_publicOutput_le_stop (StmtIn := StmtIn) (StmtOut := StmtOut)
      (oSpec := oSpec) (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt) (T_H := T_H)
      (T_P := T_P) N witness.joint
  have htv' :
      tvDist
          ((fun observation => observation.publicOutput) <$>
            ((fun sample => sample.h0) <$> witness.joint))
          ((fun observation => observation.publicOutput) <$>
            ((fun sample => sample.h1) <$> witness.joint)) ≤
        (Pr[ fun sample => sample.stop.τ ≤ N | witness.joint ]).toReal := by
    simpa only [Functor.map_map, Function.comp_apply] using htv
  rw [witness.h0_marginal, witness.h1_marginal,
    Hyb0Observed_map_publicOutput_eq_Hyb0, Hyb1Observed_map_publicOutput_eq_Hyb1] at htv'
  exact htv'.trans witness.first_stop_bound

/-- One sample of the exact H₁/H₂ image-fibre coupling.  The left component retains the
lossless H₁ observation, so its raw request log, order, and repeated-key multiplicity remain
available to the construction.  The right component is the actual H₂ public output. -/
structure Hyb12ImageFibreCouplingSample where
  h1 : Hyb1Observation (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P)
  h2 : ConcreteHybridOutput (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (Salt := Salt)

/-- The concrete endpoint witness for revised Claim 5.22.  Its construction is the paper's
image-fibre coupling: sample an encoded table, retain its decoded image table and an image
witness, then sample one uniform representative from every exposed fibre.  Equation (46a)
gives the H₁ encoded-table marginal; the fibre cache gives the adaptive H₂ marginal and reuses
the representative at a repeated key.  The construction must also carry the observed H₁ log
through the H₂ line-4 map, so `outputs_agree` includes the final public game output rather than
only a table marginal.  No decoder-surjectivity assumption is permitted here. -/
structure Hyb12ImageFibreCouplingWitness
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) where
  joint : ProbComp (Hyb12ImageFibreCouplingSample (oSpec := oSpec) (StmtIn := StmtIn)
    (StmtOut := StmtOut) (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt) (T_H := T_H)
    (T_P := T_P))
  h1_marginal : (fun sample => sample.h1) <$> joint =
    Hyb1Observed (Salt := Salt) (T_H := T_H) (T_P := T_P) oSpecImpl V maliciousProver
  h2_marginal : (fun sample => sample.h2) <$> joint =
    Hyb2 (Salt := Salt) (T_H := T_H) (T_P := T_P) oSpecImpl V maliciousProver
  outputs_agree : ∀ sample : Hyb12ImageFibreCouplingSample (oSpec := oSpec)
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) (δ := δ)
      (Salt := Salt) (T_H := T_H) (T_P := T_P), sample.h1.publicOutput = sample.h2

/-- The only unresolved operational premise of Claim 5.22.  The exact Core-only proof route is
recorded in `Security.DecodedFibreCoupling`: `sampleImageFibreTablePair` proves the uniform H₁
table marginal, `evalDist_decodedFibreLazyImpl_eq_eager` proves adaptive/repeated-key fibre
realization, and the remaining live-runner factorization preserves the observed log.  This is
temporary proof state, not a new public paper assumption and not evidence that Claim 5.22 has
already been closed. -/
noncomputable def Hyb12ImageFibreCoupling
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) : Prop :=
  Nonempty (Hyb12ImageFibreCouplingWitness (StmtIn := StmtIn) (StmtOut := StmtOut)
    (oSpec := oSpec) (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt) (T_H := T_H)
    (T_P := T_P) oSpecImpl V maliciousProver)

/-- Updated Claim 5.22: reparameterizing an encoded challenge table by first sampling its
decoded value and then one lifted representative is exact.  The codec bias belongs to Claim 5.23
instead; retaining it here was the old-paper ordering and would make the revised hybrid proof
target the wrong statement. -/
noncomputable def Claim522
    [Section5Nonempty pSpec]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) : Prop :=
  HybridTVDist (Hyb1 (Salt := Salt) (T_H := T_H) (T_P := T_P) oSpecImpl V maliciousProver)
    (Hyb2 (Salt := Salt) (T_H := T_H) (T_P := T_P) oSpecImpl V maliciousProver) = 0

/-- The purely probabilistic endpoint of the H₁/H₂ image-fibre coupling.  Once the concrete
Core-only joint execution has been constructed, the revised public Claim 5.22 follows with
zero loss. -/
lemma claim522_of_hyb12ImageFibreCoupling
    [Section5Nonempty pSpec]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (hCoupling : Hyb12ImageFibreCoupling (StmtIn := StmtIn) (StmtOut := StmtOut)
      (oSpec := oSpec) (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt) (T_H := T_H)
      (T_P := T_P) oSpecImpl V maliciousProver) :
    Claim522 (StmtIn := StmtIn) (StmtOut := StmtOut) (oSpec := oSpec) (pSpec := pSpec)
      (U := U) (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P) oSpecImpl V maliciousProver := by
  rcases hCoupling with ⟨witness⟩
  let Sample := Hyb12ImageFibreCouplingSample (oSpec := oSpec) (StmtIn := StmtIn)
    (StmtOut := StmtOut) (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt) (T_H := T_H)
    (T_P := T_P)
  have hpointwise :
      (fun sample : Sample => sample.h1.publicOutput) = (fun sample : Sample => sample.h2) :=
    funext witness.outputs_agree
  have hmap :
      (fun sample : Sample => sample.h1.publicOutput) <$> witness.joint =
        (fun sample : Sample => sample.h2) <$> witness.joint :=
    congrArg (fun f => f <$> witness.joint) hpointwise
  change tvDist
    (Hyb1 (Salt := Salt) (T_H := T_H) (T_P := T_P) oSpecImpl V maliciousProver)
    (Hyb2 (Salt := Salt) (T_H := T_H) (T_P := T_P) oSpecImpl V maliciousProver) = 0
  rw [← Hyb1Observed_map_publicOutput_eq_Hyb1 (Salt := Salt) (T_H := T_H) (T_P := T_P)
    oSpecImpl V maliciousProver, ← witness.h1_marginal, ← witness.h2_marginal]
  simp only [Functor.map_map]
  rw [hmap]
  exact tvDist_self _

/-- One sample of the Claim-5.23 codec coupling.  `h4` retains the actual eager salted FS table
*with* its real Hyb4 output; the later private-shadow proof therefore cannot accidentally use a
separately sampled table. -/
structure Hyb23CodecCouplingSample (T_H T_P : Type)
    [LawfulTraceNablaImpl T_H T_P StmtIn U] where
  h2 : ConcreteHybridOutput (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (Salt := Salt)
  h3 : KeyLemma.HybridGameRevisedMappedObservation
    (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt)
    (fsChallengeOracle (StmtIn × Salt) pSpec) T_H T_P
    (ProverTransform.D2SAlgoMemo StmtIn U δ Salt pSpec)
  h4 : Hyb4ObservedSample (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (Salt := Salt)

/-- A concrete adaptive codec coupling.  Its two output marginals are the real Hyb2 and Hyb3
games, and its third marginal is the lossless observed Hyb4 run, retaining the table actually
used to produce that Hyb4 output.  The event may depend on the whole coupled sample, so a proof
may expose table cells in adaptive order; the off-event equality is exactly the property consumed
by the Claim-5.24 private shadow. -/
structure Hyb23CodecCouplingWitness
    [SampleableType U]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (tₚ : ℕ) where
  joint : ProbComp (Hyb23CodecCouplingSample (StmtIn := StmtIn) (StmtOut := StmtOut)
    (oSpec := oSpec) (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt)
    T_H T_P)
  h2_marginal : (fun sample => sample.h2) <$> joint =
    Hyb2 (Salt := Salt) (T_H := T_H) (T_P := T_P) oSpecImpl V maliciousProver
  h3_marginal : (fun sample => sample.h3) <$> joint =
    Hyb3Observed (Salt := Salt) (T_H := T_H) (T_P := T_P) oSpecImpl V maliciousProver
  h4_marginal : (fun sample => sample.h4) <$> joint =
    Hyb4Observed (Salt := Salt) (T_H := T_H) (T_P := T_P) oSpecImpl V maliciousProver
  codecBad : Hyb23CodecCouplingSample (StmtIn := StmtIn) (StmtOut := StmtOut)
    (oSpec := oSpec) (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt) T_H T_P → Prop
  codecBad_bound :
    (Pr[ codecBad | joint ]).toReal ≤
      etaStarCodecTerm (tₚ : ℝ) (iSup fun i => (codec.decodingBias i : ℝ))
        (∑ i, (codec.decodingBias i : ℝ))
  /-- The partial bridge's out-of-image branch is not hidden as an ordinary D2S abort: it is a
  codec mismatch and is charged by this same, single event. -/
  imageFailure_charged : ∀ sample,
    Hyb3CodecImageFailure (T_H := T_H) (T_P := T_P) sample.h3 → codecBad sample
  agrees_off_codecBad : ∀ sample, ¬ codecBad sample → sample.h2 = sample.h3.publicOutput

/-- The probability-theoretic endgame of Claim 5.23.  The cryptographic content is the
adaptive construction of `Hyb23CodecCouplingWitness`; once it is available, equality outside
`codecBad` gives the displayed Hyb2--Hyb3 distance by the standard identical-until-bad lemma. -/
private lemma tvDist_map_h2_h3_le_codecBad
    [SampleableType U]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (tₚ : ℕ)
    (witness : Hyb23CodecCouplingWitness (StmtIn := StmtIn) (StmtOut := StmtOut)
      (oSpec := oSpec) (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt) (T_H := T_H)
      (T_P := T_P) oSpecImpl V maliciousProver tₚ) :
    tvDist
        ((fun sample => sample.h2) <$> witness.joint)
        ((fun sample => sample.h3.publicOutput) <$> witness.joint) ≤
      (Pr[ witness.codecBad | witness.joint ]).toReal := by
  simpa only [map_eq_bind_pure_comp, Function.comp_apply] using
    (tvDist_bind_left_event_le witness.joint
      (fun sample => pure sample.h2)
      (fun sample => pure sample.h3.publicOutput)
      witness.codecBad
      (fun sample hnot => by simp [witness.agrees_off_codecBad sample hnot]))

/-- A constructed codec coupling immediately gives the quantitative Hyb2--Hyb3 consequence of
Claim 5.23.  The retained Hyb4 observation is intentionally not projected here: it is reserved
for the private-shadow coupling of Claim 5.24, avoiding a duplicate codec charge. -/
lemma hyb23CodecCouplingWitness_tvdist
    [SampleableType U]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (tₚ : ℕ)
    (witness : Hyb23CodecCouplingWitness (StmtIn := StmtIn) (StmtOut := StmtOut)
      (oSpec := oSpec) (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt) (T_H := T_H)
      (T_P := T_P) oSpecImpl V maliciousProver tₚ) :
    HybridTVDist
        (Hyb2 (Salt := Salt) (T_H := T_H) (T_P := T_P) oSpecImpl V maliciousProver)
        (Hyb3 (Salt := Salt) (T_H := T_H) (T_P := T_P) oSpecImpl V maliciousProver) ≤
      etaStarCodecTerm (tₚ : ℝ) (iSup fun i => (codec.decodingBias i : ℝ))
        (∑ i, (codec.decodingBias i : ℝ)) := by
  have htv := tvDist_map_h2_h3_le_codecBad (StmtIn := StmtIn) (StmtOut := StmtOut)
    (oSpec := oSpec) (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt) (T_H := T_H)
    (T_P := T_P) oSpecImpl V maliciousProver tₚ witness
  have htv' :
      tvDist
          ((fun sample => sample.h2) <$> witness.joint)
          ((fun observation => observation.publicOutput) <$>
            ((fun sample => sample.h3) <$> witness.joint)) ≤
        (Pr[ witness.codecBad | witness.joint ]).toReal := by
    simpa only [Functor.map_map, Function.comp_apply] using htv
  rw [witness.h2_marginal, witness.h3_marginal,
    Hyb3Observed_map_publicOutput_eq_Hyb3] at htv'
  exact htv'.trans witness.codecBad_bound

/-- The only adversarial resource used by the codec coupling: each fresh source standard-table
cell is caused by a source forward-permutation query.  Hash and inverse-permutation budgets do
not enter Claim 5.23's bound. -/
abbrev IsClaim523ForwardQueryBound
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) (tₚ : ℕ) : Prop :=
  by
    classical
    exact OracleComp.IsQueryBoundP maliciousProver
      (KeyLemma.isLemma5_1PermQuery (oSpec := oSpec) (StmtIn := StmtIn) (U := U)) tₚ

/-- Updated Claim 5.23: the codec comparison is an adaptive three-way coupling of Hyb2, Hyb3,
and the Hyb4 standard table.  This is stronger than a bare TV bound and records the shared table
needed by Lemma 5.24a.  Its sole resource premise is the `tₚ` bound on source forward permutation
queries, exactly as in the revised paper's fresh-cell accounting. -/
noncomputable def Claim523
    [DecidableEq ι] [Section5Nonempty pSpec]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (tₚ : ℕ) : Prop :=
  IsClaim523ForwardQueryBound (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
    (δ := δ) maliciousProver tₚ →
    Nonempty (Hyb23CodecCouplingWitness (StmtIn := StmtIn) (StmtOut := StmtOut)
      (oSpec := oSpec) (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt) (T_H := T_H)
      (T_P := T_P) oSpecImpl V maliciousProver tₚ)

/-- The updated Claim 5.24 endpoint statement.  Claim 5.23 already pays the codec mismatch, so
the public comparison is Hyb2 versus Hyb4 and contains that codec term exactly once, followed by
the stateful stopped-permutation envelope `D(T,N_𝒱)`.  Under the revised nonempty-round scope,
`N_𝒱 > 0`; the generic exceptional split remains inside the reusable stopped-extension core. -/
noncomputable def Claim524
    [DecidableEq ι] [Section5Nonempty pSpec]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (tₕ tₚ tₚᵢ : ℕ) : Prop :=
  KeyLemma.IsLemma5_1QueryBound maliciousProver tₕ tₚ tₚᵢ →
    let T := tₕ + tₚ + tₚᵢ
    let nV := DuplexSpongeFS.verifierPermCallCount (pSpec := pSpec) (δ := δ)
    HybridTVDist
      (Hyb2 (Salt := Salt) (T_H := T_H) (T_P := T_P) oSpecImpl V maliciousProver)
      (Hyb4 (Salt := Salt) (T_H := T_H) (T_P := T_P) oSpecImpl V maliciousProver) ≤
        etaStarCodecTerm (tₚ : ℝ) (iSup fun i => (codec.decodingBias i : ℝ))
          (∑ i, (codec.decodingBias i : ℝ)) + Dcap U T nV

/-- The full revised Lemma 5.1 statement with its *actual* endpoint experiments and fixed
algorithm witnesses.  Its error bound uses the exact stateful `N_𝒱`; no unused lower-bound
premise on the adversary's permutation-query count is retained. -/
noncomputable def Lemma51
    [DecidableEq ι] [Section5Nonempty pSpec]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (tₕ tₚ tₚᵢ : ℕ) : Prop :=
  ∀ maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ,
      KeyLemma.IsLemma5_1QueryBound maliciousProver tₕ tₚ tₚᵢ →
        HybridTVDist (Hyb0 (Salt := Salt) (T_H := T_H) (T_P := T_P) oSpecImpl V maliciousProver)
          (Hyb4 (Salt := Salt) (T_H := T_H) (T_P := T_P) oSpecImpl V maliciousProver) ≤
            KeyLemma.ηStar U tₕ tₚ tₚᵢ
              (DuplexSpongeFS.verifierPermCallCount (pSpec := pSpec) (δ := δ))
              codec.decodingBias ∧
          KeyLemma.IsD2SAlgoChallengeQueryBound
            (ProverTransform.d2sAlgoRevised (T_H := T_H) (T_P := T_P) (δ := δ) (Salt := Salt)
              (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
            maliciousProver tₕ tₚ tₚᵢ

end Statement

end DuplexSpongeFS
