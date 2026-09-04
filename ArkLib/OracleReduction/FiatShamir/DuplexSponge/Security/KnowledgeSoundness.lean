/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen, Michele Orrù, Yuxi Zheng
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Soundness

/-!
# Knowledge Soundness of Duplex Sponge Fiat–Shamir (CO25 §6)

This file formalizes Construction 6.3 and Theorem 6.2 from CO25, using the soundness infrastructure
and Section 5 witness interface defined in `Soundness.lean` and `KeyLemma.lean`.

## Theorem 6.2: IP SR-KS → DSFS straightline KS

Bespoke, query-bounded form mirroring `duplex_sponge_fiat_shamir_soundness`.  (An earlier attempt
phrased the conclusion in the *generic* library `Verifier.knowledgeSoundness`; that notion is
selective + **unbounded**, so it cannot carry the query-bounded `η★` term —
`duplex_sponge_fiat_shamir_straightline_knowledge_soundness` instead concludes CO25 Def 3.6
`adaptiveNARGKnowledgeSoundness` with a query-bounded adversary class.) -/

open OracleComp OracleSpec ProtocolSpec

open ToVCVio.VCVNorm
  (simulateQ_bind_congr logging_strip₂ logging_strip₃ simulateQ_optionT_map optionT_liftM_eq_lift
   simulateQ_optionT_mk)

namespace DuplexSpongeFS

open DuplexSpongeFS.ProverTransform DuplexSpongeFS.TraceTransform DuplexSpongeFS.DSTraceStorage
open DuplexSpongeFS.KeyLemma

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  {U : Type} [SpongeUnit U] [SpongeSize] [VCVCompatible U]
  [∀ i, VCVCompatible (pSpec.Message i)]
  [codec : Codec pSpec U]
  {δ : Nat}
  {Salt : Type} [VCVCompatible Salt] [SaltCodec U δ Salt]
  [DecidableEq StmtIn] [DecidableEq U]
  {T_H : Type} {T_P : Type}
  [LawfulTraceNablaImpl T_H T_P StmtIn U]

noncomputable section

local instance : SampleableType U := VCVCompatible.toSampleableType
local instance (i : pSpec.ChallengeIdx) : SampleableType (pSpec.Challenge i) :=
  VCVCompatible.toSampleableType

/-- The DSFS **straightline knowledge-soundness game** (bespoke, query-bounded).
Runs the proof-only malicious prover and the DSFS verifier, then runs the straightline extractor
on the proof and combined query log. -/
def dsfsKSGameDist
    -- Bare straightline-extractor shape (matching the Def-3.6 experiment): the extractor's spec
    -- carries its own `(Unit →ₒ U)` sampler slot (Construction 6.3's D2STrace), answered by
    -- `d2sUnitSampleImpl` in the same eager block as the prover/verifier.
    (dsfsExtractor : StmtIn →
      FullTranscript ⟨!v[.P_to_V], !v[DSSaltedProof (pSpec := pSpec) (U := U) δ]⟩ →
      QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U) →
      QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U) →
        OptionT (OracleComp (Unit →ₒ U)) WitIn)
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    ProbComp (StmtIn × Option WitIn × Option StmtOut) := do
  -- Prover + §5.8 forward verifier under the eager sponge `hyb0Impl`; their logs `tr, tr_𝒱` are
  -- read out as DATA (kept separate, CO25 Construction 6.3).  Then the extractor runs separately
  -- over its own `(Unit →ₒ U)` sampler (`d2sUnitSampleImpl`) — reading challenges from the logs,
  -- querying no challenge oracle (Def 3.14), so it never sees the sponge state `σ`.
  -- Same five-field read-out as the paper-faithful `adaptiveNARGKnowledgeSoundnessExp`, so the
  -- Def-3.6 experiment/game bridge is definitional after the verifier wrapper normalizes.
  let ⟨stmtIn, proof, proveLog, stmtOut?, verifyLog⟩ ←
    (simulateQ (hyb0Impl oSpecImpl) (do
      let ⟨⟨stmtIn, proof⟩, proveLog⟩ ← (simulateQ loggingOracle maliciousProver).run
      let ⟨stmtOut?, verifyLog⟩ ←
        (simulateQ loggingOracle (runForwardVerifierWide δ V stmtIn proof)).run
      pure (stmtIn, proof, proveLog, stmtOut?, verifyLog))).run' (← hyb0Init)
  let witIn? ← simulateQ (d2sUnitSampleImpl (U := U))
    (dsfsExtractor stmtIn
      (Fin.cons proof (fun i => i.elim0) :
        FullTranscript ⟨!v[.P_to_V], !v[DSSaltedProof (pSpec := pSpec) (U := U) δ]⟩)
      proveLog verifyLog).run
  pure (stmtIn, witIn?, stmtOut?)

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)] [VCVCompatible U]
  [∀ i, VCVCompatible (pSpec.Message i)] [DecidableEq StmtIn] [DecidableEq U] in
/-- **§6.2 de-abort lemma (KS).**  The de-aborted, tagged §5.8 game `dsfsGame` equals the *raw*
prover+verifier read-out (the read-out `dsfsKSGameDist` keeps — including the query logs) composed
with de-abort+tag.  KS analog of the proven `dsfsNargSoundnessExp_eq_dsfsGame`'s `keyA`, but
**keeping the query logs** (Construction 6.3's `E_std` consumes them, so they cannot be stripped).
-/
theorem dsfsGame_run_eq_deabortTag
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    (dsfsGame (δ := δ) V maliciousProver :
        OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
          (Option (DSFSGameOutput (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
            (pSpec := pSpec) (U := U) (δ := δ))))
      = (fun five : StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ ×
            QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U) × Option StmtOut ×
            QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U) =>
          five.2.2.2.1.map (fun s =>
            ((five.1, s, five.2.1,
              five.2.2.1.map (fun e => (SourceTag.prover, e)) ++
                five.2.2.2.2.map (fun e => (SourceTag.verifier, e))) :
              DSFSGameOutput (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
                (pSpec := pSpec) (U := U) (δ := δ))))
        <$> (do
          let ⟨⟨stmtIn, proof⟩, proveLog⟩ ← (simulateQ loggingOracle maliciousProver).run
          let ⟨stmtOut?, verifyLog⟩ ←
            (simulateQ loggingOracle (runForwardVerifierWide δ V stmtIn proof)).run
          pure (stmtIn, proof, proveLog, stmtOut?, verifyLog)) := by
  change OptionT.run (dsfsGame (δ := δ) V maliciousProver) = _
  unfold dsfsGame
  vcv_norm

/-- Canonical left injection into a binary oracle sum.  Naming this generic construction keeps
Lean from selecting a longer, reassociation-based `SubSpec` path at concrete nested sums. -/
private def liftCompLeft {j k : Type} {spec : OracleSpec j} {auxSpec : OracleSpec k} {α : Type}
    (X : OracleComp spec α) : OracleComp (spec + auxSpec) α :=
  liftComp X (spec + auxSpec)

/-- Common prover/verifier read-out underlying both sides of the Hyb₄ KS equivalence. -/
private def hyb4KSReadout
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (d2sAlgoTransform : D2SAlgoTransform (δ := δ) (Salt := Salt)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U)
      (fsChallengeOracle (StmtIn × Salt) pSpec))
      (StmtIn × FSSaltedProof pSpec Salt ×
        QueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) × Option StmtOut ×
        QueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)) := do
  let ⟨stmtAndProof?, proveLogRaw⟩ ←
    (simulateQ loggingOracle (d2sAlgoTransform maliciousProver)).run
  let stmtAndProof := stmtAndProof?.getD default
  let ⟨stmtOut?, verifyLogRaw⟩ ←
    (simulateQ loggingOracle (basicFSVerifierComp V stmtAndProof)).run
  pure (stmtAndProof.1, stmtAndProof.2,
    filterD2SChallengePlusUnitQueryLog (oSpec := oSpec) (U := U) proveLogRaw,
    stmtOut?,
    filterD2SChallengePlusUnitQueryLog (oSpec := oSpec) (U := U) verifyLogRaw)

/-- The same read-out in the reassociated coin-bearing NARG oracle model. -/
private def coinNARGKSReadout
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (d2sAlgoTransform : D2SAlgoTransform (δ := δ) (Salt := Salt)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    OracleComp ((oSpec + srChallengeOracle (StmtIn × Salt) pSpec) +
      ((Unit →ₒ U) + unifSpec))
      (StmtIn × FSSaltedProof pSpec Salt ×
        QueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) × Option StmtOut ×
        QueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)) := do
  let ⟨⟨x, π⟩, tr⟩ ←
    (simulateQ loggingOracle
      (nargInducedProver maliciousProver d2sAlgoTransform)).run
  let ⟨stmtOut?, trV⟩ ← liftCompLeft (auxSpec := ((Unit →ₒ U) + unifSpec))
    (simulateQ loggingOracle (fsSaltedVerify V x π).run).run
  pure (x, π, tr.fst, stmtOut?, trV)

omit [SpongeUnit U] [SpongeSize] codec [DecidableEq StmtIn] [DecidableEq U] in
private theorem simulateQ_coinVerifierLog_eq_hyb4VerifierLog
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (x : StmtIn) (π : FSSaltedProof pSpec Salt) :
    simulateQ
        ((((srImplLift (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec) oSpecImpl).addLift
          (srChallengeQueryImpl' (Statement := StmtIn × Salt) (pSpec := pSpec)) :
            QueryImpl (oSpec + srChallengeOracle (StmtIn × Salt) pSpec)
              (StateT (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp)).addLift
          (d2sAuxImpl (U := U))))
        (liftCompLeft (auxSpec := ((Unit →ₒ U) + unifSpec))
          (simulateQ loggingOracle (fsSaltedVerify V x π).run).run) =
      (fun p => (p.1,
        filterD2SChallengePlusUnitQueryLog (oSpec := oSpec) (U := U) p.2)) <$>
        simulateQ (srHyb4Impl (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec)
          (U := U) oSpecImpl)
          (simulateQ loggingOracle (basicFSVerifierComp V (x, π))).run := by
  unfold basicFSVerifierComp
  rw [← simulateQ_map, filter_withQueryLog_simulateQ_liftFS]
  have hHandler := expVerifyHandler_eq_hybChallengeImpl_compose_liftFS
    (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec) (U := U) oSpecImpl
  rw [hybChallengeImpl_eq_srAddLift] at hHandler
  let X := (simulateQ loggingOracle (fsSaltedVerify V x π).run).run
  calc
    simulateQ
        ((((srImplLift (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec) oSpecImpl).addLift
          (srChallengeQueryImpl' (Statement := StmtIn × Salt) (pSpec := pSpec)) :
            QueryImpl (oSpec + srChallengeOracle (StmtIn × Salt) pSpec)
              (StateT (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp)).addLift
          (d2sAuxImpl (U := U))))
        (liftCompLeft (auxSpec := ((Unit →ₒ U) + unifSpec)) X)
      = simulateQ
          ((srImplLift (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec) oSpecImpl).addLift
            (srChallengeQueryImpl' (Statement := StmtIn × Salt) (pSpec := pSpec))) X := by
        unfold liftCompLeft
        simp only [QueryImpl.addLift_def, QueryImpl.liftTarget_self,
          QueryImpl.simulateQ_add_liftComp_left]
    _ = simulateQ
          ((srHyb4Impl (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec) (U := U) oSpecImpl) ∘ₛ
            liftFSSaltedQueriesToD2SChallengePlusUnit) X := by
        exact (congrArg (fun H => simulateQ H X) hHandler).symm
    _ = simulateQ
          (srHyb4Impl (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec) (U := U) oSpecImpl)
          (simulateQ liftFSSaltedQueriesToD2SChallengePlusUnit X) := by
        rw [QueryImpl.simulateQ_compose]

omit [SaltCodec U δ Salt] codec [DecidableEq StmtIn] [DecidableEq U] in
private theorem simulateQ_coinNARGKSReadout_eq_hyb4KSReadout
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (d2sAlgoTransform : D2SAlgoTransform (δ := δ) (Salt := Salt)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    simulateQ
        ((((srImplLift (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec) oSpecImpl).addLift
          (srChallengeQueryImpl' (Statement := StmtIn × Salt) (pSpec := pSpec)) :
            QueryImpl (oSpec + srChallengeOracle (StmtIn × Salt) pSpec)
              (StateT (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp)).addLift
          (d2sAuxImpl (U := U))))
        (coinNARGKSReadout V maliciousProver d2sAlgoTransform) =
      simulateQ
        (srHyb4Impl (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec)
          (U := U) oSpecImpl)
        (hyb4KSReadout V maliciousProver d2sAlgoTransform) := by
  classical
  unfold coinNARGKSReadout hyb4KSReadout nargInducedProver basicFSVerifierComp
  rw [withQueryLog_simulateQ_srReassoc]
  simp only [WriterT.run_map', simulateQ_bind, simulateQ_map, simulateQ_pure,
    ← QueryImpl.simulateQ_compose,
    srHyb4Impl_eq_expHandler_compose_srReassoc, bind_map_left, Functor.map_map]
  refine bind_congr fun x => ?_
  rw [simulateQ_coinVerifierLog_eq_hyb4VerifierLog V oSpecImpl]
  unfold basicFSVerifierComp
  simp only [← QueryImpl.simulateQ_compose, bind_map_left]
  refine bind_congr fun xV => ?_
  rw [srReassocQueryLog_fst]
  rfl

omit [∀ i, VCVCompatible (pSpec.Challenge i)] [VCVCompatible U] codec
  [SaltCodec U δ Salt] [DecidableEq StmtIn] [DecidableEq U] in
private theorem basicFiatShamirGame_run_eq_hyb4KSReadout
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (d2sAlgoTransform : D2SAlgoTransform (δ := δ) (Salt := Salt)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    (basicFiatShamirGame V (d2sAlgoTransform maliciousProver)).run =
      (fun ⟨x, π, trP, stmtOut?, trV⟩ =>
        stmtOut?.map fun stmtOut =>
          (x, stmtOut, π,
            trP.map (fun e => (SourceTag.prover, e)) ++
              trV.map (fun e => (SourceTag.verifier, e)))) <$>
        hyb4KSReadout V maliciousProver d2sAlgoTransform := by
  unfold basicFiatShamirGame hyb4KSReadout
  vcv_norm

omit codec [SaltCodec U δ Salt] [DecidableEq StmtIn] [DecidableEq U] in
private theorem adaptiveNARGKS_eq_coinNARGKSReadout
    (E_std : StmtIn → FSSaltedProof pSpec Salt →
      QueryLog (oSpec + srChallengeOracle (StmtIn × Salt) pSpec) →
      QueryLog (oSpec + srChallengeOracle (StmtIn × Salt) pSpec) →
        OptionT (OracleComp (Unit →ₒ U)) WitIn)
    (V : Verifier oSpec StmtIn StmtOut pSpec) (oSpecImpl : QueryImpl oSpec ProbComp)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (d2sAlgoTransform : D2SAlgoTransform (δ := δ) (Salt := Salt)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    adaptiveNARGKnowledgeSoundnessExpWithCoins
        (init := srInitDIP (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec))
        (impl := (srImplLift (StmtIn := StmtIn) (Salt := Salt)
          (pSpec := pSpec) oSpecImpl).addLift (srChallengeQueryImpl'
            (Statement := StmtIn × Salt) (pSpec := pSpec)))
        d2sAuxImpl (d2sUnitSampleImpl (U := U))
        (Verifier.singleSaltFiatShamir (Salt := Salt) V) E_std
        (nargInducedProver maliciousProver d2sAlgoTransform) = (do
      let s ← srInitDIP (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec)
      let a ← StateT.run' (simulateQ
          ((((srImplLift (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec) oSpecImpl).addLift
            (srChallengeQueryImpl' (Statement := StmtIn × Salt) (pSpec := pSpec)) :
              QueryImpl (oSpec + srChallengeOracle (StmtIn × Salt) pSpec)
                (StateT (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp)).addLift
            (d2sAuxImpl (U := U))))
          (coinNARGKSReadout V maliciousProver d2sAlgoTransform)) s
      let witIn? ← simulateQ (d2sUnitSampleImpl (U := U))
        (E_std a.1 a.2.1 a.2.2.1 a.2.2.2.2).run
      pure (a.1, witIn?, a.2.2.2.1)) := by
  classical
  unfold adaptiveNARGKnowledgeSoundnessExpWithCoins coinNARGKSReadout
    nargInducedProver liftCompLeft
  simp only [fsSaltedNIV_verify]
  simp only [WriterT.run_map', simulateQ_bind, simulateQ_map, simulateQ_pure,
    ← QueryImpl.simulateQ_compose, StateT.run'_bind', StateT.run'_pure',
    bind_map_left, pure_bind, bind_assoc]

/-- **§6.2 extractor kernel `k`**. Runs the basic-FS NARG-KS extractor `E_std`
on the basic-FS game output. -/
noncomputable def ksFactKernel
    (E_std : StmtIn → FSSaltedProof pSpec Salt →
      QueryLog (oSpec + srChallengeOracle (StmtIn × Salt) pSpec) →
      QueryLog (oSpec + srChallengeOracle (StmtIn × Salt) pSpec) →
        OptionT (OracleComp (Unit →ₒ U)) WitIn) :
    Option (BasicFiatShamirGameOutput (oSpec := oSpec) (StmtIn := StmtIn)
        (StmtOut := StmtOut) (pSpec := pSpec) (Salt := Salt)) →
      ProbComp (StmtIn × Option WitIn × Option StmtOut) :=
  fun out => match out with
    -- `Hyb` produced no output (game abort): a non-accepting triple (`stmtOut? = none`), which
    -- `nargKSFailEvent` reads as no break.  The placeholder statement is never inspected.
    | none => pure ((default : StmtIn), none, none)
    | some result => do
        -- Recover `(tr_𝒫, tr_𝒱)` from the combined tagged log by source.
        let tr := result.2.2.2
        let trP := TaggedQueryLog.proverLog tr
        let trV := TaggedQueryLog.verifierLog tr
        -- `E_std` reads its challenges from `trP, trV` (CO25 Def 3.14 — no challenge-oracle query);
        -- its only oracle is the `𝒰(Σ)` sampler `(Unit →ₒ U)`, answered by `d2sUnitSampleImpl`.
        -- Both logs are already the bare `oSpec + srChallenge` transcript (no prover coins) —
        -- matching the coin-stripped `tr.fst` feed in the Def-3.6 experiment.
        let witIn? ← simulateQ (d2sUnitSampleImpl (U := U))
          (E_std result.1 result.2.2.1 trP trV).run
        pure (result.1, witIn?, some result.2.1)

set_option maxHeartbeats 1000000 in
-- The de-abort rewrite then `probEvent_bind_congr'` over the wide read-out tuple is
-- elaboration-heavy, so the heartbeat budget is raised.
omit [VCVCompatible Salt] [∀ i, VCVCompatible (pSpec.Challenge i)] in
/-- **§6.2 HELPER `hL1` (Hyb₀ step).**  KS analog of the proven soundness
`dsfsGame_falseAccept_eq_hyb0`: the DSFS straightline-KS game (Construction 6.3 over `E_std`) equals
`Hyb₀ >>= ksFactKernel E_std` on the `nargKSFailEvent` marginal (the §5.8 `D2STrace` line-4 map
preserves the read-out; the `E_std` kernel is threaded through). -/
theorem dsfs_knowledge_soundness_failure_eq_hyb0
    [∀ i, DecidableEq (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Message i)]
    (E_std : StmtIn → FSSaltedProof pSpec Salt →
      QueryLog (oSpec + srChallengeOracle (StmtIn × Salt) pSpec) →
      QueryLog (oSpec + srChallengeOracle (StmtIn × Salt) pSpec) →
        OptionT (OracleComp (Unit →ₒ U)) WitIn)
    (V : Verifier oSpec StmtIn StmtOut pSpec) (oSpecImpl : QueryImpl oSpec ProbComp)
    (relIn : Set (StmtIn × WitIn)) (langOut : Set StmtOut)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    Pr[ nargKSFailEvent relIn langOut |
        dsfsKSGameDist
          (dsfsStraightlineExtractor (T_H := T_H) (T_P := T_P) E_std)
          oSpecImpl V maliciousProver ]
      = Pr[ nargKSFailEvent relIn langOut |
          hyb_0 (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
            (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
            oSpecImpl V maliciousProver
            (d2sTraceSalted (T_H := T_H) (T_P := T_P) (δ := δ) (Salt := Salt)
              (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
            >>= ksFactKernel E_std ] := by
  classical
  -- A Pr-level (marginal) equality, NOT a distribution equality.  `dsfsKSGameDist` runs the
  -- extractor on EVERY run (incl. verifier-reject), while `hyb_0 >>= k` de-aborts a reject run to
  -- `(default, none, none)` and never runs `E_std` there.  These distributions genuinely
  -- DIFFER on reject (the extractor may even `failure`), but `nargKSFailEvent` is blind to a reject
  -- run (`stmtOut? = none ⇒ False`), so the *marginals* agree: both `0` on reject, identical on
  -- accept (same `E_std`, same logs).  `dsfsGame_run_eq_deabortTag` makes both factor through the
  -- SAME raw prover+verifier read-out; we then compare each five-field read-out.
  conv_rhs =>
    simp only [hyb_0, mappedDSFSGameDist, dsfsGameDist]
    rw [dsfsGame_run_eq_deabortTag, simulateQ_map]
    simp only [ksFactKernel, StateT.run'_map', bind_map_left, map_bind, bind_assoc]
  conv_lhs =>
    simp only [dsfsKSGameDist, dsfsStraightlineExtractor, runSection58TraceMap]
  refine probEvent_bind_congr' _ _ (fun s => ?_)
  refine probEvent_bind_congr' _ _ (fun five => ?_)
  obtain ⟨stmtIn, proof, proveLog, stmtOut?, verifyLog⟩ := five
  rcases stmtOut? with _ | st
  · -- reject (`stmtOut? = none`): `nargKSFailEvent` is `False` on every output (both sides yield a
    -- `none` statement-out), so both marginals are `0` — the differing reject behaviour (incl. a
    -- possible `E_std` `failure` on the LHS) is invisible to the event.
    dsimp only
    simp only [Option.map_none, pure_bind]
    refine (probEvent_eq_zero fun x hx => ?_).trans (probEvent_eq_zero fun x hx => ?_).symm
    · simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hx
      obtain ⟨_, _, rfl⟩ := hx
      simp [nargKSFailEvent]
    · simp only [ksFactKernel, support_pure, Set.mem_singleton_iff] at hx
      subst hx
      simp [nargKSFailEvent]
  · -- accept: `dsfsKSGameDist`'s fused `D2STrace ≫ E_std` equals `k`'s split version (same `E_std`,
    -- same logs), so the two read-out distributions coincide and the marginals are equal.
    refine probEvent_congr' (fun _ _ => Iff.rfl) ?_
    dsimp only
    simp only [Option.map_some, Fin.cons_zero, OptionT.run_bind, OptionT.run_lift, Option.elimM,
      simulateQ_bind, pure_bind, bind_assoc]
    rw [evalSPMF_bind, evalSPMF_bind]; congr 1; funext x
    cases x <;> simp only [Option.elim, Option.getD, pure_bind] <;> rfl

omit [SaltCodec U δ Salt] codec [DecidableEq StmtIn] [DecidableEq U] in
/-- **§6.2 HELPER `hL3` (the Hyb₄ problem).**  KS twin of the soundness `hyb4_hdist`:
`Hyb₄ >>= ksFactKernel E_std` and the coin-bearing basic-FS NARG straightline-KS experiment
(Def 3.6) for `nargInducedProver`, verifier `fsSaltedVerify V`, and extractor `E_std` have the
same failure-event probability.  Their full distributions may differ after verifier rejection,
where the latter still runs the extractor; both outcomes lie outside `nargKSFailEvent`.  On
acceptance, the eager↔presampled / `deriveTranscript` / prover-de-abort game equivalence identifies
their readouts (shared in substance with §6.1's `hyb4_hdist`). -/
theorem hyb4_knowledge_soundness_failure_eq_single_salt
    (E_std : StmtIn → FSSaltedProof pSpec Salt →
      QueryLog (oSpec + srChallengeOracle (StmtIn × Salt) pSpec) →
      QueryLog (oSpec + srChallengeOracle (StmtIn × Salt) pSpec) →
        OptionT (OracleComp (Unit →ₒ U)) WitIn)
    (V : Verifier oSpec StmtIn StmtOut pSpec) (oSpecImpl : QueryImpl oSpec ProbComp)
    (relIn : Set (StmtIn × WitIn)) (langOut : Set StmtOut)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (d2sAlgoTransform : D2SAlgoTransform (δ := δ) (Salt := Salt)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    Pr[ nargKSFailEvent relIn langOut |
        hyb_4 (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
          (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          oSpecImpl V maliciousProver d2sAlgoTransform >>= ksFactKernel E_std ]
      = Pr[ nargKSFailEvent relIn langOut |
          adaptiveNARGKnowledgeSoundnessExpWithCoins
            (init := srInitDIP (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec))
            (impl := (srImplLift (StmtIn := StmtIn) (Salt := Salt)
              (pSpec := pSpec) oSpecImpl).addLift (srChallengeQueryImpl'
                (Statement := StmtIn × Salt) (pSpec := pSpec)))
            d2sAuxImpl (d2sUnitSampleImpl (U := U))
            (Verifier.singleSaltFiatShamir (Salt := Salt) V)
            E_std
            (nargInducedProver maliciousProver d2sAlgoTransform) ] := by
  classical
  rw [adaptiveNARGKS_eq_coinNARGKSReadout E_std V oSpecImpl]
  unfold hyb_4 basicFiatShamirGameDist
  simp only [hybChallengeInit, srInitDIP]
  rw [hybChallengeImpl_eq_srAddLift]
  simp only [bind_assoc]
  refine probEvent_bind_congr' _ _ (fun s => ?_)
  change probEvent
      (StateT.run'
          (simulateQ (srHyb4Impl (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec)
            (U := U) oSpecImpl)
            (basicFiatShamirGame V (d2sAlgoTransform maliciousProver)).run) s >>=
        ksFactKernel E_std)
      (nargKSFailEvent relIn langOut) = _
  let acceptOutput :
      (StmtIn × FSSaltedProof pSpec Salt ×
        QueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) × Option StmtOut ×
        QueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)) →
          Option (BasicFiatShamirGameOutput (oSpec := oSpec) (StmtIn := StmtIn)
            (StmtOut := StmtOut) (pSpec := pSpec) (Salt := Salt)) :=
    fun ⟨x, π, trP, stmtOut?, trV⟩ => stmtOut?.map fun stmtOut =>
      (x, stmtOut, π,
        trP.map (fun e => (SourceTag.prover, e)) ++
          trV.map (fun e => (SourceTag.verifier, e)))
  have hGame :
      (basicFiatShamirGame V (d2sAlgoTransform maliciousProver)).run =
        acceptOutput <$> hyb4KSReadout V maliciousProver d2sAlgoTransform := by
    simpa only [acceptOutput] using
      (basicFiatShamirGame_run_eq_hyb4KSReadout V maliciousProver d2sAlgoTransform)
  have hGameRun := congrArg
    (fun c => StateT.run'
      (simulateQ (srHyb4Impl (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec)
        (U := U) oSpecImpl) c) s) hGame
  have hGameEvent := congrArg
    (fun head => probEvent (head >>= ksFactKernel E_std) (nargKSFailEvent relIn langOut)) hGameRun
  apply Eq.trans hGameEvent
  have hMap :
      StateT.run'
          (simulateQ (srHyb4Impl (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec)
            (U := U) oSpecImpl)
            (acceptOutput <$>
              hyb4KSReadout V maliciousProver d2sAlgoTransform)) s =
        acceptOutput <$> StateT.run'
          (simulateQ (srHyb4Impl (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec)
            (U := U) oSpecImpl)
            (hyb4KSReadout V maliciousProver d2sAlgoTransform)) s := by
    rw [simulateQ_map]
    exact StateT.run'_map' _ _ _
  have hMapEvent := congrArg
    (fun head => probEvent (head >>= ksFactKernel E_std) (nargKSFailEvent relIn langOut)) hMap
  apply Eq.trans hMapEvent
  simp only [bind_map_left]
  have hReadout := simulateQ_coinNARGKSReadout_eq_hyb4KSReadout
    V oSpecImpl maliciousProver d2sAlgoTransform
  have hRun := congrArg (fun c => StateT.run' c s) hReadout
  change StateT.run' _ s = StateT.run' _ s at hRun
  let rightKernel :
      (StmtIn × FSSaltedProof pSpec Salt ×
        QueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) × Option StmtOut ×
        QueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)) →
          ProbComp (StmtIn × Option WitIn × Option StmtOut) := fun a => do
    let witIn? ← simulateQ (d2sUnitSampleImpl (U := U))
      (E_std a.1 a.2.1 a.2.2.1 a.2.2.2.2).run
    pure (a.1, witIn?, a.2.2.2.1)
  have hHeadEvent := congrArg
    (fun head => probEvent (head >>= rightKernel) (nargKSFailEvent relIn langOut)) hRun
  apply Eq.trans ?_ hHeadEvent.symm
  refine probEvent_bind_congr' _ _ (fun a => ?_)
  obtain ⟨x, π, trP, stmtOut?, trV⟩ := a
  rcases stmtOut? with _ | stmtOut
  · dsimp [rightKernel, acceptOutput]
    unfold ksFactKernel
    dsimp only
    refine (probEvent_eq_zero fun y hy => ?_).trans
      (probEvent_eq_zero fun y hy => ?_).symm
    · simp only [support_pure, Set.mem_singleton_iff] at hy
      subst hy
      simp [nargKSFailEvent]
    · simp only [support_bind, support_pure, Set.mem_iUnion,
        Set.mem_singleton_iff] at hy
      obtain ⟨_, _, rfl⟩ := hy
      simp [nargKSFailEvent]
  · dsimp [rightKernel, acceptOutput]
    refine probEvent_congr' (fun _ _ => Iff.rfl) ?_
    unfold ksFactKernel
    dsimp only
    simp only [TaggedQueryLog.proverLog_tagAppend,
      TaggedQueryLog.verifierLog_tagAppend]

/-- **Construction 6.3 in CO25 Def-3.6 (NARG) shape** — the straightline extractor witnessing the
DSFS NARG's `adaptiveNARGKnowledgeSoundness`.  Wraps `dsfsStraightlineExtractor E_std` (the
`Extractor.Straightline` form) into the Def-3.6 extractor type: build the non-interactive transcript
from the proof `π` and thread the prover log `tr` and verifier log `tr_𝒱` through to
`dsfsStraightlineExtractor`'s two slots. -/
noncomputable def dsfsNargExtractor
    {T_H : Type} {T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (E_std : StmtIn → FSSaltedProof pSpec Salt →
      QueryLog (oSpec + srChallengeOracle (StmtIn × Salt) pSpec) →
      QueryLog (oSpec + srChallengeOracle (StmtIn × Salt) pSpec) →
        OptionT (OracleComp (Unit →ₒ U)) WitIn) :
    (stmtIn : StmtIn) → (π : DSSaltedProof (pSpec := pSpec) (U := U) δ) →
    (tr_P : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)) →
    (tr_V : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)) →
    OptionT (OracleComp (Unit →ₒ U)) WitIn :=
  -- Construction 6.3 in NARG shape: wrap `dsfsStraightlineExtractor` (which runs the REAL
  -- `D2STrace(tr ‖ tr_V)` over its `(Unit →ₒ U)` sampler slot, splits into prover/verifier logs by
  -- source tag, and feeds `E_std`).  `T_H/T_P` are passed explicitly (undetermined at the call).
  fun stmtIn proof tr_P tr_V =>
    dsfsStraightlineExtractor (T_H := T_H) (T_P := T_P) (stmtIn : StmtIn)
      (E_std := E_std)
      ((Fin.cons proof (fun i => i.elim0)) :
        FullTranscript ⟨!v[.P_to_V], !v[DSSaltedProof (pSpec := pSpec) (U := U) δ]⟩)
      tr_P tr_V

omit [VCVCompatible Salt] in
/-- **DSFS NARG-KS experiment = sponge KS game** (CO25 §6.2 game-equivalence). -/
theorem dsfsNargKSExp_eq_dsfsKSGame
    (E_std : StmtIn → FSSaltedProof pSpec Salt →
      QueryLog (oSpec + srChallengeOracle (StmtIn × Salt) pSpec) →
      QueryLog (oSpec + srChallengeOracle (StmtIn × Salt) pSpec) →
        OptionT (OracleComp (Unit →ₒ U)) WitIn)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (relIn : Set (StmtIn × WitIn)) (langOut : Set StmtOut)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    Pr[ nargKSFailEvent relIn langOut |
        adaptiveNARGKnowledgeSoundnessExp hyb0Init (hyb0Impl oSpecImpl) (d2sUnitSampleImpl (U := U))
          (Verifier.dsfsNargNIV δ V)
          (dsfsNargExtractor (T_H := T_H) (T_P := T_P) E_std)
          maliciousProver ]
      = Pr[ nargKSFailEvent relIn langOut |
          dsfsKSGameDist
            (dsfsStraightlineExtractor (T_H := T_H) (T_P := T_P) E_std)
            oSpecImpl V maliciousProver ] := by
  classical
  -- Both sides produce the Def-3.6 triple directly (no read-out re-encoding); the failure
  -- probability follows from the distribution equality `experiment = game`.
  have hdist :
      adaptiveNARGKnowledgeSoundnessExp hyb0Init (hyb0Impl oSpecImpl) (d2sUnitSampleImpl (U := U))
          (Verifier.dsfsNargNIV δ V)
          (dsfsNargExtractor (T_H := T_H) (T_P := T_P) E_std)
          maliciousProver
        = dsfsKSGameDist
            (dsfsStraightlineExtractor (T_H := T_H) (T_P := T_P) E_std)
            oSpecImpl V maliciousProver := by
    -- Post-decoupling BOTH sides split identically (prover/verifier under `hyb0Impl`, then
    -- `E_std` separately under `d2sUnitSampleImpl`). `dsfsNargVerify`/`dsfsNargExtractor` unfold
    -- to the game's `runForwardVerifierWide`/`dsfsStraightlineExtractor` definitionally.
    unfold adaptiveNARGKnowledgeSoundnessExp dsfsKSGameDist dsfsNargExtractor
    -- `Verifier.dsfsNargNIV`'s verify is defeq to `dsfsNargVerify` (`Fin.cons … 0 = π`); rewrite to
    -- the bare-function form, then unfold it to the game's `runForwardVerifierWide`.
    simp only [dsfsNargNIV_verify]
    unfold dsfsNargVerify
    simp [OptionT.run_mk, simulateQ_map, map_bind, bind_map_left,
      bind_assoc]
  rw [hdist]

/-- Internal lifting lemma: a query-bounded basic-FS straightline-KS result yields the
corresponding DSFS straightline-KS result, with Lemma 5.1's additive error. -/
private theorem dsfsStraightlineKS_of_basicFS
    [∀ i, DecidableEq (pSpec.Challenge i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    [DecidableEq ι]
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (relIn : Set (StmtIn × WitIn)) (langOut : Set StmtOut)
    (tₕ tₚ tₚᵢ : ℕ)
    (hKeyLemma : KeyLemmaSecurityWitness (δ := δ) (Salt := Salt) (oSpec := oSpec)
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
      (T_H := T_H) (T_P := T_P) oSpecImpl V tₕ tₚ tₚᵢ)
    (ε_sr : ENNReal)
    (hBasicFS : Verifier.adaptiveNARGKnowledgeSoundnessWithCoins (WitIn := WitIn)
        (init := srInitDIP (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec))
        (impl := (srImplLift (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec) oSpecImpl).addLift
          srChallengeQueryImpl')
        d2sAuxImpl (d2sUnitSampleImpl (U := U))
        (verifier := Verifier.singleSaltFiatShamir (Salt := Salt) V)
        relIn langOut
        (bound := basicFSCompiledKSBound
          (ProverTransform.d2sAlgo (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P)
            (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) tₕ tₚ tₚᵢ)
        ε_sr) :
    -- CO25 **Def 3.6** (`adaptiveNARGKnowledgeSoundness`) at the DSFS NARG: every
    -- query-bounded proof-only DSFS attacker is quantified directly.
    (Verifier.dsfsNargNIV δ V).adaptiveNARGKnowledgeSoundness (WitIn := WitIn)
      (init := hyb0Init) (impl := hyb0Impl oSpecImpl)
      (auxImplE := d2sUnitSampleImpl (U := U))
      (relIn := relIn) (langOut := langOut)
      (bound := fun maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ =>
        IsLemma5_1QueryBound maliciousProver tₕ tₚ tₚᵢ)
      (error := ε_sr + ENNReal.ofReal
        (ηStar U tₕ tₚ tₚᵢ (L_totalRateBlocks δ pSpec) codec.decodingBias)) := by
  obtain ⟨E_std, hE_std⟩ := hBasicFS
  let d2sAlgoTransform := ProverTransform.d2sAlgo
    (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P)
    (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
  exact (by
    -- Extractor witness: Construction 6.3 in NARG shape (`dsfsNargExtractor`) over `E_std`.
    use dsfsNargExtractor (T_H := T_H) (T_P := T_P) E_std
    intro maliciousProver hQB
    -- Step 0: the DSFS NARG-KS experiment (Def 3.6) IS the sponge KS game `dsfsKSGameDist` on the
    -- extraction-failure marginal (`dsfsNargKSExp_eq_dsfsKSGame`); rewrite to the sponge game so
    -- the §6.2 hybrid calc applies verbatim.
    rw [dsfsNargKSExp_eq_dsfsKSGame E_std V oSpecImpl relIn langOut
        maliciousProver]
    -- **Seam #1 (Key Lemma 5.1, concrete-transform form).** The explicit Section 5 hypothesis
    -- carries the same `d2sTraceSalted` / `ProverTransform.d2sAlgo` maps used by Construction 6.3.
    have hTv := (hKeyLemma.valid maliciousProver hQB).1
    -- **Seam #2 (the §6.2 game-match)** — the shared extractor kernel `k := ksFactKernel E_std`
    -- and the two equalities `hL1` (Step 1: unfold Construction 6.3) ∧ `hL3` (Step 3: Hyb₄ =
    -- NARG-KS game, KS twin of `hyb4_eq_coinNARGgame`), consumed directly by the calc below.
    let k := ksFactKernel (StmtOut := StmtOut) (Salt := Salt) E_std
    have hL1 := dsfs_knowledge_soundness_failure_eq_hyb0
      (T_H := T_H) (T_P := T_P) E_std V oSpecImpl relIn langOut maliciousProver
    have hL3 := hyb4_knowledge_soundness_failure_eq_single_salt
      E_std V oSpecImpl relIn langOut maliciousProver d2sAlgoTransform
    let H0 := hyb_0 (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
        (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
        oSpecImpl V maliciousProver
        (d2sTraceSalted (T_H := T_H) (T_P := T_P) (δ := δ) (Salt := Salt)
          (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    let H4 := hyb_4 (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
        (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
        oSpecImpl V maliciousProver d2sAlgoTransform
    -- `set` folds `hyb_0`/`hyb_4` in the Key-Lemma hypothesis to `H0`/`H4`, so
    -- `hTv : tvDist H0 H4 ≤ η★`
    -- is the Key-Lemma bound directly.  The kernel `k` is the SAME on both hybrids (Def 3.14:
    -- `E_std` needs no carried `f`), so `tvDist_bind_right_le` transports it through `>>= k`.
    -- All `≤` bridges below are **proven**: Step 1 (`hL1`), B3, data-processing
    -- (`tvDist_bind_right_le`), the Key-Lemma bound (`hTv`), Step 3 (`hL3`), Step 4
    -- (`hE_std`).
    calc Pr[ nargKSFailEvent relIn langOut |
            dsfsKSGameDist
              (dsfsStraightlineExtractor (T_H := T_H) (T_P := T_P) E_std)
              oSpecImpl V maliciousProver ]
        = Pr[ nargKSFailEvent relIn langOut | H0 >>= k ] := by
          exact hL1
      _ ≤ Pr[ nargKSFailEvent relIn langOut | H4 >>= k ]
            + ENNReal.ofReal (tvDist (H0 >>= k) (H4 >>= k)) := by
          exact probEvent_le_probEvent_add_ofReal_tvDist (H0 >>= k)
            (H4 >>= k) (nargKSFailEvent relIn langOut)
      _ ≤ Pr[ nargKSFailEvent relIn langOut | H4 >>= k ] + ENNReal.ofReal (tvDist H0 H4) := by
          exact add_le_add le_rfl (ENNReal.ofReal_le_ofReal (tvDist_bind_right_le k H0 H4))
      _ ≤ Pr[ nargKSFailEvent relIn langOut | H4 >>= k ]
            + ENNReal.ofReal
              (ηStar U tₕ tₚ tₚᵢ (L_totalRateBlocks δ pSpec) codec.decodingBias) := by
          refine add_le_add le_rfl (ENNReal.ofReal_le_ofReal ?_)
          -- `let H0`/`let H4` do not rewrite hypotheses, so `hTv` keeps its args `hyb_0 …
          -- d2sTraceSalted` / `hyb_4 … d2sAlgo`.  The
          -- goal's `tvDist H0 H4` unfolds to `hyb_0 … d2sTraceSalted` /
          -- `hyb_4 … d2sAlgoTransform` — a *different syntactic term* in slot 2, though
          -- `d2sAlgoTransform := d2sAlgo`
          -- definitionally.  A plain `exact hTv` would force `isDefEq` to reconcile `H4 ≡ hyb_4 …
          -- d2sAlgo` by whnf-ing the enormous `hyb_4` game body → heartbeat blow-up.  `convert`
          -- descends by congruence instead, keeping `hyb_4` rigid on the application spine and
          -- discharging only the tiny `d2sAlgoTransform`-vs-`d2sAlgo` leaf.
          convert hTv
      -- Step 3 (`rw [hL3]`: Hyb₄ = NARG-KS game) ∘ Step 4 (`hE_std`: Theorem 3.19 on `𝒫̃_std`).
      -- `refine add_le_add ?_ (le_refl _)` takes the event from the *goal*, then `exact` discharges
      -- the bound by full defeq (unfolding the NARG-KS-experiment event `match` aux-defs).
      _ ≤ ε_sr + ENNReal.ofReal
              (ηStar U tₕ tₚ tₚᵢ (L_totalRateBlocks δ pSpec) codec.decodingBias) := by
          rw [hL3]
          refine add_le_add ?_ (le_refl _)
          exact hE_std (nargInducedProver maliciousProver d2sAlgoTransform)
            ⟨maliciousProver, hQB, rfl⟩
  )

/-- **Theorem 6.2** — straightline knowledge soundness of DSFS, with Lemma 5.1's concrete
challenge-query guarantee passed through the single-salt reduction.  Its public error is the
salt-aware Section-6 coarsening `ηStarTotal`, while the reduction itself uses the exact
`ηStar` bound from Lemma 5.1. -/
theorem duplex_sponge_fiat_shamir_straightline_knowledge_soundness
    [∀ i, DecidableEq (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Message i)]
    [DecidableEq ι]
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (V : Verifier oSpec StmtIn StmtOut pSpec) (oSpecImpl : QueryImpl oSpec ProbComp)
    (relIn : Set (StmtIn × WitIn)) (langOut : Set StmtOut)
    (tₕ tₚ tₚᵢ : ℕ)
    (t : ℕ) (hTotal : tₕ + tₚ + tₚᵢ ≤ t)
    (ε_sr : ENNReal)
    (hKeyLemma : KeyLemmaSecurityWitness (δ := δ) (Salt := Salt) (oSpec := oSpec)
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
      (T_H := T_H) (T_P := T_P) oSpecImpl V tₕ tₚ tₚᵢ)
    (h_IP_SR_KS : Verifier.StateRestoration.knowledgeSoundnessWithCoins
        (init := srInitDIP) (impl := srImplLift oSpecImpl)
        ((Unit →ₒ U) + unifSpec) d2sAuxImpl
        (relInSalted relIn) (unitOutputRelation langOut) (saltedIPVerifier (Salt := Salt) V)
        (fun prover => IsSaltedFSChallengeQueryBound prover (θStar tₕ tₚ tₚᵢ)) ε_sr) :
    (Verifier.dsfsNargNIV (U := U) δ V).adaptiveNARGKnowledgeSoundness
      (WitIn := WitIn)
      (init := hyb0Init) (impl := hyb0Impl oSpecImpl)
      (auxImplE := d2sUnitSampleImpl (U := U))
      (relIn := relIn) (langOut := langOut)
      (bound := fun maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ =>
        IsLemma5_1QueryBound maliciousProver tₕ tₚ tₚᵢ)
      (error := ε_sr + ENNReal.ofReal
        (ηStarTotal U t (L_totalRateBlocks δ pSpec) codec.decodingBias)) := by
  obtain ⟨extractor, hExact⟩ :=
    dsfsStraightlineKS_of_basicFS (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
    (StmtOut := StmtOut) (WitIn := WitIn) (pSpec := pSpec) (U := U)
    (T_H := T_H) (T_P := T_P) V oSpecImpl relIn langOut tₕ tₚ tₚᵢ hKeyLemma ε_sr
    (hBasicFS := basicFS_straightlineKS_withCompiledBound
        (d2sAlgoTransform := ProverTransform.d2sAlgo
          (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P)
        (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
        V oSpecImpl relIn langOut tₕ tₚ tₚᵢ
        (hD2SBound := by
          intro maliciousP pBounded
          have h_res := (hKeyLemma.valid maliciousP pBounded).2
          convert h_res
        )
        ε_sr h_IP_SR_KS
    )
  use extractor
  intro P hBound
  exact (hExact P hBound).trans <| add_le_add le_rfl (ENNReal.ofReal_le_ofReal
    (etaStar_le_etaStarTotal U tₕ tₚ tₚᵢ (L_totalRateBlocks δ pSpec)
      t codec.decodingBias hTotal))
end

end DuplexSpongeFS
