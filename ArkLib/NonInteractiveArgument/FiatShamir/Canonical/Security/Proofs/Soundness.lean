/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Michele Orrù, Quang Dao, Yuxi Zheng
-/
module

public import ArkLib.NonInteractiveArgument.FiatShamir.Canonical.Construction
public import ArkLib.InteractiveProof.StateRestorationSoundness
public import ArkLib.NonInteractiveArgument.Serialization.Security
public import ArkLib.NonInteractiveArgument.Legacy
public import ArkLib.OracleReduction.ProtocolSpec.DeriveTranscript
public import VCVio.OracleComp.Coercions.SubSpec.Routing

/-!
# Proofs of canonical Fiat–Shamir soundness and knowledge soundness

The proofs repackage the prover's output and reconstruct the verifier's transcript and log
under the same oracle realization. The knowledge-soundness proofs transport a supplied
state-restoration extractor. The last section specializes the reductions to ordinary
public-coin protocols without an ambient oracle.

The public theorems are in `Canonical/Security/Soundness.lean`.

## References

* [Chiesa, A. and Orrù, M., *A Fiat–Shamir Transformation From Duplex Sponges*][CO25]
-/

@[expose] public section

section StateRestorationTransfer

open ProtocolSpec OracleComp OracleSpec OracleReduction

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]

namespace CanonicalFS

variable [∀ i, SampleableType (pSpec.Challenge i)]
  [DecidableEq StmtIn]
  [∀ i, DecidableEq (pSpec.Message i)]

/-- Induce an SR prover from an adaptive FS prover:
`(𝕩, (τ, α)) ← P; return ((𝕩, τ), α)`.
The statement `𝕩`, chosen salt `τ`, and full prover-message tuple `α` are repackaged without
adding queries. The FS and single-salt SR query types coincide, so the original oracle calls,
including private sampling through `privateSpec`, are retained. -/
def srInducedProver {Salt : Type} [VCVCompatible Salt]
    {κ : Type} {privateSpec : OracleSpec κ}
    (P : OracleComp ((oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec) + privateSpec)
      (StmtIn × FSSaltedNARGString pSpec Salt)) :
    Prover.StateRestoration.Soundness oSpec privateSpec StmtIn pSpec (Salt := Salt) := do
  let ⟨x, nargString⟩ ← P
  return ⟨(x, nargString.1), nargString.2⟩

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)] [DecidableEq StmtIn]
  [∀ i, DecidableEq (pSpec.Message i)] in
/-- The induced SR prover is `P` followed by a pure repackaging of its output — in particular it
makes *exactly* the queries `P` makes. -/
lemma srInducedProver_eq_map {Salt : Type} [VCVCompatible Salt]
    {κ : Type} {privateSpec : OracleSpec κ}
    (P : OracleComp ((oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec) + privateSpec)
      (StmtIn × FSSaltedNARGString pSpec Salt)) :
    srInducedProver (Salt := Salt) P
      = (fun p => ((p.1, p.2.1), p.2.2)) <$> P := by
  rw [map_eq_bind_pure_comp]
  exact bind_congr fun p => rfl

/-- Induce an SR knowledge-soundness prover from an adaptive FS prover:
`(𝕩, (τ, α)) ← P; return ((𝕩, τ), α, ())`.
The unit value `()` supplies the generic SR interface's output witness. As with
`srInducedProver`, the oracle calls and their order are unchanged. -/
def srInducedProverKS {Salt : Type} [VCVCompatible Salt]
    {κ : Type} {privateSpec : OracleSpec κ}
    (P : OracleComp ((oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec) + privateSpec)
      (StmtIn × FSSaltedNARGString pSpec Salt)) :
    Prover.StateRestoration.KnowledgeSoundness
      oSpec privateSpec StmtIn Unit pSpec (Salt := Salt) := do
  let ⟨x, nargString⟩ ← P
  return ⟨(x, nargString.1), nargString.2, ()⟩

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)] [DecidableEq StmtIn]
  [∀ i, DecidableEq (pSpec.Message i)] in
/-- The induced SR-KS prover is `P` followed by a pure repackaging of its output — in particular
it makes *exactly* the queries `P` makes. -/
lemma srInducedProverKS_eq_map {Salt : Type} [VCVCompatible Salt]
    {κ : Type} {privateSpec : OracleSpec κ}
    (P : OracleComp ((oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec) + privateSpec)
      (StmtIn × FSSaltedNARGString pSpec Salt)) :
    srInducedProverKS (Salt := Salt) P
      = (fun p => ((p.1, p.2.1), p.2.2, ())) <$> P := by
  rw [map_eq_bind_pure_comp]
  exact bind_congr fun p => rfl

/-- Delegate FS extraction to the non-rewinding SR extractor `E`. Given `π = (τ, α)`, compute
`ρ := Messages.challengesOfLog (𝕩, τ) α tr_V.snd` and assemble the transcript `T = (α, ρ)`
in protocol order, then return `E 𝕩 τ () T tr_P tr_V.fst`.

The log `tr_V.snd` contains verifier queries for FS messages, while `tr_V.fst` contains its
ambient queries to `oSpec`. The prover log `tr_P` contains both kinds of query and is passed
intact. The value `()` supplies the SR output witness. Subsequent extractor calls use
`oSpec + unifSpec`.

Reconstruction rescans `tr_V.snd` for each verifier-message position. With `k` such positions
and `N` log entries, this uses up to `O(k * N)` entry inspections, plus transcript assembly
and one invocation of `E`. -/
def fsSRDelegatingExtractor {Salt : Type} [VCVCompatible Salt]
    (E : Extractor.StateRestoration oSpec StmtIn WitIn Unit pSpec (Salt := Salt))
    (x : StmtIn) (π : FSSaltedNARGString pSpec Salt)
    (tr_P tr_V : QueryLog (oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec)) :
    OptionT (OracleComp (oSpec + unifSpec)) WitIn :=
  E x π.1 ()
    (FullTranscript.ofMessagesChallenges π.2
      (Messages.challengesOfLog (x, π.1) π.2 tr_V.snd))
    tr_P tr_V.fst

/-- Embed the delegated base-oracle computation into the NARG extractor interface.
The verifier message and helper slots are available in the ambient type but are not used here. -/
def fsSRDelegatingNARGExtractor {Salt : Type} [VCVCompatible Salt]
    (E : Extractor.StateRestoration oSpec StmtIn WitIn Unit pSpec (Salt := Salt))
    (x : StmtIn) (π : FSSaltedNARGString pSpec Salt)
    (tr_P tr_V : QueryLog (oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec)) :
    OptionT (OracleComp ((oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec) + unifSpec))
      WitIn :=
  OptionT.mk (liftComp (fsSRDelegatingExtractor E x π tr_P tr_V).run
    ((oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec) + unifSpec))

omit [VCVCompatible StmtIn] [∀ i, SampleableType (pSpec.Challenge i)] in
/-- Canonical verifier logs reconstruct the SR inputs exactly. This is equality of entire
oracle computations, not just of pure witness values, so subsequent extractor queries are
preserved under any common interpretation. -/
lemma fsSRDelegatingExtractor_canonical {Salt : Type} [VCVCompatible Salt]
    (E : Extractor.StateRestoration oSpec StmtIn WitIn Unit pSpec (Salt := Salt))
    (x : StmtIn) (π : FSSaltedNARGString pSpec Salt)
    (tr_P : QueryLog (oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec))
    (tr_V : QueryLog oSpec)
    (cs : pSpec.ChallengesUpTo ⟨n, Nat.lt_succ_self n⟩) :
    fsSRDelegatingExtractor E x π tr_P
      (QueryLog.inr (canonChalLog (x, π.1) π.2 ⟨n, Nat.lt_succ_self n⟩ cs)
        ++ QueryLog.inl tr_V) =
      E x π.1 ()
        (FullTranscript.ofMessagesChallenges π.2
          (fun r => cs ⟨⟨r.1.1, r.1.2⟩, r.2⟩)) tr_P tr_V := by
  unfold fsSRDelegatingExtractor
  rw [QueryLog.snd_append, QueryLog.snd_inr, QueryLog.snd_inl, List.append_nil]
  rw [QueryLog.fst_append, QueryLog.fst_inr, QueryLog.fst_inl, List.nil_append]
  rw [Messages.challengesOfLog_canonChalLog]

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)] [DecidableEq StmtIn]
  [∀ i, DecidableEq (pSpec.Message i)] in
/-- The FS verifier reconstructs the same transcript as the SR game, then runs the IP verifier.
This equality retains all queries and their order, including queries made by the IP verifier. -/
private lemma fsSaltedVerify_eq_deriveTranscriptSR {Salt : Type} [VCVCompatible Salt]
    (V : Verifier oSpec StmtIn StmtOut pSpec) (x : StmtIn) (π : FSSaltedNARGString pSpec Salt) :
    (fsSaltedVerify V x π).run =
      (Messages.deriveTranscriptSR (oSpec := oSpec) (x, π.1) π.2 : OracleComp _ _) >>=
        fun t => liftComp (V.verify x t).run
          (oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec) := by
  dsimp only [fsSaltedVerify, Verifier.verifyFiatShamir,
    ProtocolSpec.Messages.deriveTranscriptFS]
  simp only [OptionT.liftM_def, OptionT.run_bind, Option.elimM, OptionT.run_lift, bind_assoc,
    pure_bind, Option.elim_some]
  refine bind_congr fun t => ?_
  rw [show (liftM (V.verify x t).run :
      OptionT (OracleComp (oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec))
        (Option StmtOut)) =
    OptionT.lift (liftM (V.verify x t).run :
      OracleComp (oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec) (Option StmtOut)) from
    (OracleComp.monadLift_liftM_OptionT _).symm]
  simp only [OptionT.run_lift, bind_assoc, pure_bind, Option.elim_some,
    OracleComp.liftComp_eq_liftM]
  trans (liftM (V.verify x t).run : OracleComp _ _) >>= pure
  · apply bind_congr
    intro result
    cases result <;> rfl
  · exact bind_pure _

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)] [DecidableEq StmtIn]
  [∀ i, DecidableEq (pSpec.Message i)] in
/-- Canonical form of the logged single-salt FS verifier run: query the verifier message tuple, run
the (logged) base verifier on the assembled transcript, and read out the decision together with
the canonical verifier message log followed by the (left-embedded) base-verifier log. -/
private lemma logged_fsSaltedVerify {Salt : Type} [VCVCompatible Salt]
    (V : Verifier oSpec StmtIn StmtOut pSpec) (x : StmtIn) (π : FSSaltedNARGString pSpec Salt) :
    (simulateQ loggingOracle ((fsSaltedVerify (Salt := Salt) V x π).run)).run
    = chalTupleUpTo (oSpec := oSpec) (x, π.1) π.2 ⟨n, Nat.lt_succ_self n⟩ >>= fun cs =>
        (liftComp ((simulateQ loggingOracle
            ((V.verify x (Transcript.ofMessagesChallenges
              (π.2.take ⟨n, Nat.lt_succ_self n⟩) cs)).run)).run)
          (oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec)) >>= fun q =>
          pure (q.1, QueryLog.inr (canonChalLog (x, π.1) π.2 ⟨n, Nat.lt_succ_self n⟩ cs)
            ++ QueryLog.inl q.2) := by
  rw [fsSaltedVerify_eq_deriveTranscriptSR]
  refine Eq.trans (OracleComp.withQueryLog_bind _ _) ?_
  rw [show (Messages.deriveTranscriptSR (oSpec := oSpec) (x, π.1) π.2 :
      OracleComp (oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec) _).withQueryLog
    = chalTupleUpTo (oSpec := oSpec) (x, π.1) π.2 ⟨n, Nat.lt_succ_self n⟩ >>= fun cs =>
        pure (Transcript.ofMessagesChallenges (π.2.take ⟨n, Nat.lt_succ_self n⟩) cs,
          QueryLog.inr (canonChalLog (x, π.1) π.2 ⟨n, Nat.lt_succ_self n⟩ cs))
    from logged_deriveTranscriptSRAux_eq (x, π.1) π.2 ⟨n, Nat.lt_succ_self n⟩]
  refine Eq.trans (bind_assoc _ _ _) ?_
  refine bind_congr fun cs => ?_
  change ((Prod.map id
      fun l => (canonChalLog (x, π.1) π.2 ⟨n, Nat.lt_succ_self n⟩ cs).inr ++ l) <$>
    ((V.verify x (Transcript.ofMessagesChallenges (Messages.take ⟨n, Nat.lt_succ_self n⟩ π.2)
      cs)).run.liftComp (oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec)).withQueryLog) = _
  rw [show ((liftComp ((V.verify x (Transcript.ofMessagesChallenges
        (π.2.take ⟨n, Nat.lt_succ_self n⟩) cs)).run)
        (oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec))).withQueryLog
    = (liftComp ((simulateQ loggingOracle ((V.verify x (Transcript.ofMessagesChallenges
          (π.2.take ⟨n, Nat.lt_succ_self n⟩) cs)).run)).run)
        (oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec)) >>= fun p =>
        pure (p.1, QueryLog.inl p.2)
    from withQueryLog_liftComp_left_of_query (fun t => rfl) _]
  refine Eq.trans (map_bind _ _ _) ?_
  refine bind_congr fun q => ?_
  refine Eq.trans (map_pure _ _) ?_
  rfl

omit [VCVCompatible StmtIn] [∀ i, SampleableType (pSpec.Challenge i)] in
/-- **FS↔SR KS crosswalk (the core of [CO25, Theorem 3.19])**: with the Construction-3.19
delegating extractor, the coin-bearing NARG KS experiment for the single-salt FS
verifier is the original-statement marginal of the coin-bearing SR-KS experiment for the induced
SR prover — with the *same* SR extractor `E` receiving the same transcript and the same
(projected) query logs. -/
private lemma fsKSExtractionSetup_eq_map_srKSExtractionSetup {Salt : Type} [VCVCompatible Salt]
    {κ : Type} {privateSpec : OracleSpec κ}
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (E : Extractor.StateRestoration oSpec StmtIn WitIn Unit pSpec (Salt := Salt))
    (P : OracleComp ((oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec) + privateSpec)
      (StmtIn × FSSaltedNARGString pSpec Salt)) :
    (do
      let ⟨⟨x, π⟩, tr⟩ ← (simulateQ loggingOracle P).run
      (fun a => (x, fsSRDelegatingExtractor E x π tr.fst a.2, a.1)) <$>
        liftComp (simulateQ loggingOracle (fsSaltedVerify V x π).run).run
          ((oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec) + privateSpec)
          (h := instMonadLiftTOfMonadLift
            (OracleQuery (oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec))
            (OracleQuery (oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec))
            (OracleQuery ((oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec) + privateSpec))))
    = (fun out : (StmtIn × Salt) × OptionT (OracleComp (oSpec + unifSpec)) WitIn ×
        Option StmtOut × Unit =>
        (out.1.1, out.2.1, out.2.2.1)) <$>
      (do
        let ⟨⟨stmtIn, messages, _unit⟩, tr⟩ ←
          (simulateQ loggingOracle (srInducedProverKS P)).run
        let transcript ← liftComp (messages.deriveTranscriptSR (oSpec := oSpec) stmtIn)
          ((oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec) + privateSpec)
        let ⟨stmtOut, tr_V⟩ ←
          liftComp (simulateQ loggingOracle
            (V.run stmtIn.1 transcript).run).run _
        return (stmtIn, E stmtIn.1 stmtIn.2 () transcript tr.fst tr_V,
          stmtOut, ())) := by
  classical
  -- Align the prover stage: the induced SR prover is `P` with a pure repackaging, so its logged
  -- run is the logged run of `P` with the same log.
  simp only [srInducedProverKS_eq_map, simulateQ_map, WriterT.run_map,
    bind_map_left, map_bind]
  refine bind_congr fun p => ?_
  -- Verify stage: canonical form of the logged FS verifier, and the explicit form of the SR
  -- transcript derivation.
  rw [logged_fsSaltedVerify]
  rw [show (Messages.deriveTranscriptSR (oSpec := oSpec) (p.1.1, p.1.2.1) p.1.2.2 :
      OracleComp _ _)
    = chalTupleUpTo (oSpec := oSpec) (pSpec := pSpec) (p.1.1, p.1.2.1) p.1.2.2
        ⟨n, Nat.lt_succ_self n⟩ >>= fun cs =>
        pure (Transcript.ofMessagesChallenges (p.1.2.2.take ⟨n, Nat.lt_succ_self n⟩) cs)
    from Messages.deriveTranscriptSR_eq_chalTupleUpTo _ _]
  -- Push the lifts through both sides and align stage by stage.
  simp only [liftComp_bind, liftComp_pure, map_bind, map_pure]
  conv_rhs =>
    enter [1]
    erw [liftComp_bind (h := instMonadLiftTOfMonadLift
      (OracleQuery (oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec))
      (OracleQuery (oSpec + (fsVerifierMessageOracle (StmtIn × Salt) pSpec + privateSpec)))
      (OracleQuery (oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec + privateSpec)))]
  simp only [bind_assoc]
  rw [liftComp_inst_irrel
    (i₁ := instMonadLiftTOfMonadLift
      (OracleQuery (oSpec + srVerifierMessageOracle (StmtIn × Salt) pSpec))
      (OracleQuery (oSpec + srVerifierMessageOracle (StmtIn × Salt) pSpec))
      (OracleQuery (oSpec + srVerifierMessageOracle (StmtIn × Salt) pSpec + privateSpec)))
    (i₂ := instMonadLiftTOfMonadLift
      (OracleQuery (oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec))
      (OracleQuery (oSpec + (fsVerifierMessageOracle (StmtIn × Salt) pSpec + privateSpec)))
      (OracleQuery (oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec + privateSpec)))
    (fun t => by rcases t with t | t <;> rfl)
    (chalTupleUpTo (oSpec := oSpec) (p.1.1, p.1.2.1) p.1.2.2 ⟨n, Nat.lt_succ_self n⟩)]
  refine bind_congr fun cs => ?_
  refine OracleComp.bind_congr' ?_ fun q => ?_
  · refine liftComp_liftComp ?_ _
    intro t
    rfl
  · -- The delegated extractor receives the reconstructed transcript and the
    -- projected logs, which coincide with the SR experiment's transcript and logs.
    refine congrArg pure ?_
    refine congrArg (fun w => (p.1.1, w, q.1)) ?_
    rw [fsSRDelegatingExtractor_canonical]
    rfl

omit [VCVCompatible StmtIn] in
/-- Delegating extraction preserves the SR failure probability, including the extractor's
private sampling and its ambient queries in the final verifier state. -/
private lemma fsKSShared_failure_eq {Salt : Type} [VCVCompatible Salt]
    {κ : Type} {privateSpec : OracleSpec κ} (privateImpl : QueryImpl privateSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (E : Extractor.StateRestoration oSpec StmtIn WitIn Unit pSpec (Salt := Salt))
    (fsInit : ProbComp (QueryImpl (srVerifierMessageOracle (StmtIn × Salt) pSpec) Id))
    (fsImpl : QueryImpl oSpec
      (StateT (QueryImpl (srVerifierMessageOracle (StmtIn × Salt) pSpec) Id) ProbComp))
    (relIn : Set (StmtIn × WitIn)) (langOut : Set StmtOut)
    (P : OracleComp ((oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec) + privateSpec)
      (StmtIn × FSSaltedNARGString pSpec Salt)) :
    Pr{let out ← adaptiveNARGKnowledgeSoundnessExp fsInit
          (fsImpl.addLift srChallengeQueryImpl') privateImpl
          ((fsImpl.addLift (srChallengeQueryImpl'
          (Statement := StmtIn × Salt) (pSpec := pSpec)) : QueryImpl _
            (StateT (QueryImpl (srVerifierMessageOracle (StmtIn × Salt) pSpec) Id)
              ProbComp)).addLift
          (QueryImpl.id' unifSpec))
          (Verifier.compileFiatShamir (Salt := Salt) V)
          (fsSRDelegatingNARGExtractor E) P}[nargKSFailEvent relIn langOut out] =
      Verifier.StateRestoration.knowledgeSoundnessFailureProb (Salt := Salt)
        fsInit fsImpl privateImpl E
        relIn {yu : StmtOut × Unit | yu.1 ∈ langOut}
        V (srInducedProverKS P) := by
  let publicImpl : QueryImpl (oSpec + srVerifierMessageOracle (StmtIn × Salt) pSpec)
      (StateT (QueryImpl (srVerifierMessageOracle (StmtIn × Salt) pSpec) Id) ProbComp) :=
    fsImpl.addLift (srChallengeQueryImpl' (Statement := StmtIn × Salt) (pSpec := pSpec))
  have hbase : (publicImpl.addLift (QueryImpl.id' unifSpec) : QueryImpl _
      (StateT (QueryImpl (srVerifierMessageOracle (StmtIn × Salt) pSpec) Id) ProbComp)) ∘ₛ
      (fun q => liftM (OracleSpec.query q) : QueryImpl (oSpec + unifSpec)
        (OracleComp ((oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec) + unifSpec))) =
      fsImpl.addLift (QueryImpl.id' unifSpec) := by
    funext q
    cases q with
    | inl q =>
      change simulateQ _ (liftM
        (((oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec) + unifSpec).query
          (.inl (.inl q)))) = _
      rw [simulateQ_spec_query]
      rfl
    | inr q =>
      change simulateQ _ (liftM
        (((oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec) + unifSpec).query
          (.inr q))) = _
      rw [simulateQ_spec_query]
      rfl
  dsimp only [publicImpl] at hbase
  have h := congrArg (fun computation =>
    StateT.run' (σ := QueryImpl (srVerifierMessageOracle (StmtIn × Salt) pSpec) Id)
      (m := ProbComp) (do
      let out ← simulateQ (publicImpl.addLift privateImpl) computation
      let w ← simulateQ (fsImpl.addLift (QueryImpl.id' unifSpec)) out.2.1.run
      pure (out.1, w, out.2.2))) (fsKSExtractionSetup_eq_map_srKSExtractionSetup V E P)
  have h' := congrArg (fun computation =>
    Pr{let out ← do computation (← fsInit)}[nargKSFailEvent relIn langOut out]) h
  simp only [adaptiveNARGKnowledgeSoundnessExp_eq,
    Verifier.StateRestoration.knowledgeSoundnessFailureProb_eq]
  unfold fsSRDelegatingNARGExtractor Verifier.StateRestoration.knowledgeSoundnessProverVerifierExp
  simp only [simulateQ_bind, simulateQ_pure, simulateQ_map, bind_map_left,
    OptionT.run_mk, liftComp_def, ← QueryImpl.simulateQ_compose, hbase,
    bind_assoc, pure_bind, runVerifierWithLog, withQueryLog] at h' ⊢
  convert h' using 1
  · apply congrArg prEvent
    simp only [map_bind, publicImpl, fsSaltedVerify]
    rfl
  · apply congrArg prEvent
    simp only [map_bind, map_pure, StateT.run'_bind', StateT.run'_pure']
    refine bind_congr (m := ProbComp) fun s => ?_
    refine bind_congr fun p => ?_
    refine bind_congr fun tr => ?_
    refine bind_congr fun v => ?_
    cases p.1.1.2.2
    refine bind_congr fun w => ?_
    cases w.1 <;> cases v.1.1 <;> rfl

omit [VCVCompatible StmtIn] in
/-- Transport a supplied SR extractor, without choosing it after the query budget.
The conclusion uses the NARG extractor interface documented above. Repackaging preserves all
queries, and the selector implication transfers the same `IsQueryBoundP` budget.
Adapted from the straightline case of **[snarg-book, Theorem 14.4.1]**. -/
theorem _root_.CanonicalFS.SoundnessProofs.transferFixedExtractor
    {Salt : Type} [VCVCompatible Salt]
    {κ : Type} (privateSpec : OracleSpec κ) (privateImpl : QueryImpl privateSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (relIn : Set (StmtIn × WitIn)) (langOut : Set StmtOut)
    (fsInit : ProbComp (QueryImpl (srVerifierMessageOracle (StmtIn × Salt) pSpec) Id))
    (fsImpl : QueryImpl oSpec
      (StateT (QueryImpl (srVerifierMessageOracle (StmtIn × Salt) pSpec) Id) ProbComp))
    (E : Extractor.StateRestoration oSpec StmtIn WitIn Unit pSpec (Salt := Salt))
    (queryBoundSelector srQueryBoundSelector :
      ((oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec) + privateSpec).Domain → Prop)
    [DecidablePred queryBoundSelector] [DecidablePred srQueryBoundSelector]
    (hCount : ∀ q, srQueryBoundSelector q → queryBoundSelector q)
    (t : ℕ) (ε : ENNReal)
    (h_sr_ks : ∀ P : Prover.StateRestoration.KnowledgeSoundness
      oSpec privateSpec StmtIn Unit pSpec (Salt := Salt),
      P.IsQueryBoundP srQueryBoundSelector t →
      Verifier.StateRestoration.knowledgeSoundnessFailureProb (Salt := Salt)
        fsInit fsImpl privateImpl E
        relIn {yu : StmtOut × Unit | yu.1 ∈ langOut}
        V P ≤ ε) :
    ∀ P : OracleComp ((oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec) + privateSpec)
      (StmtIn × FSSaltedNARGString pSpec Salt), P.IsQueryBoundP queryBoundSelector t →
      Pr{let out ← adaptiveNARGKnowledgeSoundnessExp fsInit
          (fsImpl.addLift srChallengeQueryImpl') privateImpl
          ((fsImpl.addLift (srChallengeQueryImpl'
          (Statement := StmtIn × Salt) (pSpec := pSpec)) : QueryImpl _
            (StateT (QueryImpl (srVerifierMessageOracle (StmtIn × Salt) pSpec) Id)
              ProbComp)).addLift
          (QueryImpl.id' unifSpec))
          (Verifier.compileFiatShamir (Salt := Salt) V)
          (fsSRDelegatingNARGExtractor E) P}[nargKSFailEvent relIn langOut out] ≤ ε := by
  intro P hP
  rw [fsKSShared_failure_eq privateImpl V E fsInit fsImpl relIn langOut P]
  apply h_sr_ks (srInducedProverKS P)
  rw [srInducedProverKS_eq_map, OracleComp.isQueryBoundP_map_iff]
  exact OracleComp.IsQueryBoundP.of_imp hCount hP

end CanonicalFS

section CanonicalSecurity

open CanonicalFS

variable [∀ i, SampleableType (pSpec.Challenge i)]
  [DecidableEq StmtIn]
  [∀ i, DecidableEq (pSpec.Message i)]

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [DecidableEq StmtIn] [∀ i, DecidableEq (pSpec.Message i)]
  in
/-- **[CO25, Theorem 3.18]** Single-salt FS soundness from IP SR-soundness.

If `V` has state-restoration soundness for `langIn` in the game with salt space `Salt`, with error
`ε`, then `Verifier.compileFiatShamir V` has adaptive NARG soundness in the ROM with error `ε`.

**Proof**: repackage the FS prover's output as the original statement, salt context, and
prover messages.
The SR game reconstructs the same transcript and runs the same verifier, so its
false-acceptance probability equals that of the FS experiment. Apply SR soundness directly.

The premise and conclusion use `IsQueryBoundP` with the same natural-number budget `t`.
The selectors satisfy `srQueryBoundSelector q → queryBoundSelector q`: every query counted in the
SR premise is also counted in the FS conclusion. For the paper-facing formulation, choose
`srQueryBoundSelector = publicQuerySelector Verifier.StateRestoration.isSrChallengeMove` and
`queryBoundSelector = nargPublicQuery`.
To count only queries for verifier messages, choose the move selector on both sides. Repackaging
preserves queries exactly, so neither choice increases the budget or the soundness error.
Adapted from **[snarg-book, Theorem 14.3.1]** to the single-salt construction. -/
theorem _root_.CanonicalFS.SoundnessProofs.transferSoundnessWithSampler
    {Salt : Type} [VCVCompatible Salt]
    {κ : Type} (privateSpec : OracleSpec κ) (privateImpl : QueryImpl privateSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (fsInit : ProbComp (QueryImpl (srVerifierMessageOracle (StmtIn × Salt) pSpec) Id))
    (fsImpl : QueryImpl oSpec
      (StateT (QueryImpl (srVerifierMessageOracle (StmtIn × Salt) pSpec) Id) ProbComp))
    (queryBoundSelector srQueryBoundSelector :
      ((oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec) + privateSpec).Domain → Prop)
    [DecidablePred queryBoundSelector] [DecidablePred srQueryBoundSelector]
    (hCount : ∀ q, srQueryBoundSelector q → queryBoundSelector q)
    (t : ℕ) (ε : ENNReal)
    -- SR soundness of the original IP in the game with the same salt context.
    (h_sr : ∀ P : Prover.StateRestoration.Soundness oSpec privateSpec StmtIn pSpec (Salt := Salt),
      P.IsQueryBoundP srQueryBoundSelector t →
      Verifier.StateRestoration.soundnessFailureProb (Salt := Salt) fsInit fsImpl privateImpl
        langIn langOut V P ≤ ε) :
    ∀ P : OracleComp ((oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec) + privateSpec)
      (StmtIn × FSSaltedNARGString pSpec Salt), P.IsQueryBoundP queryBoundSelector t →
      Pr{let out ← adaptiveNARGSoundnessExp fsInit (fsImpl.addLift srChallengeQueryImpl')
          privateImpl (Verifier.compileFiatShamir (Salt := Salt) V) P}[
            nargSoundFailEvent langIn langOut out] ≤ ε := by
  intro P hP
  have hBound : (srInducedProver P).IsQueryBoundP srQueryBoundSelector t := by
    rw [srInducedProver_eq_map, OracleComp.isQueryBoundP_map_iff]
    exact OracleComp.IsQueryBoundP.of_imp hCount hP
  have hSound := h_sr (srInducedProver P) hBound
  suffices hSame :
      Pr{let out ← adaptiveNARGSoundnessExp fsInit
          (fsImpl.addLift srChallengeQueryImpl') privateImpl
          (Verifier.compileFiatShamir (Salt := Salt) V) P}[
          nargSoundFailEvent langIn langOut out] =
      Verifier.StateRestoration.soundnessFailureProb (Salt := Salt) fsInit fsImpl privateImpl
        langIn langOut V (srInducedProver P) by
    exact hSame.trans_le hSound
  simp only [adaptiveNARGSoundnessExp_eq_option, Verifier.StateRestoration.soundnessFailureProb_eq,
    srSoundnessGame]
  rw [prEvent_def, prEvent_def]
  refine congrArg (fun computation : ProbComp Prop => 𝒟[computation] {True}) ?_
  simp only [map_bind]
  refine bind_congr (m := ProbComp) fun state => ?_
  rw [← StateT.run'_map', ← StateT.run'_map', ← simulateQ_map, ← simulateQ_map]
  apply congrArg (fun computation :
    StateT (QueryImpl (srVerifierMessageOracle (StmtIn × Salt) pSpec) Id) ProbComp Prop =>
      computation.run' state)
  apply congrArg (simulateQ _)
  rw [show (liftM P : OptionT
      (OracleComp ((oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec) + privateSpec))
      (StmtIn × FSSaltedNARGString pSpec Salt)) = OptionT.lift P from rfl]
  simp only [srInducedProver_eq_map, Verifier.compileFiatShamir, Fin.cons_zero,
    fsSaltedVerify_eq_deriveTranscriptSR, Verifier.run,
    OptionT.monad_bind_eq_bind, OptionT.bind, OptionT.monad_pure_eq_pure, OptionT.pure,
    OptionT.lift, OptionT.mk, bind_assoc, pure_bind, bind_map_left, map_bind, map_pure,
    liftComp_bind]
  refine bind_congr fun p => ?_
  rw [liftComp_inst_irrel
    (i₁ := instMonadLiftTOfMonadLift
      (OracleQuery (oSpec + srVerifierMessageOracle (StmtIn × Salt) pSpec))
      (OracleQuery (oSpec + srVerifierMessageOracle (StmtIn × Salt) pSpec))
      (OracleQuery ((oSpec + srVerifierMessageOracle (StmtIn × Salt) pSpec) + privateSpec)))
    (i₂ := instMonadLiftTOfMonadLift
      (OracleQuery (oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec))
      (OracleQuery (oSpec + (fsVerifierMessageOracle (StmtIn × Salt) pSpec + privateSpec)))
      (OracleQuery ((oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec) + privateSpec)))
    (fun q => by cases q <;> rfl)
    (Messages.deriveTranscriptSR (oSpec := oSpec) (p.1, p.2.1) p.2.2)]
  refine bind_congr (m := OracleComp
    ((oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec) + privateSpec)) fun transcript => ?_
  refine OracleComp.bind_congr' ?_ fun out => ?_
  · refine liftComp_liftComp ?_ (V.verify p.1 transcript).run
    intro q
    rfl
  · cases out <;> simp only [map_pure, nargSoundFailEvent, and_comm]

omit [VCVCompatible StmtIn] [DecidableEq StmtIn]
  [∀ i, DecidableEq (pSpec.Message i)] in
/-- **[CO25, Theorem 3.19]** — One SR extractor yields
one NARG extractor for every natural-number query budget, with the same error function.
The query selectors satisfy `srQueryBoundSelector q → queryBoundSelector q`, as in the
soundness theorem.
The NARG extractor interface permits randomness and both logs; it does not establish the
deterministic, prover-trace-only contract of Definition 3.6.
Adapted from the straightline case of **[snarg-book, Theorem 14.4.1]**. -/
theorem _root_.CanonicalFS.SoundnessProofs.transferKnowledgeSoundnessWithSampler
    {Salt : Type} [VCVCompatible Salt]
    {κ : Type} (privateSpec : OracleSpec κ) (privateImpl : QueryImpl privateSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (relIn : Set (StmtIn × WitIn)) (langOut : Set StmtOut)
    (fsInit : ProbComp (QueryImpl (srVerifierMessageOracle (StmtIn × Salt) pSpec) Id))
    (fsImpl : QueryImpl oSpec
      (StateT (QueryImpl (srVerifierMessageOracle (StmtIn × Salt) pSpec) Id) ProbComp))
    (queryBoundSelector srQueryBoundSelector :
      ((oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec) + privateSpec).Domain → Prop)
    [DecidablePred queryBoundSelector] [DecidablePred srQueryBoundSelector]
    (hCount : ∀ q, srQueryBoundSelector q → queryBoundSelector q)
    (ε : ℕ → ENNReal)
    (hSR : ∃ E : Extractor.StateRestoration oSpec StmtIn WitIn Unit pSpec (Salt := Salt),
      ∀ t, ∀ P : Prover.StateRestoration.KnowledgeSoundness
        oSpec privateSpec StmtIn Unit pSpec (Salt := Salt),
        P.IsQueryBoundP srQueryBoundSelector t →
        Verifier.StateRestoration.knowledgeSoundnessFailureProb (Salt := Salt)
          fsInit fsImpl privateImpl E
          relIn {yu : StmtOut × Unit | yu.1 ∈ langOut}
          V P ≤ ε t) :
    ∃ extractor : StmtIn → FSSaltedNARGString pSpec Salt →
      QueryLog (oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec) →
      QueryLog (oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec) →
      OptionT (OracleComp ((oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec) + unifSpec))
        WitIn,
      ∀ t, ∀ P : OracleComp ((oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec) + privateSpec)
        (StmtIn × FSSaltedNARGString pSpec Salt), P.IsQueryBoundP queryBoundSelector t →
        Pr{let out ← adaptiveNARGKnowledgeSoundnessExp fsInit
            (fsImpl.addLift srChallengeQueryImpl') privateImpl
            ((fsImpl.addLift (srChallengeQueryImpl'
          (Statement := StmtIn × Salt) (pSpec := pSpec)) : QueryImpl _
            (StateT (QueryImpl (srVerifierMessageOracle (StmtIn × Salt) pSpec) Id)
              ProbComp)).addLift
          (QueryImpl.id' unifSpec))
            (Verifier.compileFiatShamir (Salt := Salt) V) extractor P}[
              nargKSFailEvent relIn langOut out] ≤ ε t := by
  classical
  let _ : DecidableEq StmtIn := Classical.decEq _
  let _ (i : pSpec.MessageIdx) : DecidableEq (pSpec.Message i) := Classical.decEq _
  obtain ⟨E, hE⟩ := hSR
  refine ⟨fsSRDelegatingNARGExtractor E, ?_⟩
  intro t
  exact CanonicalFS.SoundnessProofs.transferFixedExtractor
    privateSpec privateImpl V relIn langOut fsInit fsImpl E
    queryBoundSelector srQueryBoundSelector hCount t (ε t) (hE t)

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [DecidableEq StmtIn] [∀ i, DecidableEq (pSpec.Message i)] in
/-- Single-salt FS soundness with standard private randomness. -/
theorem _root_.CanonicalFS.SoundnessProofs.transferSoundness
    {Salt : Type} [VCVCompatible Salt]
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (fsInit : ProbComp (QueryImpl (srVerifierMessageOracle (StmtIn × Salt) pSpec) Id))
    (fsImpl : QueryImpl oSpec
      (StateT (QueryImpl (srVerifierMessageOracle (StmtIn × Salt) pSpec) Id) ProbComp))
    (queryBoundSelector :
      (oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec).Domain → Prop)
    (srQueryBoundSelector : (oSpec + srVerifierMessageOracle (StmtIn × Salt) pSpec).Domain → Prop)
    [DecidablePred queryBoundSelector] [DecidablePred srQueryBoundSelector]
    (hCount : ∀ q, srQueryBoundSelector q → queryBoundSelector q)
    (t : ℕ) (ε : ENNReal)
    -- SR soundness of the original IP in the game with the same salt context.
    (h_sr : Verifier.StateRestoration.soundnessQueryBounded (Salt := Salt)
      fsInit fsImpl langIn langOut V
      srQueryBoundSelector t ε) :
    Verifier.adaptiveNARGSoundnessQueryBounded
      fsInit (fsImpl.addLift srChallengeQueryImpl')
      (Verifier.compileFiatShamir (Salt := Salt) V) langIn langOut queryBoundSelector t ε := by
  exact CanonicalFS.SoundnessProofs.transferSoundnessWithSampler
    unifSpec (QueryImpl.id' unifSpec) V langIn langOut
    fsInit fsImpl (publicQuerySelector queryBoundSelector)
    (publicQuerySelector srQueryBoundSelector)
    (by intro q h; cases q with
        | inl q => exact hCount q h
        | inr _ => exact h.elim) t ε h_sr

omit [VCVCompatible StmtIn] [DecidableEq StmtIn]
  [∀ i, DecidableEq (pSpec.Message i)] in
/-- Single-salt FS knowledge soundness with standard private randomness. -/
theorem _root_.CanonicalFS.SoundnessProofs.transferKnowledgeSoundness
    {Salt : Type} [VCVCompatible Salt]
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (relIn : Set (StmtIn × WitIn)) (langOut : Set StmtOut)
    (fsInit : ProbComp (QueryImpl (srVerifierMessageOracle (StmtIn × Salt) pSpec) Id))
    (fsImpl : QueryImpl oSpec
      (StateT (QueryImpl (srVerifierMessageOracle (StmtIn × Salt) pSpec) Id) ProbComp))
    (queryBoundSelector :
      (oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec).Domain → Prop)
    (srQueryBoundSelector : (oSpec + srVerifierMessageOracle (StmtIn × Salt) pSpec).Domain → Prop)
    [DecidablePred queryBoundSelector] [DecidablePred srQueryBoundSelector]
    (hCount : ∀ q, srQueryBoundSelector q → queryBoundSelector q)
    (ε : ℕ → ENNReal)
    (hSR : Verifier.StateRestoration.knowledgeSoundnessQueryBounded (Salt := Salt)
      fsInit fsImpl relIn
      {yu : StmtOut × Unit | yu.1 ∈ langOut}
      V srQueryBoundSelector ε) :
    Verifier.adaptiveNARGKnowledgeSoundnessQueryBounded
      fsInit (fsImpl.addLift (srChallengeQueryImpl' (pSpec := pSpec)))
      ((fsImpl.addLift (srChallengeQueryImpl'
          (Statement := StmtIn × Salt) (pSpec := pSpec)) : QueryImpl _
            (StateT (QueryImpl (srVerifierMessageOracle (StmtIn × Salt) pSpec) Id)
              ProbComp)).addLift
          (QueryImpl.id' unifSpec))
      (Verifier.compileFiatShamir (Salt := Salt) V) relIn langOut queryBoundSelector ε := by
  exact CanonicalFS.SoundnessProofs.transferKnowledgeSoundnessWithSampler
    unifSpec (QueryImpl.id' unifSpec) V relIn langOut
    fsInit fsImpl (publicQuerySelector queryBoundSelector)
    (publicQuerySelector srQueryBoundSelector)
    (by intro q h; cases q with
        | inl q => exact hCount q h
        | inr _ => exact h.elim) ε hSR

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [DecidableEq StmtIn] [∀ i, DecidableEq (pSpec.Message i)] in
/-- Soundness of canonical Fiat-Shamir for every salt length, including zero.
The SR game carries salt separately from the original statement and input relation. -/
theorem _root_.CanonicalFS.SoundnessProofs.saltLengthSoundness
    {U : Type} [VCVCompatible U] (saltLength : ℕ)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (fsInit : ProbComp
      (QueryImpl (srVerifierMessageOracle (StmtIn × Vector U saltLength) pSpec) Id))
    (fsImpl : QueryImpl oSpec
      (StateT (QueryImpl (srVerifierMessageOracle (StmtIn × Vector U saltLength) pSpec) Id)
        ProbComp))
    (queryBoundSelector :
      (oSpec + fsVerifierMessageOracle (StmtIn × Vector U saltLength) pSpec).Domain → Prop)
    (srQueryBoundSelector :
      (oSpec + srVerifierMessageOracle (StmtIn × Vector U saltLength) pSpec).Domain → Prop)
    [DecidablePred queryBoundSelector] [DecidablePred srQueryBoundSelector]
    (hCount : ∀ q, srQueryBoundSelector q → queryBoundSelector q)
    (t : ℕ) (ε : ENNReal)
    -- SR soundness of the original IP in the game with the same salt context.
    (h_sr : Verifier.StateRestoration.soundnessQueryBounded (Salt := Vector U saltLength)
      fsInit fsImpl langIn langOut V
      srQueryBoundSelector t ε) :
    Verifier.adaptiveNARGSoundnessQueryBounded
      fsInit (fsImpl.addLift srChallengeQueryImpl')
      (V.fiatShamirSalted (U := U) saltLength) langIn langOut queryBoundSelector t ε := by
  exact CanonicalFS.SoundnessProofs.transferSoundness (Salt := Vector U saltLength)
    V langIn langOut fsInit fsImpl
    queryBoundSelector srQueryBoundSelector hCount t ε h_sr

omit [VCVCompatible StmtIn] [DecidableEq StmtIn]
  [∀ i, DecidableEq (pSpec.Message i)] in
/-- Knowledge soundness of canonical Fiat-Shamir for every salt length, including zero.
The SR game carries salt separately from the original statement and input relation. -/
theorem _root_.CanonicalFS.SoundnessProofs.saltLengthKnowledgeSoundness
    {U : Type} [VCVCompatible U] (saltLength : ℕ)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (relIn : Set (StmtIn × WitIn)) (langOut : Set StmtOut)
    (fsInit : ProbComp
      (QueryImpl (srVerifierMessageOracle (StmtIn × Vector U saltLength) pSpec) Id))
    (fsImpl : QueryImpl oSpec
      (StateT (QueryImpl (srVerifierMessageOracle (StmtIn × Vector U saltLength) pSpec) Id)
        ProbComp))
    (queryBoundSelector :
      (oSpec + fsVerifierMessageOracle (StmtIn × Vector U saltLength) pSpec).Domain → Prop)
    (srQueryBoundSelector :
      (oSpec + srVerifierMessageOracle (StmtIn × Vector U saltLength) pSpec).Domain → Prop)
    [DecidablePred queryBoundSelector] [DecidablePred srQueryBoundSelector]
    (hCount : ∀ q, srQueryBoundSelector q → queryBoundSelector q)
    (ε : ℕ → ENNReal)
    (hSR : Verifier.StateRestoration.knowledgeSoundnessQueryBounded (Salt := Vector U saltLength)
      fsInit fsImpl relIn
      {yu : StmtOut × Unit | yu.1 ∈ langOut}
      V srQueryBoundSelector ε) :
    Verifier.adaptiveNARGKnowledgeSoundnessQueryBounded
      fsInit (fsImpl.addLift (srChallengeQueryImpl' (pSpec := pSpec)))
      ((fsImpl.addLift (srChallengeQueryImpl'
          (Statement := StmtIn × Vector U saltLength) (pSpec := pSpec)) : QueryImpl _
            (StateT (QueryImpl
              (srVerifierMessageOracle (StmtIn × Vector U saltLength) pSpec) Id) ProbComp)).addLift
          (QueryImpl.id' unifSpec))
      (V.fiatShamirSalted (U := U) saltLength) relIn langOut queryBoundSelector ε := by
  exact CanonicalFS.SoundnessProofs.transferKnowledgeSoundness (Salt := Vector U saltLength)
    V relIn langOut fsInit fsImpl
    queryBoundSelector srQueryBoundSelector hCount ε hSR


end CanonicalSecurity

end StateRestorationTransfer

/-! ## Public-coin protocols without ambient oracles -/

section PublicCoin

open OracleComp OracleSpec ProtocolSpec
open scoped ProbabilityTheory

namespace CanonicalFS

variable {n : ℕ} {pSpec : ProtocolSpec n} {Statement Witness : Type}
  {Salt : Type} [VCVCompatible Salt]
  [∀ i, SampleableType (pSpec.Challenge i)]

/-- The NARG's public handler answers only the pre-sampled round functions. -/
def publicCoinOracleImpl : QueryImpl ([]ₒ + fsVerifierMessageOracle (Statement × Salt) pSpec)
    (StateT (QueryImpl (srVerifierMessageOracle (Statement × Salt) pSpec) Id) ProbComp) :=
  (IP.emptyImpl (σ := QueryImpl
    (srVerifierMessageOracle (Statement × Salt) pSpec) Id)).addLift srChallengeQueryImpl'

private def extractionImpl :
    QueryImpl (([]ₒ + fsVerifierMessageOracle (Statement × Salt) pSpec) + unifSpec)
      (StateT (QueryImpl (srVerifierMessageOracle (Statement × Salt) pSpec) Id) ProbComp) :=
  publicCoinOracleImpl.addLift (QueryImpl.id' unifSpec)

omit [VCVCompatible Salt] [∀ i, SampleableType (pSpec.Challenge i)] in
private theorem publicCoinQuerySelector :
    _root_.Verifier.StateRestoration.isSrChallengeMove
      (StmtIn := Statement) (Salt := Salt) (pSpec := pSpec) (oSpec := []ₒ) =
      (fun _ => True) := by
  funext q
  cases q with
  | inl q => nomatch q
  | inr q => rfl

variable [∀ i, VCVCompatible (pSpec.Challenge i)]
  [DecidableEq Statement] [∀ i, DecidableEq (pSpec.Message i)]

private def standaloneExtractor
    (E : Extractor.StateRestoration []ₒ Statement Witness Unit pSpec (Salt := Salt))
    (x : Statement) (π : FSSaltedNARGString pSpec Salt)
    (trP trV : QueryLog ([]ₒ + fsVerifierMessageOracle (Statement × Salt) pSpec)) :
    OptionT ProbComp Witness :=
  OptionT.mk (simulateQ (((fun q => nomatch q) : QueryImpl []ₒ ProbComp) +
      QueryImpl.id' unifSpec)
    (fsSRDelegatingExtractor E x π trP trV).run)

/-- Reconstruct the IP transcript from recorded verifier queries and run the SR extractor.
Only the prover's SR move-response trace is supplied as the extractor's query log. -/
def publicCoinExtractor
    (E : IP.SRExtractor Statement Witness pSpec (Salt := Salt)) :
    NARG.Extractor ([]ₒ + fsVerifierMessageOracle (Statement × Salt) pSpec)
      Statement Witness (FSSaltedNARGString pSpec Salt) :=
  fun x π trP trV => E x π.1
    (FullTranscript.ofMessagesChallenges π.2
      (Messages.challengesOfLog (x, π.1) π.2 trV.snd)) trP.snd

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- The extractor's observable interface is exactly the ordinary SR interface. -/
theorem publicCoinExtractor_apply
    (E : IP.SRExtractor Statement Witness pSpec (Salt := Salt))
    (x : Statement) (π : FSSaltedNARGString pSpec Salt)
    (trP trV : QueryLog ([]ₒ + fsVerifierMessageOracle (Statement × Salt) pSpec)) :
    publicCoinExtractor E x π trP trV =
      E x π.1
        (FullTranscript.ofMessagesChallenges π.2
          (Messages.challengesOfLog (x, π.1) π.2 trV.snd)) trP.snd := rfl

omit [∀ i, SampleableType (pSpec.Challenge i)] in
private theorem standaloneExtractor_toReduction
    (E : IP.SRExtractor Statement Witness pSpec (Salt := Salt)) :
    standaloneExtractor E.toReduction = publicCoinExtractor E := by
  funext x π trP trV
  unfold publicCoinExtractor standaloneExtractor fsSRDelegatingExtractor
    IP.SRExtractor.toReduction
  simp only [OptionT.run_mk]
  rw [QueryImpl.simulateQ_add_liftComp_right, simulateQ_id']
  rfl

private theorem standaloneExtractor_simulate
    (E : Extractor.StateRestoration []ₒ Statement Witness Unit pSpec (Salt := Salt))
    (x : Statement) (π : FSSaltedNARGString pSpec Salt)
    (trP trV : QueryLog ([]ₒ + fsVerifierMessageOracle (Statement × Salt) pSpec)) :
    simulateQ extractionImpl (fsSRDelegatingNARGExtractor E x π trP trV).run =
      StateT.lift (standaloneExtractor E x π trP trV).run := by
  unfold fsSRDelegatingNARGExtractor standaloneExtractor
  simp only [OptionT.run_mk, liftComp_def, ← QueryImpl.simulateQ_compose]
  change _ = liftM (simulateQ (((fun q => nomatch q) : QueryImpl []ₒ ProbComp) +
      QueryImpl.id' unifSpec)
    (fsSRDelegatingExtractor E x π trP trV).run)
  rw [← simulateQ_liftTarget]
  congr 1
  funext q
  cases q with
  | inl q => nomatch q
  | inr q =>
    change simulateQ extractionImpl
      (liftM ((([]ₒ + fsVerifierMessageOracle (Statement × Salt) pSpec) + unifSpec).query
        (.inr q))) = _
    rw [simulateQ_spec_query]
    rfl

private theorem standaloneExtractor_experiment_eq
    (init : ProbComp (QueryImpl (srVerifierMessageOracle (Statement × Salt) pSpec) Id))
    (V : IP.Verifier Statement pSpec)
    (E : Extractor.StateRestoration []ₒ Statement Witness Unit pSpec (Salt := Salt))
    (P : NARG.Prover ([]ₒ + fsVerifierMessageOracle (Statement × Salt) pSpec)
      Statement (FSSaltedNARGString pSpec Salt)) :
    adaptiveNARGKnowledgeSoundnessExp init publicCoinOracleImpl (QueryImpl.id' unifSpec)
      ((QueryImpl.id' unifSpec).liftTarget (StateT _ ProbComp))
      (_root_.Verifier.compileFiatShamir (Salt := Salt) V) (standaloneExtractor E) P =
    adaptiveNARGKnowledgeSoundnessExp init publicCoinOracleImpl (QueryImpl.id' unifSpec)
      extractionImpl (_root_.Verifier.compileFiatShamir (Salt := Salt) V)
      (fsSRDelegatingNARGExtractor E) P := by
  simp only [adaptiveNARGKnowledgeSoundnessExp_eq]
  simp only [standaloneExtractor_simulate, simulateQ_liftTarget, simulateQ_id']
  rfl

end CanonicalFS

namespace CanonicalFS

/-- Restricting the input size commutes with compiling the public verifier. -/
private theorem ofPublic_compileFiatShamir_restrictSize {n : ℕ} {pSpec : ProtocolSpec n}
    {Statement Salt : Type} [VCVCompatible Salt]
    (V : IP.Verifier Statement pSpec) (size : Statement → ℕ) (limit : ℕ) :
    NARG.Verifier.ofPublic
      (_root_.Verifier.compileFiatShamir (Salt := Salt) (V.restrictSize size limit)) =
    (NARG.Verifier.ofPublic (_root_.Verifier.compileFiatShamir (Salt := Salt) V)).restrictSize
      size limit := by
  ext x tr
  apply OptionT.ext
  simp only [NARG.Verifier.ofPublic, NARG.Verifier.restrictSize, _root_.Verifier.liftOracles,
    _root_.Verifier.compileFiatShamir, fsSaltedVerify, _root_.Verifier.verifyFiatShamir,
    _root_.Verifier.restrictSize,
    OptionT.run_map]
  simp only [OptionT.liftM_def, OptionT.run_bind, Option.elimM, OptionT.run_lift, bind_assoc,
    pure_bind, Option.elim_some, liftComp_bind, OptionT.run_mk, map_bind]
  apply bind_congr
  intro derived
  simp only [liftM_map, OptionT.run_map, liftComp_map, bind_map_left]
  apply bind_congr
  intro accepted
  cases accepted with
  | none => rfl
  | some accepted => cases accepted <;> rfl

section Families

variable {Statement Witness : Type}
  {rounds : ℕ → ℕ → ℕ} {pSpec : ∀ sec n, ProtocolSpec (rounds sec n)}
  {Salt : ℕ → ℕ → ℕ → Type} [∀ sec s n, VCVCompatible (Salt sec s n)]
  [∀ sec n i, SampleableType ((pSpec sec n).Challenge i)]
  [∀ sec n i, VCVCompatible ((pSpec sec n).Challenge i)]
  (init : ∀ sec s n, ProbComp
    (QueryImpl (srVerifierMessageOracle (Statement × Salt sec s n) (pSpec sec n)) Id))
  (V : ∀ sec n, IP.Verifier Statement (pSpec sec n))
  (size : Statement → ℕ) (saltSize : ℕ → ℕ → ℕ)

omit [∀ sec n i, VCVCompatible ((pSpec sec n).Challenge i)] in
/-- Canonical Fiat--Shamir soundness with the full public parameters and size-restricted
state-restoration premise. The reduction preserves the error and public-query budget. -/
theorem _root_.CanonicalFS.SoundnessProofs.publicCoinSoundness (language : Set Statement)
    (error : ℕ → ℕ → ℕ → ℕ → ENNReal)
    (hSR : ∀ sec, IP.srSoundness (init sec) (fun _ n => V sec n)
      language size (error sec)) :
    NARG.adaptiveSoundness
      (fun sec n => []ₒ +
        fsVerifierMessageOracle (Statement × Salt sec (saltSize sec n) n) (pSpec sec n))
      (fun sec n => init sec (saltSize sec n) n)
      (fun _ _ => publicCoinOracleImpl)
      (fun sec n => NARG.Verifier.ofPublic
        (_root_.Verifier.compileFiatShamir (Salt := Salt sec (saltSize sec n) n) (V sec n)))
      language size (fun sec n t => error sec (saltSize sec n) n t) := by
  classical
  intro sec n t P hP
  rw [← NARG.soundnessExperiment_restrictSize_failureProb_eq,
    ← ofPublic_compileFiatShamir_restrictSize (Salt := Salt sec (saltSize sec n) n)
      (V sec n) size n]
  rw [NARG.soundnessExperiment_ofPublic]
  have h := CanonicalFS.SoundnessProofs.transferSoundness
    ((V sec n).restrictSize size n) language {true}
    (init sec (saltSize sec n) n) IP.emptyImpl
    (_root_.Verifier.StateRestoration.isSrChallengeMove (Salt := Salt sec (saltSize sec n) n))
    (_root_.Verifier.StateRestoration.isSrChallengeMove (Salt := Salt sec (saltSize sec n) n))
    (fun _ h => h) t (error sec (saltSize sec n) n t) (hSR sec (saltSize sec n) n t)
  simpa only [publicCoinOracleImpl, publicCoinQuerySelector, NARG.soundnessFailureEvent] using
    h P (by simpa only [publicCoinQuerySelector] using hP)

/-- The canonical FS extractor constructed from a supplied state-restoration extractor family
satisfies the adaptive knowledge-soundness bound for every parameter and query budget. -/
theorem _root_.CanonicalFS.SoundnessProofs.publicCoinKnowledgeSoundnessWithExtractor
    [DecidableEq Statement] [∀ sec n i, DecidableEq ((pSpec sec n).Message i)]
    (relation : Set (Statement × Witness))
    (error : ℕ → ℕ → ℕ → ℕ → ENNReal)
    (E : ∀ sec s n, IP.SRExtractor Statement Witness (pSpec sec n)
      (Salt := Salt sec s n))
    (hE : ∀ sec, IP.srKnowledgeSoundnessWithExtractor
      (init sec) (fun _ n => V sec n) relation size (E sec) (error sec)) :
    NARG.adaptiveKnowledgeSoundnessWithExtractor
      (fun sec n => []ₒ +
        fsVerifierMessageOracle (Statement × Salt sec (saltSize sec n) n) (pSpec sec n))
      (fun sec n => init sec (saltSize sec n) n)
      (fun _ _ => publicCoinOracleImpl)
      (fun sec n => NARG.Verifier.ofPublic
        (_root_.Verifier.compileFiatShamir (Salt := Salt sec (saltSize sec n) n) (V sec n)))
      relation size (fun sec n => publicCoinExtractor (E sec (saltSize sec n) n))
      (fun sec n t => error sec (saltSize sec n) n t) := by
  classical
  intro sec n t P hP
  rw [← NARG.knowledgeSoundnessExperiment_restrictSize_failureProb_eq,
    ← ofPublic_compileFiatShamir_restrictSize (Salt := Salt sec (saltSize sec n) n)
      (V sec n) size n]
  rw [NARG.knowledgeSoundnessExperiment_ofPublic]
  have hGeneric := IP.srKnowledgeSoundnessQueryBoundedWithExtractor_to_generic
    (init sec (saltSize sec n) n) relation ((V sec n).restrictSize size n)
    (E sec (saltSize sec n) n) t (error sec (saltSize sec n) n t) (hE sec (saltSize sec n) n t)
  have hBound : P.IsQueryBoundP (publicQuerySelector
      (_root_.Verifier.StateRestoration.isSrChallengeMove
        (Salt := Salt sec (saltSize sec n) n) (oSpec := []ₒ))) t := by
    simpa only [publicCoinQuerySelector] using hP
  have h := CanonicalFS.SoundnessProofs.transferFixedExtractor
    unifSpec (QueryImpl.id' unifSpec) ((V sec n).restrictSize size n) relation {true}
    (init sec (saltSize sec n) n) IP.emptyImpl (E sec (saltSize sec n) n).toReduction
    (publicQuerySelector (_root_.Verifier.StateRestoration.isSrChallengeMove
      (Salt := Salt sec (saltSize sec n) n)))
    (publicQuerySelector (_root_.Verifier.StateRestoration.isSrChallengeMove
      (Salt := Salt sec (saltSize sec n) n)))
    (fun _ h => h) t (error sec (saltSize sec n) n t) hGeneric P hBound
  change Pr{let out ← (adaptiveNARGKnowledgeSoundnessExp (init sec (saltSize sec n) n)
      publicCoinOracleImpl (QueryImpl.id' unifSpec) NARG.privateExtractorImpl
      (_root_.Verifier.compileFiatShamir (Salt := Salt sec (saltSize sec n) n)
        ((V sec n).restrictSize size n))
      (publicCoinExtractor (E sec (saltSize sec n) n)) P)}[
        nargKSFailEvent relation {true} out] ≤ error sec (saltSize sec n) n t
  rw [← standaloneExtractor_toReduction (E sec (saltSize sec n) n)]
  change Pr{let out ← (adaptiveNARGKnowledgeSoundnessExp (init sec (saltSize sec n) n)
      publicCoinOracleImpl (QueryImpl.id' unifSpec)
      ((QueryImpl.id' unifSpec).liftTarget (StateT _ ProbComp))
      (_root_.Verifier.compileFiatShamir (Salt := Salt sec (saltSize sec n) n)
        ((V sec n).restrictSize size n))
      (standaloneExtractor (E sec (saltSize sec n) n).toReduction) P)}[
        nargKSFailEvent relation {true} out] ≤ error sec (saltSize sec n) n t
  rw [standaloneExtractor_experiment_eq]
  exact h

/-- One ordinary state-restoration extractor family gives one canonical FS extractor family
for all public security parameters, instance-size bounds, and query budgets. -/
theorem _root_.CanonicalFS.SoundnessProofs.publicCoinKnowledgeSoundness
    (relation : Set (Statement × Witness))
    (error : ℕ → ℕ → ℕ → ℕ → ENNReal)
    (hSR : ∀ sec, IP.srKnowledgeSoundness (init sec) (fun _ n => V sec n)
      relation size (error sec)) :
    NARG.adaptiveKnowledgeSoundness
      (fun sec n => []ₒ +
        fsVerifierMessageOracle (Statement × Salt sec (saltSize sec n) n) (pSpec sec n))
      (fun sec n => init sec (saltSize sec n) n)
      (fun _ _ => publicCoinOracleImpl)
      (fun sec n => NARG.Verifier.ofPublic
        (_root_.Verifier.compileFiatShamir (Salt := Salt sec (saltSize sec n) n) (V sec n)))
      relation size (fun sec n t => error sec (saltSize sec n) n t) := by
  classical
  choose E hE using hSR
  exact ⟨_, CanonicalFS.SoundnessProofs.publicCoinKnowledgeSoundnessWithExtractor
    init V size saltSize relation error E hE⟩

end Families

end CanonicalFS

end PublicCoin

section ProtocolVerifier

open OracleComp OracleSpec ProtocolSpec

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {Stmt Wit Salt : Type}

/-- The typed protocol's security verifier is exactly the legacy basic-FS verifier. -/
theorem InteractiveProtocol.compileFiatShamir_toVerifier [VCVCompatible Salt]
    (P : InteractiveProtocol oSpec Stmt Wit pSpec) (sampleSalt : OracleComp oSpec Salt) :
    (P.compileFiatShamir sampleSalt).toVerifier =
      P.verifier.toReductionVerifier.compileFiatShamir := by
  apply Verifier.ext
  funext stmt messages
  apply OptionT.ext
  have hm : messages = Fin.cons (messages 0) (fun i => i.elim0) := by
    funext i
    fin_cases i
    rfl
  rw [hm]
  simpa [NonInteractiveArgument.toVerifier, InteractiveProtocol.compileFiatShamir, OptionT.lift]
    using (P.verifier.compileFiatShamir_eq_verify stmt (messages 0)).symm

end ProtocolVerifier
