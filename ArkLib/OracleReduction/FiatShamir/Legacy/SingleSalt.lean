/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Michele Orrù
-/
module

public import ArkLib.OracleReduction.FiatShamir.Legacy.KnowledgeGames
public import ArkLib.OracleReduction.FiatShamir.Legacy.Lifting
public import ArkLib.OracleReduction.ProtocolSpec.DeriveTranscript
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic

/-!
# Canonical single-salt Fiat–Shamir knowledge-security transport

Narrow port of the proved knowledge-security part of ArkLib PR #848,
commit `1c5c5bd7ed9d4a6407974a12ff95893fbdbc02bb`, to the current probability API.
This is the existing conditional reduction, not a new proof of its restoration-security premise.
The native interaction bridge supplies that separate premise.
-/

@[expose] public section

noncomputable section

open ProtocolSpec OracleComp OracleSpec OracleReduction
open scoped ProbabilityTheory

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]

/-- A single public salt paired with the complete prover-message tuple. -/
abbrev FSSaltedProof (pSpec : ProtocolSpec n) (Salt : Type) := Salt × pSpec.Messages

/-- The single-salt verifier derives every challenge, then runs the interactive verifier.
This is the eager legacy verifier; the native stopped verifier has a separate correspondence. -/
def Verifier.singleSaltFiatShamir {Salt : Type} [VCVCompatible Salt]
    (V : Verifier oSpec StmtIn StmtOut pSpec) :
    NonInteractiveVerifier (FSSaltedProof pSpec Salt)
      (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) StmtIn StmtOut where
  verify := fun stmtIn proof => OptionT.mk do
    let saltedProof : FSSaltedProof pSpec Salt := proof 0
    let transcript ← saltedProof.2.deriveTranscriptFS (oSpec := oSpec) (stmtIn, saltedProof.1)
    liftComp (V.verify stmtIn transcript).run (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)

/-- The single-salt FS verifier run as a NARG `verify` (CO25 `V_std^f(x,·)`): build the
single-message transcript from the proof and run `Verifier.singleSaltFiatShamir V`. Used by
the DSFS Section 5 `Hyb₄`/basic-FS game so both games refer to the same verifier. -/
def fsSaltedVerify {Salt : Type} [VCVCompatible Salt]
    (V : Verifier oSpec StmtIn StmtOut pSpec) :
    StmtIn → FSSaltedProof pSpec Salt →
      OptionT (OracleComp (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)) StmtOut :=
  fun stmtIn proof =>
    (Verifier.singleSaltFiatShamir (Salt := Salt) V).verify stmtIn
      (Fin.cons proof (fun i => i.elim0))

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)] in
/-- The normalized verifier is exactly the verifier body in PR #848. In particular, the
base verifier's failure and all of its oracle queries are preserved by normalization. -/
theorem fsSaltedVerify_eq_original {Salt : Type} [VCVCompatible Salt]
    (V : Verifier oSpec StmtIn StmtOut pSpec) (x : StmtIn)
    (proof : FSSaltedProof pSpec Salt) :
    fsSaltedVerify V x proof = (do
      let transcript ← proof.2.deriveTranscriptFS (oSpec := oSpec) (x, proof.1)
      Option.getM (← (V.verify x transcript).run)) := by
  apply OptionT.ext
  simp only [fsSaltedVerify, Verifier.singleSaltFiatShamir, Fin.cons_zero, OptionT.run_mk,
    OptionT.run_bind, OptionT.run_monadLift, Option.elimM, bind_map_left,
    monadLift_self, Option.elim_some]
  apply bind_congr
  intro transcript
  rw [show (liftM (V.verify x transcript).run :
      OptionT (OracleComp (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec))
        (Option StmtOut)) =
    OptionT.lift (liftM (V.verify x transcript).run :
      OracleComp (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) (Option StmtOut)) from
        (OracleComp.monadLift_liftM_OptionT _).symm]
  simp only [OptionT.run_lift, bind_assoc, pure_bind, Option.elim_some,
    OracleComp.liftComp_eq_liftM]
  have hget (choice : Option StmtOut) :
      (Option.getM choice :
        OptionT (OracleComp (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)) StmtOut).run =
          pure choice := by cases choice <;> rfl
  simp_rw [hget]
  simp only [bind_pure]

section SingleSaltSecurity

variable [∀ i, SampleableType (pSpec.Challenge i)]
  [DecidableEq StmtIn]
  [∀ i, DecidableEq (pSpec.Message i)]


/-- Lift the IP verifier `V` to accept `StmtIn × Salt` by ignoring the salt component.

The SR challenge oracle for this lifted verifier is `srChallengeOracle (StmtIn × Salt) pSpec`,
which equals `fsChallengeOracle (StmtIn × Salt) pSpec` by alias. -/
def saltedIPVerifier {Salt : Type} (V : Verifier oSpec StmtIn StmtOut pSpec) :
    Verifier oSpec (StmtIn × Salt) StmtOut pSpec where
  verify := fun ⟨stmtIn, _⟩ transcript => V.verify stmtIn transcript

/-- Lift a soundness language `langIn : Set StmtIn` to `Set (StmtIn × Salt)`,
ignoring the salt. -/
def langInSalted {Salt : Type} (langIn : Set StmtIn) : Set (StmtIn × Salt) :=
  {p | p.1 ∈ langIn}

/-- Lift an input relation `relIn : Set (StmtIn × WitIn)` to
`Set ((StmtIn × Salt) × WitIn)`, ignoring the salt. -/
def relInSalted {Salt : Type} (relIn : Set (StmtIn × WitIn)) : Set ((StmtIn × Salt) × WitIn) :=
  {p | ⟨p.1.1, p.2⟩ ∈ relIn}

/-- View an accepting-output set as the relation-valued interface expected by ArkLib's generic
state-restoration definitions. The `Unit` component carries no adversarial claim. -/
def unitOutputRelation (langOut : Set StmtOut) : Set (StmtOut × Unit) :=
  {p | p.1 ∈ langOut}

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)] [DecidableEq StmtIn]
  [∀ i, DecidableEq (pSpec.Message i)] in
/-- `Verifier.singleSaltFiatShamir`'s `verify` on the length-1 transcript `Fin.cons π 0` is, by
definition, the bare FS-NARG `verify` map `fsSaltedVerify V x π`.  Bridges the NIV-shaped
`adaptiveNARG*Exp init impl (Verifier.singleSaltFiatShamir V)` experiments back to the
`fsSaltedVerify`-shaped §6.1/§6.2 game-match proofs (`simp only [fsSaltedNIV_verify]` after
unfolding the experiment restores the `fsSaltedVerify`-form goal). -/
theorem fsSaltedNIV_verify {Salt : Type} [VCVCompatible Salt]
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (x : StmtIn) (π : FSSaltedProof pSpec Salt) :
    (Verifier.singleSaltFiatShamir (Salt := Salt) V).verify x (Fin.cons π (fun i => i.elim0))
      = fsSaltedVerify V x π :=
  rfl



/-- The coin-bearing SR knowledge-soundness prover induced by an adaptive FS NARG KS prover
(the KS analog of `srInducedProver`): run `P` for `(𝕩, (τ, m))` and output the salted statement
`(𝕩, τ)`, the messages `m`, and the canonical unit required by the generic SR interface. -/
def srInducedProverKS {Salt : Type} [VCVCompatible Salt]
    {κ : Type} {auxSpec : OracleSpec κ}
    (P : OracleComp ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + auxSpec)
      (StmtIn × FSSaltedProof pSpec Salt)) :
    Prover.StateRestoration.KnowledgeSoundnessWithCoins oSpec (StmtIn × Salt) Unit pSpec
      auxSpec := do
  let ⟨x, proof⟩ ← P
  return ⟨(x, proof.1), proof.2, ()⟩

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)] [DecidableEq StmtIn]
  [∀ i, DecidableEq (pSpec.Message i)] in
/-- The induced SR-KS prover is `P` followed by a pure repackaging of its output — in particular
it makes *exactly* the queries `P` makes. -/
lemma srInducedProverKS_eq_map {Salt : Type} [VCVCompatible Salt]
    {κ : Type} {auxSpec : OracleSpec κ}
    (P : OracleComp ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + auxSpec)
      (StmtIn × FSSaltedProof pSpec Salt)) :
    srInducedProverKS (Salt := Salt) P
      = (fun p => ((p.1, p.2.1), p.2.2, ())) <$> P := by
  rw [map_eq_bind_pure_comp]
  exact bind_congr fun p => rfl

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)] [DecidableEq StmtIn]
  [∀ i, DecidableEq (pSpec.Message i)] in
/-- **Query-budget preservation (Construction 3.19)**: the induced SR-KS prover satisfies exactly
the query bounds `P` does, for any VCVio budget discipline `(b, canQuery, cost)`. -/
lemma isQueryBound_srInducedProverKS_iff {Salt : Type} [VCVCompatible Salt]
    {κ : Type} {auxSpec : OracleSpec κ} {B : Type}
    (P : OracleComp ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + auxSpec)
      (StmtIn × FSSaltedProof pSpec Salt))
    (b : B) (canQuery : _ → B → Prop) (cost : _ → B → B) :
    (srInducedProverKS (Salt := Salt) P).IsQueryBound b canQuery cost
      ↔ P.IsQueryBound b canQuery cost := by
  rw [srInducedProverKS_eq_map, OracleComp.isQueryBound_map_iff]

/-- **CO25 Construction 3.19 adaptation (two-log, oracle-capable wrapper)**:
parse the salted proof
`π = (τ, m)`, rebuild the IP transcript from `m` and the verifier's logged challenge queries
(`Messages.challengesOfLog` on the challenge part of `tr_V`), and run the SR extractor `E` on
the salted statement `(𝕩, τ)` with the canonical unit required only by ArkLib's generic SR
interface, the prover's query log (the SR move-response trace — `fsChallengeOracle =
srChallengeOracle` by alias, so the paper's `FSToSR` trace map is the identity), and the verifier's
`oSpec`-query log.

This is an explicit computation, not a classical witness choice. `Messages.challengesOfLog`
rescans the verifier trace for each challenge round: with `k` rounds and `N` log entries this
uses up to `O(k * N)` entry inspections, plus transcript assembly and one invocation of `E`.
This implementation does not claim a single-pass, `O(N)` reconstruction. -/
def fsSRDelegatingExtractor {Salt : Type} [VCVCompatible Salt]
    (E : Extractor.StateRestoration oSpec (StmtIn × Salt) WitIn Unit pSpec)
    (x : StmtIn) (π : FSSaltedProof pSpec Salt)
    (tr_P tr_V : QueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)) :
    OptionT (OracleComp oSpec) WitIn :=
  E (x, π.1) ()
    (FullTranscript.ofMessagesChallenges π.2
      (Messages.challengesOfLog (x, π.1) π.2 tr_V.snd))
    tr_P tr_V.fst

/-- Embed the delegated base-oracle computation into the NARG extractor interface.
The challenge and helper slots are available in the ambient type but are not used here. -/
def fsSRDelegatingNargExtractor {Salt : Type} [VCVCompatible Salt]
    {κE : Type} {auxSpecE : OracleSpec κE}
    (E : Extractor.StateRestoration oSpec (StmtIn × Salt) WitIn Unit pSpec)
    (x : StmtIn) (π : FSSaltedProof pSpec Salt)
    (tr_P tr_V : QueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)) :
    OptionT (OracleComp ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + auxSpecE)) WitIn :=
  OptionT.mk (liftComp (fsSRDelegatingExtractor E x π tr_P tr_V).run
    ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + auxSpecE))

omit [VCVCompatible StmtIn] [∀ i, SampleableType (pSpec.Challenge i)] in
/-- Canonical verifier logs reconstruct the SR inputs exactly. This is equality of entire
oracle computations, not just of pure witness values, so subsequent extractor queries are
preserved under any common interpretation. -/
lemma fsSRDelegatingExtractor_canonical {Salt : Type} [VCVCompatible Salt]
    (E : Extractor.StateRestoration oSpec (StmtIn × Salt) WitIn Unit pSpec)
    (x : StmtIn) (π : FSSaltedProof pSpec Salt)
    (tr_P : QueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec))
    (tr_V : QueryLog oSpec)
    (cs : pSpec.ChallengesUpTo ⟨n, Nat.lt_succ_self n⟩) :
    fsSRDelegatingExtractor E x π tr_P
      (QueryLog.inr (canonChalLog (x, π.1) π.2 ⟨n, Nat.lt_succ_self n⟩ cs)
        ++ QueryLog.inl tr_V) =
      E (x, π.1) ()
        (FullTranscript.ofMessagesChallenges π.2
          (fun r => cs ⟨⟨r.1.1, r.1.2⟩, r.2⟩)) tr_P tr_V := by
  unfold fsSRDelegatingExtractor
  rw [QueryLog.snd_append, QueryLog.snd_inr, QueryLog.snd_inl, List.append_nil]
  rw [QueryLog.fst_append, QueryLog.fst_inr, QueryLog.fst_inl, List.nil_append]
  rw [Messages.challengesOfLog_canonChalLog]

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)] [DecidableEq StmtIn]
  [∀ i, DecidableEq (pSpec.Message i)] in
/-- Canonical form of the logged single-salt FS verifier run: query the challenge tuple, run
the (logged) base verifier on the assembled transcript, and read out the decision together with
the canonical challenge log followed by the (left-embedded) base-verifier log. -/
private lemma logged_fsSaltedVerify {Salt : Type} [VCVCompatible Salt]
    (V : Verifier oSpec StmtIn StmtOut pSpec) (x : StmtIn) (π : FSSaltedProof pSpec Salt) :
    (simulateQ loggingOracle ((fsSaltedVerify (Salt := Salt) V x π).run)).run
    = chalTupleUpTo (oSpec := oSpec) (x, π.1) π.2 ⟨n, Nat.lt_succ_self n⟩ >>= fun cs =>
        (liftComp ((simulateQ loggingOracle
            ((V.verify x (Transcript.ofMessagesChallenges
              (π.2.take ⟨n, Nat.lt_succ_self n⟩) cs)).run)).run)
          (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)) >>= fun q =>
          pure (q.1, QueryLog.inr (canonChalLog (x, π.1) π.2 ⟨n, Nat.lt_succ_self n⟩ cs)
            ++ QueryLog.inl q.2) := by
  have hrun : (fsSaltedVerify (Salt := Salt) V x π).run
      = (Messages.deriveTranscriptSR (oSpec := oSpec) (x, π.1) π.2 : OracleComp _ _)
          >>= fun t => liftComp ((V.verify x t).run)
            (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) := by
    rfl
  rw [hrun]
  refine Eq.trans (OracleComp.withQueryLog_bind _ _) ?_
  rw [show (Messages.deriveTranscriptSR (oSpec := oSpec) (x, π.1) π.2 :
      OracleComp (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) _).withQueryLog
    = chalTupleUpTo (oSpec := oSpec) (x, π.1) π.2 ⟨n, Nat.lt_succ_self n⟩ >>= fun cs =>
        pure (Transcript.ofMessagesChallenges (π.2.take ⟨n, Nat.lt_succ_self n⟩) cs,
          QueryLog.inr (canonChalLog (x, π.1) π.2 ⟨n, Nat.lt_succ_self n⟩ cs))
    from logged_deriveTranscriptSRAux_eq (x, π.1) π.2 ⟨n, Nat.lt_succ_self n⟩]
  refine Eq.trans (bind_assoc _ _ _) ?_
  refine bind_congr fun cs => ?_
  change ((Prod.map id
      fun l => (canonChalLog (x, π.1) π.2 ⟨n, Nat.lt_succ_self n⟩ cs).inr ++ l) <$>
    ((V.verify x (Transcript.ofMessagesChallenges (Messages.take ⟨n, Nat.lt_succ_self n⟩ π.2)
      cs)).run.liftComp (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)).withQueryLog) = _
  rw [show ((liftComp ((V.verify x (Transcript.ofMessagesChallenges
        (π.2.take ⟨n, Nat.lt_succ_self n⟩) cs)).run)
        (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec))).withQueryLog
    = (liftComp ((simulateQ loggingOracle ((V.verify x (Transcript.ofMessagesChallenges
          (π.2.take ⟨n, Nat.lt_succ_self n⟩) cs)).run)).run)
        (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)) >>= fun p =>
        pure (p.1, QueryLog.inl p.2)
    from withQueryLog_liftComp_inl (fun t => rfl) _]
  refine Eq.trans (map_bind _ _ _) ?_
  refine bind_congr fun q => ?_
  refine Eq.trans (map_pure _ _) ?_
  rfl

omit [VCVCompatible StmtIn] [∀ i, SampleableType (pSpec.Challenge i)] in
/-- **FS↔SR KS crosswalk (the core of CO25 Theorem 3.19)**: with the Construction-3.19
delegating extractor, the coin-bearing NARG KS experiment for the single-salt FS
verifier is the salted-statement marginal of the coin-bearing SR-KS experiment for the induced
SR prover — with the *same* SR extractor `E` receiving the same transcript and the same
(projected) query logs. -/
private lemma fsKSReadout_eq_map_srKSReadout {Salt : Type} [VCVCompatible Salt]
    {κ : Type} {auxSpec : OracleSpec κ}
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (E : Extractor.StateRestoration oSpec (StmtIn × Salt) WitIn Unit pSpec)
    (P : OracleComp ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + auxSpec)
      (StmtIn × FSSaltedProof pSpec Salt)) :
    (do
      let ⟨⟨x, π⟩, tr⟩ ← (simulateQ loggingOracle P).run
      (fun a => (x, fsSRDelegatingExtractor E x π tr.fst a.2, a.1)) <$>
        liftComp (simulateQ loggingOracle (fsSaltedVerify V x π).run).run
          ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + auxSpec)
          (h := instMonadLiftTOfMonadLift
            (OracleQuery (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec))
            (OracleQuery (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec))
            (OracleQuery ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + auxSpec))))
    = (fun out : (StmtIn × Salt) × OptionT (OracleComp oSpec) WitIn × Option StmtOut × Unit =>
        (out.1.1, out.2.1, out.2.2.1)) <$>
      (do
        let ⟨⟨stmtIn, messages, _unit⟩, tr⟩ ←
          (simulateQ loggingOracle (srInducedProverKS P)).run
        let transcript ← liftComp (messages.deriveTranscriptSR (oSpec := oSpec) stmtIn)
          ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + auxSpec)
        let ⟨stmtOut, tr_V⟩ ←
          liftComp (simulateQ loggingOracle
            ((saltedIPVerifier (Salt := Salt) V).run stmtIn transcript).run).run _
        return (stmtIn, E stmtIn () transcript tr.fst tr_V,
          stmtOut, ())) := by
  classical
  -- Align the prover stage: the induced SR prover is `P` with a pure repackaging, so its logged
  -- run is the logged run of `P` with the same log.
  refine Eq.trans ?_ (Eq.symm (congrArg (fun z => _ <$> z)
    (Eq.trans (congrArg (· >>= _) (show (simulateQ loggingOracle
        (srInducedProverKS (Salt := Salt) P)).run
      = (simulateQ loggingOracle P).run >>= fun p =>
          pure (((p.1.1, p.1.2.1), p.1.2.2, ()), p.2) from by
        refine Eq.trans (OracleComp.withQueryLog_bind _ _) (bind_congr fun p => ?_)
        simp only [OracleComp.withQueryLog_pure, map_pure, Prod.map, id, List.append_nil]))
      (Eq.trans (bind_assoc _ _ _) (bind_congr fun p => pure_bind _ _)))))
  simp only [map_bind]
  refine bind_congr fun p => ?_
  -- Verify stage: canonical form of the logged FS verifier, and the explicit form of the SR
  -- transcript derivation.
  refine Eq.trans (congrArg (fun z : OracleComp (oSpec + srChallengeOracle (StmtIn × Salt) pSpec)
      (Option StmtOut × QueryLog (oSpec + srChallengeOracle (StmtIn × Salt) pSpec)) =>
    (fun a => (p.1.1, fsSRDelegatingExtractor E p.1.1 p.1.2 p.2.fst a.2, a.1)) <$>
      z.liftComp (oSpec + srChallengeOracle (StmtIn × Salt) pSpec + auxSpec)
        (h := instMonadLiftTOfMonadLift
          (OracleQuery (oSpec + srChallengeOracle (StmtIn × Salt) pSpec))
          (OracleQuery (oSpec + srChallengeOracle (StmtIn × Salt) pSpec))
          (OracleQuery (oSpec + srChallengeOracle (StmtIn × Salt) pSpec + auxSpec))))
    (logged_fsSaltedVerify V p.1.1 p.1.2)) ?_
  rw [show (Messages.deriveTranscriptSR (oSpec := oSpec) (p.1.1, p.1.2.1) p.1.2.2 :
      OracleComp _ _)
    = chalTupleUpTo (oSpec := oSpec) (pSpec := pSpec) (p.1.1, p.1.2.1) p.1.2.2
        ⟨n, Nat.lt_succ_self n⟩ >>= fun cs =>
        pure (Transcript.ofMessagesChallenges (p.1.2.2.take ⟨n, Nat.lt_succ_self n⟩) cs)
    from Messages.deriveTranscriptSR_eq_chalTupleUpTo _ _]
  -- Push the lifts through both sides and align stage by stage.
  refine Eq.trans (congrArg (fun z => _ <$> z)
    (OracleComp.liftComp_bind
      (h := instMonadLiftTOfMonadLift
        (OracleQuery (oSpec + srChallengeOracle (StmtIn × Salt) pSpec))
        (OracleQuery (oSpec + srChallengeOracle (StmtIn × Salt) pSpec))
        (OracleQuery (oSpec + srChallengeOracle (StmtIn × Salt) pSpec + auxSpec))) _ _ _)) ?_
  refine Eq.trans (map_bind _ _ _) ?_
  refine Eq.trans ?_ (Eq.symm (Eq.trans (congrArg (· >>= _)
    (OracleComp.liftComp_bind
      (h := instMonadLiftTOfMonadLift
        (OracleQuery (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec))
        (OracleQuery (oSpec + (fsChallengeOracle (StmtIn × Salt) pSpec + auxSpec)))
        (OracleQuery (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec + auxSpec))) _ _ _))
    (Eq.trans (bind_assoc _ _ _) (bind_congr fun cs =>
      Eq.trans (congrArg (· >>= _) (OracleComp.liftComp_pure _ _)) (pure_bind _ _)))))
  rw [liftComp_inst_irrel
    (i₁ := instMonadLiftTOfMonadLift
      (OracleQuery (oSpec + srChallengeOracle (StmtIn × Salt) pSpec))
      (OracleQuery (oSpec + srChallengeOracle (StmtIn × Salt) pSpec))
      (OracleQuery (oSpec + srChallengeOracle (StmtIn × Salt) pSpec + auxSpec)))
    (i₂ := instMonadLiftTOfMonadLift
      (OracleQuery (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec))
      (OracleQuery (oSpec + (fsChallengeOracle (StmtIn × Salt) pSpec + auxSpec)))
      (OracleQuery (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec + auxSpec)))
    (fun t => by rcases t with t | t <;> rfl)
    (chalTupleUpTo (oSpec := oSpec) (p.1.1, p.1.2.1) p.1.2.2 ⟨n, Nat.lt_succ_self n⟩)]
  refine bind_congr fun cs => ?_
  refine Eq.trans (congrArg (fun z => _ <$> z)
    (OracleComp.liftComp_bind
      (h := instMonadLiftTOfMonadLift
        (OracleQuery (oSpec + srChallengeOracle (StmtIn × Salt) pSpec))
        (OracleQuery (oSpec + srChallengeOracle (StmtIn × Salt) pSpec))
        (OracleQuery (oSpec + srChallengeOracle (StmtIn × Salt) pSpec + auxSpec))) _ _ _)) ?_
  refine Eq.trans (map_bind _ _ _) ?_
  refine Eq.trans (bind_congr fun q => Eq.trans
    (congrArg (fun z => _ <$> z)
      (OracleComp.liftComp_pure
        (h := instMonadLiftTOfMonadLift
          (OracleQuery (oSpec + srChallengeOracle (StmtIn × Salt) pSpec))
          (OracleQuery (oSpec + srChallengeOracle (StmtIn × Salt) pSpec))
          (OracleQuery (oSpec + srChallengeOracle (StmtIn × Salt) pSpec + auxSpec))) _ _))
    (map_pure _ _)) ?_
  simp only [map_pure]
  refine liftComp_liftComp_bind_congr ?_ _ _ _ fun q => ?_
  case _ => intro t; rfl
  -- Read-out equality: the delegated extractor receives the reconstructed transcript and the
  -- projected logs, which coincide with the SR experiment's transcript and logs.
  have hchal := Messages.challengesOfLog_canonChalLog
    (p.1.1, p.1.2.1) p.1.2.2 cs
  refine congrArg pure ?_
  refine congrArg (fun w => (p.1.1, w, q.1)) ?_
  unfold fsSRDelegatingExtractor
  rw [QueryLog.snd_append, QueryLog.snd_inr, QueryLog.snd_inl, List.append_nil]
  rw [QueryLog.fst_append, QueryLog.fst_inr, QueryLog.fst_inl, List.nil_append]
  rw [hchal]
  rfl

omit [VCVCompatible StmtIn] [∀ i, SampleableType (pSpec.Challenge i)] in
/-- The delegated extractor is executed after the verifier, in the same oracle computation.
Thus interpreting this equality preserves all shared-state correlations, including fresh
queries made by the extractor. -/
private lemma fsKSExecution_eq_map_srKSExecution {Salt : Type} [VCVCompatible Salt]
    {κ : Type} {auxSpec : OracleSpec κ}
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (E : Extractor.StateRestoration oSpec (StmtIn × Salt) WitIn Unit pSpec)
    (P : OracleComp ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + auxSpec)
      (StmtIn × FSSaltedProof pSpec Salt)) :
    (do
      let ⟨⟨x, π⟩, tr⟩ ← (simulateQ loggingOracle P).run
      let a ← liftComp (simulateQ loggingOracle (fsSaltedVerify V x π).run).run
        ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + auxSpec)
        (h := instMonadLiftTOfMonadLift
          (OracleQuery (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec))
          (OracleQuery (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec))
          (OracleQuery ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + auxSpec)))
      let w ← liftComp (fsSRDelegatingExtractor E x π tr.fst a.2).run
        ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + auxSpec)
      pure (x, w, a.1)) =
    (fun out : (StmtIn × Salt) × Option WitIn × Option StmtOut × Unit =>
      (out.1.1, out.2.1, out.2.2.1)) <$> (do
      let ⟨⟨stmtIn, messages, _unit⟩, tr⟩ ←
        (simulateQ loggingOracle (srInducedProverKS P)).run
      let transcript ← liftComp (messages.deriveTranscriptSR (oSpec := oSpec) stmtIn)
        ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + auxSpec)
      let ⟨stmtOut, tr_V⟩ ← liftComp (simulateQ loggingOracle
        ((saltedIPVerifier (Salt := Salt) V).run stmtIn transcript).run).run _
      let w ← liftComp (E stmtIn () transcript tr.fst tr_V).run
        ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + auxSpec)
      pure (stmtIn, w, stmtOut, ())) := by
  have h := congrArg (fun computation => computation >>= fun out => do
    let w ← liftComp out.2.1.run
      ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + auxSpec)
    pure (out.1, w, out.2.2)) (fsKSReadout_eq_map_srKSReadout V E P)
  simpa only [bind_assoc, bind_map_left, map_bind, map_pure, pure_bind] using h

omit [VCVCompatible StmtIn] in
/-- Executing the delegated extractor gives exactly the SR extraction-failure probability.
This uses the same initial state and handler throughout, not a fresh oracle realization. -/
private lemma fsKSExecution_failure_eq {Salt : Type} [VCVCompatible Salt]
    {κ : Type} {auxSpec : OracleSpec κ} (auxImpl : QueryImpl auxSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (E : Extractor.StateRestoration oSpec (StmtIn × Salt) WitIn Unit pSpec)
    (fsInit : ProbComp (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id))
    (fsImpl : QueryImpl oSpec
      (StateT (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp))
    (relIn : Set (StmtIn × WitIn)) (langOut : Set StmtOut)
    (P : OracleComp ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + auxSpec)
      (StmtIn × FSSaltedProof pSpec Salt)) :
    Pr{let result ← do
      StateT.run' (simulateQ ((((fsImpl.addLift srChallengeQueryImpl') :
        QueryImpl (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)
          (StateT (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id)
            ProbComp)).addLift auxImpl) :
        QueryImpl ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + auxSpec)
          (StateT (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp)) (do
        let ⟨⟨x, π⟩, tr⟩ ← (simulateQ loggingOracle P).run
        let a ← liftComp (simulateQ loggingOracle (fsSaltedVerify V x π).run).run
          ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + auxSpec)
          (h := instMonadLiftTOfMonadLift
            (OracleQuery (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec))
            (OracleQuery (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec))
            (OracleQuery ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + auxSpec)))
        let w ← liftComp (fsSRDelegatingExtractor E x π tr.fst a.2).run
          ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + auxSpec)
        pure (x, w, a.1))) (← fsInit)}[nargKSFailEvent relIn langOut result] =
      Verifier.StateRestoration.coinKSExperimentProb fsInit fsImpl auxImpl E
        (relInSalted relIn) (unitOutputRelation langOut) (saltedIPVerifier V)
        (srInducedProverKS P) := by
  rw [fsKSExecution_eq_map_srKSExecution V E P]
  simp only [simulateQ_map, StateT.run'_map']
  unfold Verifier.StateRestoration.coinKSExperimentProb
  simp only [bind_map_left]
  apply congrArg (fun program : ProbComp Prop => 𝒟[program] {True})
  apply bind_congr
  intro table
  apply bind_congr
  rintro ⟨⟨x, salt⟩, witness, output, seed⟩
  cases seed
  cases witness <;> cases output <;> rfl

omit [VCVCompatible StmtIn] in
/-- The shared-oracle single-salt NARG game has exactly the induced state-restoration
failure probability, with the same prover, uniform draws, and canonical verifier transcript. -/
theorem fsKSShared_failure_eq {Salt : Type} [VCVCompatible Salt]
    {κ κE : Type} {auxSpec : OracleSpec κ} (auxImpl : QueryImpl auxSpec ProbComp)
    {auxSpecE : OracleSpec κE} (auxImplE : QueryImpl auxSpecE ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (E : Extractor.StateRestoration oSpec (StmtIn × Salt) WitIn Unit pSpec)
    (fsInit : ProbComp (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id))
    (fsImpl : QueryImpl oSpec
      (StateT (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp))
    (relIn : Set (StmtIn × WitIn)) (langOut : Set StmtOut)
    (P : OracleComp ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + auxSpec)
      (StmtIn × FSSaltedProof pSpec Salt)) :
    Pr{let result ← adaptiveNARGKnowledgeSoundnessExpWithCoins fsInit
        (fsImpl.addLift srChallengeQueryImpl') auxImpl auxImplE
        (Verifier.singleSaltFiatShamir (Salt := Salt) V)
        (fsSRDelegatingNargExtractor E) P}[nargKSFailEvent relIn langOut result] =
      Verifier.StateRestoration.coinKSExperimentProb fsInit fsImpl auxImpl E
        (relInSalted relIn) (unitOutputRelation langOut) (saltedIPVerifier V)
        (srInducedProverKS P) := by
  have hbase {κ' : Type} {aSpec : OracleSpec κ'} (aImpl : QueryImpl aSpec ProbComp) :
      (((fsImpl.addLift srChallengeQueryImpl' :
        QueryImpl (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)
          (StateT (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp)).addLift
          aImpl) ∘ₛ (fun q => liftM (OracleSpec.query q) :
            QueryImpl oSpec (OracleComp
              ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + aSpec)))) = fsImpl := by
    funext q
    simp only [QueryImpl.compose]
    change simulateQ _
      (liftM (((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + aSpec).query
        (Sum.inl (Sum.inl q))) :
        OracleComp ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + aSpec) _) = fsImpl q
    simp [QueryImpl.addLift]
  unfold adaptiveNARGKnowledgeSoundnessExpWithCoins fsSRDelegatingNargExtractor
    runVerifierWithLog withQueryLog
  simpa only [OptionT.run_mk, simulateQ_bind, simulateQ_pure,
    QueryImpl.liftTarget_self, QueryImpl.simulateQ_add_liftComp_left,
    OracleComp.liftComp_def, ← QueryImpl.simulateQ_compose,
    bind_assoc, pure_bind, fsSaltedNIV_verify, hbase, OracleSpec.loggingOracle] using
    fsKSExecution_failure_eq auxImpl V E fsInit fsImpl relIn langOut P

omit [VCVCompatible StmtIn] in
/-- Transport a supplied SR extractor, without choosing it after the query budget.
The conclusion uses the NARG extractor interface documented above. -/
theorem single_salt_fiat_shamir_knowledge_soundness_of_fixedExtractor
    {Salt : Type} [VCVCompatible Salt]
    {κ : Type} (auxSpec : OracleSpec κ) (auxImpl : QueryImpl auxSpec ProbComp)
    -- The extractor's own helper/sampler oracle (`P`-independent), generic so the caller picks it
    -- (DSFS passes `(Unit →ₒ U)` for Construction 6.3's D2STrace; the bare FS extractor ignores
    -- it).
    {κE : Type} (auxSpecE : OracleSpec κE) (auxImplE : QueryImpl auxSpecE ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (relIn : Set (StmtIn × WitIn)) (langOut : Set StmtOut)
    (fsInit : ProbComp (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id))
    (fsImpl : QueryImpl oSpec
      (StateT (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp))
    (E : Extractor.StateRestoration oSpec (StmtIn × Salt) WitIn Unit pSpec)
    (srBound : Prover.StateRestoration.KnowledgeSoundnessWithCoins oSpec (StmtIn × Salt) Unit
      pSpec auxSpec → Prop)
    (bound : OracleComp ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + auxSpec)
      (StmtIn × FSSaltedProof pSpec Salt) → Prop)
    (hBound : ∀ P, bound P → srBound (srInducedProverKS P))
    (ε : ENNReal)
    -- Coin-bearing SR knowledge soundness of the salted IP.
    (h_sr_ks : Verifier.StateRestoration.knowledgeSoundnessWithCoinsWithExtractor
        fsInit fsImpl auxSpec auxImpl
        (relInSalted (Salt := Salt) relIn) (unitOutputRelation langOut)
        (saltedIPVerifier (Salt := Salt) V)
        E srBound ε) :
    -- Adaptive, coin-bearing KS of the single-salt FS argument,
    -- phrased as a property of the NARG verifier `Verifier.singleSaltFiatShamir V`.
    Verifier.adaptiveNARGKnowledgeSoundnessWithCoinsWithExtractor (WitIn := WitIn)
      (init := fsInit) (impl := fsImpl.addLift srChallengeQueryImpl')
      auxImpl auxImplE
      (verifier := Verifier.singleSaltFiatShamir (Salt := Salt) V)
      relIn langOut
      (fsSRDelegatingNargExtractor E)
      (bound := bound) ε := by
  intro P hP
  rw [fsKSShared_failure_eq auxImpl auxImplE V E fsInit fsImpl relIn langOut P]
  exact h_sr_ks (srInducedProverKS P) (hBound P hP)

omit [VCVCompatible StmtIn] [DecidableEq StmtIn]
  [∀ i, DecidableEq (pSpec.Message i)] in
/-- **Theorem 3.19 of CO25, adapted to the NARG extractor interface** — One SR extractor yields
one NARG extractor for the entire bound/error family. The conclusion permits randomness and both
logs; it does not establish the deterministic, prover-trace-only contract of Definition 3.6. -/
theorem single_salt_fiat_shamir_knowledge_soundness
    {Salt B : Type} [VCVCompatible Salt]
    {κ : Type} (auxSpec : OracleSpec κ) (auxImpl : QueryImpl auxSpec ProbComp)
    {κE : Type} (auxSpecE : OracleSpec κE) (auxImplE : QueryImpl auxSpecE ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (relIn : Set (StmtIn × WitIn)) (langOut : Set StmtOut)
    (fsInit : ProbComp (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id))
    (fsImpl : QueryImpl oSpec
      (StateT (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp))
    (srBound : B → Prover.StateRestoration.KnowledgeSoundnessWithCoins oSpec
      (StmtIn × Salt) Unit pSpec auxSpec → Prop)
    (bound : B → OracleComp ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + auxSpec)
      (StmtIn × FSSaltedProof pSpec Salt) → Prop)
    (hBound : ∀ b P, bound b P → srBound b (srInducedProverKS P))
    (ε : B → ENNReal)
    (hSR : Verifier.StateRestoration.knowledgeSoundnessWithCoins
      fsInit fsImpl auxSpec auxImpl (relInSalted relIn) (unitOutputRelation langOut)
      (saltedIPVerifier (Salt := Salt) V) srBound ε) :
    Verifier.adaptiveNARGKnowledgeSoundnessWithCoins
      fsInit (fsImpl.addLift srChallengeQueryImpl') auxImpl auxImplE
      (Verifier.singleSaltFiatShamir (Salt := Salt) V) relIn langOut bound ε := by
  classical
  let _ : DecidableEq StmtIn := Classical.decEq _
  let _ (i : pSpec.MessageIdx) : DecidableEq (pSpec.Message i) := Classical.decEq _
  let _ (i : pSpec.ChallengeIdx) : DecidableEq (pSpec.Challenge i) := Classical.decEq _
  obtain ⟨E, hE⟩ := hSR
  refine ⟨fsSRDelegatingNargExtractor E, ?_⟩
  intro b
  exact single_salt_fiat_shamir_knowledge_soundness_of_fixedExtractor
    auxSpec auxImpl auxSpecE auxImplE V relIn langOut fsInit fsImpl E
    (srBound b) (bound b) (hBound b) (ε b) (hE b)


end SingleSaltSecurity
