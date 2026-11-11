/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Core.Completeness
public import ArkLib.Interaction.Core.Legacy.OracleAppend
public import ArkLib.Interaction.Core.Legacy.OracleKnowledge
public import ArkLib.Interaction.Core.Legacy.PureSlots
public import ArkLib.Interaction.Core.Security.Agreement
public import ArkLib.ProofSystem.Sumcheck.Core.Indexed

/-!
# The interaction-layer Sumcheck is the embedded legacy Sumcheck

This file proves that the interaction-layer Sumcheck verifier and the embedding
`embedOracleVerifier` of the legacy oracle verifier `Spec.oracleVerifier` produce equal programs
at the common observation: the legacy result `LegacyResult`, after reindexing the challenges to
the legacy challenge oracle and decoding the transcript.

The proof runs through three correspondences.

* **Tree and transcripts.** The Sumcheck tree `protocol R deg n` is the oracle tree of the legacy
  protocol specification (`protocol_eq`), and decoding a transcript of the oracle tree is
  `decodeTranscript` (`oracleDecode_eq_decodeTranscript`).
* **Decision.** On every completed run, the decision of the Sumcheck verifier and the decision of
  the embedded legacy verifier, read on the Sumcheck tree (`legacyVerifier`), are the same program
  before any query is answered (`decide_eq_legacy`). Both run the legacy decision fold, and
  `route` sends each legacy message query to the node that the embedding's routing `queryMsg`
  selects on the legacy oracle tree (`route_heq_queryMsg`). Hence the two verifiers make the same
  queries in the same order, and their logged runs are equal (`runWithLog_eq_legacy`).
* **Challenges.** The uniform challenge oracle of the Sumcheck tree is the reindexed uniform legacy
  challenge oracle (`challengeQueryImpl_eq_legacy`).

The main results are:

* `run_eq_legacy`: for every prover, the reindexed and finalized run of the Sumcheck verifier is
  the reindexed and finalized run of the embedded legacy verifier against the same prover. The
  result keeps the decoded transcript, the prover's output and the accepted statement separately.
* `run_legacyProver`: against the embedded legacy honest prover, that program is the legacy run
  `OracleReduction.run`. The legacy honest prover's challenge slots are `pure`
  (`legacyProver_pureChallengeSlots`), so the exchange of challenge sampling and the prover's
  challenge step holds as program equality.
* `verifier_agrees`: the two verifiers agree in the sense of `OracleVerifier.Agrees`. With the
  transport lemmas of `OracleVerifier` along `protocol_eq`, this carries every security notion of
  the classical model from the embedded legacy verifier to the Sumcheck verifier. The transfers
  themselves are in `LegacyCompleteness`, `Soundness`, `Knowledge` and `RoundByRound`.
* `decide_ambient_trace`: once the input and path oracles are answered from the run's data, both
  decisions are `pure` of the legacy verdict in every lawful monad, so they make no ambient query.
-/

@[expose] public section

namespace Sumcheck.Core
open scoped ENNReal NNReal
open Polynomial PFunctor FreeM Interaction.Core Interaction.TwoParty.Lens Interaction.Oracle
  OracleComp OracleSpec ProtocolSpec Interaction.Core.Legacy

/-- Transporting a constant language problem changes only its context type. -/
@[simp] theorem _root_.Interaction.Core.OracleVerifier.langProblem_cast
    {s s' : OracleProtocol} {T : Type} (e : s' = s) (L : Set T) :
    (e ▸ (langProblem (Ctx := Path s') L)) = langProblem (Ctx := Path s) L := by
  subst e
  rfl

/-! ## Tree and transcript correspondence -/

section Tree

/-- One node followed by a fixed continuation, at equal nodes and continuations. -/
private theorem liftBind_congr' {P : PFunctor.{1, 0}} {a a' : P.A} {t t' : FreeM P PUnit.{1}}
    (ha : a = a') (ht : t = t') :
    (FreeM.liftBind a fun _ => t) = FreeM.liftBind a' fun _ => t' := by
  subst ha ht; rfl

/-- Two nodes followed by a fixed continuation, at equal nodes and continuations. -/
private theorem liftBind₂_congr {P : PFunctor.{1, 0}} {a a' b b' : P.A}
    {t t' : FreeM P PUnit.{1}} (ha : a = a') (hb : b = b') (ht : t = t') :
    (FreeM.liftBind a fun _ => FreeM.liftBind b fun _ => t) =
      FreeM.liftBind a' fun _ => FreeM.liftBind b' fun _ => t' := by
  subst ha hb ht; rfl

variable (R : Type) [CommSemiring R] (deg : ℕ)


/-- The interaction-layer Sumcheck tree is the oracle tree of the legacy Sumcheck protocol. -/
theorem protocol_eq : ∀ n, protocol R deg n = oracleProtocol (Spec.pSpec R deg n)
  | 0 => rfl
  | n + 1 => by
    rw [protocol_succ, protocol_eq n]
    let N := Fin.vsum fun _ : Fin n => 2
    let A := Spec.SingleRound.pSpec R deg
    let B := Spec.pSpec R deg n
    change _ = @chain (2 + N) OraclePoly (oracleRound (A ++ₚ B)) 0 (2 + N) (by omega)
    rw [chain_congr_len _ 0 (Nat.add_comm 2 N) _ (by omega)]
    refine liftBind₂_congr ?_ ?_ ?_
    · exact (oracleRound_append_castAdd A B 0).symm
    · exact (oracleRound_append_castAdd A B 1).symm
    · exact (chain_natAdd (a := 2) _ _ (oracleRound_append_natAdd A B) 0 N (by omega)
        (by omega)).symm

variable {R deg}

/-- **Transcript correspondence.** Decoding an interaction-layer Sumcheck transcript gives the
legacy full transcript that the legacy embedding reads off the same path. -/
theorem oracleDecode_eq_decodeTranscript : ∀ (n : ℕ) (tr : PathAlong oracleSig (protocol R deg n))
    (tr' : PathAlong oracleSig (oracleProtocol (Spec.pSpec R deg n))), HEq tr tr' →
      oracleDecode (Spec.pSpec R deg n) tr' = decodeTranscript n tr
  | 0, _, _, _ => funext fun i => i.elim0
  | n + 1, ⟨msg, ⟨chal, tail⟩⟩, tr', htr => by
    let N := Fin.vsum fun _ : Fin n => 2
    let A := Spec.SingleRound.pSpec R deg
    let B := Spec.pSpec R deg n
    have hlen : N + 2 = 2 + N := Nat.add_comm N 2
    have hch : @chain (2 + N) OraclePoly (oracleRound (A ++ₚ B)) 0 (2 + N) (by omega) =
        chain (oracleRound (A ++ₚ B)) 0 (N + 2) (by omega) :=
      chain_congr_len _ 0 hlen.symm _ _
    change decodeFrom oracleSig (oracleRound (A ++ₚ B)) (fun j => oracleMoveEquiv (A ++ₚ B) j _ rfl)
      0 (2 + N) _ default tr' = _
    obtain ⟨p, hp⟩ : ∃ p : PathAlong oracleSig (chain (oracleRound (A ++ₚ B)) 0 (N + 2)
        (by omega)), HEq tr' p := ⟨cast (congrArg _ hch) tr', (cast_heq _ _).symm⟩
    rw [decodeFrom_congr_len _ _ _ 0 hlen _ _ _ p tr' hp.symm]
    obtain ⟨d0, d1, rest⟩ := p
    have hrest : protocol R deg n = chain (oracleRound (A ++ₚ B)) 2 N (by omega) :=
      (protocol_eq R deg n).trans
        (chain_natAdd (a := 2) _ _ (oracleRound_append_natAdd A B) 0 N (by omega) (by omega)).symm
    obtain ⟨h0, h12⟩ := heq_pathAlong_liftBind oracleSig
      (oracleRound_append_castAdd A B 0).symm
      (liftBind_congr' (oracleRound_append_castAdd A B 1).symm hrest) (htr.trans hp)
    obtain ⟨h1, h2⟩ := heq_pathAlong_liftBind oracleSig
      (oracleRound_append_castAdd A B 1).symm hrest h12
    change _ = decodeTranscript (n + 1) (consTranscript msg chal tail)
    rw [decodeTranscript_succ]
    funext i
    refine Fin.addCases (m := 2) (n := N) (fun i => ?_) (fun j => ?_) i
    · rw [FullTranscript.append, Fin.happend_left]
      refine eq_of_heq (HEq.trans ?_ (cast_heq _ _).symm)
      match i with
      | ⟨0, _⟩ =>
        refine (heq_of_eq (decodeFrom_succ_self oracleSig _ _ 0 (N + 1) _ default d0
          ⟨d1, rest⟩)).trans ?_
        exact (oracleMoveEquiv_heq _ _ _ _ d0).trans h0.symm
      | ⟨1, _⟩ =>
        refine (heq_of_eq (decodeFrom_succ_self oracleSig _ _ 1 N (by omega) _ d1 rest)).trans ?_
        exact (oracleMoveEquiv_heq _ _ _ _ d1).trans h1.symm
    · rw [FullTranscript.append, Fin.happend_right]
      refine eq_of_heq (HEq.trans ?_ (cast_heq _ _).symm)
      let tail' : PathAlong oracleSig (oracleProtocol B) :=
        cast (congrArg (PathAlong oracleSig) (protocol_eq R deg n)) tail
      have ih := oracleDecode_eq_decodeTranscript n tail tail' (cast_heq _ _).symm
      refine (decodeFrom_append_natAdd A B 0 N (by omega) (by omega) _ default rest tail'
        (h2.symm.trans (cast_heq _ _).symm) j (Nat.zero_le _)).trans ?_
      exact heq_of_eq (congrFun ih j)

end Tree

/-! ## The decision in any lawful monad -/

section DecideM
variable {R : Type} [CommSemiring R] [DecidableEq R] [SampleableType R] {deg n : ℕ}
  {d : ℕ} (D : Fin d ↪ R) {ι : Type} {ambient : OracleSpec ι}

/-- On any completed run, the decision returns the legacy verdict of the decoded transcript, for
ambient queries answered in any lawful monad. -/
theorem simulateQ_decide_monad {m : Type → Type} [Monad m] [LawfulMonad m]
    (amb : QueryImpl ambient m) (stmt : Spec.StatementRound R n 0)
    (data : ∀ i, Spec.OracleStatement R n deg i) (tr : PathAlong oracleSig (protocol R deg n)) :
    simulateQ (QueryImpl.addLift amb ((pathResources (Spec.polynomialFamily R n deg)
        (protocol R deg n)
        (projectPathAlong oracleSig _ tr)).answer (data, payloads _ tr)))
      ((verifier R deg n D ambient).decide stmt _ (toView _ tr)).run =
      (pure (legacyVerdict R deg n D ambient stmt (decodeTranscript n tr)) : m _) := by
  rw [verifier_decide, simulateQ_decisionLift_monad, viewChallenges_toView]
  congr 1
  exact QueryImpl.simulateQ_simulateQ_eq_of_apply (simulateQ_route n tr) _

end DecideM
/-! ## Routing correspondence -/

section Routing
variable {R : Type} [CommSemiring R] {deg : ℕ}

/-- **Routing correspondence.** `route` sends each legacy message query to the node of the Sumcheck
tree that the routing `queryMsg` of the legacy embedding selects on the legacy oracle tree, with
the same query. -/
theorem route_heq_queryMsg : ∀ (n : ℕ) (p : FreeM.Path (protocol R deg n))
    (p' : FreeM.Path (oracleProtocol (Spec.pSpec R deg n))), HEq p p' →
    ∀ (i : (Spec.pSpec R deg n).MessageIdx)
      (q : OracleInterface.Query ((Spec.pSpec R deg n).Message i)),
      HEq (route R deg n p ⟨i, q⟩)
        (queryMsg (pSpec := Spec.pSpec R deg n) 0 _ (Nat.zero_add _) p' i (Nat.zero_le _) q)
  | 0, _, _, _, i, _ => i.1.elim0
  | n + 1, ⟨⟨⟩, ⟨⟨⟩, p⟩⟩, p', hp, i, q => by
    let N := Fin.vsum fun _ : Fin n => 2
    let A := Spec.SingleRound.pSpec R deg
    let B := Spec.pSpec R deg n
    have hlen : 2 + N = N + 2 := Nat.add_comm 2 N
    have hrest : protocol R deg n = chain (oracleRound (A ++ₚ B)) 2 N (by omega) :=
      (protocol_eq R deg n).trans
        (chain_natAdd (a := 2) _ _ (oracleRound_append_natAdd A B) 0 N (by omega) (by omega)).symm
    have htail : (FreeM.liftBind (OraclePos.challenge R) fun _ => protocol R deg n) =
        chain (oracleRound (A ++ₚ B)) 1 (N + 1) (by omega) :=
      liftBind_congr' (oracleRound_append_castAdd A B 1).symm hrest
    obtain ⟨p'', hp''⟩ : ∃ p'' : FreeM.Path
        (@chain (2 + N) OraclePoly (oracleRound (A ++ₚ B)) 0 (N + 2) (by omega)), HEq p' p'' :=
      ⟨cast (congrArg FreeM.Path (chain_congr_len _ 0 hlen _ _)) p', (cast_heq _ _).symm⟩
    have hp0 := hp.trans hp''
    obtain ⟨b0, p1⟩ := p''
    have h1 : HEq (⟨⟨⟩, p⟩ : FreeM.Path (FreeM.liftBind (OraclePos.challenge R) fun _ =>
        protocol R deg n)) p1 :=
      heq_path_liftBind (oracleRound_append_castAdd A B 0).symm htail hp0
    obtain ⟨b1, p2⟩ := p1
    have h2 : HEq p p2 :=
      heq_path_liftBind (oracleRound_append_castAdd A B 1).symm hrest h1
    obtain ⟨s, rfl⟩ := (MessageIdx.sumEquiv (pSpec₁ := A) (pSpec₂ := B)).surjective i
    refine (heq_of_eq (route_succ_sumEquiv _ p s q)).trans ?_
    refine HEq.trans ?_ (queryMsg_congr_len (P := A ++ₚ B) 0 hlen.symm _ _ ⟨b0, b1, p2⟩ p'
      hp''.symm _ _ q)
    rcases s with i0 | i'
    · obtain rfl := Unique.eq_default i0
      obtain ⟨q', hq, hk⟩ := queryAlongHEq_heq _ _
        (by simp [MessageIdx.inl, ProtocolSpec.append, Fin.vappend_eq_append, Fin.append_left])
        (message_interface_inl (pSpec₂ := B) default).symm
        (fun q' => roundRoute R deg n p ⟨default, q'⟩) q
      refine hk.trans (HEq.symm (queryMsgNode_heq_root (P := A ++ₚ B) ⟨0, by omega⟩
        (oracleSuffix (A ++ₚ B) 1 (N + 1) (by omega)) _ _ rfl
        (Fin.vappend_left A.dir B.dir 0) ⟨b0, b1, p2⟩ _ rfl _ q
        (X := R⦃≤ deg⦄[X]) (t := FreeM.liftBind (OraclePos.challenge R) fun _ => protocol R deg n)
        (r := ⟨⟨⟩, p⟩) (Fin.vappend_left A.«Type» B.«Type» 0)
        (fun _ => (message_interface_inl (pSpec₂ := B) default).symm) htail.symm h1.symm hq))
    · obtain ⟨q', hq, hk⟩ := queryAlongHEq_heq _ _
        (Fin.vappend_right A.«Type» B.«Type» i'.1)
        (message_interface_inr (pSpec₁ := A) i').symm
        (fun q' => simulateQ (tailLift R deg n p) (route R deg n p ⟨i', q'⟩)) q
      refine hk.trans (HEq.symm (queryMsgNode_heq_liftRight (P := A ++ₚ B) ⟨0, by omega⟩
        (oracleSuffix (A ++ₚ B) 1 (N + 1) (by omega)) _ _ rfl
        (Fin.vappend_left A.dir B.dir 0) ⟨b0, b1, p2⟩ _ (by simp [MessageIdx.inr]) _ q
        (X := R⦃≤ deg⦄[X]) (t := FreeM.liftBind (OraclePos.challenge R) fun _ => protocol R deg n)
        (r := ⟨⟨⟩, p⟩) (x := route R deg n p ⟨i', q'⟩) (Fin.vappend_left A.«Type» B.«Type» 0)
        (fun _ => (message_interface_inl (pSpec₂ := B) default).symm) htail.symm h1.symm
        (response_eq (Fin.vappend_right A.«Type» B.«Type» i'.1)
          (message_interface_inr (pSpec₁ := A) i').symm hq) fun hlt => ?_))
      refine (queryMsgNode_heq_challenge (P := A ++ₚ B) ⟨1, by omega⟩
        (oracleSuffix (A ++ₚ B) 2 N (by omega)) _ _ rfl
        (Fin.vappend_left A.dir B.dir 1) ⟨b1, p2⟩ _ _ q (by simp [MessageIdx.inr]; omega)).trans ?_
      have hB : HEq p2 (cast (congrArg FreeM.Path (protocol_eq R deg n)) p) :=
        h2.symm.trans (cast_heq _ _).symm
      refine (queryMsg_append_natAdd A B 0 N (by omega) (by omega) p2 _ hB i' _ (Nat.zero_le _) q
        q' hq).trans ?_
      exact (route_heq_queryMsg n p _ (cast_heq _ _).symm i' q').symm

end Routing

/-! ## The embedded legacy verifier on the Sumcheck tree -/

section Simulate

/-- Simulating heterogeneously equal programs by one family of handlers, at equal indices, gives
heterogeneously equal programs. -/
private theorem simulateQ_heq_of_heq {X : Type*} {I J : X → Type} (S : ∀ x, OracleSpec (I x))
    (T : ∀ x, OracleSpec (J x)) (f : ∀ x, QueryImpl (S x) (OracleComp (T x))) {α : Type}
    {x x' : X} (hx : x = x') {oa : OracleComp (S x) α} {oa' : OracleComp (S x') α}
    (h : HEq oa oa') : HEq (simulateQ (f x) oa) (simulateQ (f x') oa') := by
  subst hx; cases h; rfl

/-- Simulating one program by handlers that agree query by query, at equal indices of the
target, gives heterogeneously equal programs. -/
private theorem simulateQ_heq_of_apply {κ : Type} {spec : OracleSpec κ} {X : Type*} {J : X → Type}
    (T : ∀ x, OracleSpec (J x)) {x x' : X} (hx : x = x') (f : QueryImpl spec (OracleComp (T x)))
    (g : QueryImpl spec (OracleComp (T x'))) (h : ∀ q, HEq (f q) (g q)) {α : Type}
    (oa : OracleComp spec α) : HEq (simulateQ f oa) (simulateQ g oa) := by
  subst hx
  obtain rfl : f = g := funext fun q => eq_of_heq (h q)
  rfl

end Simulate

section LegacyVerifier
variable (R : Type) [CommSemiring R] [DecidableEq R] [SampleableType R] (deg n : ℕ)
  {d : ℕ} (D : Fin d ↪ R) {ι : Type} (ambient : OracleSpec ι)

/-- The target of the decision's queries on a path of an oracle tree: the ambient oracle, the
input polynomial and the path's oracles. -/
private abbrev decisionSpec (x : Σ s : OracleProtocol.{0}, Path s) :=
  ambient + (pathResources (Spec.polynomialFamily R n deg) x.1 x.2).spec

/-- Lift path-oracle queries into the decision's query interface, on any oracle tree. -/
private def pathLift (x : Σ s : OracleProtocol.{0}, Path s) :
    QueryImpl (pathFamily x.1 x.2).spec (OracleComp (decisionSpec R deg n ambient x)) :=
  fun q => liftM ((decisionSpec R deg n ambient x).query (.inr (.inr q)))

variable {R deg n ambient}

omit [DecidableEq R] [SampleableType R] in
/-- The embedding's routing of a legacy message query, lifted into the decision's interface, is a
query of the path oracles lifted by `pathLift`. -/
private theorem decisionImpl_message (p : Path (oracleProtocol (Spec.pSpec R deg n)))
    (q : [(Spec.pSpec R deg n).Message]ₒ.Domain) :
    decisionImpl (oSpec := ambient) (OStmtIn := Spec.OracleStatement R n deg) p (.inr (.inr q)) =
      simulateQ (pathLift R deg n ambient ⟨_, p⟩)
        (queryMsg (pSpec := Spec.pSpec R deg n) 0 _ _ p q.1 (Nat.zero_le _) q.2) := by
  change simulateQ _ (simulateQ _ _) = _
  refine QueryImpl.simulateQ_simulateQ_eq_of_apply (fun t => ?_) _
  simp [pathLift]
  rfl

variable (R deg n ambient) [∀ t, Inhabited (ambient.Range t)]

/-- The embedding of the legacy Sumcheck oracle verifier, read on the interaction-layer Sumcheck
tree. -/
noncomputable def legacyVerifier : OracleVerifier ambient (protocol R deg n)
    (Spec.StatementRound R n 0) (fun _ => Spec.StatementRound R n (Fin.last n))
    (Spec.polynomialFamily R n deg) (fun _ => Spec.polynomialFamily R n deg) :=
  (protocol_eq R deg n).symm ▸ embedOracleVerifier (Spec.oracleVerifier R deg D n ambient)

variable {R deg n D ambient}

/-- On corresponding transcripts, the decision of the Sumcheck verifier and the decision of the
embedded legacy verifier are the same program before any query is answered: both run the legacy
decision fold on the same challenges, and each message query goes to the same oracle node. -/
theorem decide_heq_embed (stmt : Spec.StatementRound R n 0)
    (tr : PathAlong oracleSig (protocol R deg n))
    (tr' : PathAlong oracleSig (oracleProtocol (Spec.pSpec R deg n))) (htr : HEq tr tr') :
    HEq ((verifier R deg n D ambient).decide stmt _ (toView _ tr))
      ((embedOracleVerifier (Spec.oracleVerifier R deg D n ambient)).decide stmt _
        (toView _ tr')) := by
  have hp : HEq (projectPathAlong oracleSig _ tr) (projectPathAlong oracleSig _ tr') := by
    have key : ∀ (s s' : OracleProtocol.{0}) (_ : s = s') (t : PathAlong oracleSig s)
        (t' : PathAlong oracleSig s'), HEq t t' →
          HEq (projectPathAlong oracleSig s t) (projectPathAlong oracleSig s' t') := by
      intro s s' e t t' h; subst e; cases h; rfl
    exact key _ _ (protocol_eq R deg n) tr tr' htr
  have hx : (⟨protocol R deg n, projectPathAlong oracleSig _ tr⟩ : Σ s : OracleProtocol.{0},
      Path s) = ⟨_, projectPathAlong oracleSig _ tr'⟩ := Sigma.ext (protocol_eq R deg n) hp
  have hch : viewChallenges (toView _ tr) = Legacy.viewChallenges (toView _ tr').val := by
    rw [viewChallenges_toView, Legacy.viewChallenges_toView,
      oracleDecode_eq_decodeTranscript n tr tr' htr]
  change HEq (simulateQ (decisionLift R deg n ambient _) (simulateQ (route R deg n _)
      (legacyProgram R deg n D ambient stmt (viewChallenges (toView _ tr)))))
    (simulateQ (decisionImpl _) (OracleComp.liftComp (legacyProgram R deg n D ambient stmt
      (Legacy.viewChallenges (toView _ tr').val)) _))
  rw [hch, OracleComp.liftComp_def, ← QueryImpl.simulateQ_compose,
    ← QueryImpl.simulateQ_compose]
  refine simulateQ_heq_of_apply (decisionSpec R deg n ambient) hx _ _ (fun ⟨i, q⟩ => ?_) _
  rw [QueryImpl.apply_compose, QueryImpl.apply_compose]
  change _ ≍ simulateQ (decisionImpl _) (liftM ((ambient + ([Spec.OracleStatement R n deg]ₒ +
    [(Spec.pSpec R deg n).Message]ₒ)).query (.inr (.inr ⟨i, q⟩))))
  rw [simulateQ_spec_query]
  refine HEq.trans ?_ (heq_of_eq (decisionImpl_message _ ⟨i, q⟩).symm)
  exact simulateQ_heq_of_heq (fun x => (pathFamily x.1 x.2).spec)
    (decisionSpec R deg n ambient) (pathLift R deg n ambient) hx
    (route_heq_queryMsg n _ _ hp i q)

/-- **Decision correspondence.** On every completed run, the decision of the Sumcheck verifier is
the decision of the embedded legacy verifier read on the Sumcheck tree, as a program before any
query is answered. -/
theorem decide_eq_legacy (stmt : Spec.StatementRound R n 0)
    (tr : PathAlong oracleSig (protocol R deg n)) :
    (verifier R deg n D ambient).decide stmt _ (toView _ tr) =
      (legacyVerifier R deg n D ambient).decide stmt _ (toView _ tr) := by
  have htr : HEq tr (cast (congrArg (PathAlong oracleSig) (protocol_eq R deg n)) tr) :=
    (cast_heq _ _).symm
  exact eq_of_heq ((decide_heq_embed stmt tr _ htr).trans
    (OracleVerifier.decide_cast (inputs := Spec.polynomialFamily R n deg)
      (outputs := Spec.polynomialFamily R n deg)
      (protocol_eq R deg n).symm (embedOracleVerifier (Spec.oracleVerifier R deg D n ambient))
      stmt tr _ htr).symm)

/-- On every completed run, the Sumcheck verifier and the embedded legacy verifier keep the same
output data: the input polynomial. -/
theorem outputMap_eq_legacy (stmt : Spec.StatementRound R n 0)
    (data : ∀ i, Spec.OracleStatement R n deg i) (tr : PathAlong oracleSig (protocol R deg n)) :
    ((verifier R deg n D ambient).outputMap stmt _ (toView _ tr)).f
        (data, payloads _ tr) =
      ((legacyVerifier R deg n D ambient).outputMap stmt _ (toView _ tr)).f
        (data, payloads _ tr) := by
  have htr : HEq tr (cast (congrArg (PathAlong oracleSig) (protocol_eq R deg n)) tr) :=
    (cast_heq _ _).symm
  refine Eq.trans ?_
    (OracleVerifier.outputMap_cast (inputs := Spec.polynomialFamily R n deg)
      (outputs := Spec.polynomialFamily R n deg) (protocol_eq R deg n).symm
      (embedOracleVerifier (Spec.oracleVerifier R deg D n ambient)) stmt data _ _ htr).symm
  exact (embedOracleVerifier_outputMap_f (Spec.oracleVerifier R deg D n ambient) stmt data _).symm

variable (R deg n D ambient)

/-- **Agreement.** The Sumcheck verifier agrees with the embedded legacy verifier, so every
security notion of the classical model transfers between them. -/
theorem verifier_agrees :
    OracleVerifier.Agrees (verifier R deg n D ambient) (legacyVerifier R deg n D ambient) :=
  OracleVerifier.Agrees.of_decide_eq decide_eq_legacy outputMap_eq_legacy

/-- **Query trace.** For every prover, the logged run of the Sumcheck verifier is the logged run of
the embedded legacy verifier read on the Sumcheck tree. The log records the decision's queries
before they are answered, so the two verifiers make the same queries in the same order. -/
theorem runWithLog_eq_legacy (stmt : Spec.StatementRound R n 0)
    (data : ∀ i, Spec.OracleStatement R n deg i)
    {Out : PathAlong oracleSig (protocol R deg n) → Type}
    (p : Prover oracleSig ambient (protocol R deg n) Out) :
    (verifier R deg n D ambient).runWithLog stmt data p =
      (legacyVerifier R deg n D ambient).runWithLog stmt data p :=
  OracleVerifier.runWithLog_eq_of_decide_eq decide_eq_legacy outputMap_eq_legacy stmt data p

end LegacyVerifier

/-! ## Challenge correspondence -/

section Uniform
variable (R : Type) [CommSemiring R] [SampleableType R] (deg : ℕ)

/-- Every challenge of the legacy single-round specification is a uniform ring element. -/
theorem singleRound_challenge_uniform :
    ∀ i, HEq ($ᵗ ((Spec.SingleRound.pSpec R deg).Challenge i)) ($ᵗ R) :=
  uniform_append _ !p[] _
    (uniform_append _ ⟨!v[.V_to_P], !v[R]⟩ _
      (uniform_append ⟨!v[.P_to_V], !v[R⦃≤ deg⦄[X]]⟩ !p[] _
        (fun i => isEmptyElim (α := ChallengeIdx ⟨!v[.P_to_V], !v[R⦃≤ deg⦄[X]]⟩) i)
        (fun i => i.1.elim0))
      (fun ⟨⟨0, _⟩, _⟩ => HEq.rfl))
    (fun i => i.1.elim0)

/-- Every challenge of the legacy Sumcheck specification is a uniform ring element. -/
theorem challenge_uniform : ∀ (n : ℕ) (i : (Spec.pSpec R deg n).ChallengeIdx),
    HEq ($ᵗ ((Spec.pSpec R deg n).Challenge i)) ($ᵗ R)
  | 0, i => i.1.elim0
  | n + 1, i => uniform_append (Spec.SingleRound.pSpec R deg) (Spec.pSpec R deg n) _
      (singleRound_challenge_uniform R deg) (challenge_uniform n) i

end Uniform

section ChallengeImpl
variable (R : Type) [CommSemiring R] [SampleableType R] (deg : ℕ)

/-- The uniform challenge oracle samples a uniform ring element at every challenge node. -/
theorem challengeQueryImpl_heq : ∀ (k : ℕ) (c : ChallengeNode oracleSig (protocol R deg k)),
    HEq (challengeQueryImpl oracleSig (protocol R deg k) c) ($ᵗ R)
  | 0, ⟨n, _⟩ => nomatch n
  | _ + 1, ⟨.inl _, h⟩ => nomatch h
  | _ + 1, ⟨.inr ⟨_, .inl _⟩, _⟩ => HEq.rfl
  | k + 1, ⟨.inr ⟨_, .inr ⟨_, c⟩⟩, h⟩ => challengeQueryImpl_heq k ⟨c, h⟩

/-- The reindexed uniform legacy challenge oracle samples a uniform ring element at every
challenge node. -/
theorem legacyChallengeImpl_heq (n : ℕ)
    (c : ChallengeNode oracleSig (oracleProtocol (Spec.pSpec R deg n))) :
    HEq (oracleChallengeImpl (pSpec := Spec.pSpec R deg n) ProtocolSpec.challengeQueryImpl c)
      ($ᵗ R) :=
  (oracleChallengeImpl_heq _ _ c).trans (challenge_uniform R deg n _)

/-- **Challenge correspondence.** The uniform challenge oracle of the interaction-layer Sumcheck
tree is the reindexed uniform legacy challenge oracle. -/
theorem challengeQueryImpl_eq_legacy (n : ℕ) :
    challengeQueryImpl oracleSig (protocol R deg n) =
      (protocol_eq R deg n).symm ▸
        oracleChallengeImpl (pSpec := Spec.pSpec R deg n) ProtocolSpec.challengeQueryImpl :=
  OracleVerifier.queryImpl_eq_cast _ _ _ fun c c' _ =>
    (challengeQueryImpl_heq R deg n c).trans (legacyChallengeImpl_heq R deg n c').symm

end ChallengeImpl

/-! ## Program equality -/

section Run
variable (R : Type) [CommSemiring R] [DecidableEq R] [SampleableType R] (deg n : ℕ)
  {d : ℕ} (D : Fin d ↪ R) {ι : Type} (ambient : OracleSpec ι) [∀ t, Inhabited (ambient.Range t)]

/-- The legacy challenge oracle answering the challenge nodes of the Sumcheck tree. -/
noncomputable def challengeReindex :
    QueryImpl (ambient + challengeSpec oracleSig (protocol R deg n))
    (OracleComp (ambient + [(Spec.pSpec R deg n).Challenge]ₒ)) :=
  (protocol_eq R deg n).symm ▸ oracleChallengeReindex ambient (Spec.pSpec R deg n)

variable {R deg n}

/-- Read a Sumcheck run as a legacy result. -/
def finalize {WitOut : Type}
    (r : Observation oracleSig (protocol R deg n)
      (fun _ => (Spec.StatementRound R n (Fin.last n) × (∀ i, Spec.OracleStatement R n deg i)) ×
        WitOut)
      (fun _ => Spec.StatementRound R n (Fin.last n) × (∀ i, Spec.OracleStatement R n deg i))) :
    LegacyResult (Spec.pSpec R deg n)
      (Spec.StatementRound R n (Fin.last n) × (∀ i, Spec.OracleStatement R n deg i)) WitOut :=
  r.2.2.map fun t => ((decodeTranscript n r.1, r.2.1), t)

variable (R deg n)

/-- **Program equality.** For every prover, the Sumcheck run, with challenges reindexed to the
legacy challenge oracle and read as a legacy result, is the same program as the run of the embedded
legacy verifier against the same prover. The program includes every ambient query of the prover
and of the decision. -/
theorem run_eq_legacy {WitOut : Type} (stmt : Spec.StatementRound R n 0)
    (oStmt : ∀ i, Spec.OracleStatement R n deg i)
    (p : Prover oracleSig ambient (protocol R deg n) (fun _ =>
      (Spec.StatementRound R n (Fin.last n) × (∀ i, Spec.OracleStatement R n deg i)) × WitOut)) :
    simulateQ (challengeReindex R deg n ambient)
        (finalize <$> (verifier R deg n D ambient).run stmt oStmt p) =
      simulateQ (oracleChallengeReindex ambient (Spec.pSpec R deg n))
        (oracleFinalize <$> (embedOracleVerifier (Spec.oracleVerifier R deg D n ambient)).run
          stmt oStmt ((protocol_eq R deg n) ▸ p)) := by
  rw [(verifier_agrees R deg n D ambient).run_eq]
  exact OracleVerifier.run_cast (protocol_eq R deg n).symm _ _ finalize oracleFinalize
    (fun tr out v => by
      simp only [finalize, oracleFinalize]
      rw [← oracleDecode_eq_decodeTranscript n _ tr (eqRec_heq _ _)]) stmt oStmt p

end Run

/-! ## The legacy honest prover -/

section Slots
variable (R : Type) [CommSemiring R] (deg : ℕ) {d : ℕ} (D : Fin d ↪ R) (n : ℕ)
  {ι : Type} (oSpec : OracleSpec ι)

/-- The simple single-round Sumcheck prover receives its challenge with a `pure` slot. -/
theorem simple_pureChallengeSlots :
    PureChallengeSlots (Spec.SingleRound.Simple.prover R deg oSpec) := by
  rintro ⟨⟨_ | _ | k, hk⟩, h⟩ st
  · nomatch h
  · exact ⟨_, rfl⟩
  · omega

variable [DecidableEq R] [SampleableType R]

/-- The legacy honest Sumcheck prover receives every challenge with a `pure` slot: it is a
sequential composition of lifted single-round provers, each of which has a `pure` challenge slot
and a pure output. -/
theorem legacyProver_pureChallengeSlots :
    PureChallengeSlots (Spec.oracleReduction R deg D n oSpec).prover :=
  pureChallengeSlots_seqCompose _ _ _
    (fun i => Spec.SingleRound.instOutputIsPureReduction R n deg D oSpec i)
    (fun _ => pureChallengeSlots_liftContext _ _ (simple_pureChallengeSlots R deg oSpec))

end Slots

section LegacyProver
variable (R : Type) [CommSemiring R] [DecidableEq R] [SampleableType R] (deg n : ℕ)
  {d : ℕ} (D : Fin d ↪ R) {ι : Type} (ambient : OracleSpec ι)

/-- The legacy honest Sumcheck prover, embedded and read on the interaction-layer tree. -/
noncomputable def legacyProver
    (stmt : Spec.StatementRound R n 0 × ∀ i, Spec.OracleStatement R n deg i)
    (wit : Unit) : Prover oracleSig ambient (protocol R deg n)
      (fun _ => (Spec.StatementRound R n (Fin.last n) × (∀ i, Spec.OracleStatement R n deg i)) ×
        Unit) :=
  (protocol_eq R deg n).symm ▸
    embedOracleProver (Spec.oracleReduction R deg D n ambient).prover stmt.1 stmt.2 wit

end LegacyProver

/-! ## The honest legacy run and the ambient trace of the decision -/

section Honest

/-- Transport and transport back along the same equality cancel. -/
private theorem eqRec_eqRec_symm {α : Sort*} {F : α → Sort*} {a b : α} (e : b = a) (x : F a) :
    e ▸ (e.symm ▸ x) = x := by
  subst e; rfl

variable (R : Type) [CommSemiring R] [DecidableEq R] [SampleableType R] (deg n : ℕ)
  {d : ℕ} (D : Fin d ↪ R) {ι : Type} (ambient : OracleSpec ι) [∀ t, Inhabited (ambient.Range t)]

/-- **Honest run.** Against the embedded legacy honest prover, the reindexed and finalized Sumcheck
run is the legacy run of `Spec.oracleReduction`, as a program. -/
theorem run_legacyProver (stmt : Spec.StatementRound R n 0)
    (oStmt : ∀ i, Spec.OracleStatement R n deg i) :
    simulateQ (challengeReindex R deg n ambient)
        (finalize <$> (verifier R deg n D ambient).run stmt oStmt
          (legacyProver R deg n D ambient (stmt, oStmt) ())) =
      ((Spec.oracleReduction R deg D n ambient).run stmt oStmt ()).run := by
  rw [run_eq_legacy]
  simp only [legacyProver]
  have h := eqRec_eqRec_symm (F := fun s => Prover oracleSig ambient s (fun _ =>
      (Spec.StatementRound R n (Fin.last n) × (∀ i, Spec.OracleStatement R n deg i)) × Unit))
    (protocol_eq R deg n)
    (embedOracleProver (Spec.oracleReduction R deg D n ambient).prover stmt oStmt ())
  rw [h]
  exact simulateQ_oracleFinalize_run _
    (legacyProver_pureChallengeSlots R deg D n ambient) stmt oStmt ()

/-- **Ambient trace of the decision.** Answer the input and path oracles from the run's data, and
the ambient oracle by any implementation in any lawful monad. Then the decisions of the Sumcheck
verifier and of the embedded legacy verifier are both `pure` of the legacy verdict, so neither
reaches the ambient oracle: a monad that logs ambient queries records none. The queries to the
message oracles, which the decisions do make, are compared by `runWithLog_eq_legacy`. -/
theorem decide_ambient_trace {m : Type → Type} [Monad m] [LawfulMonad m]
    (amb : QueryImpl ambient m) (stmt : Spec.StatementRound R n 0)
    (data : ∀ i, Spec.OracleStatement R n deg i) (tr : PathAlong oracleSig (protocol R deg n)) :
    simulateQ (QueryImpl.addLift amb ((pathResources (Spec.polynomialFamily R n deg)
        (protocol R deg n)
        (projectPathAlong oracleSig _ tr)).answer (data, payloads _ tr)))
      ((verifier R deg n D ambient).decide stmt _ (toView _ tr)).run =
      (pure (legacyVerdict R deg n D ambient stmt (decodeTranscript n tr)) : m _) ∧
    simulateQ (QueryImpl.addLift amb ((pathResources (Spec.polynomialFamily R n deg)
        (protocol R deg n)
        (projectPathAlong oracleSig _ tr)).answer (data, payloads _ tr)))
      ((legacyVerifier R deg n D ambient).decide stmt _ (toView _ tr)).run =
      (pure (legacyVerdict R deg n D ambient stmt (decodeTranscript n tr)) : m _) :=
  ⟨simulateQ_decide_monad D amb stmt data tr, by
    rw [← decide_eq_legacy]; exact simulateQ_decide_monad D amb stmt data tr⟩

end Honest
section SimpleCompatibility
variable (R : Type) [CommSemiring R] (deg : ℕ)

local instance : ∀ i, OracleInterface ((Spec.SingleRound.pSpec R deg).Challenge i) :=
  ProtocolSpec.challengeOracleInterface

/-- The legacy two-message transcript corresponding to the typed concrete path. -/
def simpleLegacyTranscript (p : R⦃≤ deg⦄[X]) (r : R) :
    (Spec.SingleRound.pSpec R deg).FullTranscript :=
  fun i => Fin.cases p (fun j => Fin.cases r (fun k => Fin.elim0 k) j) i

/-- The first Simple transcript entry is the sent polynomial. -/
@[simp]
theorem simpleLegacyTranscript_message (p : R⦃≤ deg⦄[X]) (r : R) :
    simpleLegacyTranscript R deg p r 0 = p := rfl

/-- The second Simple transcript entry is the prescribed challenge. -/
@[simp]
theorem simpleLegacyTranscript_challenge (p : R⦃≤ deg⦄[X]) (r : R) :
    simpleLegacyTranscript R deg p r 1 = r := rfl

/-- Run the actual legacy prover with its challenge query answered by the chosen challenge. -/
theorem simpleLegacyProver_run {ι : Type} (ambient : OracleSpec ι)
    (p : R⦃≤ deg⦄[X]) (target r : R) :
    simulateQ (OracleInterface.simOracle ambient
      (T := (Spec.SingleRound.pSpec R deg).Challenge) (simpleLegacyTranscript R deg p r).challenges)
      ((Spec.SingleRound.Simple.prover R deg ambient).run (target, fun _ => p) ()) =
      pure (simpleLegacyTranscript R deg p r, ((p.val.eval r, r), fun _ : Unit => p), ()) := by
  have hfirst : (Spec.SingleRound.Simple.prover R deg ambient).runToRound (1 : Fin 3)
      (target, fun _ => p) () =
      pure (ProtocolSpec.Transcript.concat (m := (0 : Fin 2))
        (pSpec := Spec.SingleRound.pSpec R deg) p (fun i => Fin.elim0 i), p) := by
    erw [Prover.runToRound_succ (0 : Fin 2)]
    erw [Prover.processRound_of_dir_eq_P_to_V 0 rfl]
    simp [Spec.SingleRound.Simple.prover]
    rfl
  have hsecond : simulateQ
      (OracleInterface.simOracle ambient (T := (Spec.SingleRound.pSpec R deg).Challenge)
        (simpleLegacyTranscript R deg p r).challenges)
      ((Spec.SingleRound.Simple.prover R deg ambient).runToRound (2 : Fin 3)
        (target, fun _ => p) ()) =
      pure (ProtocolSpec.Transcript.concat (m := (1 : Fin 2)) r
        (ProtocolSpec.Transcript.concat (m := (0 : Fin 2))
          (pSpec := Spec.SingleRound.pSpec R deg) p (fun i => Fin.elim0 i)),
        (p, r)) := by
    erw [Prover.runToRound_succ (1 : Fin 2)]
    erw [Prover.processRound_of_dir_eq_V_to_P 1 rfl, hfirst]
    simp only [Spec.SingleRound.Simple.prover, LawfulMonad.pure_bind, monadLift_pure,
      ProtocolSpec.getChallenge, LawfulApplicative.map_pure, LawfulMonad.bind_pure_comp,
      simulateQ_map, HasQuery.query]
    erw [simulateQ_query]
    rfl
  simp only [Prover.run, simulateQ_bind]
  change (simulateQ _ ((Spec.SingleRound.Simple.prover R deg ambient).runToRound
    (2 : Fin 3) (target, fun _ => p) ()) >>= _) = _
  rw [hsecond]
  have ht : ProtocolSpec.Transcript.concat (m := (1 : Fin 2)) r
      (ProtocolSpec.Transcript.concat (m := (0 : Fin 2))
        (pSpec := Spec.SingleRound.pSpec R deg) p (fun i => Fin.elim0 i)) =
      simpleLegacyTranscript R deg p r := by
    funext i
    fin_cases i <;> rfl
  simp only [Spec.SingleRound.Simple.prover, LawfulMonad.pure_bind, monadLift_pure, simulateQ_pure]
  erw [ht]

/-- The Simple legacy verifier has the same scalar verdict as the native arbitrary-message run,
including rejection and retention of the original input polynomial. -/
theorem simpleLegacyVerifier_correspondence [DecidableEq R]
    {ι : Type} (ambient : OracleSpec ι) {m : ℕ} (D : Fin m ↪ R)
    (p q : R⦃≤ deg⦄[X]) (target r : R) :
    (Option.map Prod.fst) <$>
      ((Spec.SingleRound.Simple.oracleVerifier R deg D ambient).toVerifier.verify
        (target, fun _ => p) (simpleLegacyTranscript R deg q r)).run =
      (fun result => result.2.2.map
        (fun out => (out.1.target, out.1.challenges ⟨0, by decide⟩))) <$>
        indexedExecute (Finset.univ.map D).toList.get ambient (QueryImpl.id' ambient) (pure r)
          (fun _ => univariateData p) q target := by
  rw [Spec.SingleRound.Simple.oracleVerifier_eq_verifier, indexedExecuteAt_list_eq]
  by_cases h : (∑ x, q.val.eval (D x)) = target <;>
    simp [Spec.SingleRound.Simple.verifier, Finset.sum_map_toList, h, Fin.snoc]

end SimpleCompatibility

end Sumcheck.Core
