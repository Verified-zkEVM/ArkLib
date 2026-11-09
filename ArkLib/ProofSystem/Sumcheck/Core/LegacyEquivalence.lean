/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Core.Completeness
public import ArkLib.Interaction.Core.Legacy.OracleExecution
public import ArkLib.Interaction.Core.Legacy.Security
public import ArkLib.Interaction.Core.Security.Soundness
public import ArkLib.Interaction.Core.Security.Completeness

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
  in every lawful monad, and both are `pure` of the legacy verdict (`verifier_agrees`,
  `decide_trace`). In particular neither makes an ambient query, so their query traces agree.
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
* `Agrees` and its consequences, and the transport lemmas along `protocol_eq`, which carry every
  security notion of the classical model from the embedded legacy verifier to the Sumcheck
  verifier. The transfers themselves are in `Completeness`, `Soundness`, `Knowledge` and
  `RoundByRound`.
-/

@[expose] public section

namespace Sumcheck.Core
open scoped ENNReal NNReal
open Polynomial PFunctor FreeM Interaction.Core Interaction.TwoParty.Lens Interaction.Oracle
  OracleComp OracleSpec ProtocolSpec Interaction.Core.Legacy

/-! ## The legacy oracle tree of an appended specification -/

section Chain
variable {P : PFunctor.{1, 0}}

/-- Chains of equal remaining length are equal. -/
theorem chain_congr_len {N : ℕ} (pos : Fin N → P.A) (k : ℕ) {m m' : ℕ} (hm : m = m')
    (h : k + m = N) (h' : k + m' = N) : chain pos k m h = chain pos k m' h' := by
  subst hm; rfl

/-- A chain that starts `a` positions into `pos` is the chain of `pos'` when the positions of
`pos` past `a` are those of `pos'`. -/
theorem chain_natAdd {a M : ℕ} (pos : Fin (a + M) → P.A) (pos' : Fin M → P.A)
    (hpos : ∀ j, pos (Fin.natAdd a j) = pos' j) :
    ∀ (k m : ℕ) (h : a + k + m = a + M) (h' : k + m = M),
      chain pos (a + k) m h = chain pos' k m h'
  | _, 0, _, _ => rfl
  | k, m + 1, h, h' => by
    have ih := chain_natAdd pos pos' hpos (k + 1) m (by omega) (by omega)
    change FreeM.liftBind (pos (Fin.natAdd a ⟨k, by omega⟩))
        (fun _ => chain pos (a + (k + 1)) m (by omega)) =
      FreeM.liftBind (pos' ⟨k, by omega⟩) (fun _ => chain pos' (k + 1) m (by omega))
    rw [hpos, ih]

end Chain

section Round
/-- Oracle positions with equal payload types and interfaces are equal. -/
theorem oracle_congr {X X' : Type} {I : OracleInterface X} {I' : OracleInterface X'}
    (hX : X = X') (hI : HEq I I') : OraclePos.oracle X I = OraclePos.oracle X' I' := by
  subst hX; cases eq_of_heq hI; rfl

variable {N N' : ℕ} (p : ProtocolSpec N) (p' : ProtocolSpec N')
  [O : ∀ i, OracleInterface (p.Message i)] [O' : ∀ i, OracleInterface (p'.Message i)]

/-- Rounds with equal directions, types and message interfaces give equal oracle positions. -/
theorem oraclePos_congr (j : Fin N) (j' : Fin N') (hT : p.«Type» j = p'.«Type» j')
    (hO : ∀ h h', HEq (O ⟨j, h⟩) (O' ⟨j', h'⟩)) :
    ∀ (d d' : Direction) (h : p.dir j = d) (h' : p'.dir j' = d'), d = d' →
      oraclePos p j d h = oraclePos p' j' d' h'
  | .P_to_V, _, h, h', rfl => oracle_congr hT (hO h h')
  | .V_to_P, _, _, _, rfl => congrArg OraclePos.challenge hT

/-- Rounds with equal directions, types and message interfaces give equal oracle rounds. -/
theorem oracleRound_congr (j : Fin N) (j' : Fin N') (hd : p.dir j = p'.dir j')
    (hT : p.«Type» j = p'.«Type» j') (hO : ∀ h h', HEq (O ⟨j, h⟩) (O' ⟨j', h'⟩)) :
    oracleRound p j = oracleRound p' j' :=
  oraclePos_congr p p' j j' hT hO _ _ rfl rfl hd

end Round

section Append
variable {a b : ℕ} (A : ProtocolSpec a) (B : ProtocolSpec b)
  [OA : ∀ i, OracleInterface (A.Message i)] [OB : ∀ i, OracleInterface (B.Message i)]

/-- A round of an appended specification past its first part is the round of the second part. -/
theorem oracleRound_append_natAdd (j : Fin b) :
    oracleRound (A ++ₚ B) (Fin.natAdd a j) = oracleRound B j :=
  oracleRound_congr _ _ _ _ (Fin.vappend_right _ _ j) (Fin.vappend_right _ _ j)
    fun _ h' => (message_interface_inr (pSpec₁ := A) ⟨j, h'⟩).symm

/-- A round of an appended specification within its first part is the round of the first part. -/
theorem oracleRound_append_castAdd (j : Fin a) :
    oracleRound (A ++ₚ B) (Fin.castAdd b j) = oracleRound A j :=
  oracleRound_congr _ _ _ _ (Fin.vappend_left _ _ j) (Fin.vappend_left _ _ j)
    fun _ h' => (message_interface_inl (pSpec₂ := B) ⟨j, h'⟩).symm

end Append

section Path
variable {P : PFunctor.{1, 0}} (l : PFunctor.Lens P rolePoly.{0})

/-- One node followed by a fixed continuation, at equal nodes and continuations. -/
theorem liftBind_congr' {a a' : P.A} {t t' : FreeM P PUnit.{1}} (ha : a = a') (ht : t = t') :
    (FreeM.liftBind a fun _ => t) = FreeM.liftBind a' fun _ => t' := by
  subst ha ht; rfl

/-- Two nodes followed by a fixed continuation, at equal nodes and continuations. -/
theorem liftBind₂_congr {a a' b b' : P.A} {t t' : FreeM P PUnit.{1}} (ha : a = a') (hb : b = b')
    (ht : t = t') :
    (FreeM.liftBind a fun _ => FreeM.liftBind b fun _ => t) =
      FreeM.liftBind a' fun _ => FreeM.liftBind b' fun _ => t' := by
  subst ha hb ht; rfl

/-- Heterogeneously equal paths through equal nodes have heterogeneously equal moves and
rests. -/
theorem heq_pathAlong_liftBind {a a' : P.A} {t t' : FreeM P PUnit.{1}} (ha : a = a') (ht : t = t')
    {d : Move l a} {r : PathAlong l t} {d' : Move l a'} {r' : PathAlong l t'}
    (h : HEq (⟨d, r⟩ : PathAlong l (FreeM.liftBind a fun _ => t))
      (⟨d', r'⟩ : PathAlong l (FreeM.liftBind a' fun _ => t'))) :
    HEq d d' ∧ HEq r r' := by
  subst ha ht
  cases eq_of_heq h
  exact ⟨HEq.rfl, HEq.rfl⟩

/-- Heterogeneously equal pairs of heterogeneously typed components have equal components. -/
theorem heq_of_sigma_heq {X X' Y Y' : Type} (hX : X = X') (hY : Y = Y') {x : X} {y : Y} {x' : X'}
    {y' : Y'} (h : HEq (⟨x, y⟩ : (_ : X) × Y) (⟨x', y'⟩ : (_ : X') × Y')) :
    HEq x x' ∧ HEq y y' := by
  subst hX hY
  cases eq_of_heq h
  exact ⟨HEq.rfl, HEq.rfl⟩

/-- Decoding along chains of equal remaining length agrees on heterogeneously equal paths. -/
theorem decodeFrom_congr_len {n : ℕ} {pSpec : ProtocolSpec n} (pos : Fin n → P.A)
    (e : (j : Fin n) → Move l (pos j) ≃ pSpec.«Type» j) (k : ℕ) {m m' : ℕ} (hm : m = m')
    (h : k + m = n) (h' : k + m' = n) (pre : Transcript ⟨k, by omega⟩ pSpec)
    (p : PathAlong l (chain pos k m h)) (p' : PathAlong l (chain pos k m' h')) (hp : HEq p p') :
    decodeFrom l pos e k m' h' pre p' = decodeFrom l pos e k m h pre p := by
  subst hm; cases eq_of_heq hp; rfl

end Path

section Decode
variable {N : ℕ} (p : ProtocolSpec N) [O : ∀ i, OracleInterface (p.Message i)]

/-- The move equivalence of an oracle round is the identity up to the type equality. -/
theorem oracleMoveEquiv_heq (j : Fin N) :
    ∀ (d : Direction) (h : p.dir j = d) (x : Move oracleSig (oraclePos p j d h)),
      HEq (oracleMoveEquiv p j d h x) x
  | .P_to_V, _, _ => HEq.rfl
  | .V_to_P, _, _ => HEq.rfl

end Decode

section DecodeAppend
variable {a b : ℕ} (A : ProtocolSpec a) (B : ProtocolSpec b)
  [OA : ∀ i, OracleInterface (A.Message i)] [OB : ∀ i, OracleInterface (B.Message i)]

/-- Reading a chain over an appended spec past its first part reads the chain over the second
part. -/
theorem decodeFrom_append_natAdd : ∀ (k m : ℕ) (h : a + k + m = a + b) (h' : k + m = b)
    (pre : Transcript ⟨a + k, by omega⟩ (A ++ₚ B)) (pre' : Transcript ⟨k, by omega⟩ B)
    (q : PathAlong oracleSig (chain (oracleRound (A ++ₚ B)) (a + k) m h))
    (q' : PathAlong oracleSig (chain (oracleRound B) k m h')) (_ : HEq q q')
    (j : Fin b) (_ : k ≤ j.val),
    HEq (decodeFrom oracleSig (oracleRound (A ++ₚ B))
        (fun j => oracleMoveEquiv (A ++ₚ B) j _ rfl) (a + k) m h pre q (Fin.natAdd a j))
      (decodeFrom oracleSig (oracleRound B) (fun j => oracleMoveEquiv B j _ rfl) k m h' pre' q' j)
  | k, 0, _, h', _, _, _, _, _, j, hj => absurd j.isLt (by omega)
  | k, m + 1, h, h', pre, pre', ⟨d, q⟩, ⟨d', q'⟩, hq, ⟨j, hjb⟩, hj => by
    obtain ⟨hd, hq⟩ := heq_of_sigma_heq
      (congrArg (Move oracleSig) (oracleRound_append_natAdd A B ⟨k, by omega⟩))
      (congrArg (PathAlong oracleSig)
        (chain_natAdd _ _ (oracleRound_append_natAdd A B) (k + 1) m (by omega) (by omega))) hq
    rcases Nat.lt_or_eq_of_le hj with hlt | rfl
    · rw [decodeFrom_succ, decodeFrom_succ]
      exact decodeFrom_append_natAdd (k + 1) m (by omega) (by omega) _ _ q q' hq ⟨j, hjb⟩ hlt
    · refine (heq_of_eq (decodeFrom_succ_self oracleSig _ _ (a + k) m h pre d q)).trans ?_
      refine HEq.trans ?_ (heq_of_eq (decodeFrom_succ_self oracleSig _ _ k m h' pre' d' q').symm)
      exact (oracleMoveEquiv_heq _ _ _ _ d).trans (hd.trans (oracleMoveEquiv_heq _ _ _ _ d').symm)

end DecodeAppend

/-! ## Tree and transcript correspondence -/

section Tree
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

attribute [local implicit_reducible] FreeM.replicate in
/-- Decoding one more round prepends that round's message and challenge. -/
theorem decodeTranscript_succ {n : ℕ} (msg : R⦃≤ deg⦄[X]) (chal : R)
    (tail : PathAlong oracleSig (protocol R deg n)) :
    decodeTranscript (n + 1) (consTranscript msg chal tail) =
      roundFullTranscript msg chal ++ₜ decodeTranscript n tail := rfl

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

omit [DecidableEq R] [SampleableType R] in
/-- Lifted decision queries answered from the actual data, with ambient queries answered in any
lawful monad, are a pure computation of the path oracles. -/
theorem simulateQ_decisionLift_monad {m : Type → Type} [Monad m] [LawfulMonad m]
    (amb : QueryImpl ambient m) (p : Path (protocol R deg n))
    (data : ∀ i, Spec.OracleStatement R n deg i)
    (pl : ∀ i, OracleData (protocol R deg n) p i) {α : Type}
    (oa : OracleComp (oracles (protocol R deg n) p) α) :
    simulateQ (QueryImpl.addLift amb ((sumFamily (polyFamily R deg n)
        (pathFamily (protocol R deg n) p)).behaviorOfRealizations (sumData data pl)))
      (simulateQ (decisionLift R deg n ambient p) oa) =
      (pure (simulateQ ((pathFamily (protocol R deg n) p).behaviorOfRealizations pl) oa) :
        m α) := by
  refine (QueryImpl.simulateQ_simulateQ_eq_of_apply
    (impl := ((pathFamily (protocol R deg n) p).behaviorOfRealizations pl).liftTarget m)
    (fun t => ?_) oa).trans ?_
  · simp only [QueryImpl.addLift_def]
    exact QueryImpl.simulateQ_add_query_right _ _ _
  · rw [simulateQ_liftTarget]
    rfl

/-- On any completed run, the decision returns the legacy verdict of the decoded transcript, for
ambient queries answered in any lawful monad. -/
theorem simulateQ_decide_monad {m : Type → Type} [Monad m] [LawfulMonad m]
    (amb : QueryImpl ambient m) (stmt : Spec.StatementRound R n 0)
    (data : ∀ i, Spec.OracleStatement R n deg i) (tr : PathAlong oracleSig (protocol R deg n)) :
    simulateQ (QueryImpl.addLift amb ((sumFamily (polyFamily R deg n)
        (pathFamily (protocol R deg n) (projectPathAlong oracleSig _ tr))).behaviorOfRealizations
          (sumData data (payloads _ tr))))
      ((verifier R deg n D ambient).decide stmt _ (toView _ tr)).run =
      (pure (legacyVerdict R deg n D ambient stmt (decodeTranscript n tr)) : m _) := by
  rw [verifier_decide, simulateQ_decisionLift_monad, viewChallenges_toView]
  congr 1
  exact QueryImpl.simulateQ_simulateQ_eq_of_apply (simulateQ_route n tr) _

end DecideM

/-! ## Agreeing verifiers

Two oracle verifiers on the same tree agree when, on every completed run, their decisions are the
same program in every lawful monad and their output data agree. Agreeing verifiers have equal runs,
equal extraction games and the same valid-acceptance predicate, so every security notion of the
classical model holds for one exactly when it holds for the other. -/

section Agree
variable {ι I J S T : Type} {ambient : OracleSpec ι} {s : OracleProtocol}
  {A : I → Type} {B : J → Type} {inputs : OracleFamily I A} {outputs : OracleFamily J B}

/-- Two oracle verifiers on the same tree agree on every completed run: their decisions, with the
input and path oracles answered from the actual data and ambient queries answered in any lawful
monad, are the same program, and their output data agree. -/
def Agrees (V V' : OracleVerifier ambient s S T inputs outputs) : Prop :=
  ∀ (stmt : S) (data : ∀ i, A i) (tr : PathAlong oracleSig s),
    (∀ (m : Type → Type) [Monad m] [LawfulMonad m] (amb : QueryImpl ambient m),
      simulateQ (QueryImpl.addLift (r := m) amb ((sumFamily inputs
          (pathFamily s (projectPathAlong oracleSig s tr))).behaviorOfRealizations
            (sumData data (payloads s tr))))
          (V.decide stmt _ (toView s tr)).run =
        simulateQ (QueryImpl.addLift (r := m) amb ((sumFamily inputs
          (pathFamily s (projectPathAlong oracleSig s tr))).behaviorOfRealizations
            (sumData data (payloads s tr))))
          (V'.decide stmt _ (toView s tr)).run) ∧
    (V.outputMap stmt _ (toView s tr)).f (sumData data (payloads s tr)) =
      (V'.outputMap stmt _ (toView s tr)).f (sumData data (payloads s tr))

variable {V V' : OracleVerifier ambient s S T inputs outputs}

/-- Agreeing verifiers have equal runs against every prover. -/
theorem Agrees.run_eq (h : Agrees V V') (stmt : S) (data : ∀ i, A i)
    {Out : PathAlong oracleSig s → Type} (p : Prover oracleSig ambient s Out) :
    V.run stmt data p = V'.run stmt data p := by
  simp only [Interaction.Core.OracleVerifier.run]
  refine bind_congr fun r => ?_
  obtain ⟨d, o⟩ := h stmt data r.1
  rw [d, o]

/-- Agreeing verifiers accept validly at the same statements and transcripts. -/
theorem Agrees.validAcceptance_iff (h : Agrees V V') {σ : Type}
    (impl : QueryImpl ambient (StateT σ ProbComp)) (langOut : T × (∀ j, B j) → Prop)
    (stmt : S × (∀ i, A i)) (tr : PathAlong oracleSig s) :
    V.validAcceptance impl langOut stmt tr ↔ V'.validAcceptance impl langOut stmt tr := by
  obtain ⟨d, o⟩ := h stmt.1 stmt.2 tr
  simp only [Interaction.Core.OracleVerifier.validAcceptance, d, o]

/-- Agreeing verifiers have equal extraction games, for every extractor and prover. -/
theorem Agrees.extractionGame_eq (h : Agrees V V') {Wout : Type}
    {Out : PathAlong oracleSig s → Type} {Witness : (S × (∀ i, A i)) → Type}
    (readOut : ∀ tr, Out tr → Wout) (E : Extractor.OracleStraightline ambient s Witness Wout)
    (stmt : S × (∀ i, A i)) (p : Prover oracleSig ambient s Out) :
    V.extractionGame readOut E stmt p = V'.extractionGame readOut E stmt p := by
  have key : ∀ W : OracleVerifier ambient s S T inputs outputs,
      W.extractionGame readOut E stmt p =
        (((fun z => (z.1, z.2.1, z.2.2.fst)) <$> W.runWithLog stmt.1 stmt.2 p) >>= fun y =>
          match y.1.2.2 with
          | none => pure (y.1, none)
          | some _ => (fun ex => (y.1, ex)) <$> OracleComp.liftComp
              (E stmt (readOut y.1.1 y.1.2.1) y.1.1 y.2.1 y.2.2).run
              (ambient + challengeSpec oracleSig s) :
          OracleComp (ambient + challengeSpec oracleSig s)
            (Observation oracleSig s Out (T × (∀ j, B j)) × Option (Witness stmt))) := by
    intro W
    rw [bind_map_left, Interaction.Core.OracleVerifier.extractionGame]
    refine bind_congr fun x => ?_
    rcases x with ⟨⟨tr, out, _ | v⟩, pl, vl⟩ <;> simp
  rw [key, key, Interaction.Core.OracleVerifier.runWithLog_fst,
    Interaction.Core.OracleVerifier.runWithLog_fst, bind_assoc, bind_assoc]
  refine bind_congr (m := OracleComp (ambient + challengeSpec oracleSig s)) fun x => ?_
  obtain ⟨d, o⟩ := h stmt.1 stmt.2 x.1.1
  dsimp only
  rw [d, o]

end Agree

section Cast
variable {ι I J S T : Type} {ambient : OracleSpec ι} {s s' : OracleProtocol}
  {A : I → Type} {B : J → Type} {inputs : OracleFamily I A} {outputs : OracleFamily J B}

/-- Transporting a verifier along a tree equality does not change its decision on corresponding
transcripts. -/
theorem decide_cast (e : s' = s) (V : OracleVerifier ambient s' S T inputs outputs) (stmt : S)
    (data : ∀ i, A i) (tr : PathAlong oracleSig s) (tr' : PathAlong oracleSig s')
    (htr : HEq tr tr') (m : Type → Type) [Monad m] [LawfulMonad m] (amb : QueryImpl ambient m) :
    simulateQ (QueryImpl.addLift (r := m) amb ((sumFamily inputs
        (pathFamily s (projectPathAlong oracleSig s tr))).behaviorOfRealizations
          (sumData data (payloads s tr))))
        ((e ▸ V : OracleVerifier ambient s S T inputs outputs).decide stmt _ (toView s tr)).run =
      simulateQ (QueryImpl.addLift (r := m) amb ((sumFamily inputs
        (pathFamily s' (projectPathAlong oracleSig s' tr'))).behaviorOfRealizations
          (sumData data (payloads s' tr'))))
        (V.decide stmt _ (toView s' tr')).run := by
  subst e; cases eq_of_heq htr; rfl

/-- Transporting a verifier along a tree equality does not change its output data on
corresponding transcripts. -/
theorem outputMap_cast (e : s' = s) (V : OracleVerifier ambient s' S T inputs outputs) (stmt : S)
    (data : ∀ i, A i) (tr : PathAlong oracleSig s) (tr' : PathAlong oracleSig s')
    (htr : HEq tr tr') :
    ((e ▸ V : OracleVerifier ambient s S T inputs outputs).outputMap stmt _ (toView s tr)).f
        (sumData data (payloads s tr)) =
      (V.outputMap stmt _ (toView s' tr')).f (sumData data (payloads s' tr')) := by
  subst e; cases eq_of_heq htr; rfl

end Cast

/-! ## The embedded legacy verifier on the Sumcheck tree -/

section LegacyVerifier
variable (R : Type) [CommSemiring R] [DecidableEq R] [SampleableType R] (deg n : ℕ)
  {d : ℕ} (D : Fin d ↪ R) {ι : Type} (ambient : OracleSpec ι) [∀ t, Inhabited (ambient.Range t)]

/-- The embedding of the legacy Sumcheck oracle verifier, read on the interaction-layer Sumcheck
tree. -/
noncomputable def legacyVerifier : OracleVerifier ambient (protocol R deg n)
    (Spec.StatementRound R n 0) (Spec.StatementRound R n (Fin.last n)) (polyFamily R deg n)
    (polyFamily R deg n) :=
  (protocol_eq R deg n).symm ▸ embedOracleVerifier (Spec.oracleVerifier R deg D n ambient)

/-- **Decision correspondence.** The Sumcheck verifier agrees with the embedded legacy verifier: on
every completed run both decisions are `pure` of the legacy verdict of the decoded transcript,
and both keep the input polynomial as output oracle. -/
theorem verifier_agrees :
    Agrees (verifier R deg n D ambient) (legacyVerifier R deg n D ambient) := by
  intro stmt data tr
  have htr : HEq tr (cast (congrArg (PathAlong oracleSig) (protocol_eq R deg n)) tr) :=
    (cast_heq _ _).symm
  refine ⟨fun m _ _ amb => ?_, ?_⟩
  · refine (simulateQ_decide_monad D amb stmt data tr).trans (Eq.trans ?_
      (decide_cast (inputs := polyFamily R deg n) (outputs := polyFamily R deg n)
        (protocol_eq R deg n).symm (embedOracleVerifier (Spec.oracleVerifier R deg D n ambient))
        stmt data _ _ htr m amb).symm)
    refine Eq.trans ?_ (simulateQ_embedOracleVerifier_decide amb _ stmt data _).symm
    rw [simulateQ_legacy_verify, simulateQ_pure, oracleDecode_eq_decodeTranscript n tr _ htr]
  · refine Eq.trans ?_
      (outputMap_cast (inputs := polyFamily R deg n) (outputs := polyFamily R deg n)
        (protocol_eq R deg n).symm (embedOracleVerifier (Spec.oracleVerifier R deg D n ambient))
        stmt data _ _ htr).symm
    exact (embedOracleVerifier_outputMap_f (Spec.oracleVerifier R deg D n ambient) stmt data _).symm

end LegacyVerifier

/-! ## Challenge correspondence -/

section Uniform

/-- A sampler mapped along a type equality is the same sampler. -/
theorem heq_of_cast_map {α β : Type} (h : α = β) {x : ProbComp α} {y : ProbComp β}
    (hxy : cast h <$> x = y) : HEq x y := by
  subst h; subst hxy; exact (heq_of_eq (LawfulFunctor.id_map x)).symm

/-- If every challenge of two specifications is sampled as `x`, then so is every challenge of
their append. -/
theorem uniform_append {a b : ℕ} (A : ProtocolSpec a) (B : ProtocolSpec b)
    [∀ i, SampleableType (A.Challenge i)] [∀ i, SampleableType (B.Challenge i)] {X : Type}
    (x : ProbComp X) (hA : ∀ i, HEq ($ᵗ (A.Challenge i)) x) (hB : ∀ i, HEq ($ᵗ (B.Challenge i)) x) :
    ∀ i : (A ++ₚ B).ChallengeIdx, HEq ($ᵗ ((A ++ₚ B).Challenge i)) x := by
  intro i
  obtain ⟨j | j, rfl⟩ := (ChallengeIdx.sumEquiv (pSpec₁ := A) (pSpec₂ := B)).surjective i
  · exact (heq_of_cast_map _ (uniformSample_challenge_append_inl j)).trans (hA j)
  · exact (heq_of_cast_map _ (uniformSample_challenge_append_inr j)).trans (hB j)

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

/-- Mapping a sampler along a function that is the identity up to a type equality gives the same
sampler. -/
theorem map_heq_self {X Y : Type} (hXY : X = Y) (f : X → Y) (hf : ∀ x, HEq (f x) x)
    (x : ProbComp X) : HEq (f <$> x) x := by
  subst hXY
  have : f = id := funext fun y => eq_of_heq (hf y)
  subst this
  exact heq_of_eq (LawfulFunctor.id_map x)

variable {N : ℕ} (p : ProtocolSpec N) [O : ∀ i, OracleInterface (p.Message i)]

/-- The move type of an oracle round is the round's type. -/
theorem oracleMove_eq (j : Fin N) :
    ∀ (d : Direction) (h : p.dir j = d), Move oracleSig (oraclePos p j d h) = p.«Type» j
  | .P_to_V, _ => rfl
  | .V_to_P, _ => rfl

/-- The inverse move equivalence of an oracle round is the identity up to the type equality. -/
theorem oracleMoveEquiv_symm_heq (j : Fin N) :
    ∀ (d : Direction) (h : p.dir j = d) (y : p.«Type» j),
      HEq ((oracleMoveEquiv p j d h).symm y) y
  | .P_to_V, _, _ => HEq.rfl
  | .V_to_P, _, _ => HEq.rfl

/-- A challenge node of a chain of oracle rounds has the type of its legacy challenge round. -/
theorem oracleChallengeSpec_eq : ∀ (k m : ℕ) (h : k + m = N)
    (c : ChallengeNode oracleSig (chain (oracleRound p) k m h)),
    challengeSpec oracleSig (chain (oracleRound p) k m h) c =
      p.Challenge ((oracleLayout p).challengeRound k m h c)
  | _, 0, _, c => c.val.elim
  | k, _ + 1, _, ⟨.inl _, _⟩ => oracleMove_eq p ⟨k, by omega⟩ _ rfl
  | k, m + 1, _, ⟨.inr ⟨_, c⟩, hc⟩ => oracleChallengeSpec_eq (k + 1) m _ ⟨c, hc⟩

/-- Reading a legacy challenge as a move of its challenge node is the identity up to the type
equality. -/
theorem oracleChallengeMove_symm_heq : ∀ (k m : ℕ) (h : k + m = N)
    (c : ChallengeNode oracleSig (chain (oracleRound p) k m h))
    (y : p.Challenge ((oracleLayout p).challengeRound k m h c)),
    HEq (((oracleLayout p).challengeMove k m h c).symm y) y
  | _, 0, _, c, _ => c.val.elim
  | k, _ + 1, _, ⟨.inl _, _⟩, y => oracleMoveEquiv_symm_heq p ⟨k, by omega⟩ _ rfl y
  | k, m + 1, _, ⟨.inr ⟨_, c⟩, hc⟩, y => oracleChallengeMove_symm_heq (k + 1) m _ ⟨c, hc⟩ y

variable (R : Type) [CommSemiring R] [SampleableType R] (deg : ℕ)

attribute [local implicit_reducible] FreeM.replicate Node.position challengeSpec in
/-- The uniform challenge oracle samples a uniform ring element at every challenge node. -/
theorem challengeQueryImpl_heq : ∀ (k : ℕ) (c : ChallengeNode oracleSig (protocol R deg k)),
    HEq (challengeQueryImpl oracleSig (protocol R deg k) c) ($ᵗ R)
  | 0, ⟨n, _⟩ => nomatch n
  | _ + 1, ⟨.inl _, h⟩ => nomatch h
  | _ + 1, ⟨.inr ⟨_, .inl _⟩, _⟩ => HEq.rfl
  | k + 1, ⟨.inr ⟨_, .inr ⟨_, c⟩⟩, h⟩ => challengeQueryImpl_heq k ⟨c, h⟩

/-- The reindexed uniform legacy challenge oracle samples a uniform ring element at every challenge
node. -/
theorem oracleChallengeImpl_heq (n : ℕ)
    (c : ChallengeNode oracleSig (oracleProtocol (Spec.pSpec R deg n))) :
    HEq (oracleChallengeImpl (pSpec := Spec.pSpec R deg n) ProtocolSpec.challengeQueryImpl c)
      ($ᵗ R) :=
  (map_heq_self (oracleChallengeSpec_eq _ 0 _ _ c).symm _
    (oracleChallengeMove_symm_heq _ 0 _ _ c) _).trans (challenge_uniform R deg n _)

/-- Challenge oracles on equal trees are equal when they agree on corresponding nodes. -/
theorem queryImpl_eq_cast {s s' : OracleProtocol} (e : s' = s)
    (f : QueryImpl (challengeSpec oracleSig s) ProbComp)
    (g : QueryImpl (challengeSpec oracleSig s') ProbComp)
    (h : ∀ c c', HEq c c' → HEq (f c) (g c')) : f = e ▸ g := by
  subst e; exact funext fun c => eq_of_heq (h c c HEq.rfl)

/-- **Challenge correspondence.** The uniform challenge oracle of the interaction-layer Sumcheck
tree is the reindexed uniform legacy challenge oracle. -/
theorem challengeQueryImpl_eq_legacy (n : ℕ) :
    challengeQueryImpl oracleSig (protocol R deg n) =
      (protocol_eq R deg n).symm ▸
        oracleChallengeImpl (pSpec := Spec.pSpec R deg n) ProtocolSpec.challengeQueryImpl :=
  queryImpl_eq_cast _ _ _ fun c c' _ =>
    (challengeQueryImpl_heq R deg n c).trans (oracleChallengeImpl_heq R deg n c').symm

end ChallengeImpl

/-! ## Security notions of agreeing and transported verifiers -/

section Notions
variable {ι I J S T σ : Type} {ambient : OracleSpec ι} {s s' : OracleProtocol}
  {A : I → Type} {B : J → Type} {inputs : OracleFamily I A} {outputs : OracleFamily J B}
  {V V' : OracleVerifier ambient s S T inputs outputs}

/-- Agreeing verifiers have the same classical model. -/
theorem Agrees.classicalModel_eq (h : Agrees V V') {Out : PathAlong oracleSig s → Type}
    [MeasurableSpace (Observation oracleSig s Out (T × (∀ j, B j)))] (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (draw : QueryImpl (challengeSpec oracleSig s) ProbComp) :
    V.classicalModel (Out := Out) init impl draw = V'.classicalModel init impl draw := by
  simp only [Interaction.Core.OracleVerifier.classicalModel, h.run_eq]

/-- Agreeing verifiers are knowledge sound in the classical straight-line interface together. -/
theorem Agrees.knowledgeSoundness_iff (h : Agrees V V') {Out : PathAlong oracleSig s → Type}
    {Wout : Type} [mObs : MeasurableSpace (Observation oracleSig s Out (T × (∀ j, B j)))]
    (init : ProbComp σ) (impl : QueryImpl ambient (StateT σ ProbComp))
    (draw : QueryImpl (challengeSpec oracleSig s) ProbComp) (readOut : ∀ tr, Out tr → Wout)
    (input : StatementProblem (S × (∀ i, A i))) (output : StatementProblem (T × (∀ j, B j)))
    [mWit : ∀ stmt, MeasurableSpace (input.Witness () stmt)]
    (J : OutputJudgement (Observation oracleSig s Out (T × (∀ j, B j))) _ output) (ε : ℝ≥0∞) :
    knowledgeSoundness (V.classicalModel init impl draw) input output J
        (V.classicalStraightline (input.Witness ()) init impl draw readOut) ε ↔
      knowledgeSoundness (V'.classicalModel init impl draw) input output J
        (V'.classicalStraightline (input.Witness ()) init impl draw readOut) ε := by
  simp only [knowledgeSoundness, knowledgeSoundnessWith,
    Interaction.Core.OracleVerifier.classicalStraightline,
    Interaction.Core.OracleVerifier.classicalModel, h.run_eq, h.extractionGame_eq]

/-- Agreeing verifiers are sound together. -/
theorem Agrees.soundness_iff (h : Agrees V V') {Out : PathAlong oracleSig s → Type}
    [mObs : MeasurableSpace (Observation oracleSig s Out (T × (∀ j, B j)))]
    (init : ProbComp σ) (impl : QueryImpl ambient (StateT σ ProbComp))
    (draw : QueryImpl (challengeSpec oracleSig s) ProbComp)
    (input : StatementProblem (S × (∀ i, A i))) (output : StatementProblem (T × (∀ j, B j)))
    (verdict : Observation oracleSig s Out (T × (∀ j, B j)) → Option (T × (∀ j, B j)))
    (ε : ℝ≥0∞) :
    soundness (V.classicalModel init impl draw) input output verdict ε ↔
      soundness (V'.classicalModel init impl draw) input output verdict ε := by
  rw [h.classicalModel_eq]

/-- Agreeing verifiers are complete together, for the same honest prover. -/
theorem Agrees.completeness_iff (h : Agrees V V') {Out : PathAlong oracleSig s → Type}
    [mObs : MeasurableSpace (Observation oracleSig s Out (T × (∀ j, B j)))]
    (init : ProbComp σ) (impl : QueryImpl ambient (StateT σ ProbComp))
    (draw : QueryImpl (challengeSpec oracleSig s) ProbComp)
    (input : StatementProblem (S × (∀ i, A i))) (output : StatementProblem (T × (∀ j, B j)))
    (J : OutputJudgement (Observation oracleSig s Out (T × (∀ j, B j))) _ output)
    (honest : ∀ stmt, input.Witness () stmt → Prover oracleSig ambient s Out) (ε : ℝ≥0∞) :
    completeness (V.classicalModel init impl draw) input output J honest ε ↔
      completeness (V'.classicalModel init impl draw) input output J honest ε := by
  simp only [completeness, Interaction.Core.OracleVerifier.classicalModel, h.run_eq]

/-- Agreeing verifiers have the same valid-acceptance predicate. -/
theorem Agrees.validAcceptance_eq (h : Agrees V V')
    (impl : QueryImpl ambient (StateT σ ProbComp)) (langOut : T × (∀ j, B j) → Prop) :
    V.validAcceptance impl langOut = V'.validAcceptance impl langOut := by
  funext stmt tr
  exact propext (h.validAcceptance_iff impl langOut stmt tr)

/-- Agreeing verifiers are round-by-round sound together. -/
theorem Agrees.rbrSoundness_iff (h : Agrees V V') (impl : QueryImpl ambient (StateT σ ProbComp))
    (input : StatementProblem (S × (∀ i, A i))) (output : StatementProblem (T × (∀ j, B j)))
    (draw : QueryImpl (challengeSpec oracleSig s) ProbComp) (ε : ChallengeNode oracleSig s → ℝ≥0∞) :
    V.rbrSoundness impl input output draw ε ↔ V'.rbrSoundness impl input output draw ε := by
  simp only [Interaction.Core.OracleVerifier.rbrSoundness, h.validAcceptance_eq]

/-- Agreeing verifiers are round-by-round knowledge sound together. -/
theorem Agrees.rbrKnowledgeSoundness_iff (h : Agrees V V') {W Win : Type}
    (impl : QueryImpl ambient (StateT σ ProbComp)) (admissible : S × (∀ i, A i) → Prop)
    (relIn : (S × (∀ i, A i)) → Win → Prop) (relOut : (T × (∀ j, B j)) → W → Prop)
    (draw : QueryImpl (challengeSpec oracleSig s) ProbComp) (ε : ChallengeNode oracleSig s → ℝ≥0∞) :
    V.rbrKnowledgeSoundness impl admissible relIn relOut draw ε ↔
      V'.rbrKnowledgeSoundness impl admissible relIn relOut draw ε := by
  simp only [Interaction.Core.OracleVerifier.rbrKnowledgeSoundness, h.validAcceptance_eq]

end Notions

section CastNotions
variable {ι I J S T σ WitIn WitOut : Type} {ambient : OracleSpec ι} {s s' : OracleProtocol}
  {A : I → Type} {B : J → Type} {inputs : OracleFamily I A} {outputs : OracleFamily J B}

/-- The legacy knowledge judgement on any oracle tree: the output statement and its output witness
are read from the prover's output, and the verdict from the verifier's output. -/
abbrev knowledgeJudgement (s : OracleProtocol) (relOut : Set ((T × ∀ j, B j) × WitOut)) :
    OutputJudgement (Observation oracleSig s (fun _ => (T × (∀ j, B j)) × WitOut)
      (T × (∀ j, B j))) (T × (∀ j, B j)) (relProblem relOut) :=
  OutputJudgement.ofObservation (relProblem relOut) (fun _ o => o.1) (fun obs _ _ => obs.2.1.2)

/-- Transporting a verifier and its challenge oracle along a tree equality preserves knowledge
soundness for legacy relations. -/
theorem knowledgeSoundness_cast (e : s' = s) (V : OracleVerifier ambient s' S T inputs outputs)
    (init : ProbComp σ) (impl : QueryImpl ambient (StateT σ ProbComp))
    (draw : QueryImpl (challengeSpec oracleSig s') ProbComp)
    (relIn : Set ((S × ∀ i, A i) × WitIn)) (relOut : Set ((T × ∀ j, B j) × WitOut))
    (ε : ℝ≥0∞) :
    (letI : MeasurableSpace (Observation oracleSig s (fun _ => (T × (∀ j, B j)) × WitOut)
      (T × (∀ j, B j))) := ⊤
    letI : MeasurableSpace WitIn := ⊤
    knowledgeSoundness ((e ▸ V).classicalModel init impl (e ▸ draw))
      (relProblem relIn) (relProblem relOut)
      (knowledgeJudgement s relOut)
      ((e ▸ V).classicalStraightline (fun _ => WitIn) init impl (e ▸ draw)
        (fun _ (o : (T × (∀ j, B j)) × WitOut) => o.2))
      ε) ↔
    (letI : MeasurableSpace (Observation oracleSig s' (fun _ => (T × (∀ j, B j)) × WitOut)
      (T × (∀ j, B j))) := ⊤
    letI : MeasurableSpace WitIn := ⊤
    knowledgeSoundness (V.classicalModel init impl draw)
      (relProblem relIn) (relProblem relOut)
      (knowledgeJudgement s' relOut)
      (V.classicalStraightline (fun _ => WitIn) init impl draw
        (fun _ (o : (T × (∀ j, B j)) × WitOut) => o.2)) ε) := by
  subst e; exact Iff.rfl

/-- Transporting a verifier and its challenge oracle along a tree equality preserves soundness for
legacy languages, for every prover output family. -/
theorem soundness_cast (e : s' = s) (V : OracleVerifier ambient s' S T inputs outputs)
    (init : ProbComp σ) (impl : QueryImpl ambient (StateT σ ProbComp))
    (draw : QueryImpl (challengeSpec oracleSig s') ProbComp)
    (langIn : Set (S × ∀ i, A i)) (langOut : Set (T × ∀ j, B j)) (ε : ℝ≥0∞) :
    (∀ Out : PathAlong oracleSig s → Type,
      letI : MeasurableSpace (Observation oracleSig s Out (T × (∀ j, B j))) := ⊤
      soundness ((e ▸ V).classicalModel (Out := Out) init impl (e ▸ draw))
        (langProblem langIn) (langProblem langOut) (fun obs => obs.2.2) ε) ↔
    (∀ Out : PathAlong oracleSig s' → Type,
      letI : MeasurableSpace (Observation oracleSig s' Out (T × (∀ j, B j))) := ⊤
      soundness (V.classicalModel (Out := Out) init impl draw)
        (langProblem langIn) (langProblem langOut) (fun obs => obs.2.2) ε) := by
  subst e; exact Iff.rfl

/-- Transporting a verifier, its challenge oracle and its error along a tree equality preserves
round-by-round soundness. -/
theorem rbrSoundness_cast (e : s' = s) (V : OracleVerifier ambient s' S T inputs outputs)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (input : StatementProblem (S × (∀ i, A i))) (output : StatementProblem (T × (∀ j, B j)))
    (draw : QueryImpl (challengeSpec oracleSig s') ProbComp)
    (ε : ChallengeNode oracleSig s' → ℝ≥0∞) :
    (e ▸ V).rbrSoundness impl input output (e ▸ draw) (e ▸ ε) ↔
      V.rbrSoundness impl input output draw ε := by
  subst e; exact Iff.rfl

/-- Transporting a verifier, its challenge oracle and its error along a tree equality preserves
round-by-round knowledge soundness. -/
theorem rbrKnowledgeSoundness_cast (e : s' = s) (V : OracleVerifier ambient s' S T inputs outputs)
    {W Win : Type} (impl : QueryImpl ambient (StateT σ ProbComp))
    (admissible : S × (∀ i, A i) → Prop)
    (relIn : (S × (∀ i, A i)) → Win → Prop) (relOut : (T × (∀ j, B j)) → W → Prop)
    (draw : QueryImpl (challengeSpec oracleSig s') ProbComp)
    (ε : ChallengeNode oracleSig s' → ℝ≥0∞) :
    (e ▸ V).rbrKnowledgeSoundness impl admissible relIn relOut (e ▸ draw) (e ▸ ε) ↔
      V.rbrKnowledgeSoundness impl admissible relIn relOut draw ε := by
  subst e; exact Iff.rfl

/-- A constant error is unchanged by transport along a tree equality. -/
theorem eqRec_const (e : s' = s) (x : ℝ≥0∞) :
    (e ▸ fun _ : ChallengeNode oracleSig s' => x) = fun _ : ChallengeNode oracleSig s => x := by
  subst e; rfl

/-- Transporting a verifier, its challenge oracle and its honest prover along a tree equality
preserves completeness for legacy relations. -/
theorem completeness_cast (e : s' = s) (V : OracleVerifier ambient s' S T inputs outputs)
    (init : ProbComp σ) (impl : QueryImpl ambient (StateT σ ProbComp))
    (draw : QueryImpl (challengeSpec oracleSig s') ProbComp)
    (relIn : Set ((S × ∀ i, A i) × WitIn)) (relOut : Set ((T × ∀ j, B j) × WitOut))
    (honest : ∀ (_ : S × ∀ i, A i) (_ : WitIn),
      Prover oracleSig ambient s' (fun _ => (T × (∀ j, B j)) × WitOut))
    (ε : ℝ≥0∞) :
    (letI : MeasurableSpace (Observation oracleSig s (fun _ => (T × (∀ j, B j)) × WitOut)
      (T × (∀ j, B j))) := ⊤
    completeness ((e ▸ V).classicalModel init impl (e ▸ draw))
      (relProblem relIn) (relProblem relOut) (knowledgeJudgement s relOut)
      (fun stmt wit => e ▸ honest stmt wit) ε) ↔
    (letI : MeasurableSpace (Observation oracleSig s' (fun _ => (T × (∀ j, B j)) × WitOut)
      (T × (∀ j, B j))) := ⊤
    completeness (V.classicalModel init impl draw)
      (relProblem relIn) (relProblem relOut) (knowledgeJudgement s' relOut) honest ε) := by
  subst e; exact Iff.rfl

end CastNotions

/-! ## Program equality -/

section RunCast
variable {ι I J S T X κ Y : Type} {ambient : OracleSpec ι} {s s' : OracleProtocol}
  {A : I → Type} {B : J → Type} {inputs : OracleFamily I A} {outputs : OracleFamily J B}
  {spec : OracleSpec κ}

/-- Transporting a verifier and a challenge reindexing along a tree equality, and the prover back,
gives the same finalized program when the two finalizations agree on corresponding transcripts. -/
theorem run_cast (e : s' = s) (V : OracleVerifier ambient s' S T inputs outputs)
    (impl : QueryImpl (ambient + challengeSpec oracleSig s') (OracleComp spec))
    (f : Observation oracleSig s (fun _ => X) (T × (∀ j, B j)) → Y)
    (g : Observation oracleSig s' (fun _ => X) (T × (∀ j, B j)) → Y)
    (hfg : ∀ tr out v, f ⟨e ▸ tr, out, v⟩ = g ⟨tr, out, v⟩)
    (stmt : S) (data : ∀ i, A i) (p : Prover oracleSig ambient s (fun _ => X)) :
    simulateQ (e ▸ impl) (f <$> (e ▸ V).run stmt data p) =
      simulateQ impl (g <$> V.run stmt data (e.symm ▸ p)) := by
  subst e
  have : f = g := funext fun ⟨tr, out, v⟩ => hfg tr out v
  subst this; rfl

end RunCast

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
      (Spec.StatementRound R n (Fin.last n) × (∀ i, Spec.OracleStatement R n deg i))) :
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
  exact run_cast (protocol_eq R deg n).symm _ _ finalize oracleFinalize (fun tr out v => by
    simp only [finalize, oracleFinalize]
    rw [← oracleDecode_eq_decodeTranscript n _ tr (eqRec_heq _ _)]) stmt oStmt p

end Run

/-! ## Pure challenge slots of the legacy honest prover

The legacy Sumcheck prover is a sequential composition of lifted single-round provers. Each
single-round prover receives its challenge with a `pure` slot and has a pure output, and appending,
lifting and sequential composition preserve both, so every challenge slot of the composed prover is
`pure`. This is the hypothesis under which the legacy run equals the counterpart-first run as a
program. -/

section PureSlots
variable {ι : Type} {oSpec : OracleSpec ι}

/-- A computation heterogeneously equal to `pure f` is `pure`. -/
theorem pure_of_heq {X Y : Type} (hXY : X = Y) {x : OracleComp oSpec Y} {f : X}
    (h : HEq x (pure f : OracleComp oSpec X)) : ∃ g, x = pure g := by
  subst hXY; exact ⟨f, eq_of_heq h⟩

variable {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  {S₁ W₁ S₂ W₂ S₃ W₃ : Type}

/-- Appending legacy provers keeps every challenge slot `pure` when the first prover's output is
pure. -/
theorem pureChallengeSlots_append (P₁ : Prover oSpec S₁ W₁ S₂ W₂ pSpec₁)
    (P₂ : Prover oSpec S₂ W₂ S₃ W₃ pSpec₂) [h : P₁.OutputIsPure]
    (h₁ : PureChallengeSlots P₁) (h₂ : PureChallengeSlots P₂) :
    PureChallengeSlots (P₁.append P₂) := by
  rintro ⟨i, hDir⟩ st
  by_cases hi : i.val < m
  · have hDir₁ : pSpec₁.dir ⟨i.val, hi⟩ = .V_to_P := by
      simpa [Fin.vappend_left_of_lt, hi] using hDir
    obtain ⟨f, hf⟩ := h₁ ⟨⟨i.val, hi⟩, hDir₁⟩
      (cast (Prover.append_prvState_left _ _ rfl) st)
    refine pure_of_heq ?_ (HEq.trans ?_ (heq_of_eq hf))
    · have hT : (pSpec₁ ++ₚ pSpec₂).«Type» i = pSpec₁.«Type» ⟨i.val, hi⟩ := by
        exact (congrArg (pSpec₁ ++ₚ pSpec₂).«Type»
          (Fin.ext rfl : i = Fin.castAdd n ⟨i.val, hi⟩)).trans (append_Type_castAdd _)
      have hS := Prover.append_prvState_left (P₁ := P₁) (P₂ := P₂) i.succ
        (⟨i.val, hi⟩ : Fin m).succ rfl
      exact congrArg₂ (fun A B => A → B) hT.symm hS.symm
    · conv_lhs => unfold Prover.append
      dsimp only
      rw [dite_eq_left hi]
      refine (cast_heq _ _).trans (heq_of_eq ?_)
      congr 1
  by_cases him : i.val = m
  · have hn : 0 < n := by have := i.isLt; omega
    have hDir₂ : pSpec₂.dir ⟨0, hn⟩ = .V_to_P := by
      have := (congrArg (pSpec₁ ++ₚ pSpec₂).dir
        (Fin.ext (by simp [him]) : i = Fin.natAdd m ⟨0, hn⟩)).symm.trans hDir
      simpa [Fin.vappend_right_of_not_lt] using this
    obtain ⟨out, hout⟩ := h.output_is_pure
    have hS₁ := Prover.append_prvState_left (P₁ := P₁) (P₂ := P₂) i.castSucc (Fin.last m)
      (by simp [him])
    obtain ⟨f, hf⟩ := h₂ ⟨⟨0, hn⟩, hDir₂⟩ (P₂.input (out (cast hS₁ st)))
    refine pure_of_heq ?_ (HEq.trans ?_ (heq_of_eq hf))
    · have hT : (pSpec₁ ++ₚ pSpec₂).«Type» i = pSpec₂.«Type» ⟨0, hn⟩ :=
        (congrArg (pSpec₁ ++ₚ pSpec₂).«Type»
          (Fin.ext (by simp [him]) : i = Fin.natAdd m ⟨0, hn⟩)).trans (append_Type_natAdd _)
      have hS := Prover.append_prvState_right (P₁ := P₁) (P₂ := P₂) i.succ
        (⟨0, hn⟩ : Fin n).succ (by simp; omega) (by simp; omega)
      exact congrArg₂ (fun A B => A → B) hT.symm hS.symm
    · conv_lhs => unfold Prover.append
      dsimp only
      rw [dite_eq_right hi, dite_eq_left him]
      refine (cast_heq _ _).trans (heq_of_eq ?_)
      rw [hout]
      simp only [LawfulMonad.pure_bind]
      exact congrArg (fun z => P₂.receiveChallenge ⟨⟨0, hn⟩, hDir₂⟩ (P₂.input (out z)))
        (eq_of_heq ((cast_heq _ _).trans (cast_heq _ _).symm))
  have hik : i.val - m < n := by have := i.isLt; omega
  have hidx : i = Fin.natAdd m ⟨i.val - m, hik⟩ := Fin.ext (by simp; omega)
  have hDir₂ : pSpec₂.dir ⟨i.val - m, hik⟩ = .V_to_P := by
    have := (congrArg (pSpec₁ ++ₚ pSpec₂).dir hidx).symm.trans hDir
    simpa [Fin.vappend_right_of_not_lt] using this
  have hS₂ := Prover.append_prvState_right (P₁ := P₁) (P₂ := P₂) i.castSucc
    (⟨i.val - m, hik⟩ : Fin n).castSucc (by simp; omega) (by simp; omega)
  obtain ⟨f, hf⟩ := h₂ ⟨⟨i.val - m, hik⟩, hDir₂⟩ (cast hS₂ st)
  refine pure_of_heq ?_ (HEq.trans ?_ (heq_of_eq hf))
  · have hT : (pSpec₁ ++ₚ pSpec₂).«Type» i = pSpec₂.«Type» ⟨i.val - m, hik⟩ :=
      (congrArg (pSpec₁ ++ₚ pSpec₂).«Type» hidx).trans (append_Type_natAdd _)
    have hS := Prover.append_prvState_right (P₁ := P₁) (P₂ := P₂) i.succ
      (⟨i.val - m, hik⟩ : Fin n).succ (by simp; omega) (by simp; omega)
    exact congrArg₂ (fun A B => A → B) hT.symm hS.symm
  · conv_lhs => unfold Prover.append
    dsimp only
    rw [dite_eq_right hi, dite_eq_right him]
    refine (cast_heq _ _).trans (heq_of_eq ?_)
    congr 1
    exact eq_of_heq ((heq_dcast _ _).trans ((cast_heq _ _).trans (cast_heq _ _).symm))

/-- The identity prover has no challenge slots. -/
theorem pureChallengeSlots_id {S W : Type} :
    PureChallengeSlots (Prover.id : Prover oSpec S W S W !p[]) := fun i => Fin.elim0 i.1

/-- Lifting a legacy prover to an outer context keeps its challenge slots `pure`. -/
theorem pureChallengeSlots_liftContext {n : ℕ} {pSpec : ProtocolSpec n}
    {OS OW IS IW OS' OW' IS' IW' : Type}
    (lens : Context.Lens OS OS' IS IS' OW OW' IW IW')
    (P : Prover oSpec IS IW IS' IW' pSpec) (h : PureChallengeSlots P) :
    PureChallengeSlots (P.liftContext lens) := by
  rintro i ⟨st, s, w⟩
  obtain ⟨f, hf⟩ := h i st
  exact ⟨fun chal => ⟨f chal, s, w⟩, by simp [Prover.liftContext, hf]⟩

/-- Sequentially composing legacy provers with pure outputs keeps every challenge slot `pure`. -/
theorem pureChallengeSlots_seqCompose : ∀ {k : ℕ} (Stmt Wit : Fin (k + 1) → Type)
    {n : Fin k → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (P : (i : Fin k) →
      Prover oSpec (Stmt i.castSucc) (Wit i.castSucc) (Stmt i.succ) (Wit i.succ) (pSpec i))
    (_ : ∀ i, (P i).OutputIsPure) (_ : ∀ i, PureChallengeSlots (P i)),
    PureChallengeSlots (Prover.seqCompose Stmt Wit P)
  | 0, _, _, _, _, _, _, _ => pureChallengeSlots_id
  | _ + 1, Stmt, Wit, _, _, P, hO, hP => by
    exact pureChallengeSlots_append _ _ (h := hO 0) (hP 0)
      (pureChallengeSlots_seqCompose (Stmt ∘ Fin.succ) (Wit ∘ Fin.succ) (fun i => P i.succ)
        (fun i => hO i.succ) (fun i => hP i.succ))

end PureSlots

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

/-- The legacy honest Sumcheck prover receives every challenge with a `pure` slot. -/
theorem legacyProver_pureChallengeSlots :
    PureChallengeSlots (Spec.oracleReduction R deg D n oSpec).prover :=
  pureChallengeSlots_seqCompose _ _ _
    (fun i => Spec.SingleRound.instOutputIsPureReduction R n deg D oSpec i)
    (fun _ => pureChallengeSlots_liftContext _ _ (simple_pureChallengeSlots R deg oSpec))

end Slots

section LegacyProver
variable (R : Type) [CommSemiring R] [DecidableEq R] [SampleableType R] (deg n : ℕ)
  {d : ℕ} (D : Fin d ↪ R) {ι : Type} (ambient : OracleSpec ι) [∀ t, Inhabited (ambient.Range t)]

/-- The legacy honest Sumcheck prover, embedded and read on the interaction-layer tree. -/
noncomputable def legacyProver
    (stmt : Spec.StatementRound R n 0 × ∀ i, Spec.OracleStatement R n deg i)
    (wit : Unit) : Prover oracleSig ambient (protocol R deg n)
      (fun _ => (Spec.StatementRound R n (Fin.last n) × (∀ i, Spec.OracleStatement R n deg i)) ×
        Unit) :=
  (protocol_eq R deg n).symm ▸
    embedOracleProver (Spec.oracleReduction R deg D n ambient).prover stmt.1 stmt.2 wit

end LegacyProver

/-! ## The honest legacy run and the decision trace -/

section Honest

/-- Transport and transport back along the same equality cancel. -/
theorem eqRec_eqRec_symm {α : Sort*} {F : α → Sort*} {a b : α} (e : b = a) (x : F a) :
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

/-- **Decision trace.** In every lawful monad, with ambient queries answered by any implementation,
the decisions of the Sumcheck verifier and of the embedded legacy verifier are both `pure` of the
legacy verdict. Neither makes an ambient query; instantiating the monad with a logging monad shows
that their query traces are equal and empty. -/
theorem decide_trace {m : Type → Type} [Monad m] [LawfulMonad m]
    (amb : QueryImpl ambient m) (stmt : Spec.StatementRound R n 0)
    (data : ∀ i, Spec.OracleStatement R n deg i) (tr : PathAlong oracleSig (protocol R deg n)) :
    simulateQ (QueryImpl.addLift amb ((sumFamily (polyFamily R deg n)
        (pathFamily (protocol R deg n) (projectPathAlong oracleSig _ tr))).behaviorOfRealizations
          (sumData data (payloads _ tr))))
      ((verifier R deg n D ambient).decide stmt _ (toView _ tr)).run =
      (pure (legacyVerdict R deg n D ambient stmt (decodeTranscript n tr)) : m _) ∧
    simulateQ (QueryImpl.addLift amb ((sumFamily (polyFamily R deg n)
        (pathFamily (protocol R deg n) (projectPathAlong oracleSig _ tr))).behaviorOfRealizations
          (sumData data (payloads _ tr))))
      ((legacyVerifier R deg n D ambient).decide stmt _ (toView _ tr)).run =
      (pure (legacyVerdict R deg n D ambient stmt (decodeTranscript n tr)) : m _) :=
  ⟨simulateQ_decide_monad D amb stmt data tr,
    (((verifier_agrees R deg n D ambient) stmt data tr).1 m amb).symm.trans
      (simulateQ_decide_monad D amb stmt data tr)⟩

end Honest
end Sumcheck.Core
