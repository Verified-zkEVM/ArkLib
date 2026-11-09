/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Core.Protocol
public import ArkLib.ProofSystem.Sumcheck.Spec.General
public import ArkLib.Interaction.Core.LegacyAppend

/-!
# Sumcheck verification and execution in the interaction layer

The verifier of the replicated Sumcheck protocol is the passive sampler, which requests one ring
challenge per round as a query to the challenge oracle, followed by the legacy decision fold
`Spec.oracleVerifierProgram` applied to the completed run. The verifier does not choose the
challenge distribution: the requests are uniform when the challenge oracle is interpreted with
`challengeQueryImpl`, as in `perfectCompleteness_uniform`.

The decision reads the challenges from the verifier view and answers each legacy message query
through `route`, which sends it to the oracle node of its round. The output oracle is the input
polynomial, kept by an embedding output map.

The routing and the verifier are generic in the message carrier and the input family:
`verifierOn` runs the same legacy decision fold on `protocolOn R M eval n`, and `verifier` is its
instance at the polynomial carrier and the input polynomial family.

The interaction always runs every round. A failed round check makes the legacy fold return
`none` and skips only the later checks.

The main results are:

* `simulateQ_route`: answering routed queries from the run's payloads answers the legacy message
  queries from the decoded transcript `decodeTranscript`;
* `simulateQ_decide`: on any completed run the decision returns `legacyVerdict` of the decoded
  transcript, the verdict of the legacy oracle verifier (`simulateQ_legacy_verify`);
* `run_verifier_foldRounds` and `run_verifier_honestProver`: closed forms of the execution;
* `legacyVerdict_eq_none`: a first round whose sum misses the target is rejected, whatever the
  later rounds.
-/

@[expose] public section

namespace Sumcheck.Core
open Polynomial PFunctor FreeM Interaction.Core Interaction.TwoParty.Lens Interaction.Oracle
  OracleComp OracleSpec ProtocolSpec

/-! ## Decoding -/

section Decode

variable {R : Type} [CommSemiring R] {deg : ℕ}

attribute [local implicit_reducible] FreeM.replicate

/-- The legacy full transcript of one round. -/
def roundFullTranscript (msg : R⦃≤ deg⦄[X]) (chal : R) :
    FullTranscript (Spec.SingleRound.pSpec R deg)
  | 0 => msg
  | 1 => chal

/-- The legacy full transcript with the given round messages and challenges. -/
def legacyTranscript : (k : ℕ) → (Fin k → R⦃≤ deg⦄[X]) → (Fin k → R) →
    FullTranscript (Spec.pSpec R deg k)
  | 0, _, _ => fun i => i.elim0
  | k + 1, msgs, chals => roundFullTranscript (msgs 0) (chals 0) ++ₜ
      legacyTranscript k (Fin.tail msgs) (Fin.tail chals)

/-- The round messages of an interaction-layer transcript. -/
def transcriptMessages :
    (k : ℕ) → PathAlong oracleSig (protocol R deg k) → Fin k → R⦃≤ deg⦄[X]
  | 0, _ => Fin.elim0
  | k + 1, tr => Fin.cons (headMessage tr) (transcriptMessages k (tailTranscript tr))

/-- The challenges of an interaction-layer transcript. -/
def transcriptChallenges : (k : ℕ) → PathAlong oracleSig (protocol R deg k) → Fin k → R
  | 0, _ => Fin.elim0
  | k + 1, tr => Fin.cons (headChallenge tr) (transcriptChallenges k (tailTranscript tr))

/-- Decode an interaction-layer transcript into the legacy full transcript. -/
def decodeTranscript (k : ℕ) (tr : PathAlong oracleSig (protocol R deg k)) :
    FullTranscript (Spec.pSpec R deg k) :=
  legacyTranscript k (transcriptMessages k tr) (transcriptChallenges k tr)

end Decode

/-! ## Routing message queries -/

section Route

variable (R : Type) [CommSemiring R] (deg : ℕ) (M : Type) (eval : M → R → R)

attribute [local implicit_reducible] FreeM.replicate

/-- Route the round message's queries to the first oracle node of a replicated protocol over the
message carrier `M`. -/
def roundRouteOn (k : ℕ) (p : Path (protocolOn R M eval k)) :
    QueryImpl [(Spec.SingleRound.pSpec R deg).Message]ₒ
      (OracleComp (oracles (protocolOn R M eval (k + 1)) ⟨⟨⟩, ⟨⟨⟩, p⟩⟩)) :=
  fun ⟨i, q⟩ => by
    obtain rfl := Unique.eq_default i
    exact liftM
      ((oracles (protocolOn R M eval (k + 1)) ⟨⟨⟩, ⟨⟨⟩, p⟩⟩).query ⟨.inl ⟨⟩, q⟩)

omit [CommSemiring R] in
/-- Lift the queries of the remaining rounds to a replicated protocol with one more round, over
the message carrier `M`. -/
def tailLiftOn (k : ℕ) (p : Path (protocolOn R M eval k)) :
    QueryImpl (oracles (protocolOn R M eval k) p)
      (OracleComp (oracles (protocolOn R M eval (k + 1)) ⟨⟨⟩, ⟨⟨⟩, p⟩⟩)) :=
  fun q => liftM
    ((oracles (protocolOn R M eval (k + 1)) ⟨⟨⟩, ⟨⟨⟩, p⟩⟩).query ⟨.inr q.1, q.2⟩)

/-- Route legacy message queries to the oracle nodes of a completed shape path, over the message
carrier `M`. The legacy and node queries are both evaluation points in `R`. -/
def routeOn : (k : ℕ) → (p : Path (protocolOn R M eval k)) →
    QueryImpl [(Spec.pSpec R deg k).Message]ₒ (OracleComp (oracles (protocolOn R M eval k) p))
  | 0, _ => fun q => q.1.1.elim0
  | k + 1, ⟨⟨⟩, ⟨⟨⟩, p⟩⟩ => Legacy.appendRoute (roundRouteOn R deg M eval k p)
      (fun q => simulateQ (tailLiftOn R M eval k p) (routeOn k p q))

/-- Route the round message's queries to the first oracle node of a replicated protocol. -/
def roundRoute (k : ℕ) (p : Path (protocol R deg k)) :
    QueryImpl [(Spec.SingleRound.pSpec R deg).Message]ₒ
      (OracleComp (oracles (protocol R deg (k + 1)) ⟨⟨⟩, ⟨⟨⟩, p⟩⟩)) :=
  roundRouteOn R deg _ _ k p

/-- Lift the queries of the remaining rounds to a replicated protocol with one more round. -/
def tailLift (k : ℕ) (p : Path (protocol R deg k)) :
    QueryImpl (oracles (protocol R deg k) p)
      (OracleComp (oracles (protocol R deg (k + 1)) ⟨⟨⟩, ⟨⟨⟩, p⟩⟩)) :=
  tailLiftOn R _ _ k p

/-- Route legacy message queries to the oracle nodes of a completed shape path. -/
def route (k : ℕ) (p : Path (protocol R deg k)) :
    QueryImpl [(Spec.pSpec R deg k).Message]ₒ (OracleComp (oracles (protocol R deg k) p)) :=
  routeOn R deg _ _ k p

end Route

section RouteAnswer

variable {R : Type} [CommSemiring R] {deg : ℕ}

attribute [local implicit_reducible] FreeM.replicate projectPathAlong projectPathAlongLocalMap
  Displayed.LocalMap.toHom Displayed.LocalMap.toHomFun

/-- A routed query of a replicated protocol with one more round splits by its legacy half. -/
theorem route_succ_sumEquiv (k : ℕ) (p : Path (protocol R deg k))
    (s : (Spec.SingleRound.pSpec R deg).MessageIdx ⊕ (Spec.pSpec R deg k).MessageIdx)
    (q : OracleInterface.Query
      ((Spec.SingleRound.pSpec R deg ++ₚ Spec.pSpec R deg k).Message (MessageIdx.sumEquiv s))) :
    route R deg (k + 1) ⟨⟨⟩, ⟨⟨⟩, p⟩⟩ ⟨MessageIdx.sumEquiv s, q⟩ =
      Legacy.routePart (roundRoute R deg k p)
        (fun q => simulateQ (tailLift R deg k p) (route R deg k p q))
        s q :=
  Legacy.appendRoute_sumEquiv _ _ s q

/-- Answering routed queries from the run's payloads answers the legacy message queries from the
decoded transcript. -/
theorem simulateQ_route : (k : ℕ) → (tr : PathAlong oracleSig (protocol R deg k)) →
    (q : [(Spec.pSpec R deg k).Message]ₒ.Domain) →
    simulateQ (payloadImpl (protocol R deg k) tr)
        (route R deg k (projectPathAlong oracleSig _ tr) q) =
      OracleInterface.simOracle0 (Spec.pSpec R deg k).Message (decodeTranscript k tr).messages q
  | 0, _, q => q.1.1.elim0
  | k + 1, ⟨msg, ⟨chal, tail⟩⟩, ⟨j, q⟩ => by
    obtain ⟨s, rfl⟩ := (MessageIdx.sumEquiv (pSpec₁ := Spec.SingleRound.pSpec R deg)
      (pSpec₂ := Spec.pSpec R deg k)).surjective j
    refine (congrArg (simulateQ _)
      (route_succ_sumEquiv k (projectPathAlong oracleSig _ tail) s q)).trans ?_
    rcases s with i | i
    · refine Legacy.simulateQ_queryAlongHEq _ _ _ _ _ _ _ (roundFullTranscript msg chal i.1)
        ?_ ?_ q
      · exact (FullTranscript.fst_apply_heq _ _).symm.trans
          (heq_of_eq (congrFun (FullTranscript.append_fst _ _) _))
      · intro q'
        obtain rfl := Unique.eq_default i
        exact simulateQ_spec_query _ _
    · refine Legacy.simulateQ_queryAlongHEq _ _ _ _ _ _ _
        ((decodeTranscript k tail).messages i) ?_ ?_ q
      · exact (FullTranscript.snd_apply_heq _ _).symm.trans
          (heq_of_eq (congrFun (FullTranscript.append_snd _ _) _))
      · intro q'
        refine (QueryImpl.simulateQ_simulateQ_eq_of_apply
          (impl := payloadImpl (protocol R deg k) tail) (fun t => ?_) _).trans
          (simulateQ_route k tail ⟨i, q'⟩)
        exact simulateQ_spec_query _ _

end RouteAnswer

/-! ## Challenges in the verifier view -/

section View

variable {R : Type} [CommSemiring R] {deg : ℕ}

attribute [local implicit_reducible] FreeM.replicate projectPathAlong projectPathAlongLocalMap
  Displayed.LocalMap.toHom Displayed.LocalMap.toHomFun

omit [CommSemiring R] in
/-- The challenges recorded in a verifier view over the message carrier `M`, in round order. -/
def viewChallengeListOn {M : Type} {eval : M → R → R} :
    (k : ℕ) → PathAlong viewSig (protocolOn R M eval k) → Fin k → R
  | 0, _ => Fin.elim0
  | k + 1, v => Fin.cons v.2.1 (viewChallengeListOn k v.2.2)

/-- The challenges recorded in a verifier view, in round order. -/
def viewChallengeList (k : ℕ) (v : PathAlong viewSig (protocol R deg k)) : Fin k → R :=
  viewChallengeListOn k v

/-- Erasing the messages keeps every challenge. -/
theorem viewChallengeList_toView : (k : ℕ) → (tr : PathAlong oracleSig (protocol R deg k)) →
    viewChallengeList k (toView (protocol R deg k) tr).1 = transcriptChallenges k tr
  | 0, _ => rfl
  | k + 1, ⟨_, ⟨chal, tail⟩⟩ => by
    change (Fin.cons chal (viewChallengeList k (toView (protocol R deg k) tail).1) :
        Fin (k + 1) → R) =
      Fin.cons chal (transcriptChallenges k tail)
    rw [viewChallengeList_toView k tail]

/-- The challenge entries of one round. -/
def roundChallengeFn (chal : R) : Legacy.ChallengeFn (Spec.SingleRound.pSpec R deg)
  | 0 => fun h => nomatch h
  | 1 => fun _ => chal

/-- The challenge entries of the legacy transcript with the given challenges. -/
def legacyChallengeFn : (k : ℕ) → (Fin k → R) → Legacy.ChallengeFn (Spec.pSpec R deg k)
  | 0, _ => fun i => i.elim0
  | k + 1, chals => Fin.fappend₂ (A := Direction) (B := Type)
        (F := fun dir type => dir = Direction.V_to_P → type)
      (roundChallengeFn (deg := deg) (chals 0)) (legacyChallengeFn k (Fin.tail chals))

/-- A transported challenge entry is the original entry at the transported position. -/
private theorem cast_challengeFn_heq {a a' : Direction} {T T' : Type} (ea : a = a') (eT : T = T')
    (e : (a = .V_to_P → T) = (a' = .V_to_P → T')) (f : a = .V_to_P → T) (h : a' = .V_to_P) :
    HEq (cast e f h) (f (ea.trans h)) := by
  subst ea
  subst eT
  rfl

/-- Every challenge of a legacy transcript is its challenge entry, whatever the messages. -/
theorem legacyTranscript_apply_challenge : (k : ℕ) → (msgs : Fin k → R⦃≤ deg⦄[X]) →
    (chals : Fin k → R) → (i : Fin (Fin.vsum fun _ : Fin k => 2)) →
    (h : (Spec.pSpec R deg k).dir i = .V_to_P) →
    legacyTranscript k msgs chals i = legacyChallengeFn k chals i h
  | 0, _, _, i, _ => i.elim0
  | k + 1, msgs, chals, i, h => by
    change (roundFullTranscript (msgs 0) (chals 0) ++ₜ
        legacyTranscript k (Fin.tail msgs) (Fin.tail chals)) i =
      Fin.fappend₂ (A := Direction) (B := Type)
        (F := fun dir type => dir = Direction.V_to_P → type)
        (roundChallengeFn (deg := deg) (chals 0))
        (legacyChallengeFn (deg := deg) k (Fin.tail chals)) i h
    induction i using Fin.addCases with
    | left i =>
      have e₁ := Fin.happend_left (roundFullTranscript (msgs 0) (chals 0))
        (legacyTranscript k (Fin.tail msgs) (Fin.tail chals)) i
      have e₂ := congrFun (Fin.fappend₂_left (A := Direction) (B := Type)
        (F₂ := fun dir type => dir = Direction.V_to_P → type)
        (α₁ := (Spec.SingleRound.pSpec R deg).dir) (α₂ := (Spec.SingleRound.pSpec R deg).Type)
        (β₁ := (Spec.pSpec R deg k).dir) (β₂ := (Spec.pSpec R deg k).Type)
        (roundChallengeFn (chals 0)) (legacyChallengeFn (deg := deg) k (Fin.tail chals)) i) h
      refine eq_of_heq (((heq_of_eq e₁).trans (cast_heq _ _)).trans (HEq.symm
        ((heq_of_eq e₂).trans ((cast_challengeFn_heq (Fin.vappend_left _ _ i).symm
          (Fin.vappend_left _ _ i).symm _ _ h).trans ?_))))
      fin_cases i
      · exact nomatch (Fin.vappend_left _ _ _).symm.trans h
      · exact HEq.rfl
    | right i =>
      have e₁ := Fin.happend_right (roundFullTranscript (msgs 0) (chals 0))
        (legacyTranscript k (Fin.tail msgs) (Fin.tail chals)) i
      have e₂ := congrFun (Fin.fappend₂_right (A := Direction) (B := Type)
        (F₂ := fun dir type => dir = Direction.V_to_P → type)
        (α₁ := (Spec.SingleRound.pSpec R deg).dir) (α₂ := (Spec.SingleRound.pSpec R deg).Type)
        (β₁ := (Spec.pSpec R deg k).dir) (β₂ := (Spec.pSpec R deg k).Type)
        (roundChallengeFn (chals 0)) (legacyChallengeFn (deg := deg) k (Fin.tail chals)) i) h
      refine eq_of_heq (((heq_of_eq e₁).trans (cast_heq _ _)).trans (HEq.symm
        ((heq_of_eq e₂).trans ((cast_challengeFn_heq (Fin.vappend_right _ _ i).symm
          (Fin.vappend_right _ _ i).symm _ _ h).trans ?_))))
      exact heq_of_eq (legacyTranscript_apply_challenge k _ _ i _).symm

/-- The legacy challenges recorded in a verifier view over the message carrier `M`. -/
def viewChallengesOn {M : Type} {eval : M → R → R} {k : ℕ} {p : Path (protocolOn R M eval k)}
    (v : View (protocolOn R M eval k) p) : (Spec.pSpec R deg k).Challenges :=
  fun j => legacyChallengeFn k (viewChallengeListOn k v.1) j.1 j.2

/-- The legacy challenges recorded in a verifier view. It is `viewChallengesOn` at the
polynomial carrier. -/
def viewChallenges {k : ℕ} {p : Path (protocol R deg k)} (v : View (protocol R deg k) p) :
    (Spec.pSpec R deg k).Challenges :=
  fun j => legacyChallengeFn k (viewChallengeList k v.1) j.1 j.2

/-- The view of a run has the challenges of its decoded transcript. -/
theorem viewChallenges_toView (k : ℕ) (tr : PathAlong oracleSig (protocol R deg k)) :
    viewChallenges (toView (protocol R deg k) tr) = (decodeTranscript k tr).challenges := by
  funext j
  unfold viewChallenges
  rw [viewChallengeList_toView]
  exact (legacyTranscript_apply_challenge k _ _ j.1 j.2).symm

end View

/-! ## The verifier -/

section Verifier

variable (R : Type) [CommSemiring R] [DecidableEq R] [SampleableType R] (deg n : ℕ)
  {d : ℕ} (D : Fin d ↪ R) {ι : Type} (ambient : OracleSpec ι)

/-- The input and output oracle: the multivariate polynomial with evaluation queries.

It is noncomputable because the legacy evaluation interface of multivariate polynomials is. Only
its types enter the verifier, which stays executable. -/
noncomputable def polyFamily : OracleFamily Unit (Spec.OracleStatement R n deg) :=
  ⟨fun _ => inferInstance⟩

/-- The legacy check of round `i`, retyped to query only that round's message. -/
def roundCheck (i : Fin n) (stmt : Spec.StatementRound R n i.castSucc)
    (chals : (Spec.SingleRound.pSpec R deg).Challenges) :
    OptionT (OracleComp [(Spec.SingleRound.pSpec R deg).Message]ₒ)
      (Spec.StatementRound R n i.succ) :=
  OptionT.mk (Spec.messageOnlyRoundProgram R deg n ambient
    ((Spec.SingleRound.oracleVerifier R n deg D ambient i).verify stmt chals).run
    (Spec.SingleRound.oracleVerifier_only_message_queries R n deg D ambient i stmt chals))

/-- The legacy decision fold. It queries only the round polynomials sent by the prover. -/
def legacyProgram (stmt : Spec.StatementRound R n 0)
    (chals : (Spec.pSpec R deg n).Challenges) :
    OracleComp [(Spec.pSpec R deg n).Message]ₒ (Option (Spec.StatementRound R n (Fin.last n))) :=
  Spec.oracleVerifierProgram R deg (Spec.StatementRound R n) (roundCheck R deg n D ambient)
    stmt chals

/-- The legacy oracle verifier runs exactly the legacy decision fold. -/
theorem legacy_verify_eq (stmt : Spec.StatementRound R n 0)
    (chals : (Spec.pSpec R deg n).Challenges) :
    (Spec.oracleVerifier R deg D n ambient).verify stmt chals = OptionT.mk
      (OracleComp.liftComp (legacyProgram R deg n D ambient stmt chals)
        (ambient + ([Spec.OracleStatement R n deg]ₒ + [(Spec.pSpec R deg n).Message]ₒ))) :=
  rfl

section On

variable (M : Type) (eval : M → R → R) {I : Type} {A : I → Type} (inputs : OracleFamily I A)

omit [DecidableEq R] [SampleableType R] in
/-- Lift path-oracle queries into the decision's query interface, over the message carrier `M`
and the input family `inputs`. -/
@[macro_inline]
def decisionLiftOn (p : Path (protocolOn R M eval n)) :
    QueryImpl (oracles (protocolOn R M eval n) p)
      (OracleComp (ambient + (sumFamily inputs (pathFamily (protocolOn R M eval n) p)).spec)) :=
  fun q => liftM ((ambient + (sumFamily inputs
    (pathFamily (protocolOn R M eval n) p)).spec).query (.inr ⟨.inr q.1, q.2⟩))

/-- The Sumcheck oracle verifier over the message carrier `M` and the input family `inputs`: the
legacy decision fold on the view's challenges, with every message query routed to its oracle
node. The output oracle is the input family.

The decision depends on `M` only through `eval`, which answers the routed queries. The input
family enters only types. Both this definition and `decisionLiftOn` are macro-inlined, so the
compiler never receives the input family as a runtime argument and an instance at a noncomputable
input family, such as `verifier`, stays executable. -/
@[macro_inline]
def verifierOn : OracleVerifier ambient (protocolOn R M eval n) (Spec.StatementRound R n 0)
    (Spec.StatementRound R n (Fin.last n)) inputs inputs where
  decide stmt p v := OptionT.mk (simulateQ (decisionLiftOn R n ambient M eval inputs p)
    (simulateQ (routeOn R deg M eval n p)
      (legacyProgram R deg n D ambient stmt (viewChallengesOn v))))
  outputMap _ p _ :=
    { f := fun x i => x (.inl i)
      impl := fun q => liftM ((sumFamily inputs
        (pathFamily (protocolOn R M eval n) p)).spec.query ⟨.inl q.1, q.2⟩)
      law := fun _ _ => rfl }

end On

/-- Lift path-oracle queries into the decision's query interface. -/
def decisionLift (p : Path (protocol R deg n)) :
    QueryImpl (oracles (protocol R deg n) p)
      (OracleComp (ambient + (sumFamily (polyFamily R deg n)
        (pathFamily (protocol R deg n) p)).spec)) :=
  decisionLiftOn R n ambient _ _ (polyFamily R deg n) p

/-- The Sumcheck oracle verifier: the legacy decision fold on the view's challenges, with every
message query routed to its oracle node. The output oracle is the input polynomial. -/
def verifier : OracleVerifier ambient (protocol R deg n) (Spec.StatementRound R n 0)
    (Spec.StatementRound R n (Fin.last n)) (polyFamily R deg n) (polyFamily R deg n) :=
  verifierOn R deg n D ambient _ _ (polyFamily R deg n)

/-- The output map keeps the input polynomial: it is the embedding of the input slot. -/
theorem verifier_outputMap (stmt : Spec.StatementRound R n 0) (p : Path (protocol R deg n))
    (v : View (protocol R deg n) p) :
    (verifier R deg n D ambient).outputMap stmt p v =
      OracleMap.embedding (sumFamily (polyFamily R deg n) (pathFamily (protocol R deg n) p))
        (fun _ => .inl ()) :=
  rfl

/-- The decision is the legacy decision fold with its message queries renamed by `route`. -/
theorem verifier_decide (stmt : Spec.StatementRound R n 0) (p : Path (protocol R deg n))
    (v : View (protocol R deg n) p) :
    ((verifier R deg n D ambient).decide stmt p v).run = simulateQ (decisionLift R deg n ambient p)
      (simulateQ (route R deg n p) (legacyProgram R deg n D ambient stmt (viewChallenges v))) :=
  rfl

/-- The legacy verdict on a full legacy transcript, answering message queries from its messages. -/
def legacyVerdict (stmt : Spec.StatementRound R n 0) (tr : FullTranscript (Spec.pSpec R deg n)) :
    Option (Spec.StatementRound R n (Fin.last n)) :=
  simulateQ (OracleInterface.simOracle0 (Spec.pSpec R deg n).Message tr.messages)
    (legacyProgram R deg n D ambient stmt tr.challenges)

end Verifier

section Run

variable {R : Type} [CommSemiring R] [DecidableEq R] [SampleableType R] {deg n : ℕ}
  {d : ℕ} (D : Fin d ↪ R) {ι : Type} {ambient : OracleSpec ι}

omit [DecidableEq R] [SampleableType R] in
/-- Lifted path-oracle queries are answered from the path payloads, without ambient effects. -/
theorem simulateQ_decisionLift {κ : Type} {spec' : OracleSpec κ}
    (amb : QueryImpl ambient (OracleComp spec')) (p : Path (protocol R deg n))
    (data : ∀ i, Spec.OracleStatement R n deg i)
    (pl : ∀ i, OracleData (protocol R deg n) p i) {α : Type}
    (oa : OracleComp (oracles (protocol R deg n) p) α) :
    simulateQ (QueryImpl.addLift amb ((sumFamily (polyFamily R deg n)
        (pathFamily (protocol R deg n) p)).behaviorOfRealizations (sumData data pl)))
      (simulateQ (decisionLift R deg n ambient p) oa) =
      (pure (simulateQ ((pathFamily (protocol R deg n) p).behaviorOfRealizations pl) oa) :
        OracleComp spec' α) := by
  refine (QueryImpl.simulateQ_simulateQ_eq_of_apply
    (impl := ((pathFamily (protocol R deg n) p).behaviorOfRealizations pl).liftTarget _)
    (fun t => ?_) oa).trans ?_
  · exact simulateQ_spec_query _ _
  · rw [simulateQ_liftTarget]
    rfl

/-- On any completed run, the decision returns the legacy verdict of the decoded transcript. -/
theorem simulateQ_decide {κ : Type} {spec' : OracleSpec κ}
    (amb : QueryImpl ambient (OracleComp spec')) (stmt : Spec.StatementRound R n 0)
    (data : ∀ i, Spec.OracleStatement R n deg i) (tr : PathAlong oracleSig (protocol R deg n)) :
    simulateQ (QueryImpl.addLift amb ((sumFamily (polyFamily R deg n)
        (pathFamily (protocol R deg n) (projectPathAlong oracleSig _ tr))).behaviorOfRealizations
          (sumData data (payloads _ tr))))
      ((verifier R deg n D ambient).decide stmt _ (toView _ tr)).run =
      (pure (legacyVerdict R deg n D ambient stmt (decodeTranscript n tr)) :
        OracleComp spec' _) := by
  rw [verifier_decide, simulateQ_decisionLift, viewChallenges_toView]
  congr 1
  exact QueryImpl.simulateQ_simulateQ_eq_of_apply (simulateQ_route n tr) _

/-- The legacy oracle verifier, answering its queries from the oracle statement and the messages
of a legacy transcript, returns `legacyVerdict` without ambient effects. -/
theorem simulateQ_legacy_verify (stmt : Spec.StatementRound R n 0)
    (oStmt : ∀ i, Spec.OracleStatement R n deg i) (tr : FullTranscript (Spec.pSpec R deg n)) :
    simulateQ (OracleInterface.simOracle2 ambient oStmt tr.messages)
        ((Spec.oracleVerifier R deg D n ambient).verify stmt tr.challenges).run =
      pure (legacyVerdict R deg n D ambient stmt tr) := by
  rw [legacy_verify_eq]
  change simulateQ _ (OracleComp.liftComp _ _) = _
  rw [OracleComp.liftComp_def, QueryImpl.simulateQ_simulateQ_eq_of_apply
    (impl := (OracleInterface.simOracle0 _ tr.messages).liftTarget _) (fun _ => rfl),
    simulateQ_liftTarget]
  rfl

/-- Closed form of the execution against a fold of pure rounds, whatever its messages: every
round runs and draws its challenge, and the verdict is the legacy verdict of the decoded
transcript, with the input polynomial as output oracle. -/
theorem run_verifier_foldRounds {State : ℕ → Type} {Out : Type}
    (msg : (k : ℕ) → State (k + 1) → R⦃≤ deg⦄[X])
    (next : (k : ℕ) → State (k + 1) → R → State k) (finish : State 0 → Out) (st : State n)
    (stmt : Spec.StatementRound R n 0) (oStmt : ∀ i, Spec.OracleStatement R n deg i) :
    (verifier R deg n D ambient).run stmt oStmt (foldRounds msg next finish n st) =
      (fun chals => (⟨foldTranscript msg next n st chals, finish (foldState next n st chals),
        (legacyVerdict R deg n D ambient stmt
          (decodeTranscript n (foldTranscript msg next n st chals))).map fun t => (t, oStmt)⟩ :
          Observation oracleSig (protocol R deg n) (fun _ => Out)
            (Spec.StatementRound R n (Fin.last n) × ∀ i, Spec.OracleStatement R n deg i))) <$>
        drawChallenges n (fun c =>
          liftM ((ambient + challengeSpec oracleSig (protocol R deg n)).query (.inr c))) := by
  unfold Interaction.Core.OracleVerifier.run
  rw [simulate_foldRounds, run_foldRounds, _root_.bind_map_left, map_eq_bind_pure_comp]
  refine bind_congr fun chals => ?_
  simp only [simulateQ_decide]
  rfl

/-- Closed form of the honest execution: draw every challenge, then return the honest transcript
and output, and the legacy verdict of the decoded honest transcript with the input polynomial as
output oracle. -/
theorem run_verifier_honestProver (stmt : Spec.StatementRound R n 0)
    (oStmt : ∀ i, Spec.OracleStatement R n deg i) :
    (verifier R deg n D ambient).run stmt oStmt (honestProver D stmt oStmt) =
      (fun chals => (⟨honestTranscript D stmt oStmt chals, honestOutput D stmt oStmt chals,
        (legacyVerdict R deg n D ambient stmt
          (decodeTranscript n (honestTranscript D stmt oStmt chals))).map fun t => (t, oStmt)⟩ :
          Observation oracleSig (protocol R deg n) (fun _ => HonestOutput R deg n)
            (Spec.StatementRound R n (Fin.last n) × ∀ i, Spec.OracleStatement R n deg i))) <$>
        drawChallenges n (fun c =>
          liftM ((ambient + challengeSpec oracleSig (protocol R deg n)).query (.inr c))) :=
  run_verifier_foldRounds D _ _ _ _ stmt oStmt

end Run

/-! ## The legacy fold, one round at a time -/

section Split

variable {R : Type} [CommSemiring R] {deg : ℕ}

/-- Answering the prefix-routed queries of an appended transcript answers from its first part. -/
theorem simulateQ_leftMessageQuery (k : ℕ) (A : FullTranscript (Spec.SingleRound.pSpec R deg))
    (B : FullTranscript (Spec.pSpec R deg k)) {α : Type}
    (oa : OracleComp [(Spec.SingleRound.pSpec R deg).Message]ₒ α) :
    simulateQ (OracleInterface.simOracle0
        (Spec.SingleRound.pSpec R deg ++ₚ Spec.pSpec R deg k).Message
        (A ++ₜ B).messages) (simulateQ (Spec.leftMessageQuery R deg k) oa) =
      simulateQ (OracleInterface.simOracle0 _ A.messages) oa :=
  QueryImpl.simulateQ_simulateQ_eq_of_apply (fun ⟨i, q⟩ => by
    dsimp only [Spec.leftMessageQuery]
    exact Legacy.simulateQ_queryAlongHEq _ _ _ _ (OracleInterface.simOracle0
      (Spec.SingleRound.pSpec R deg ++ₚ Spec.pSpec R deg k).Message (A ++ₜ B).messages) _
      (A i.1) _
      ((heq_of_eq (congrFun (FullTranscript.append_fst A B) i.1)).symm.trans
        (FullTranscript.fst_apply_heq _ _))
      (fun _ => simulateQ_spec_query _ _) q) oa

/-- Answering the suffix-routed queries of an appended transcript answers from its second part. -/
theorem simulateQ_rightMessageQuery (k : ℕ) (A : FullTranscript (Spec.SingleRound.pSpec R deg))
    (B : FullTranscript (Spec.pSpec R deg k)) {α : Type}
    (oa : OracleComp [(Spec.pSpec R deg k).Message]ₒ α) :
    simulateQ (OracleInterface.simOracle0
        (Spec.SingleRound.pSpec R deg ++ₚ Spec.pSpec R deg k).Message
        (A ++ₜ B).messages) (simulateQ (Spec.rightMessageQuery R deg k) oa) =
      simulateQ (OracleInterface.simOracle0 _ B.messages) oa :=
  QueryImpl.simulateQ_simulateQ_eq_of_apply (fun ⟨i, q⟩ => by
    dsimp only [Spec.rightMessageQuery]
    exact Legacy.simulateQ_queryAlongHEq _ _ _ _ (OracleInterface.simOracle0
      (Spec.SingleRound.pSpec R deg ++ₚ Spec.pSpec R deg k).Message (A ++ₜ B).messages) _
      (B i.1) _
      ((heq_of_eq (congrFun (FullTranscript.append_snd A B) i.1)).symm.trans
        (FullTranscript.snd_apply_heq _ _))
      (fun _ => simulateQ_spec_query _ _) q) oa

/-- The legacy decision fold on an appended transcript runs the first round's check on the first
part, and continues on the second part only if that check passes. -/
theorem simulateQ_oracleVerifierProgram_succ (k : ℕ) (S : Fin (k + 2) → Type)
    (V : (i : Fin (k + 1)) → S i.castSucc → (Spec.SingleRound.pSpec R deg).Challenges →
      OptionT (OracleComp [(Spec.SingleRound.pSpec R deg).Message]ₒ) (S i.succ))
    (stmt : S 0) (A : FullTranscript (Spec.SingleRound.pSpec R deg))
    (B : FullTranscript (Spec.pSpec R deg k)) :
    simulateQ (OracleInterface.simOracle0 (Spec.pSpec R deg (k + 1)).Message (A ++ₜ B).messages)
        (Spec.oracleVerifierProgram R deg S V stmt (A ++ₜ B).challenges) =
      (simulateQ (OracleInterface.simOracle0 _ A.messages) (V 0 stmt A.challenges).run).bind
        fun s => simulateQ (OracleInterface.simOracle0 _ B.messages)
          (Spec.oracleVerifierProgram R deg (S ∘ Fin.succ) (fun i => V i.succ) s
            B.challenges) := by
  change simulateQ (OracleInterface.simOracle0
      (Spec.SingleRound.pSpec R deg ++ₚ Spec.pSpec R deg k).Message (A ++ₜ B).messages)
    (simulateQ (Spec.leftMessageQuery R deg k)
        (V 0 stmt (Challenges.fst (A ++ₜ B).challenges)).run
      >>= fun next => match next with
        | some next => simulateQ (Spec.rightMessageQuery R deg k)
            (Spec.oracleVerifierProgram R deg (S ∘ Fin.succ) (fun i => V i.succ) next
              (Challenges.snd (A ++ₜ B).challenges))
        | none => pure none) = _
  rw [simulateQ_bind, simulateQ_leftMessageQuery, Legacy.challenges_append_fst]
  cases simulateQ (OracleInterface.simOracle0 _ A.messages) (V 0 stmt A.challenges).run with
  | none => rfl
  | some s =>
    change simulateQ _ (simulateQ (Spec.rightMessageQuery R deg k) _) = _
    rw [simulateQ_rightMessageQuery, Legacy.challenges_append_snd]
    rfl

end Split

/-! ## Rejection -/

section Reject

variable {R : Type} [CommSemiring R] [DecidableEq R] [SampleableType R] {deg n : ℕ}
  {d : ℕ} {D : Fin d ↪ R} {ι : Type} {ambient : OracleSpec ι}

omit [DecidableEq R] [SampleableType R] in
/-- A round program that queries only its message answers from the message without effects. -/
theorem simulateQ_simOracle2_messageOnly (oStmt : ∀ i, Spec.OracleStatement R n deg i)
    (T : FullTranscript (Spec.SingleRound.pSpec R deg)) {α : Type}
    (oa : OracleComp (ambient + ([Spec.OracleStatement R n deg]ₒ +
      [(Spec.SingleRound.pSpec R deg).Message]ₒ)) α)
    (h : AllQueriesSatisfy oa (fun q => ∃ j, q = Sum.inr (Sum.inr j))) :
    simulateQ (OracleInterface.simOracle2 ambient oStmt T.messages) oa =
      pure (simulateQ (OracleInterface.simOracle0 _ T.messages)
        (Spec.messageOnlyRoundProgram R deg n ambient oa h)) := by
  induction oa using OracleComp.inductionOn with
  | pure x => rfl
  | query_bind q next ih =>
    obtain ⟨⟨j, rfl⟩, hn⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).1 h
    change _ = (pure (simulateQ (OracleInterface.simOracle0 _ T.messages) (liftM (OracleSpec.query
      (spec := [(Spec.SingleRound.pSpec R deg).Message]ₒ) j) >>= fun answer =>
        Spec.messageOnlyRoundProgram R deg n ambient (next answer) (hn answer))) :
          OracleComp ambient _)
    rw [simulateQ_bind, simulateQ_bind, simulateQ_spec_query, simulateQ_spec_query]
    exact (pure_bind (m := OracleComp ambient) _ _).trans (ih _ (hn _))

/-- A round whose message does not sum to the target over `D` fails its check. -/
theorem roundCheck_eq_none (i : Fin n) (stmt : Spec.StatementRound R n i.castSucc)
    (T : FullTranscript (Spec.SingleRound.pSpec R deg))
    (h : ∑ x ∈ Finset.univ.map D, (T 0 : R⦃≤ deg⦄[X]).val.eval x ≠ stmt.target) :
    simulateQ (OracleInterface.simOracle0 _ T.messages)
      (roundCheck R deg n D ambient i stmt T.challenges).run = none := by
  have e := congrArg (fun V => (V.verify (stmt, fun _ => 0) T).run)
    (Spec.SingleRound.oracleVerifier_eq_verifier R n deg D ambient i)
  rw [Spec.SingleRound.verifier_eq_unfolded] at e
  change Option.map _ <$> simulateQ (OracleInterface.simOracle2 ambient _ T.messages)
    ((Spec.SingleRound.oracleVerifier R n deg D ambient i).verify stmt T.challenges).run = _ at e
  rw [simulateQ_simOracle2_messageOnly _ _ _
    (Spec.SingleRound.oracleVerifier_only_message_queries R n deg D ambient i stmt
      T.challenges)] at e
  rcases hT : T 0 with ⟨p, hp⟩
  rw [hT, Finset.sum_map] at h
  simp only [MessageIdx, Nat.reduceAdd, Nat.add_zero, Fin.vcons_fin_zero, Fin.vappend_zero,
    Message, LawfulApplicative.map_pure, Spec.SingleRound.Unfolded.verifier, Fin.isValue,
    Finset.sum_map, OracleComp.guard_eq, Fin.val_succ, LawfulMonad.bind_pure_comp, hT, h,
    ↓reduceIte, OptionT.map_failure, OptionT.run_failure, FreeM.pure_inj,
    Option.map_eq_none_iff] at e
  exact e

/-- A round whose message sums to the target over `D` passes its check, and the next statement
evaluates the message at the challenge. -/
theorem roundCheck_eq_some (i : Fin n) (stmt : Spec.StatementRound R n i.castSucc)
    (T : FullTranscript (Spec.SingleRound.pSpec R deg))
    (h : ∑ x ∈ Finset.univ.map D, (T 0 : R⦃≤ deg⦄[X]).val.eval x = stmt.target) :
    simulateQ (OracleInterface.simOracle0 _ T.messages)
      (roundCheck R deg n D ambient i stmt T.challenges).run =
      some ⟨(T 0 : R⦃≤ deg⦄[X]).val.eval (T 1), Fin.snoc stmt.challenges (T 1)⟩ := by
  have e := congrArg (fun V => (V.verify (stmt, fun _ => 0) T).run)
    (Spec.SingleRound.oracleVerifier_eq_verifier R n deg D ambient i)
  rw [Spec.SingleRound.verifier_eq_unfolded] at e
  change Option.map _ <$> simulateQ (OracleInterface.simOracle2 ambient _ T.messages)
    ((Spec.SingleRound.oracleVerifier R n deg D ambient i).verify stmt T.challenges).run = _ at e
  rw [simulateQ_simOracle2_messageOnly _ _ _
    (Spec.SingleRound.oracleVerifier_only_message_queries R n deg D ambient i stmt
      T.challenges)] at e
  rcases hT : T 0 with ⟨p, hp⟩
  rw [hT, Finset.sum_map] at h
  simp only [MessageIdx, Nat.reduceAdd, Nat.add_zero, Fin.vcons_fin_zero, Fin.vappend_zero,
    Message, LawfulApplicative.map_pure, Spec.SingleRound.Unfolded.verifier, Fin.isValue,
    Finset.sum_map, OracleComp.guard_eq, Fin.val_succ, LawfulMonad.bind_pure_comp, hT, h,
    ↓reduceIte, OptionT.run_pure, FreeM.pure_inj, Option.map_eq_some_iff, Prod.mk.injEq,
    ↓existsAndEq, true_and] at e
  exact e.1

/-- If the first round fails its check, the legacy verdict rejects, whatever the later rounds. -/
theorem legacyVerdict_eq_none {k : ℕ} (stmt : Spec.StatementRound R (k + 1) 0)
    (A : FullTranscript (Spec.SingleRound.pSpec R deg)) (B : FullTranscript (Spec.pSpec R deg k))
    (h : ∑ x ∈ Finset.univ.map D, (A 0 : R⦃≤ deg⦄[X]).val.eval x ≠ stmt.target) :
    legacyVerdict R deg (k + 1) D ambient stmt (A ++ₜ B) = none := by
  refine (simulateQ_oracleVerifierProgram_succ k _ _ stmt A B).trans ?_
  rw [roundCheck_eq_none 0 stmt A h]
  rfl

end Reject

end Sumcheck.Core
