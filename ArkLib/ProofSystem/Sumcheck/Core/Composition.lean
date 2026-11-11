/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Core.Execution
public import ArkLib.ProofSystem.Sumcheck.Core.LegacyProjection

/-!
# Sumcheck rounds as composable oracle verifiers

A single round can be verified on its own: `checkVerifier` runs a check program on the round
message and the round challenge, and returns an output oracle through an oracle map. With the
legacy round check `roundCheck` and the projection map `projectionMap` as output map, it is the
standalone round `projectedVerifier`: its output oracle is the univariate round polynomial, read
from the multivariate input through the projection.

`legacyFoldVerifier` is the passive verifier of any number of rounds for a family of statement types
and per-round checks. The Sumcheck verifier is its instance at the legacy round checks
(`verifier_eq_legacyFoldVerifier`). Its statement family need not start at round `0`. The remaining
rounds after the first are a `legacyFoldVerifier` from the round-`1` statement.

The main results are:

* `run_checkVerifier`: the run of a single round, the verdict of the check on the decoded round;
* `run_projectedVerifier_roundProver` and `projectedVerifier_relation`: the honest standalone
  round through the projection map, and its output relation;
* `run_append_checkVerifier`: the run of a single round appended to any verifier, which runs both
  interactions, then the round's check and, only after it accepts, the suffix decision on the
  round's output oracle and the suffix messages;
* `run_append_legacyFoldVerifier` and `run_append_verifier`: append one round to the remaining
  rounds
  runs as the verifier of all rounds, as programs, including against a prover composed by
  `Prover.append`.

The append results are stated for a single first round, whose decision makes no ambient query.
The projection map and `projectedVerifier` are noncomputable mathematical views because the legacy
multivariate evaluation and projected-polynomial construction are noncomputable. The executable
message representation and its runtime instance belong to `Computable`.
-/

@[expose] public section

universe uI uS

namespace Sumcheck.Core
open Polynomial PFunctor FreeM Interaction.Core Interaction.TwoParty.Lens Interaction.Oracle
  OracleComp OracleSpec ProtocolSpec

/-! ## The input slot -/

section InputSlot

variable {s : OracleProtocol} {I : Type uI} {A : I → Type} (inputs : OracleFamily I A)

/-- The input slot of a run's resources, as an oracle map. -/
abbrev inputSlot (p : Path s) : OracleMap (pathResources inputs s p) inputs :=
  OracleMap.fst (Resources.ofFamily inputs) (Resources.ofFamily (pathFamily s p))

end InputSlot

/-! ## One round -/

section Check

variable {R : Type} [CommSemiring R] {deg : ℕ} {ι : Type} (ambient : OracleSpec ι)
  {I : Type} {A : I → Type} (inputs : OracleFamily I A)


/-- Route the legacy round message's queries to the oracle node of a round. -/
def checkRoute : (p : Path (round R deg)) →
    QueryImpl [(Spec.SingleRound.pSpec R deg).Message]ₒ
      (OracleComp (ambient + (pathResources inputs (round R deg) p).spec))
  | ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩ => fun ⟨i, q⟩ => by
    obtain rfl := Unique.eq_default i
    exact liftM ((ambient + (pathResources inputs (round R deg)
      ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩).spec).query (.inr (.inr ⟨.inl ⟨⟩, q⟩)))

/-- The legacy challenges of a round view. -/
def roundChallenges {p : Path (round R deg)} (v : View (round R deg) p) :
    (Spec.SingleRound.pSpec R deg).Challenges :=
  fun j => roundChallengeFn (deg := deg) (viewChallenge v) j.1 j.2

variable {S T : Type} {J : Type} {B : J → Type} {outputs : OracleFamily J B}

/-- A single round verified by `check` on the round message and challenge. The output oracle is
`out` applied to the input data and the round's message payload. -/
def checkVerifier
    (check : S → (Spec.SingleRound.pSpec R deg).Challenges →
      OptionT (OracleComp [(Spec.SingleRound.pSpec R deg).Message]ₒ) T)
    (out : S → (p : Path (round R deg)) → View (round R deg) p →
      OracleMap (pathResources inputs (round R deg) p) (Resources.ofFamily outputs)) :
    OracleVerifier ambient (round R deg) S (fun _ => T) inputs (fun _ => outputs) where
  decide stmt p v := OptionT.mk
    (simulateQ (checkRoute ambient inputs p) (check stmt (roundChallenges v)).run)
  outputMap := out

/-- The round view's challenges are those of the legacy round transcript with its challenge. -/
theorem roundChallenges_eq {p : Path (round R deg)} (v : View (round R deg) p)
    (msg : R⦃≤ deg⦄[X]) :
    roundChallenges v = (roundFullTranscript msg (viewChallenge v)).challenges := by
  funext ⟨j, h⟩
  fin_cases j
  · exact nomatch h
  · rfl

/-- The decision of a single round on a completed round, answered from the input data and the
round's payloads, runs the check on the round's message and challenge. It makes no ambient
query. -/
theorem decideWith_checkVerifier
    (check : S → (Spec.SingleRound.pSpec R deg).Challenges →
      OptionT (OracleComp [(Spec.SingleRound.pSpec R deg).Message]ₒ) T)
    (out : S → (p : Path (round R deg)) → View (round R deg) p →
      OracleMap (pathResources inputs (round R deg) p) (Resources.ofFamily outputs))
    (stmt : S) (x : ∀ i, A i) (tr : PathAlong oracleSig (round R deg)) :
    (checkVerifier ambient inputs check out).decideWith stmt _ (toView _ tr)
        ((x, payloads _ tr)) =
      pure (simulateQ (OracleInterface.simOracle0 _
          (roundFullTranscript (roundMessage tr) (roundChallenge tr)).messages)
        (check stmt
          (roundFullTranscript (roundMessage tr) (roundChallenge tr)).challenges).run) := by
  rcases tr with ⟨msg, ⟨chal, ⟨⟩⟩⟩
  change simulateQ _ (simulateQ (checkRoute ambient inputs _)
    (check stmt (roundChallenges (toView (round R deg) ⟨msg, ⟨chal, ⟨⟩⟩⟩))).run) = _
  rw [roundChallenges_eq _ msg]
  refine (QueryImpl.simulateQ_simulateQ_eq_of_apply
    (impl := (OracleInterface.simOracle0 _ (roundFullTranscript msg chal).messages).liftTarget _)
    (fun t => ?_) _).trans ?_
  · rcases t with ⟨i, q⟩
    obtain rfl := Unique.eq_default i
    exact simulateQ_spec_query _ _
  · rw [simulateQ_liftTarget]
    rfl

/-- The verdict of a round check on a completed round. -/
def checkVerdict
    (check : S → (Spec.SingleRound.pSpec R deg).Challenges →
      OptionT (OracleComp [(Spec.SingleRound.pSpec R deg).Message]ₒ) T)
    (stmt : S) (tr : PathAlong oracleSig (round R deg)) : Option T :=
  simulateQ (OracleInterface.simOracle0 _
      (roundFullTranscript (roundMessage tr) (roundChallenge tr)).messages)
    (check stmt (roundFullTranscript (roundMessage tr) (roundChallenge tr)).challenges).run

/-- The run of a single round: the interaction, then the verdict of the check on the completed
round, with the output oracle mapped from the input data and the round's payloads. -/
theorem run_checkVerifier {Out : PathAlong oracleSig (round R deg) → Type}
    (check : S → (Spec.SingleRound.pSpec R deg).Challenges →
      OptionT (OracleComp [(Spec.SingleRound.pSpec R deg).Message]ₒ) T)
    (out : S → (p : Path (round R deg)) → View (round R deg) p →
      OracleMap (pathResources inputs (round R deg) p) (Resources.ofFamily outputs))
    (stmt : S) (x : ∀ i, A i) (prover : Prover oracleSig ambient (round R deg) Out) :
    (checkVerifier ambient inputs check out).run stmt x prover =
      (fun y => (⟨y.1, y.2.1, (checkVerdict check stmt y.1).map fun t =>
          (t, (out stmt _ (toView _ y.1)).f ((x, payloads _ y.1)))⟩ :
          Observation oracleSig (round R deg) Out (fun _ => T × ∀ j, B j))) <$>
        Interaction.TwoParty.Lens.run (round R deg)
          (prover.simulate fun q =>
            liftM ((ambient + challengeSpec oracleSig (round R deg)).query (.inl q)))
          (sampler oracleSig (round R deg) fun c =>
            liftM ((ambient + challengeSpec oracleSig (round R deg)).query (.inr c))) := by
  rw [OracleVerifier.run_eq_decideWith, map_eq_bind_pure_comp]
  refine bind_congr fun y => ?_
  obtain ⟨tr, o, ⟨⟩⟩ := y
  dsimp only
  rw [decideWith_checkVerifier]
  simp only [simulateQ_pure]
  rfl

end Check

/-! ## A round appended to any verifier -/

section SplitView


variable {R : Type} [CommSemiring R] {deg : ℕ} {s : OracleProtocol}


end SplitView

section Append

variable {R : Type} [CommSemiring R] {deg : ℕ} {ι : Type} (ambient : OracleSpec ι)
  {I : Type} {A : I → Type} (inputs : OracleFamily I A)
  {J : Type} {B : J → Type} {middle : OracleFamily J B}
  {K : Type} {C : K → Type} {outputs : OracleFamily K C}
  {s : OracleProtocol} {S T U : Type}



variable (check : S → (Spec.SingleRound.pSpec R deg).Challenges →
      OptionT (OracleComp [(Spec.SingleRound.pSpec R deg).Message]ₒ) T)
    (out : S → (p : Path (round R deg)) → View (round R deg) p →
      OracleMap (pathResources inputs (round R deg) p) middle)
    (V₂ : OracleVerifier ambient s T (fun _ => U) middle (fun _ => outputs))
    (compatible : OracleVerifier.OutputCompatibility (checkVerifier ambient inputs check out)
      fun _ => V₂)

/-- The verifier after a round sees the round's output oracle and its own messages. -/
theorem suffixRoute_round (stmt : S) (x : ∀ i, A i) (msg : R⦃≤ deg⦄[X]) (chal : R)
    (tail : PathAlong oracleSig s) :
    (OracleVerifier.suffixRoute (s₂ := fun _ => s) (checkVerifier ambient inputs check out) stmt
        _ (toView ((round R deg).append fun _ => s) ⟨msg, ⟨chal, tail⟩⟩)).f
        ((x, payloads ((round R deg).append fun _ => s) ⟨msg, ⟨chal, tail⟩⟩)) =
      (((out stmt _ (toView (round R deg) ⟨msg, ⟨chal, ⟨⟩⟩⟩)).f
        ((x, payloads (round R deg) ⟨msg, ⟨chal, ⟨⟩⟩⟩))), (payloads s tail)) := by
  unfold OracleVerifier.suffixRoute
  rw [split_toView_round]
  apply Prod.ext
  · exact congrArg (out stmt _ (toView (round R deg) ⟨msg, ⟨chal, ⟨⟩⟩⟩)).f
      (prefixRoute_round inputs x msg chal tail)
  · rfl

/-- The decision of a round appended to `V₂`, on a completed run: the round's check on its
message and challenge, and, only if it accepts, the decision of `V₂` on the round's output oracle
and the messages of `s`. -/
theorem decideWith_append_checkVerifier (stmt : S) (x : ∀ i, A i)
    (tr : PathAlong oracleSig ((round R deg).append fun _ => s)) :
    ((checkVerifier ambient inputs check out).append (fun _ => V₂) compatible).decideWith stmt _
        (toView _ tr) ((x, payloads _ tr)) =
      match checkVerdict check stmt (appendHead tr) with
      | none => pure none
      | some mid => V₂.decideWith mid _ (toView s (appendTail tr))
          ((((out stmt _ (toView _ (appendHead tr))).f
            ((x, payloads _ (appendHead tr)))), (payloads s (appendTail tr)))) := by
  rcases tr with ⟨msg, ⟨chal, tail⟩⟩
  rw [OracleVerifier.append_decideWith, split_toView_round, prefixRoute_round]
  refine (congrArg (fun z => z >>= _)
    (decideWith_checkVerifier ambient inputs check out stmt x ⟨msg, ⟨chal, ⟨⟩⟩⟩)).trans ?_
  refine (pure_bind _ _).trans ?_
  rw [suffixRoute_round]
  unfold appendHead appendTail checkVerdict roundMessage roundChallenge
  simp only [split_round_suffix]
  split <;> rename_i h <;> simp only [h]

/-- The run of a round appended to `V₂`. Both interactions run first. The decision is the
round's check and, only after it accepts, the decision of `V₂` on the round's output oracle and
the messages of `s`. -/
theorem run_append_checkVerifier
    {Out : PathAlong oracleSig ((round R deg).append fun _ => s) → Type}
    (stmt : S) (x : ∀ i, A i)
    (prover : Prover oracleSig ambient ((round R deg).append fun _ => s) Out) :
    ((checkVerifier ambient inputs check out).append (fun _ => V₂) compatible).run stmt x
        prover = (do
      let ⟨tr, o, _⟩ ← Interaction.TwoParty.Lens.run ((round R deg).append fun _ => s)
        (prover.simulate fun q => liftM ((ambient + challengeSpec oracleSig
          ((round R deg).append fun _ => s)).query (.inl q)))
        (sampler oracleSig _ fun c => liftM ((ambient + challengeSpec oracleSig
          ((round R deg).append fun _ => s)).query (.inr c)))
      let verdict ← simulateQ
        (fun q => liftM ((ambient + challengeSpec oracleSig
            ((round R deg).append fun _ => s)).query (.inl q)) :
          QueryImpl ambient (OracleComp (ambient + challengeSpec oracleSig
            ((round R deg).append fun _ => s))))
        (match checkVerdict check stmt (appendHead tr) with
          | none => pure none
          | some mid => V₂.decideWith mid _ (toView s (appendTail tr))
              ((((out stmt _ (toView _ (appendHead tr))).f
                ((x, payloads _ (appendHead tr)))), (payloads s (appendTail tr)))))
      pure ⟨tr, o, verdict.map fun t =>
        (t, (compatible.outputMap stmt _ (toView _ tr)).f ((x, payloads _ tr)))⟩) := by
  rw [OracleVerifier.run_eq_decideWith]
  refine bind_congr fun y => ?_
  obtain ⟨tr, o, ⟨⟩⟩ := y
  dsimp only
  rw [decideWith_append_checkVerifier]
  rfl

end Append

/-! ## The passive verifier of any number of rounds -/

section Fold

variable (R : Type) [CommSemiring R] (deg : ℕ) {ι : Type} (ambient : OracleSpec ι)
  {I : Type} {A : I → Type} (inputs : OracleFamily I A)


/-- Lift path-oracle queries into a decision's query interface: the path lift `pathLift`. -/
def foldLift {s : OracleProtocol} (p : Path s) :
    QueryImpl (oracles s p) (OracleComp (ambient + (pathResources inputs s p).spec)) :=
  pathLift ambient inputs p

/-- The passive verifier of `k` rounds with statement family `S` and round checks `V`: the legacy
decision fold on the view's challenges, with every message query routed to its oracle node. The
output oracle is the input. -/
def legacyFoldVerifier (k : ℕ) (S : Fin (k + 1) → Type)
    (V : (i : Fin k) → S i.castSucc → (Spec.SingleRound.pSpec R deg).Challenges →
      OptionT (OracleComp [(Spec.SingleRound.pSpec R deg).Message]ₒ) (S i.succ)) :
    OracleVerifier ambient (protocol R deg k) (S 0) (fun _ => S (Fin.last k)) inputs
      (fun _ => inputs) where
  decide stmt p v := OptionT.mk (simulateQ (foldLift ambient inputs p)
    (simulateQ (route R deg k p) (Spec.oracleVerifierProgram R deg S V stmt (viewChallenges v))))
  outputMap _ p _ := inputSlot inputs p

/-- The Sumcheck verifier is the fold verifier of the legacy round checks. -/
theorem verifier_eq_legacyFoldVerifier [DecidableEq R] [SampleableType R] (n : ℕ) {d : ℕ}
    (D : Fin d ↪ R) :
    verifier R deg n D ambient = legacyFoldVerifier R deg ambient (Spec.polynomialFamily R n deg) n
      (Spec.StatementRound R n) (roundCheck R deg n D ambient) :=
  rfl

variable {R deg ambient inputs}

/-- Lifted path-oracle queries are answered from the path payloads, without ambient effects. -/
theorem simulateQ_foldLift {κ : Type} {spec' : OracleSpec κ}
    (amb : QueryImpl ambient (OracleComp spec')) {s : OracleProtocol} (p : Path s)
    (x : ∀ i, A i) (pl : ∀ i, OracleData s p i) {α : Type} (oa : OracleComp (oracles s p) α) :
    simulateQ (QueryImpl.addLift amb ((pathResources inputs s p).answer
        ((x, pl)))) (simulateQ (foldLift ambient inputs p) oa) =
      (pure (simulateQ ((pathFamily s p).behaviorOfRealizations pl) oa) :
        OracleComp spec' α) :=
  simulateQ_pathLift amb p x pl oa

/-- On any completed run, the fold verifier returns the legacy fold's verdict on the decoded
transcript, without ambient effects. -/
theorem decideWith_legacyFoldVerifier (k : ℕ) (S : Fin (k + 1) → Type)
    (V : (i : Fin k) → S i.castSucc → (Spec.SingleRound.pSpec R deg).Challenges →
      OptionT (OracleComp [(Spec.SingleRound.pSpec R deg).Message]ₒ) (S i.succ))
    (stmt : S 0) (x : ∀ i, A i) (tr : PathAlong oracleSig (protocol R deg k)) :
    (legacyFoldVerifier R deg ambient inputs k S V).decideWith stmt _ (toView _ tr)
        ((x, payloads _ tr)) =
      pure (simulateQ (OracleInterface.simOracle0 _ (decodeTranscript k tr).messages)
        (Spec.oracleVerifierProgram R deg S V stmt (decodeTranscript k tr).challenges)) := by
  change simulateQ _ (simulateQ (foldLift ambient inputs _) _) = _
  rw [simulateQ_foldLift, viewChallenges_toView]
  congr 1
  exact QueryImpl.simulateQ_simulateQ_eq_of_apply (simulateQ_route k tr) _

/-- The first of `k + 1` round checks, with the statement types of the fold's first round. -/
def foldHead {k : ℕ} {S : Fin (k + 2) → Type}
    (V : (i : Fin (k + 1)) → S i.castSucc → (Spec.SingleRound.pSpec R deg).Challenges →
      OptionT (OracleComp [(Spec.SingleRound.pSpec R deg).Message]ₒ) (S i.succ)) :
    S 0 → (Spec.SingleRound.pSpec R deg).Challenges →
      OptionT (OracleComp [(Spec.SingleRound.pSpec R deg).Message]ₒ) ((S ∘ Fin.succ) 0) :=
  V 0

variable (R deg ambient inputs)

/-- A round keeping the input, followed by the remaining rounds keeping it, keeps the input. -/
def foldCompatibility (k : ℕ) (S : Fin (k + 2) → Type)
    (V : (i : Fin (k + 1)) → S i.castSucc → (Spec.SingleRound.pSpec R deg).Challenges →
      OptionT (OracleComp [(Spec.SingleRound.pSpec R deg).Message]ₒ) (S i.succ)) :
    OracleVerifier.OutputCompatibility
      (checkVerifier ambient inputs (foldHead V) fun _ p _ => inputSlot inputs p)
      fun _ => legacyFoldVerifier R deg ambient inputs k (S ∘ Fin.succ) fun i => V i.succ where
  outputMap _ p _ := inputSlot inputs p
  agrees _ _ _ _ _ _ := rfl

variable {R deg ambient inputs}

/-- On any completed run, the first round appended to the remaining rounds decides as the fold
verifier of all rounds. -/
theorem decideWith_append_legacyFoldVerifier (k : ℕ) (S : Fin (k + 2) → Type)
    (V : (i : Fin (k + 1)) → S i.castSucc → (Spec.SingleRound.pSpec R deg).Challenges →
      OptionT (OracleComp [(Spec.SingleRound.pSpec R deg).Message]ₒ) (S i.succ))
    (stmt : S 0) (x : ∀ i, A i) (tr : PathAlong oracleSig (protocol R deg (k + 1))) :
    ((checkVerifier ambient inputs (foldHead V) fun _ p _ => inputSlot inputs p).append
        (fun _ => legacyFoldVerifier R deg ambient inputs k (S ∘ Fin.succ) fun i => V i.succ)
        (foldCompatibility R deg ambient inputs k S V)).decideWith stmt _ (toView _ tr)
        ((x, payloads _ tr)) =
      (legacyFoldVerifier R deg ambient inputs (k + 1) S V).decideWith stmt _ (toView _ tr)
        ((x, payloads _ tr)) := by
  refine (decideWith_append_checkVerifier (s := protocol R deg k) ambient inputs (foldHead V)
    (fun _ p _ => inputSlot inputs p) _ (foldCompatibility R deg ambient inputs k S V) stmt x
    tr).trans ((?_ : _ = _).trans (decideWith_legacyFoldVerifier (k + 1) S V stmt x tr).symm)
  refine Eq.trans ?_ (congrArg pure (simulateQ_oracleVerifierProgram_succ k S V stmt
    (roundFullTranscript (roundMessage (appendHead tr)) (roundChallenge (appendHead tr)))
    (decodeTranscript k (appendTail tr)))).symm
  change _ = pure ((checkVerdict (foldHead V) stmt (appendHead tr)).bind _)
  cases checkVerdict (foldHead V) stmt (appendHead tr) with
  | none => rfl
  | some mid =>
    exact decideWith_legacyFoldVerifier k (S ∘ Fin.succ) (fun i => V i.succ) mid x (appendTail tr)

/-- **Append equivalence.** One round appended to the remaining rounds runs as the fold verifier
of all rounds, as programs, against every prover. -/
theorem run_append_legacyFoldVerifier (k : ℕ) (S : Fin (k + 2) → Type)
    (V : (i : Fin (k + 1)) → S i.castSucc → (Spec.SingleRound.pSpec R deg).Challenges →
      OptionT (OracleComp [(Spec.SingleRound.pSpec R deg).Message]ₒ) (S i.succ))
    (stmt : S 0) (x : ∀ i, A i) {Out : PathAlong oracleSig (protocol R deg (k + 1)) → Type}
    (prover : Prover oracleSig ambient (protocol R deg (k + 1)) Out) :
    ((checkVerifier ambient inputs (foldHead V) fun _ p _ => inputSlot inputs p).append
        (fun _ => legacyFoldVerifier R deg ambient inputs k (S ∘ Fin.succ) fun i => V i.succ)
        (foldCompatibility R deg ambient inputs k S V)).run stmt x prover =
      (legacyFoldVerifier R deg ambient inputs (k + 1) S V).run stmt x prover := by
  rw [OracleVerifier.run_eq_decideWith (legacyFoldVerifier R deg ambient inputs (k + 1) S V),
    OracleVerifier.run_eq_decideWith]
  refine bind_congr fun y => ?_
  obtain ⟨tr, o, ⟨⟩⟩ := y
  dsimp only
  exact congrArg (fun d => simulateQ _ d >>= _)
    (decideWith_append_legacyFoldVerifier k S V stmt x tr)

/-- **Append equivalence for Sumcheck.** The round-`0` check appended to the remaining `k` rounds,
run against a prover composed by `Prover.append` from a first-round strategy `p` and a suffix
constructor `f`, runs as the Sumcheck verifier of `k + 1` rounds, as programs. -/
theorem run_append_verifier [DecidableEq R] [SampleableType R] {d : ℕ} (D : Fin d ↪ R) (k : ℕ)
    (stmt : Spec.StatementRound R (k + 1) 0) (x : ∀ i, Spec.OracleStatement R (k + 1) deg i)
    {Mid : PathAlong oracleSig (round R deg) → Type}
    {Out : PathAlong oracleSig (protocol R deg (k + 1)) → Type}
    (p : Prover oracleSig ambient (round R deg) Mid)
    (f : (tr : PathAlong oracleSig (round R deg)) → Mid tr →
      OracleComp ambient (Prover oracleSig ambient (protocol R deg k)
        fun tail => Out (PathAlong.append oracleSig (round R deg) (fun _ => protocol R deg k) tr
          tail))) :
    ((checkVerifier ambient (Spec.polynomialFamily R (k + 1) deg)
        (foldHead (roundCheck R deg (k + 1) D ambient)) fun _ p _ => inputSlot _ p).append
        (fun _ => legacyFoldVerifier R deg ambient (Spec.polynomialFamily R (k + 1) deg) k
          (Spec.StatementRound R (k + 1) ∘ Fin.succ)
          fun i => roundCheck R deg (k + 1) D ambient i.succ)
        (foldCompatibility R deg ambient _ k _ _)).run stmt x
        (Interaction.Core.Prover.append (s₂ := fun _ => protocol R deg k) (Out := Out) p f) =
      (verifier R deg (k + 1) D ambient).run stmt x
        (Interaction.Core.Prover.append (s₂ := fun _ => protocol R deg k) (Out := Out) p f) :=
  run_append_legacyFoldVerifier k (Spec.StatementRound R (k + 1))
    (roundCheck R deg (k + 1) D ambient)
    stmt x _

end Fold

/-! ## A standalone round through the projection map -/

section Projected

variable {R : Type} [CommSemiring R] {deg : ℕ} {ι : Type} {amb : OracleSpec ι}

/-- Simulating the honest round strategy keeps it: all its slots are `pure`. -/
theorem simulate_roundProver {m : Type → Type} [Monad m] [LawfulMonad m] (impl : QueryImpl amb m)
    {Out : PathAlong oracleSig (round R deg) → Type}
    (msg : R⦃≤ deg⦄[X]) (next : (chal : R) → Out (roundTranscript msg chal)) :
    Prover.simulate impl (roundProver (m := OracleComp amb) msg next) = roundProver msg next := by
  refine (Prover.simulate_node impl _ _ _).trans ?_
  change _ <$> simulateQ impl (pure _) = pure _
  erw [simulateQ_pure, LawfulApplicative.map_pure]
  refine congrArg pure (Sigma.ext rfl (heq_of_eq ?_))
  change Prover.simulate impl _ = _
  refine (Prover.simulate_node impl _ _ _).trans ?_
  erw [simulateQ_pure, LawfulApplicative.map_pure]
  refine congrArg pure (funext fun chal => ?_)
  change simulateQ impl (pure (next chal) : OracleComp amb _) = pure (next chal)
  exact simulateQ_pure impl _

variable [DecidableEq R] [SampleableType R] (n : ℕ) {d : ℕ} (D : Fin d ↪ R) (ambient : OracleSpec ι)

/-- Round `i` of an `n`-round statement on its own: the legacy round check, with the projection of
the multivariate input to the univariate round polynomial as output oracle. -/
noncomputable def projectedVerifier (i : Fin n) :
    OracleVerifier ambient (round R deg) (Spec.StatementRound R n i.castSucc)
      (fun _ => Spec.StatementRound R n i.succ) (Spec.polynomialFamily R n deg)
      (fun _ => messageFamily R deg) :=
  checkVerifier ambient _ (roundCheck R deg n D ambient i)
    fun stmt p _ => (projectionMap R deg n D i stmt).comp (inputSlot _ p)

variable {n D ambient}

/-- The run of the standalone round against the honest round strategy with message `msg`: one
challenge query, then the check's verdict on the message, with the projected round polynomial of
the input as output oracle. -/
theorem run_projectedVerifier_roundProver (i : Fin n)
    (stmt : Spec.StatementRound R n i.castSucc) (x : ∀ j, Spec.OracleStatement R n deg j)
    {Out : PathAlong oracleSig (round R deg) → Type}
    (msg : R⦃≤ deg⦄[X]) (next : (chal : R) → Out (roundTranscript msg chal)) :
    (projectedVerifier n D ambient i).run stmt x (roundProver msg next) =
      (fun chal => (⟨roundTranscript msg chal, next chal,
          (checkVerdict (roundCheck R deg n D ambient i) stmt (roundTranscript msg chal)).map
            fun t => (t, fun _ =>
              Spec.SingleRound.projectedRoundPolynomial R n deg D i stmt.challenges (x ()))⟩ :
          Observation oracleSig (round R deg) Out
            (fun _ => Spec.StatementRound R n i.succ ×
              ∀ j, Spec.SingleRound.Simple.OStmtIn R deg j))) <$>
        (liftM ((ambient + challengeSpec oracleSig (round R deg)).query
          (.inr roundChallengeNode)) : OracleComp _ R) := by
  rw [projectedVerifier, run_checkVerifier, simulate_roundProver, run_roundProver,
    Functor.map_map]
  rfl

/-- The honest standalone round accepts every challenge `chal` on a claim in the round-`i`
relation. The accepted statement has target `q.eval chal` for the projected round polynomial `q`,
which is the output oracle, and is in the round-`(i + 1)` relation with the original input. -/
theorem projectedVerifier_relation (i : Fin n)
    (stmt : Spec.StatementRound R n i.castSucc) (x : ∀ j, Spec.OracleStatement R n deg j)
    (h : ((stmt, x), ()) ∈ Spec.relationRound R n deg D i.castSucc) (chal : R) :
    let q := Spec.SingleRound.projectedRoundPolynomial R n deg D i stmt.challenges (x ())
    checkVerdict (roundCheck R deg n D ambient i) stmt (roundTranscript q chal) =
        some ⟨q.val.eval chal, Fin.snoc stmt.challenges chal⟩ ∧
      (((q.val.eval chal, chal), fun _ => q), ()) ∈
        Spec.SingleRound.Simple.outputRelation R deg ∧
      ((⟨q.val.eval chal, Fin.snoc stmt.challenges chal⟩, x), ()) ∈
        Spec.relationRound R n deg D i.succ := by
  intro q
  have hx : x = fun _ => x () := funext fun _ => rfl
  have hsum : ∑ y ∈ Finset.univ.map D, q.val.eval y = stmt.target := by
    rw [← Finset.sum_map_toList]
    rw [hx] at h
    exact Spec.SingleRound.projected_sum_of_relationRound R n deg D i stmt (x ()) h
  refine ⟨roundCheck_eq_some i stmt (roundFullTranscript q chal) hsum, rfl, ?_⟩
  rw [hx]
  exact Spec.SingleRound.relationRound_projected_output R n deg D i stmt (x ()) chal

end Projected

end Sumcheck.Core
