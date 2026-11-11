/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLibTest.ProofSystem.Sumcheck.Core.RoundByRound

/-!
# Prover effects in the Sumcheck execution

A two-round prover over `ZMod 17` performs an ambient effect before each message and one after
the last challenge, and keeps the first effect's answer in private memory for its second message.
The execution runs the prover's effects and the challenge draws in protocol order: event `0`,
the first challenge, event `2`, the second challenge, event `3`. On a claim whose round checks
pass the verdict is the last message at the last challenge; on a claim whose first check fails
every round still runs, the verdict rejects, and the decision logs only the first check's
queries. A recording handler observes the order `[0, 1, 2, 1, 3]`, with `1` standing for a
challenge. A prover that samples its private memory instead is bounded by the transferred
soundness error `2 / 17`.
-/

namespace Sumcheck.Core.EffectsTest

open Polynomial PFunctor Interaction.Core Interaction.TwoParty.Lens Interaction.Oracle
  OracleComp OracleSpec ProtocolSpec MeasureTheory Sumcheck.Core.SoundnessTest
open scoped ENNReal NNReal

/-! ## Support -/

section Support

variable {R : Type} [CommSemiring R] {deg : ℕ} {ι : Type} {amb : OracleSpec ι}

/-- Simulating a pure round simulates its continuations. -/
theorem simulate_consProver {m : Type → Type} [Monad m] [LawfulMonad m]
    (impl : QueryImpl amb m) {k : ℕ}
    {Out : FreeM.PathAlong oracleSig (protocol R deg (k + 1)) → Type} (msg : R⦃≤ deg⦄[X])
    (next : (chal : R) → Prover oracleSig amb (protocol R deg k)
      (fun tail => Out (consTranscript msg chal tail))) :
    Prover.simulate impl (consProver msg next) =
      consProver msg fun chal => Prover.simulate impl (next chal) := by
  refine (Prover.simulate_node impl _ _ _).trans ?_
  change _ <$> simulateQ impl (pure _) = pure _
  erw [simulateQ_pure, LawfulApplicative.map_pure]
  refine congrArg pure (Sigma.ext rfl (heq_of_eq ?_))
  change Prover.simulate impl _ = _
  refine (Prover.simulate_node impl _ _ _).trans ?_
  erw [simulateQ_pure, LawfulApplicative.map_pure]
  rfl

variable [DecidableEq R] [SampleableType R] {n d : ℕ} (D : Fin d ↪ R)

/-- The execution of any prover is its run against the challenge sampler, followed by the legacy
verdict of the decoded transcript, with the input oracle as output oracle. -/
theorem run_verifier_eq {Out : FreeM.PathAlong oracleSig (protocol R deg n) → Type}
    (stmt : Spec.StatementRound R n 0) (oStmt : ∀ i, Spec.OracleStatement R n deg i)
    (P : Prover oracleSig amb (protocol R deg n) Out) :
    (verifier R deg n D amb).run stmt oStmt P =
      (fun x => (⟨x.1, x.2.1, (legacyVerdict R deg n D amb stmt
          (decodeTranscript n x.1)).map fun t => (t, oStmt)⟩ :
          Observation oracleSig (protocol R deg n) Out
            (fun _ => Spec.StatementRound R n (Fin.last n) × ∀ i, Spec.OracleStatement R n deg i)))
              <$>
        Interaction.TwoParty.Lens.run (protocol R deg n)
          (P.simulate fun q => liftM ((amb + challengeSpec oracleSig (protocol R deg n)).query
            (.inl q)))
          (sampler oracleSig (protocol R deg n) fun c =>
            liftM ((amb + challengeSpec oracleSig (protocol R deg n)).query (.inr c))) := by
  unfold Interaction.Core.OracleVerifier.run
  rw [map_eq_bind_pure_comp]
  refine bind_congr fun x => ?_
  simp only [simulateQ_decide]
  rfl

end Support

/-! ## An adaptive prover with ambient effects -/

noncomputable section

/-- Seventeen is prime. -/
instance : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- The field with seventeen elements. -/
abbrev K := ZMod 17

/-- Four ambient events answered in `K`. -/
abbrev events : OracleSpec (Fin 4) := Fin 4 →ₒ K

/-- The ambient event `i`. -/
def event (i : Fin 4) : OracleComp events K := liftM (events.query i)

/-- The affine round polynomial `a * X + b`. -/
def affine {R : Type} [CommSemiring R] (a b : R) : R⦃≤ 1⦄[X] :=
  ⟨C a * X + C b, Polynomial.mem_degreeLE.mpr
    (degree_add_le_of_degree_le (degree_C_mul_X_le a) (degree_C_le.trans zero_le_one))⟩

-- Migration rows: Sumcheck Interaction/SourceRouting #1, #2.

/-- Evaluating an affine polynomial gives its affine expression. -/
theorem eval_affine {R : Type} [CommSemiring R] (a b x : R) :
    (affine a b).val.eval x = a * x + b := by
  simp only [affine, eval_add, eval_mul, eval_C, eval_X]

/-- The oracle interface of a round message answers a query by evaluation. -/
theorem answer_affine {R : Type} [CommSemiring R] (a b x : R) :
    @OracleInterface.answer _ (OracleInterface.instPolynomialDegreeLE R 1) (affine a b) x =
      a * x + b := by
  change (affine a b).val.eval x = _
  exact eval_affine a b x

/-- Routing a one-round affine message answers by evaluating that sent message. -/
theorem route_affine {R : Type} [CommSemiring R] (a b x r : R) :
    simulateQ (payloadImpl (protocol R 1 1) (SingleRoundTest.tr1 (affine a b) r))
        (route R 1 1
          (FreeM.projectPathAlong oracleSig _ (SingleRoundTest.tr1 (affine a b) r))
          ⟨⟨⟨0, by decide⟩, rfl⟩, x⟩) = pure (a * x + b) := by
  rw [simulateQ_route]
  change (pure ((affine a b).val.eval x) : Id R) = pure (a * x + b)
  rw [eval_affine]

/-- The affine evaluation law holds on natural numbers for the routing fixture's first message. -/
example (x : ℕ) : (affine 2 1).val.eval x = 2 * x + 1 := eval_affine 2 1 x

/-- The polynomial oracle answers over natural numbers for the routing fixture's first message. -/
example (x : ℕ) :
    @OracleInterface.answer _ (OracleInterface.instPolynomialDegreeLE ℕ 1) (affine 2 1) x =
      2 * x + 1 := answer_affine 2 1 x

/-- Routing the first message at challenge two returns five over natural numbers. -/
example : simulateQ (payloadImpl (protocol ℕ 1 1) (SingleRoundTest.tr1 (affine 2 1) 2))
    (route ℕ 1 1
      (FreeM.projectPathAlong oracleSig _ (SingleRoundTest.tr1 (affine 2 1) 2))
      ⟨⟨⟨0, by decide⟩, rfl⟩, (2 : ℕ)⟩) = pure (5 : ℕ) := by
  exact route_affine (2 : ℕ) 1 2 2

/-- The prover's terminal action: event `3`. -/
def finalEvent : Prover oracleSig events (protocol K 1 0) (fun _ => Unit) :=
  (do let _ ← event 3; pure () : OracleComp events Unit)

/-- The last round: the message `(b + a) * X + (a * r + 1)`, then event `3`. -/
def lastProver (a b r : K) : Prover oracleSig events (protocol K 1 1) (fun _ => Unit) :=
  consProver (affine (b + a) (a * r + 1)) fun _ => finalEvent

/-- Event `0` gives `a` and the message `a * X + 1`; after the challenge `r`, event `2` gives `b`
and the last round follows. The value `a` is private memory carried across the challenge. -/
def adaptive : Prover oracleSig events (protocol K 1 2) (fun _ => Unit) :=
  Strategy.joinSlot ((fun a => consProver (affine a 1) fun r =>
    Strategy.joinSlot ((fun b => lastProver a b r) <$> event 2)) <$> event 0)

/-- The domain `{0}`. -/
def D₀ : Fin 1 ↪ K := ⟨fun _ => 0, fun _ _ _ => Subsingleton.elim _ _⟩

@[simp] theorem D₀_apply (i : Fin 1) : D₀ i = 0 := rfl

/-- The initial claim with target `1`; the first message `a * X + 1` sums to `1` over `{0}`. -/
def initial : Spec.StatementRound K 2 0 := ⟨1, Fin.elim0⟩

/-- A claim with target `2`, which the first message misses. -/
def wrong : Spec.StatementRound K 2 0 := ⟨2, Fin.elim0⟩

/-- The zero polynomial as input oracle. -/
def original : Spec.OracleStatement K 2 1 () := ⟨0, Submodule.zero_mem _⟩

/-- The queries of a two-round execution: ambient events and challenges. -/
abbrev Q := events + challengeSpec oracleSig (protocol K 1 2)

/-- The challenge query at a challenge node. -/
abbrev drawE := fun c : ChallengeNode oracleSig (protocol K 1 2) =>
  (liftM (Q.query (.inr c)) : OracleComp Q _)

/-- The ambient event `i` inside the execution. -/
abbrev eventE (i : Fin 4) : OracleComp Q K := liftM (Q.query (.inl i))

/-- The execution's embedding of ambient queries. -/
abbrev liftEvents : QueryImpl events (OracleComp Q) := fun q => liftM (Q.query (.inl q))

/-! ## The execution runs every effect in protocol order -/

-- Migration rows: Sumcheck Interaction/Protocol #1, #2.

/-- An ambient event inside the execution is the same event query. -/
theorem simulate_event (i : Fin 4) : simulateQ liftEvents (event i) = eventE i := by
  simp [event, eventE]

/-- The terminal action runs event `3`. -/
theorem run_finalEvent
    (draw : (c : ChallengeNode oracleSig (protocol K 1 0)) →
      OracleComp Q (challengeSpec oracleSig _ c)) :
    Interaction.TwoParty.Lens.run (protocol K 1 0) (Prover.simulate liftEvents finalEvent)
        (sampler oracleSig (protocol K 1 0) draw) =
      (do let _ ← eventE 3; pure ⟨⟨⟩, (), ⟨⟩⟩) := by
  refine (run_done (l := oracleSig) (OutP := fun _ => Unit) (OutC := fun _ => PUnit)
    (simulateQ liftEvents (do let _ ← event 3; pure ())) (pure ⟨⟩)).trans ?_
  simp [simulate_event]
  rfl

/-- The last round runs event `2`, draws its challenge, then runs event `3`. -/
theorem run_last (a r : K) :
    Interaction.TwoParty.Lens.run (protocol K 1 1)
        (Prover.simulate liftEvents (Strategy.joinSlot ((fun b => lastProver a b r) <$> event 2)))
        (sampler oracleSig (protocol K 1 1) (tailDraw drawE)) = (do
      let b ← eventE 2
      let s : K ← tailDraw drawE (headNode 0)
      let _ ← eventE 3
      pure ⟨consTranscript (affine (b + a) (a * r + 1)) s ⟨⟩, (), ⟨⟩⟩) := by
  rw [Prover.simulate_joinSlot, run_joinSlot]
  simp only [simulateQ_map, Functor.map_map, bind_map_left, simulate_event]
  refine bind_congr fun b => ?_
  rw [lastProver, simulate_consProver, run_consProver]
  refine bind_congr fun s => ?_
  rw [run_finalEvent]
  simp

/-- Against the challenge sampler the prover runs event `0`, the first draw, event `2`, the
second draw and event `3`, in this order. -/
theorem run_adaptive :
    Interaction.TwoParty.Lens.run (protocol K 1 2) (Prover.simulate liftEvents adaptive)
        (sampler oracleSig (protocol K 1 2) drawE) = (do
      let a ← eventE 0
      let r : K ← drawE (headNode 1)
      let b ← eventE 2
      let s : K ← tailDraw drawE (headNode 0)
      let _ ← eventE 3
      pure ⟨consTranscript (affine a 1) r (consTranscript (affine (b + a) (a * r + 1)) s ⟨⟩),
        (), ⟨⟩⟩) := by
  rw [adaptive, Prover.simulate_joinSlot, run_joinSlot]
  simp only [simulateQ_map, Functor.map_map, bind_map_left, simulate_event]
  refine bind_congr fun a => ?_
  rw [simulate_consProver, run_consProver]
  refine bind_congr fun r => ?_
  erw [run_last a r]
  erw [LawfulMonad.bind_assoc]

/-- Both rounds pass their checks, and the verdict is the last message at the last challenge. -/
theorem verdict_adaptive (a b r s : K) :
    legacyVerdict K 1 2 D₀ events initial (decodeTranscript 2
      (consTranscript (affine a 1) r (consTranscript (affine (b + a) (a * r + 1)) s ⟨⟩))) =
      some ⟨(b + a) * s + (a * r + 1), ![r, s]⟩ := by
  refine (simulateQ_oracleVerifierProgram_succ 1 _ _ initial
    (roundFullTranscript (affine a 1) r)
    (legacyTranscript 1 (fun _ => affine (b + a) (a * r + 1)) fun _ => s)).trans ?_
  erw [roundCheck_eq_some 0 initial _ (by
    change ∑ x ∈ Finset.univ.map D₀, (affine a 1).val.eval x = 1
    simp [affine])]
  refine (simulateQ_oracleVerifierProgram_succ 0 _ _ _
    (roundFullTranscript (affine (b + a) (a * r + 1)) s)
    (legacyTranscript 0 Fin.elim0 Fin.elim0)).trans ?_
  erw [roundCheck_eq_some (R := K) (deg := 1) (n := 2) (D := D₀) (ambient := events) 1 _ _ (by
    change ∑ x ∈ Finset.univ.map D₀, (affine (b + a) (a * r + 1)).val.eval x =
      (affine a 1).val.eval r
    simp [affine])]
  change some (⟨(affine (b + a) (a * r + 1)).val.eval s,
    Fin.snoc (Fin.snoc (Fin.elim0 : Fin 0 → K) r) s⟩ : Spec.StatementRound K 2 (Fin.last 2)) = _
  have hvec : (Fin.snoc (Fin.snoc (Fin.elim0 : Fin 0 → K) r) s : Fin 2 → K) = ![r, s] :=
    funext fun i => by fin_cases i <;> rfl
  rw [hvec]
  simp [affine]

/-- The execution on a claim whose round checks pass: every effect in protocol order, then the
claim that the input polynomial evaluates to `(b + a) * s + (a * r + 1)` at the challenges
`r, s`. -/
theorem two_rounds : (verifier K 1 2 D₀ events).run initial (fun _ => original) adaptive = (do
    let a ← eventE 0
    let r : K ← drawE (headNode 1)
    let b ← eventE 2
    let s : K ← tailDraw drawE (headNode 0)
    let _ ← eventE 3
    pure (⟨consTranscript (affine a 1) r (consTranscript (affine (b + a) (a * r + 1)) s ⟨⟩), (),
      some (⟨(b + a) * s + (a * r + 1), ![r, s]⟩, fun _ => original)⟩ :
      Observation oracleSig (protocol K 1 2) (fun _ => Unit)
        (fun _ => Spec.StatementRound K 2 (Fin.last 2) × ∀ i, Spec.OracleStatement K 2 1 i))) := by
  rw [run_verifier_eq]
  erw [run_adaptive]
  refine (_root_.map_bind _ _ _).trans (bind_congr fun a => ?_)
  refine (_root_.map_bind _ _ _).trans (bind_congr fun r => ?_)
  refine (_root_.map_bind _ _ _).trans (bind_congr fun b => ?_)
  refine (_root_.map_bind _ _ _).trans (bind_congr fun s => ?_)
  refine (_root_.map_bind _ _ _).trans (bind_congr fun _ => ?_)
  refine (map_pure _ _).trans ?_
  dsimp only
  erw [verdict_adaptive]
  rfl

/-- Every challenge of the two-round protocol ranges over `K`. -/
theorem range_eq (c : ChallengeNode oracleSig (protocol K 1 2)) :
    challengeSpec oracleSig (protocol K 1 2) c = K := by
  obtain ⟨n, h⟩ := c
  rcases n with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, n⟩⟩⟩⟩
  · cases h
  · rfl
  · cases h
  · rfl
  · cases n

/-- A handler that records each query, writing `1` for a challenge: events answer `7, 3, 5, 11`
and every challenge answers `3`. -/
def record : QueryImpl Q (StateM (List ℕ))
  | .inl i => do modify (· ++ [i.val]); pure (![7, 3, 5, 11] i : K)
  | .inr c => do modify (· ++ [1]); pure (cast (range_eq c).symm (3 : K))

/-- The recorded order is `[0, 1, 2, 1, 3]`, and the final target is
`(5 + 7) * 3 + (7 * 3 + 1) = 7`. -/
example : (simulateQ record ((fun obs => obs.2.2.map fun t => t.1.target) <$>
    (verifier K 1 2 D₀ events).run initial (fun _ => original) adaptive)).run [] =
      (some 7, [0, 1, 2, 1, 3]) := by
  rw [two_rounds]
  rfl

-- Migration row: Sumcheck Interaction/Protocol #5.

/-- Passing every round check does not certify the final relation: the recorded run above accepts
the claim `⟨7, ![3, 3]⟩`, but the zero input polynomial is not `7` at the challenges `3, 3`. -/
theorem target_seven_not_final :
    ((⟨7, ![3, 3]⟩, fun _ => original), ()) ∉ Spec.relationRound K 2 1 D₀ (Fin.last 2) := by
  have : IsEmpty (Fin (2 - (Fin.last 2 : ℕ))) := ⟨fun i => by have := i.2; simp at this⟩
  simpa [Spec.relationRound, original] using (by decide : (0 : K) ≠ 7)

/-! ## A bad first round followed by a good round -/

-- Migration rows: Sumcheck Interaction/Protocol #3, #4.

/-- On the false claim the first check fails, yet the execution still runs both rounds and every
effect in protocol order, and the verdict rejects. The decision's own queries stop after the
first round's check; see `runWithLog_wrong`. -/
theorem bad_first_rounds :
    (verifier K 1 2 D₀ events).run wrong (fun _ => original) adaptive = (do
      let a ← eventE 0
      let r : K ← drawE (headNode 1)
      let b ← eventE 2
      let s : K ← tailDraw drawE (headNode 0)
      let _ ← eventE 3
      pure (⟨consTranscript (affine a 1) r (consTranscript (affine (b + a) (a * r + 1)) s ⟨⟩),
        (), none⟩ : Observation oracleSig (protocol K 1 2) (fun _ => Unit)
          (fun _ => Spec.StatementRound K 2 (Fin.last 2) × ∀ i, Spec.OracleStatement K 2 1 i))) :=
            by
  rw [run_verifier_eq]
  erw [run_adaptive]
  refine (_root_.map_bind _ _ _).trans (bind_congr fun a => ?_)
  refine (_root_.map_bind _ _ _).trans (bind_congr fun r => ?_)
  refine (_root_.map_bind _ _ _).trans (bind_congr fun b => ?_)
  refine (_root_.map_bind _ _ _).trans (bind_congr fun s => ?_)
  refine (_root_.map_bind _ _ _).trans (bind_congr fun _ => ?_)
  refine (map_pure _ _).trans ?_
  dsimp only
  erw [legacyVerdict_eq_none (k := 1) wrong (roundFullTranscript (affine a 1) r)
    (legacyTranscript 1 (fun _ => affine (b + a) (a * r + 1)) fun _ => s) (by
      change ∑ x ∈ Finset.univ.map D₀, (affine a 1).val.eval x ≠ 2
      simpa [affine, wrong] using (by decide : (1 : K) ≠ 2))]
  rfl

/-- The recorded order of the rejected execution is again `[0, 1, 2, 1, 3]`. -/
example : (simulateQ record ((fun obs => obs.2.2.isSome) <$>
    (verifier K 1 2 D₀ events).run wrong (fun _ => original) adaptive)).run [] =
      (false, [0, 1, 2, 1, 3]) := by
  rw [bad_first_rounds]
  rfl

/-! ## The decision log of a bad first round -/

section DecisionLog

variable {R : Type} [CommSemiring R] [DecidableEq R] [SampleableType R] {deg k d : ℕ}
  (D : Fin d ↪ R) {ι : Type} {ambient : OracleSpec ι} {κ : Type} {full : OracleSpec.{0, 0} κ}

/-- The first round's check of the decision on a completed run, with its message queries routed
to the oracle nodes of the run. -/
def firstCheck (stmt : Spec.StatementRound R (k + 1) 0)
    (tr : FreeM.PathAlong oracleSig (protocol R deg (k + 1))) :
    OracleComp (ambient + (pathResources (polyFamily R deg (k + 1)) _ (FreeM.projectPathAlong
      oracleSig _ tr)).spec)
      (Option (Spec.StatementRound R (k + 1) (0 : Fin (k + 1)).succ)) :=
  simulateQ (decisionLift R deg (k + 1) ambient _) (simulateQ (route R deg (k + 1) _)
    (simulateQ (Spec.leftMessageQuery R deg k) (roundCheck R deg (k + 1) D ambient 0 stmt
      (Challenges.fst (pSpec₁ := Spec.SingleRound.pSpec R deg) (pSpec₂ := Spec.pSpec R deg k)
        (viewChallenges (toView _ tr)))).run))

/-- The handler of the logged decision: ambient queries go to `amb`, and the input and message
oracles answer from the input data and the run's payloads. -/
abbrev checkHandler (amb : QueryImpl ambient (OracleComp full))
    (data : ∀ i, Spec.OracleStatement R (k + 1) deg i)
    (tr : FreeM.PathAlong oracleSig (protocol R deg (k + 1))) :
    QueryImpl (ambient + (pathResources (polyFamily R deg (k + 1)) _ (FreeM.projectPathAlong
      oracleSig _ tr)).spec) (OracleComp full) :=
  QueryImpl.addLift amb ((pathResources (polyFamily R deg (k + 1)) _ (FreeM.projectPathAlong
    oracleSig _ tr)).answer (data, payloads _ tr))

/-- When the first round's check fails, the logged decision rejects and its log is the log of
that check alone: no query of a later round is made. -/
theorem decide_log_badFirst (amb : QueryImpl ambient (OracleComp full))
    (stmt : Spec.StatementRound R (k + 1) 0) (data : ∀ i, Spec.OracleStatement R (k + 1) deg i)
    (msg : R⦃≤ deg⦄[X]) (chal : R) (tail : FreeM.PathAlong oracleSig (protocol R deg k))
    (h : ∑ x ∈ Finset.univ.map D, msg.val.eval x ≠ stmt.target) :
    (simulateQ (checkHandler amb data (consTranscript msg chal tail)).withLogging
        ((verifier R deg (k + 1) D ambient).decide stmt _
          (toView _ (consTranscript msg chal tail))).run).run =
      (fun z => (none, z.2)) <$>
        (simulateQ (checkHandler amb data (consTranscript msg chal tail)).withLogging
          (firstCheck D stmt (consTranscript msg chal tail))).run := by
  set tr := consTranscript msg chal tail
  obtain ⟨cont, hcont, hprog⟩ :
      ∃ cont : Option (Spec.StatementRound R (k + 1) (0 : Fin (k + 1)).succ) →
        OracleComp [(Spec.pSpec R deg (k + 1)).Message]ₒ
          (Option (Spec.StatementRound R (k + 1) (Fin.last (k + 1)))), cont none = pure none ∧
        legacyProgram R deg (k + 1) D ambient stmt (viewChallenges (toView _ tr)) =
          (simulateQ (Spec.leftMessageQuery R deg k) (roundCheck R deg (k + 1) D ambient 0 stmt
            (Challenges.fst (pSpec₁ := Spec.SingleRound.pSpec R deg)
              (pSpec₂ := Spec.pSpec R deg k) (viewChallenges (toView _ tr)))).run :
            OracleComp [(Spec.pSpec R deg (k + 1)).Message]ₒ _) >>= cont :=
    ⟨_, rfl, rfl⟩
  have hF : simulateQ (checkHandler amb data tr) (firstCheck D stmt tr) = pure none := by
    unfold firstCheck checkHandler
    refine (simulateQ_decisionLift_monad (m := OracleComp full) amb _ data _ _).trans ?_
    refine congrArg pure ((QueryImpl.simulateQ_simulateQ_eq_of_apply
      (simulateQ_route (k + 1) tr) _).trans ?_)
    rw [viewChallenges_toView]
    change simulateQ (OracleInterface.simOracle0 _
      (roundFullTranscript msg chal ++ₜ decodeTranscript k tail).messages)
      (simulateQ (Spec.leftMessageQuery R deg k) (roundCheck R deg (k + 1) D ambient 0 stmt
        (Challenges.fst (roundFullTranscript msg chal ++ₜ decodeTranscript k tail).challenges)).run)
      = _
    rw [simulateQ_leftMessageQuery, Legacy.challenges_append_fst,
      roundCheck_eq_none 0 stmt _ h]
  have hsupp : ∀ z ∈ support (simulateQ (checkHandler amb data tr).withLogging
      (firstCheck D stmt tr)).run, z.1 = none := by
    intro z hz
    have : z.1 ∈ support (Prod.fst <$> (simulateQ (checkHandler amb data tr).withLogging
        (firstCheck D stmt tr)).run) := by
      rw [support_map]; exact ⟨z, hz, rfl⟩
    rwa [QueryImpl.fst_map_run_withLogging, hF, support_pure, Set.mem_singleton_iff] at this
  rw [verifier_decide, hprog]
  refine (congrArg (fun x => (simulateQ (checkHandler amb data tr).withLogging x).run)
    ((congrArg (simulateQ _) (simulateQ_bind _ _ _)).trans (simulateQ_bind _ _ _))).trans ?_
  refine (congrArg WriterT.run (simulateQ_bind _ _ _)).trans ?_
  rw [WriterT.run_bind', map_eq_bind_pure_comp]
  refine bind_congr_of_forall_mem_support _ fun z hz => ?_
  obtain ⟨v, w⟩ := z
  obtain rfl : v = none := hsupp _ hz
  dsimp only
  rw [hcont]
  simp

end DecisionLog

/-- Every run of the adaptive prover sends `a * X + 1` first. -/
theorem mem_support_adaptive {x} (hx : x ∈ support (simulateQ (QueryImpl.id' Q).withLogging
    (Interaction.TwoParty.Lens.run (protocol K 1 2) (Prover.simulate liftEvents adaptive)
      (sampler oracleSig (protocol K 1 2) drawE))).run) :
    ∃ a r tail, x.1.1 = consTranscript (affine a 1) r tail := by
  have : x.1 ∈ support (Prod.fst <$> (simulateQ (QueryImpl.id' Q).withLogging
      (Interaction.TwoParty.Lens.run (protocol K 1 2) (Prover.simulate liftEvents adaptive)
        (sampler oracleSig (protocol K 1 2) drawE))).run) := by
    rw [support_map]; exact ⟨x, hx, rfl⟩
  rw [QueryImpl.fst_map_run_withLogging, simulateQ_id', run_adaptive] at this
  obtain ⟨a, -, h⟩ := support_bind_exists this
  obtain ⟨r, -, h⟩ := support_bind_exists h
  obtain ⟨b, -, h⟩ := support_bind_exists h
  obtain ⟨s, -, h⟩ := support_bind_exists h
  obtain ⟨_, -, h⟩ := support_bind_exists h
  rw [mem_support_pure_iff] at h
  exact ⟨a, r, _, congrArg Sigma.fst h⟩

/-- On the false claim the logged execution runs every effect of the adaptive prover, rejects, and
its decision log holds exactly the queries of the first round's check. -/
theorem runWithLog_wrong :
    (verifier K 1 2 D₀ events).runWithLog wrong (fun _ => original) adaptive = (do
      let x ← (simulateQ (QueryImpl.id' Q).withLogging
        (Interaction.TwoParty.Lens.run (protocol K 1 2) (Prover.simulate liftEvents adaptive)
          (sampler oracleSig (protocol K 1 2) drawE))).run
      let y ← (simulateQ (checkHandler liftEvents (fun _ => original) x.1.1).withLogging
        (firstCheck D₀ wrong x.1.1)).run
      pure ⟨⟨x.1.1, x.1.2.1, none⟩, x.2.fst, y.2⟩) := by
  unfold OracleVerifier.runWithLog
  refine bind_congr_of_forall_mem_support _ fun x hx => ?_
  obtain ⟨a, r, tail, htr⟩ := mem_support_adaptive hx
  obtain ⟨⟨tr, out, c⟩, log⟩ := x
  obtain rfl : tr = _ := htr
  dsimp only
  erw [decide_log_badFirst D₀ liftEvents wrong (fun _ => original) (affine a 1) r tail (by
    change ∑ x ∈ Finset.univ.map D₀, (affine a 1).val.eval x ≠ 2
    simpa [affine] using (by decide : (1 : K) ≠ 2))]
  simp

/-- Forgetting the logs, the logged execution on the false claim records the order
`[0, 1, 2, 1, 3]`: both rounds still run. -/
example : (simulateQ record ((fun z => z.1.2.2.isSome) <$>
    (verifier K 1 2 D₀ events).runWithLog wrong (fun _ => original) adaptive)).run [] =
      (false, [0, 1, 2, 1, 3]) := by
  rw [show ((fun z => z.1.2.2.isSome) <$>
      (verifier K 1 2 D₀ events).runWithLog wrong (fun _ => original) adaptive) =
    (fun obs => obs.2.2.isSome) <$> (Sigma.fst <$>
      (verifier K 1 2 D₀ events).runWithLog wrong (fun _ => original) adaptive) by
    rw [Functor.map_map], OracleVerifier.map_fst_runWithLog, bad_first_rounds]
  rfl

/-! ## A sampled adaptive prover -/

-- Migration row: Sumcheck Interaction/Protocol #6.

/-- The last round of the sampled prover: the message `(a + b) * X + (a * r + 1)`, then one more
sample. -/
def sampledLast (a b r : K) : Prover oracleSig unifSpec (protocol K 1 1) (fun _ => Unit) :=
  consProver (affine (a + b) (a * r + 1)) fun _ =>
    (do let _ ← ($ᵗ K); pure () : ProbComp Unit)

/-- The adaptive prover with sampled private memory. -/
def sampledAdaptive : Prover oracleSig unifSpec (protocol K 1 2) (fun _ => Unit) :=
  Strategy.joinSlot ((fun a => consProver (affine a 1) fun r =>
    Strategy.joinSlot ((fun b => sampledLast a b r) <$> ($ᵗ K))) <$> ($ᵗ K))

/-- The initial claim is false: the zero polynomial sums to `0`, not `1`, over `{0}²`. -/
theorem initial_false :
    (initial, fun _ => original) ∉ (Spec.relationRound K 2 1 D₀ 0).language := by
  simp [Set.language, Spec.relationRound, original, initial]

/-- The sampled prover makes the false claim reach the final language with probability at most
`2 / 17`, the soundness error `n * deg / |K|`. -/
example {σ : Type} (init : ProbComp σ) (impl : QueryImpl unifSpec (StateT σ ProbComp)) :
    letI : MeasurableSpace (Observation oracleSig (protocol K 1 2) (fun _ => Unit)
      (fun _ => Spec.StatementRound K 2 (Fin.last 2) × (∀ i, Spec.OracleStatement K 2 1 i))) := ⊤
    𝒟[experiment init impl (challengeQueryImpl oracleSig (protocol K 1 2))
        ((verifier K 1 2 D₀ unifSpec).run initial (fun _ => original) sampledAdaptive)]
        (accepted D₀) ≤ 2 / 17 := by
  refine (RoundByRoundTest.false_claim_bound K 2 1 D₀ unifSpec init impl sampledAdaptive initial
    (fun _ => original) initial_false).trans (le_of_eq ?_)
  rw [ZMod.card]
  norm_num

end

run_cmd
  for decl in [``Interaction.Core.Prover.simulate_joinSlot,
      ``Sumcheck.Core.EffectsTest.eval_affine, ``Sumcheck.Core.EffectsTest.answer_affine,
      ``Sumcheck.Core.EffectsTest.route_affine, ``Sumcheck.Core.EffectsTest.run_verifier_eq,
      ``Sumcheck.Core.EffectsTest.two_rounds, ``Sumcheck.Core.EffectsTest.bad_first_rounds,
      ``Sumcheck.Core.EffectsTest.range_eq, ``Sumcheck.Core.EffectsTest.decide_log_badFirst,
      ``Sumcheck.Core.EffectsTest.mem_support_adaptive,
      ``Sumcheck.Core.EffectsTest.runWithLog_wrong,
      ``Sumcheck.Core.EffectsTest.target_seven_not_final] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected axiom {ax} in {decl}"

end Sumcheck.Core.EffectsTest
