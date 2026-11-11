/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLibTest.ProofSystem.Sumcheck.Core.Effects
import ArkLibTest.ProofSystem.Sumcheck.Core.Rounds
import ArkLib.ProofSystem.Sumcheck.Core.Composition

/-!
# Two Sumcheck rounds through an exported oracle

The first round checks a bivariate input `X₀ + X₁` over `ZMod 17` without querying it. It exports
a one-variable oracle: the input with its first variable fixed to the round challenge `r`, plus
the round message at `r`. The second round is the one-round Sumcheck verifier over the exported
oracle, so its final claim is a claim about the exported polynomial.

The composite is `OracleVerifier.append` of the two. The prover sends `2 X + 1`, runs an ambient
event, sends `X + 3 r + 1 + bump`, and runs another event; its private output is an arbitrary
`hidden` natural number plus both answers, without reduction modulo the field
characteristic. Both rounds always run, and the challenges come from the
challenge oracle.

* With target `4` and `bump = 0` both checks pass, the claim summary is `(10, 10)` at the
  challenges `2, 3`, and every accepted claim lies in the final relation of the exported oracle.
* With target `0` the first check rejects.
* With `bump = 1` the first check passes and the second rejects.

The affine messages and their oracle answers, the source routing rows #1 and #2, are checked in
`Effects`.
-/

namespace Sumcheck.Core.RoutingTest
open Polynomial PFunctor FreeM Interaction.Core Interaction.TwoParty.Lens Interaction.Oracle
  OracleComp OracleSpec ProtocolSpec Sumcheck.Core.EffectsTest

noncomputable section

/-- Ambient events return natural numbers, independently of the polynomial field. -/
abbrev events : OracleSpec (Fin 4) := Fin 4 →ₒ ℕ

/-- An ambient event. -/
def event (i : Fin 4) : OracleComp events ℕ := liftM (events.query i)

/-- The ambient events and the two-round challenge oracle. -/
abbrev Q := events + challengeSpec oracleSig (protocol K 1 2)

/-- Lift an ambient event into the run's oracle. -/
abbrev eventE (i : Fin 4) : OracleComp Q ℕ := liftM (Q.query (.inl i))

/-- The challenge requests of the two-round run. -/
abbrev drawE := fun c : ChallengeNode oracleSig (protocol K 1 2) =>
  (liftM (Q.query (.inr c)) : OracleComp Q _)

/-- Preserve ambient queries when simulating the prover in the run. -/
abbrev liftEvents : QueryImpl events (OracleComp Q) := fun q => liftM (Q.query (.inl q))

/-- Simulating an event sends it to the ambient part of the run's oracle. -/
theorem simulate_event (i : Fin 4) : simulateQ liftEvents (event i) = eventE i :=
  simulateQ_spec_query _ _

/-- The domain `{0, 1}`. -/
def D₂ : Fin 2 ↪ K := ⟨fun i => (i.val : K), by decide⟩

/-- A univariate polynomial of degree at most `d` is a one-variable polynomial of individual
degree at most `d`. -/
theorem toMvPolynomial_mem {d : ℕ} {q : K[X]} (hq : q ∈ degreeLE K d) :
    q.toMvPolynomial (0 : Fin 1) ∈ MvPolynomial.restrictDegree (Fin 1) K d := by
  rw [q.as_sum_range_C_mul_X_pow, map_sum]
  refine Submodule.sum_mem _ fun i hi => ?_
  have hdeg : q.natDegree ≤ d := natDegree_le_iff_degree_le.2 (mem_degreeLE.1 hq)
  rw [map_mul, map_pow, toMvPolynomial_C, toMvPolynomial_X, MvPolynomial.C_mul_X_pow_eq_monomial,
    MvPolynomial.mem_restrictDegree]
  intro s hs j
  rw [Finset.mem_singleton.1 (MvPolynomial.support_monomial_subset hs), Fin.fin_one_eq_zero j,
    Finsupp.single_eq_same]
  exact (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)).trans hdeg

/-- The exported polynomial: the input with its first variable fixed to `r`, plus the message
at `r`, in one variable. -/
def exportPoly (r : K) (p : Spec.OracleStatement K 2 1 ()) (msg : K⦃≤ 1⦄[X]) :
    Spec.OracleStatement K 1 1 () :=
  ⟨(p.val.evalExcept 1 (fun _ => r) + C (msg.val.eval r)).toMvPolynomial 0,
    toMvPolynomial_mem (Submodule.add_mem _ (MvPolynomial.evalExcept_mem_degreeLE 1 _ p.2)
      (mem_degreeLE.2 (degree_C_le.trans (by norm_num))))⟩

/-- The exported polynomial at `y` is the input at `(r, y)` plus the message at `r`. -/
theorem eval_exportPoly (r : K) (p : Spec.OracleStatement K 2 1 ()) (msg : K⦃≤ 1⦄[X])
    (y : Fin 1 → K) :
    MvPolynomial.eval y (exportPoly r p msg).val = MvPolynomial.eval ![r, y 0] p.val +
      msg.val.eval r := by
  simp only [exportPoly, MvPolynomial.eval_toMvPolynomial, eval_add, eval_C,
    MvPolynomial.eval_evalExcept]
  have hpt : (Fin.insertNth 1 (y 0) fun _ => r : Fin 2 → K) = ![r, y 0] :=
    funext fun i => by fin_cases i <;> rfl
  rw [hpt]


/-- The resources of the first round: the bivariate input and the round message. -/
abbrev firstResources :=
  pathResources (Spec.polynomialFamily K 2 1) (round K 1) (roundPath K 1)

/-- The export map at the challenge `r`: one input query at `(r, y)` and one message query at
`r`. -/
def exportMap (r : K) : OracleMap firstResources (Spec.polynomialFamily K 1 1) where
  f x _ := exportPoly r (x.1 ()) (x.2 (.inl ⟨⟩))
  impl q := do
    let old : K ← liftM (firstResources.spec.query (.inl ⟨(), ![r, q.2 0]⟩))
    let sent : K ← liftM (firstResources.spec.query (.inr ⟨.inl ⟨⟩, r⟩))
    pure (old + sent)
  law x q := by
    rcases q with ⟨⟨⟩, y⟩
    exact (eval_exportPoly r (x.1 ()) (x.2 (.inl ⟨⟩)) y).symm

/-- The output map of the first round: the export map at the round's challenge. -/
def exportOut : K → (p : Path (round K 1)) → View (round K 1) p →
    OracleMap (pathResources (Spec.polynomialFamily K 2 1) (round K 1) p)
      (Spec.polynomialFamily K 1 1)
  | _, ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩, v => exportMap (viewChallenge v)

/-- A query to the round message at `x`. -/
def messageAt (x : K) : OracleComp [(Spec.SingleRound.pSpec K 1).Message]ₒ K :=
  liftM (OracleSpec.query (spec := [(Spec.SingleRound.pSpec K 1).Message]ₒ) ⟨default, x⟩)

/-- The first round's check: the message sums to the target over `{0, 1}`; the claim for the
second round is three times the message at the challenge. -/
def firstCheck (target : K) (chals : (Spec.SingleRound.pSpec K 1).Challenges) :
    OptionT (OracleComp [(Spec.SingleRound.pSpec K 1).Message]ₒ) (Spec.StatementRound K 1 0) := do
  let a ← OptionT.lift (messageAt 0)
  let b ← OptionT.lift (messageAt 1)
  if a + b = target then
    let v ← OptionT.lift (messageAt (chals default))
    pure ⟨3 * v, Fin.elim0⟩
  else failure

/-- The first round: the sum check, exporting the input at the challenge plus the message. -/
def firstVerifier : OracleVerifier events (round K 1) K (fun _ => Spec.StatementRound K 1 0)
    (Spec.polynomialFamily K 2 1) (fun _ => Spec.polynomialFamily K 1 1) :=
  checkVerifier events _ firstCheck exportOut

/-- The second round: the Sumcheck verifier of one round over the exported oracle. -/
def secondVerifier : OracleVerifier events (protocol K 1 1) (Spec.StatementRound K 1 0)
    (fun _ => Spec.StatementRound K 1 (Fin.last 1)) (Spec.polynomialFamily K 1 1)
    (fun _ => Spec.polynomialFamily K 1 1) :=
  verifier K 1 1 D₂ events

/-- The composite keeps the exported oracle, whatever the intermediate statement. -/
def compatible : OracleVerifier.OutputCompatibility firstVerifier fun _ => secondVerifier where
  outputMap stmt p v := (secondVerifier.outputMap ⟨0, Fin.elim0⟩ _
    (View.split (round K 1) (fun _ => protocol K 1 1) p v).2).comp
      (OracleVerifier.suffixRoute firstVerifier stmt p v)
  agrees _ _ _ _ _ _ := rfl

/-- The two rounds through the exported oracle. -/
def routed := firstVerifier.append (fun _ => secondVerifier) compatible

/-- The prover's terminal action: event `3`, and the output `hidden + tag` plus its answer. -/
def finishProver (hidden tag : ℕ) : Prover oracleSig events (protocol K 1 0) (fun _ => ℕ) :=
  ((fun fin => hidden + tag + fin) <$> event 3 : OracleComp events ℕ)

/-- The prover sends `2 X + 1`; after the challenge `r`, event `2` gives a tag, and it sends
`X + 3 r + 1 + bump`; after the last challenge, event `3` gives another. Its private output is
`hidden` plus both answers. -/
def wholeProver (hidden : ℕ) (bump : K) : Prover oracleSig events (protocol K 1 2) (fun _ => ℕ) :=
  consProver (affine 2 1) fun r => Strategy.joinSlot ((fun tag =>
    consProver (affine 1 (3 * r + 1 + bump)) fun _ => finishProver hidden tag) <$> event 2)

/-- The terminal action of the prover runs event `3`. -/
theorem run_finish (hidden tag : ℕ)
    (draw : (c : ChallengeNode oracleSig (protocol K 1 0)) →
      OracleComp Q (challengeSpec oracleSig _ c)) :
    Interaction.TwoParty.Lens.run (protocol K 1 0)
        (Prover.simulate liftEvents (finishProver hidden tag))
        (sampler oracleSig (protocol K 1 0) draw) =
      (do let fin ← eventE 3; pure ⟨⟨⟩, hidden + tag + fin, ⟨⟩⟩) := by
  refine (run_done (l := oracleSig) (OutP := fun _ => ℕ) (OutC := fun _ => PUnit)
    (simulateQ liftEvents ((fun fin => hidden + tag + fin) <$> event 3)) (pure ⟨⟩)).trans ?_
  simp
  rfl

/-- Against the challenge sampler the prover draws the first challenge, runs event `2`, draws
the second challenge and runs event `3`, in this order. -/
theorem run_wholeProver (hidden : ℕ) (bump : K) :
    Interaction.TwoParty.Lens.run (protocol K 1 2)
        (Prover.simulate liftEvents (wholeProver hidden bump))
        (sampler oracleSig (protocol K 1 2) drawE) = (do
      let r : K ← drawE (headNode 1)
      let tag ← eventE 2
      let s : K ← tailDraw drawE (headNode 0)
      let fin ← eventE 3
      pure (⟨consTranscript (affine 2 1) r
        (consTranscript (affine 1 (3 * r + 1 + bump)) s ⟨⟩), hidden + tag + fin, ⟨⟩⟩ :
          (_ : PathAlong oracleSig (protocol K 1 2)) × ℕ × PUnit)) := by
  rw [wholeProver, simulate_consProver, run_consProver]
  refine bind_congr fun r => ?_
  rw [Prover.simulate_joinSlot, run_joinSlot]
  simp only [simulateQ_map, Functor.map_map, bind_map_left, simulate_event, bind_assoc]
  refine bind_congr fun tag => ?_
  rw [simulate_consProver, run_consProver]
  simp only [bind_assoc]
  refine bind_congr fun s => ?_
  erw [run_finish]
  simp only [bind_assoc]
  rfl

/-- A message query is answered by evaluating the message. -/
theorem simulate_messageAt (msg : K⦃≤ 1⦄[X]) (chal x : K) :
    simulateQ (OracleInterface.simOracle0 _ (roundFullTranscript msg chal).messages)
      (messageAt x) = (pure (msg.val.eval x) : Id K) := by
  exact (simulateQ_spec_query _ _).trans rfl

/-- The first round's verdict: the claim three times the message at the challenge, if the message
sums to the target over `{0, 1}`. -/
theorem checkVerdict_first (target : K) (msg : K⦃≤ 1⦄[X]) (chal : K) :
    checkVerdict firstCheck target (roundTranscript msg chal) =
      if msg.val.eval 0 + msg.val.eval 1 = target then
        some ⟨3 * msg.val.eval chal, Fin.elim0⟩ else none := by
  unfold checkVerdict firstCheck
  simp only [OptionT.run_bind, OptionT.run_lift, roundMessage_roundTranscript,
    roundChallenge_roundTranscript, Option.elimM, simulateQ_bind, simulateQ_pure]
  erw [simulate_messageAt]
  erw [LawfulMonad.pure_bind]
  dsimp only [Option.elim]
  simp only [simulateQ_bind, simulateQ_pure]
  erw [simulate_messageAt]
  erw [LawfulMonad.pure_bind]
  dsimp only [Option.elim]
  split <;> rename_i h
  · rw [ite_eq_left (by exact h : msg.val.eval 0 + msg.val.eval 1 = target)]
    simp only [OptionT.run_bind, OptionT.run_lift, Option.elimM, simulateQ_bind, simulateQ_pure]
    erw [simulate_messageAt]
    rfl
  · rw [ite_eq_right (by exact h : ¬ msg.val.eval 0 + msg.val.eval 1 = target)]
    rfl

/-- The transcript of the whole prover at the challenges `r` and `s`. -/
abbrev wholeTranscript (bump r s : K) : PathAlong oracleSig (protocol K 1 2) :=
  consTranscript (affine 2 1) r (consTranscript (affine 1 (3 * r + 1 + bump)) s ⟨⟩)

/-- The composite verdict on the whole prover's transcript: the first check, then the Sumcheck
verdict of the second round on its claim. The output oracle is the exported polynomial. -/
def routedVerdict (target bump : K) (x : ∀ i, Spec.OracleStatement K 2 1 i) (r s : K) :
    Option (Spec.StatementRound K 1 (Fin.last 1) × ∀ i, Spec.OracleStatement K 1 1 i) :=
  (match checkVerdict firstCheck target (roundTranscript (affine 2 1) r) with
    | none => none
    | some mid => legacyVerdict K 1 1 D₂ events mid
        (decodeTranscript 1 (consTranscript (affine 1 (3 * r + 1 + bump)) s ⟨⟩))).map
    fun t => (t, fun _ => exportPoly r (x ()) (affine 2 1))

/-- The composite's output oracle is the exported polynomial at the first challenge. -/
theorem compatible_output (target r : K) (msg : K⦃≤ 1⦄[X])
    (tail : PathAlong oracleSig (protocol K 1 1)) (x : ∀ i, Spec.OracleStatement K 2 1 i) :
    (compatible.outputMap target _
        (toView ((round K 1).append fun _ => protocol K 1 1) ⟨msg, ⟨r, tail⟩⟩)).f
      ((x, (payloads ((round K 1).append fun _ => protocol K 1 1) ⟨msg, ⟨r, tail⟩⟩))) =
      fun _ => exportPoly r (x ()) msg := by
  funext u
  change ((OracleVerifier.suffixRoute firstVerifier target _
    (toView ((round K 1).append fun _ => protocol K 1 1) ⟨msg, ⟨r, tail⟩⟩)).f
      ((x, (payloads ((round K 1).append fun _ => protocol K 1 1) ⟨msg, ⟨r, tail⟩⟩)))
      ).1 u = _
  exact congrFun (congrArg Prod.fst
    (suffixRoute_round events _ firstCheck exportOut target x msg r tail)) u

/-- The composite run of the whole prover: the two draws and the two events in protocol order,
then the composite verdict. -/
theorem run_routed (target : K) (hidden : ℕ) (bump : K) (x : ∀ i, Spec.OracleStatement K 2 1 i) :
    routed.run target x (wholeProver hidden bump) = (do
      let r : K ← drawE (headNode 1)
      let tag ← eventE 2
      let s : K ← tailDraw drawE (headNode 0)
      let fin ← eventE 3
      pure (⟨wholeTranscript bump r s, hidden + tag + fin, routedVerdict target bump x r s⟩ :
        Observation oracleSig (protocol K 1 2) (fun _ => ℕ)
          (fun _ => Spec.StatementRound K 1 (Fin.last 1) ×
            ∀ i, Spec.OracleStatement K 1 1 i))) := by
  refine (run_append_checkVerifier (s := protocol K 1 1) _ _ _ _ _ _ _ _ _).trans ?_
  erw [run_wholeProver]
  erw [LawfulMonad.bind_assoc]
  refine bind_congr fun r => ?_
  erw [LawfulMonad.bind_assoc]
  refine bind_congr fun tag => ?_
  erw [LawfulMonad.bind_assoc]
  refine bind_congr fun s => ?_
  erw [LawfulMonad.bind_assoc]
  refine bind_congr fun fin => ?_
  erw [LawfulMonad.pure_bind]
  dsimp only
  split <;> rename_i hc
  · rw [routedVerdict, show checkVerdict firstCheck target (roundTranscript (affine 2 1) r) = none
      from hc]
    erw [simulateQ_pure, LawfulMonad.pure_bind]
    rfl
  · rename_i mid
    rw [routedVerdict,
      show checkVerdict firstCheck target (roundTranscript (affine 2 1) r) = some mid from hc]
    erw [decideWith_foldVerifier]
    erw [simulateQ_pure, LawfulMonad.pure_bind]
    erw [compatible_output]
    rfl

/-- The Sumcheck verdict of the second round on the claim `t`: the message `X + c` sums to
`2 c + 1` over `{0, 1}`; on a match the claim is the message at the challenge. -/
theorem secondVerdict (t c s : K) :
    legacyVerdict K 1 1 D₂ events ⟨t, Fin.elim0⟩
        (decodeTranscript 1 (consTranscript (affine 1 c) s ⟨⟩)) =
      if 2 * c + 1 = t then some ⟨s + c, ![s]⟩ else none := by
  have hsum : ∑ y ∈ Finset.univ.map D₂, (affine 1 c).val.eval y = 2 * c + 1 := by
    simp [D₂, eval_affine]
    ring
  refine (simulateQ_oracleVerifierProgram_succ 0 _ _ _ (roundFullTranscript (affine 1 c) s)
    (legacyTranscript 0 Fin.elim0 Fin.elim0)).trans ?_
  split <;> rename_i h
  · erw [roundCheck_eq_some (R := K) (deg := 1) (n := 1) (D := D₂) (ambient := events) 0 _ _
      (hsum.trans h)]
    change some (⟨(affine 1 c).val.eval s, Fin.snoc (Fin.elim0 : Fin 0 → K) s⟩ :
      Spec.StatementRound K 1 (Fin.last 1)) = _
    have hvec : (Fin.snoc (Fin.elim0 : Fin 0 → K) s : Fin 1 → K) = ![s] :=
      funext fun i => by fin_cases i; rfl
    rw [hvec, eval_affine, one_mul]
  · have hnone := roundCheck_eq_none (R := K) (deg := 1) (n := 1) (D := D₂)
      (ambient := events) 0 ⟨t, Fin.elim0⟩ (roundFullTranscript (affine 1 c) s)
      (fun e => h (hsum.symm.trans e))
    erw [hnone]
    rfl

/-! ## Scenarios -/

-- Migration rows: Sumcheck Interaction/SourceRouting #4–#7.

/-- The bivariate input `X₀ + X₁`, which sums to `4` over `{0, 1}²`. -/
def input : Spec.OracleStatement K 2 1 () :=
  ⟨MvPolynomial.X 0 + MvPolynomial.X 1,
    Submodule.add_mem _ (RoundsTest.X_mem 0) (RoundsTest.X_mem 1)⟩

/-- The input at `y` is `y 0 + y 1`. -/
theorem eval_input (y : Fin 2 → K) : MvPolynomial.eval y input.val = y 0 + y 1 := by
  simp [input]

/-- With target `4` and the honest second message, both rounds accept: the claim is the second
message at the last challenge, and the output oracle is the exported polynomial. -/
theorem routedVerdict_accepted (r s : K) :
    routedVerdict 4 0 (fun _ => input) r s =
      some (⟨s + (3 * r + 1), ![s]⟩, fun _ => exportPoly r input (affine 2 1)) := by
  unfold routedVerdict
  rw [checkVerdict_first, ite_eq_left (by rw [eval_affine, eval_affine]; decide)]
  dsimp only
  rw [eval_affine, secondVerdict, ite_eq_left (by ring), add_zero]
  rfl

/-- A wrong first sum rejects the composite. -/
theorem routedVerdict_prefix (bump r s : K) (x : ∀ i, Spec.OracleStatement K 2 1 i) :
    routedVerdict 0 bump x r s = none := by
  unfold routedVerdict
  rw [checkVerdict_first, ite_eq_right (by rw [eval_affine, eval_affine]; decide)]
  rfl

/-- A second message off by one passes the first check and fails the second. -/
theorem routedVerdict_suffix (r s : K) (x : ∀ i, Spec.OracleStatement K 2 1 i) :
    routedVerdict 4 1 x r s = none := by
  unfold routedVerdict
  rw [checkVerdict_first, ite_eq_left (by rw [eval_affine, eval_affine]; decide)]
  dsimp only
  rw [eval_affine, secondVerdict,
    ite_eq_right fun h => absurd (by linear_combination h : (2 : K) = 0) (by decide)]
  rfl

/-- The target of a final claim and the output oracle at its challenges. -/
def claimSummary
    (claim : Spec.StatementRound K 1 (Fin.last 1) × ∀ i, Spec.OracleStatement K 1 1 i) : K × K :=
  (claim.1.target, MvPolynomial.eval claim.1.challenges (claim.2 ()).val)

/-- The accepted claim's summary: its target `s + 3 r + 1`, and the exported polynomial at `s`,
which is `r + s` plus the first message `2 r + 1`. -/
theorem claimSummary_accepted (r s : K) :
    claimSummary (⟨s + (3 * r + 1), ![s]⟩, fun _ => exportPoly r input (affine 2 1)) =
      (s + (3 * r + 1), r + s + (2 * r + 1)) := by
  simp [claimSummary, eval_exportPoly, eval_input, eval_affine]

/-- A handler that records each query: the round of a challenge, and `i + 1` for event `i`. The
challenges answer `2` and then `3`; events `2` and `3` answer `50` and `60`. -/
def record : QueryImpl Q (StateM (List ℕ))
  | .inl i => do modify (· ++ [i.val + 1]); pure (if i = 2 then 50 else 60 : ℕ)
  | .inr c => do
      modify (· ++ [RoundsTest.roundOf c])
      pure (cast (range_eq c).symm (if RoundsTest.roundOf c = 1 then 2 else 3 : K))

/-- The recorded run of the composite: the prover's output and the summary of the final claim,
with the recorded queries. -/
def observed (target : K) (hidden : ℕ) (bump : K) : ((ℕ × Option (K × K)) × List ℕ) :=
  (simulateQ record ((fun obs => (obs.2.1, obs.2.2.map claimSummary)) <$>
    (routed.run target (fun _ => input) (wholeProver hidden bump) : OracleComp Q _))).run []

/-- The summarised run: the prover's output and the summary of the composite verdict, after the
two draws and the two events. -/
theorem summary_routed (target : K) (hidden : ℕ) (bump : K) :
    ((fun obs => (obs.2.1, obs.2.2.map claimSummary)) <$>
      (routed.run target (fun _ => input) (wholeProver hidden bump) : OracleComp Q _)) = (do
      let r : K ← drawE (headNode 1)
      let tag ← eventE 2
      let s : K ← tailDraw drawE (headNode 0)
      let fin ← eventE 3
      pure (hidden + tag + fin,
        (routedVerdict target bump (fun _ => input) r s).map claimSummary)) := by
  erw [run_routed]
  refine (_root_.map_bind _ _ _).trans (bind_congr fun r => ?_)
  refine (_root_.map_bind _ _ _).trans (bind_congr fun tag => ?_)
  refine (_root_.map_bind _ _ _).trans (bind_congr fun s => ?_)
  refine (_root_.map_bind _ _ _).trans (bind_congr fun fin => ?_)
  exact LawfulApplicative.map_pure _ _

/-- Both rounds accept, and the claim `(10, 10)` holds of the exported polynomial. -/
theorem accepted (hidden : ℕ) : observed 4 hidden 0 =
    ((hidden + 110, some (10, 10)), [1, 3, 2, 4]) := by
  refine (congrArg (fun prog => (simulateQ record prog).run [])
    (summary_routed 4 hidden 0)).trans ?_
  simp only [routedVerdict_accepted, Option.map_some, claimSummary_accepted]
  rfl

/-- A wrong first sum rejects; both rounds still run. -/
theorem prefix_rejected (hidden : ℕ) : observed 0 hidden 0 =
    ((hidden + 110, none), [1, 3, 2, 4]) := by
  refine (congrArg (fun prog => (simulateQ record prog).run [])
    (summary_routed 0 hidden 0)).trans ?_
  simp only [routedVerdict_prefix, Option.map_none]
  rfl

/-- A bad second message rejects after its challenge and the prover's last event. -/
theorem suffix_rejected (hidden : ℕ) : observed 4 hidden 1 =
    ((hidden + 110, none), [1, 3, 2, 4]) := by
  refine (congrArg (fun prog => (simulateQ record prog).run [])
    (summary_routed 4 hidden 1)).trans ?_
  simp only [routedVerdict_suffix, Option.map_none]
  rfl

/-- Every claim the composite accepts lies in the final relation of the exported oracle. -/
theorem accepted_relation (r s : K)
    (claim : Spec.StatementRound K 1 (Fin.last 1) × ∀ i, Spec.OracleStatement K 1 1 i)
    (h : routedVerdict 4 0 (fun _ => input) r s = some claim) :
    ((claim.1, claim.2), ()) ∈ Spec.relationRound K 1 1 D₂ (Fin.last 1) := by
  rw [routedVerdict_accepted] at h
  cases h
  rw [Spec.relationRound_last_iff]
  change MvPolynomial.eval ![s] (exportPoly r input (affine 2 1)).val = s + (3 * r + 1)
  rw [eval_exportPoly, eval_input, eval_affine]
  simp
  ring

end

run_cmd
  for decl in [``Sumcheck.Core.RoutingTest.exportPoly, ``Sumcheck.Core.RoutingTest.eval_exportPoly,
      ``Sumcheck.Core.RoutingTest.exportMap, ``Sumcheck.Core.RoutingTest.firstVerifier,
      ``Sumcheck.Core.RoutingTest.compatible, ``Sumcheck.Core.RoutingTest.routed,
      ``Sumcheck.Core.RoutingTest.run_wholeProver, ``Sumcheck.Core.RoutingTest.checkVerdict_first,
      ``Sumcheck.Core.RoutingTest.compatible_output, ``Sumcheck.Core.RoutingTest.run_routed,
      ``Sumcheck.Core.RoutingTest.secondVerdict, ``Sumcheck.Core.RoutingTest.routedVerdict_accepted,
      ``Sumcheck.Core.RoutingTest.routedVerdict_prefix,
      ``Sumcheck.Core.RoutingTest.routedVerdict_suffix,
      ``Sumcheck.Core.RoutingTest.summary_routed, ``Sumcheck.Core.RoutingTest.accepted,
      ``Sumcheck.Core.RoutingTest.prefix_rejected, ``Sumcheck.Core.RoutingTest.suffix_rejected,
      ``Sumcheck.Core.RoutingTest.accepted_relation] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected axiom {ax} in {decl}"

end Sumcheck.Core.RoutingTest
