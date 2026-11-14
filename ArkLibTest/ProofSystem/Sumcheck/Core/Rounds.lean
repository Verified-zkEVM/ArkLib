/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLibTest.ProofSystem.Sumcheck.Core.RoundByRound

/-!
# Several Sumcheck rounds in the interaction layer

Honest runs of two and three rounds over `ZMod 17`: the challenges are drawn from the challenge
oracle once per round, in round order, and the verdict is the input polynomial evaluated at the
challenges, with the input polynomial as output oracle. With a wrong target every round still
runs and the verdict rejects. On the bilinear input `1 + 2 X₀ + 3 X₁ + 4 X₀ X₁` with the
challenges `3` and then `5`, the run makes exactly two challenge queries, in round order, and
accepts the claim `⟨14, ![3, 5]⟩` with the input polynomial as output oracle.
-/

namespace Sumcheck.Core.RoundsTest

open Polynomial PFunctor Interaction.Core Interaction.TwoParty.Lens Interaction.Oracle
  OracleComp OracleSpec ProtocolSpec
open scoped ENNReal NNReal

/-! ## Support -/

section Support

variable {R : Type} [CommSemiring R] {deg n : ℕ} {d : ℕ} (D : Fin d ↪ R)

/-- The final relation says that the input polynomial at the challenges is the target. -/
theorem relationLast_iff_eval (p : Spec.OracleStatement R n deg ()) (t : R) (ch : Fin n → R) :
    (((⟨t, ch⟩, fun _ => p), ()) ∈ Spec.relationRound R n deg D (Fin.last n)) ↔
      MvPolynomial.eval ch p.val = t := by
  have : IsEmpty (Fin (n - (Fin.last n : ℕ))) := ⟨fun i => by have := i.2; simp at this⟩
  have hch : ∀ x : Fin (n - (Fin.last n : ℕ)) → R,
      (Fin.append ch x ∘ Fin.cast (by simp)) = ch := fun x => by
    funext i
    simp [Fin.append, Fin.addCases, Fin.cast]
  simp [Spec.relationRound, hch]

/-- Drawing two challenges queries the two challenge nodes in round order. -/
theorem drawChallenges_two {m : Type → Type} [Monad m] [LawfulMonad m]
    (draw : (c : ChallengeNode oracleSig (protocol R deg 2)) → m (challengeSpec oracleSig _ c)) :
    drawChallenges 2 draw = (do
      let c₀ : R ← draw (headNode 1)
      let c₁ : R ← tailDraw draw (headNode 0)
      pure ![c₀, c₁]) := by
  simp only [drawChallenges]
  refine bind_congr fun c₀ => ?_
  erw [LawfulMonad.bind_assoc]
  refine bind_congr fun c₁ => ?_
  erw [LawfulMonad.pure_bind]
  exact (LawfulMonad.pure_bind _ _).trans (congrArg pure (funext fun i => by fin_cases i <;> rfl))

/-- Drawing three challenges queries the three challenge nodes in round order. -/
theorem drawChallenges_three {m : Type → Type} [Monad m] [LawfulMonad m]
    (draw : (c : ChallengeNode oracleSig (protocol R deg 3)) → m (challengeSpec oracleSig _ c)) :
    drawChallenges 3 draw = (do
      let c₀ : R ← draw (headNode 2)
      let c₁ : R ← tailDraw draw (headNode 1)
      let c₂ : R ← tailDraw (tailDraw draw) (headNode 0)
      pure ![c₀, c₁, c₂]) := by
  simp only [drawChallenges]
  refine bind_congr fun c₀ => ?_
  erw [LawfulMonad.bind_assoc]
  refine bind_congr fun c₁ => ?_
  erw [LawfulMonad.bind_assoc, LawfulMonad.bind_assoc]
  refine bind_congr fun c₂ => ?_
  erw [LawfulMonad.pure_bind, LawfulMonad.pure_bind]
  exact (LawfulMonad.pure_bind _ _).trans (congrArg pure (funext fun i => by fin_cases i <;> rfl))

variable [DecidableEq R] [SampleableType R] {ι : Type} (amb : OracleSpec ι)

/-- If the honest output records the drawn challenges, the honest run on a satisfied claim
accepts the input polynomial evaluated at the challenges, with the input polynomial as output
oracle. -/
theorem run_honest_eval (stmt : Spec.StatementRound R n 0) (p : Spec.OracleStatement R n deg ())
    (h : ((stmt, fun _ => p), ()) ∈ Spec.relationRound R n deg D 0)
    (hch : ∀ chals, (honestOutput D stmt (fun _ => p) chals).1.1.challenges = chals) :
    (verifier R deg n D amb).run stmt (fun _ => p) (honestProver D stmt fun _ => p) =
      (fun chals => (⟨honestTranscript D stmt (fun _ => p) chals,
        honestOutput D stmt (fun _ => p) chals,
        some (⟨MvPolynomial.eval chals p.val, chals⟩, fun _ => p)⟩ :
          Observation oracleSig (protocol R deg n) (fun _ => HonestOutput R deg n)
            (fun _ => Spec.StatementRound R n (Fin.last n) × ∀ i, Spec.OracleStatement R n deg i)))
              <$>
        drawChallenges n (fun c =>
          liftM ((amb + challengeSpec oracleSig (protocol R deg n)).query (.inr c))) := by
  rw [run_verifier_honestProver]
  refine congrArg (· <$> _) (funext fun chals => ?_)
  obtain ⟨hv, -, hrel⟩ := legacyVerdict_honestTranscript D amb stmt _ h chals
  rw [hv]
  generalize hout : (honestOutput D stmt (fun _ => p) chals).1 = out at hrel
  obtain ⟨⟨t, ch⟩, o⟩ := out
  have hc : ch = chals := (congrArg (·.1.challenges) hout).symm.trans (hch chals)
  have ho : o = fun _ => p := (congrArg Prod.snd hout).symm.trans
    (legacyVerdict_honestTranscript D amb stmt _ h chals).2.1
  subst hc ho
  have ht := (relationLast_iff_eval D p t ch).1 hrel
  rw [← ht]
  rfl

-- Migration rows: Sumcheck Interaction/Projection #8, ProjectionTransport #2.

/-- The first stage of the verifier's decision on an honest run: from the round-`0` relation, the
round-`0` check on the honest first message and any challenge accepts a statement in the
round-`1` relation, with the input polynomial unchanged. -/
theorem firstRound_relation {k : ℕ} (stmt : Spec.StatementRound R (k + 1) 0)
    (p : Spec.OracleStatement R (k + 1) deg ())
    (h : ((stmt, fun _ => p), ()) ∈ Spec.relationRound R (k + 1) deg D 0) (r : R) : ∃ t,
      simulateQ (OracleInterface.simOracle0 _
          (roundFullTranscript (honestMessage D k (initState stmt fun _ => p)) r).messages)
        (roundCheck R deg (k + 1) D amb 0 stmt
          (roundFullTranscript (honestMessage D k (initState stmt fun _ => p)) r).challenges).run =
        some t ∧
      ((t, fun _ => p), ()) ∈ Spec.relationRound R (k + 1) deg D (0 : Fin (k + 1)).succ := by
  obtain ⟨t, ht, -, -, -, hrel⟩ :=
    honestRel_step D amb p 0 k (initState stmt fun _ => p) stmt r ⟨rfl, HEq.rfl, rfl, h⟩
  exact ⟨t, ht, hrel⟩

end Support

/-! ## Fixtures over `ZMod 17` -/

noncomputable section

/-- Seventeen is prime. -/
instance : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- The field with seventeen elements. -/
abbrev K := ZMod 17

/-- An oracle-capable ambient context, unused by the honest prover. -/
abbrev ambient : OracleSpec Unit := Unit →ₒ Unit

/-- The domain `{0, 1}`. -/
def D₂ : Fin 2 ↪ K := ⟨fun i => (i.val : K), by decide⟩

/-- A coordinate polynomial has individual degree at most one. -/
theorem X_mem {n : ℕ} (i : Fin n) :
    (MvPolynomial.X i : MvPolynomial (Fin n) K) ∈ MvPolynomial.restrictDegree (Fin n) K 1 := by
  rw [MvPolynomial.mem_restrictDegree]
  intro s hs j
  rw [MvPolynomial.support_X, Finset.mem_singleton] at hs
  subst hs
  rw [Finsupp.single_apply]
  split_ifs <;> omega

/-- A constant polynomial has individual degree at most one. -/
theorem C_mem {n : ℕ} (b : K) :
    (MvPolynomial.C b : MvPolynomial (Fin n) K) ∈ MvPolynomial.restrictDegree (Fin n) K 1 := by
  rw [MvPolynomial.mem_restrictDegree]
  intro s hs j
  have hs' := MvPolynomial.support_C_subset hs
  rw [Finset.mem_singleton] at hs'
  simp [hs']

/-- The multilinear polynomial `∑ i, a i * X i + b`. -/
def linear {n : ℕ} (a : Fin n → K) (b : K) : Spec.OracleStatement K n 1 () :=
  ⟨∑ i, MvPolynomial.C (a i) * MvPolynomial.X i + MvPolynomial.C b,
    Submodule.add_mem _ (Submodule.sum_mem _ fun i _ => by
      rw [← MvPolynomial.smul_eq_C_mul]
      exact Submodule.smul_mem _ _ (X_mem i)) (C_mem b)⟩

/-- `X₀ + 2 X₁ + 4 X₂`, which sums to `28 = 11` over `{0, 1}³`. -/
abbrev p3 : Spec.OracleStatement K 3 1 () := linear ![1, 2, 4] 0

/-- `X₀ + 2 X₁ + 1`, which sums to `10` over `{0, 1}²`. -/
abbrev p2 : Spec.OracleStatement K 2 1 () := linear ![1, 2] 1

/-- The three-variable linear polynomial has sum eleven over the Boolean cube. -/
theorem relation_p3 : ((⟨11, Fin.elim0⟩, fun _ => p3), ()) ∈ Spec.relationRound K 3 1 D₂ 0 := by
  simpa [Spec.relationRound, linear, D₂, Fin.sum_univ_three] using (by decide :
    ∑ x ∈ Fintype.piFinset fun _ : Fin 3 => Finset.univ.map D₂, (x 0 + 2 * x 1 + 4 * x 2) = 11)

/-- The two-variable linear polynomial has sum ten over the Boolean square. -/
theorem relation_p2 : ((⟨10, Fin.elim0⟩, fun _ => p2), ()) ∈ Spec.relationRound K 2 1 D₂ 0 := by
  simpa [Spec.relationRound, linear, D₂, Fin.sum_univ_two] using (by decide :
    ∑ x ∈ Fintype.piFinset fun _ : Fin 2 => Finset.univ.map D₂, (x 0 + 2 * x 1 + 1) = 10)

/-- The three-variable linear polynomial evaluates to seven at the chosen challenges. -/
theorem eval_p3 : MvPolynomial.eval ![3, 5, 7] p3.val = 7 := by
  simpa [linear, Fin.sum_univ_three] using (by decide : (3 + 2 * 5 + 4 * 7 : K) = 7)

/-- The two-variable linear polynomial evaluates to fourteen at the chosen challenges. -/
theorem eval_p2 : MvPolynomial.eval ![3, 5] p2.val = 14 := by
  simpa [linear, Fin.sum_univ_two] using (by decide : (3 + 2 * 5 + 1 : K) = 14)

/-- The challenge requests of a run: one query to the challenge oracle per challenge node. -/
abbrev drawOf (n : ℕ) :=
  fun c : ChallengeNode oracleSig (protocol K 1 n) =>
    (liftM ((ambient + challengeSpec oracleSig (protocol K 1 n)).query (.inr c)) :
      OracleComp (ambient + challengeSpec oracleSig (protocol K 1 n)) _)

/-- The observation of a three-round run on the claim `t` about `p3`. -/
abbrev Obs (n : ℕ) :=
  Observation oracleSig (protocol K 1 n) (fun _ => HonestOutput K 1 n)
    (fun _ => Spec.StatementRound K n (Fin.last n) × ∀ i, Spec.OracleStatement K n 1 i)

/-! ## Three rounds -/

-- Migration rows: Sumcheck Interaction/ArbitraryRounds #2, #3, #5.

/-- Three honest rounds on the true claim that `p3` sums to `11`: the run queries the challenge
oracle at the first, second and third round's challenge node, in that order, and accepts `p3`
evaluated at the drawn challenges, with `p3` as output oracle. -/
theorem run_three :
    (verifier K 1 3 D₂ ambient).run ⟨11, Fin.elim0⟩ (fun _ => p3)
        (honestProver D₂ ⟨11, Fin.elim0⟩ fun _ => p3) =
      (fun chals => (⟨honestTranscript D₂ ⟨11, Fin.elim0⟩ (fun _ => p3) chals,
        honestOutput D₂ ⟨11, Fin.elim0⟩ (fun _ => p3) chals,
        some (⟨MvPolynomial.eval chals p3.val, chals⟩, fun _ => p3)⟩ : Obs 3)) <$> (do
          let c₀ : K ← drawOf 3 (headNode 2)
          let c₁ : K ← tailDraw (drawOf 3) (headNode 1)
          let c₂ : K ← tailDraw (tailDraw (drawOf 3)) (headNode 0)
          pure ![c₀, c₁, c₂]) := by
  rw [run_honest_eval D₂ ambient _ p3 relation_p3 fun chals => funext fun i => by
    fin_cases i <;> rfl]
  rw [drawChallenges_three]

/-- At the challenges `3, 5, 7` the verdict is the claim `⟨7, ![3, 5, 7]⟩` with output oracle
`p3`, and it lies in the final relation. -/
example : (some (⟨MvPolynomial.eval ![3, 5, 7] p3.val, ![3, 5, 7]⟩, fun _ => p3) :
      Option (Spec.StatementRound K 3 (Fin.last 3) × ∀ i, Spec.OracleStatement K 3 1 i)) =
      some (⟨7, ![3, 5, 7]⟩, fun _ => p3) ∧
    ((⟨7, ![3, 5, 7]⟩, fun _ => p3), ()) ∈ Spec.relationRound K 3 1 D₂ (Fin.last 3) :=
  ⟨by rw [eval_p3], (relationLast_iff_eval D₂ p3 7 ![3, 5, 7]).2 eval_p3⟩

-- Migration row: Sumcheck Interaction/ArbitraryRounds #4.

/-- On the wrong target `12` the first honest message sums to `11`, so the verdict rejects; the
run still queries the challenge oracle at all three challenge nodes, in round order. The decision
queries the round messages but never the ambient oracle (`decide_ambient_trace`). -/
theorem run_three_wrong :
    (verifier K 1 3 D₂ ambient).run ⟨12, Fin.elim0⟩ (fun _ => p3)
        (honestProver D₂ ⟨12, Fin.elim0⟩ fun _ => p3) =
      (fun chals => (⟨honestTranscript D₂ ⟨12, Fin.elim0⟩ (fun _ => p3) chals,
        honestOutput D₂ ⟨12, Fin.elim0⟩ (fun _ => p3) chals, none⟩ : Obs 3)) <$> (do
          let c₀ : K ← drawOf 3 (headNode 2)
          let c₁ : K ← tailDraw (drawOf 3) (headNode 1)
          let c₂ : K ← tailDraw (tailDraw (drawOf 3)) (headNode 0)
          pure ![c₀, c₁, c₂]) := by
  rw [run_verifier_honestProver, drawChallenges_three]
  refine congrArg (· <$> _) (funext fun chals => ?_)
  have hsum := (Spec.SingleRound.projected_sum_iff_relationRound K 3 1 D₂ 0 ⟨11, Fin.elim0⟩
    p3).2 relation_p3
  rw [Finset.sum_map_toList] at hsum
  change ∑ x ∈ Finset.univ.map D₂,
    (honestMessage D₂ 2 (initState ⟨11, Fin.elim0⟩ fun _ => p3)).val.eval x = 11 at hsum
  have hv : legacyVerdict K 1 3 D₂ ambient ⟨12, Fin.elim0⟩ (decodeTranscript 3
      (honestTranscript D₂ ⟨12, Fin.elim0⟩ (fun _ => p3) chals)) = none :=
    legacyVerdict_eq_none (k := 2) _ (roundFullTranscript _ (chals 0)) (legacyTranscript 2 _ _)
      (by
        change ∑ x ∈ Finset.univ.map D₂,
          (honestMessage D₂ 2 (initState ⟨11, Fin.elim0⟩ fun _ => p3)).val.eval x ≠ 12
        rw [hsum]
        decide)
  rw [hv]
  rfl

/-! ## Two rounds -/

-- Migration rows: Sumcheck Interaction/Sequential #2, #4.

/-- Two honest rounds on the true claim that `p2` sums to `10`: the run queries the challenge
oracle at the first and then the second round's challenge node, and accepts `p2` evaluated at the
drawn challenges, with `p2` as output oracle. -/
theorem run_two :
    (verifier K 1 2 D₂ ambient).run ⟨10, Fin.elim0⟩ (fun _ => p2)
        (honestProver D₂ ⟨10, Fin.elim0⟩ fun _ => p2) =
      (fun chals => (⟨honestTranscript D₂ ⟨10, Fin.elim0⟩ (fun _ => p2) chals,
        honestOutput D₂ ⟨10, Fin.elim0⟩ (fun _ => p2) chals,
        some (⟨MvPolynomial.eval chals p2.val, chals⟩, fun _ => p2)⟩ : Obs 2)) <$> (do
          let c₀ : K ← drawOf 2 (headNode 1)
          let c₁ : K ← tailDraw (drawOf 2) (headNode 0)
          pure ![c₀, c₁]) := by
  rw [run_honest_eval D₂ ambient _ p2 relation_p2 fun chals => funext fun i => by
    fin_cases i <;> rfl]
  rw [drawChallenges_two]

/-- At the challenges `3, 5` the verdict is the claim `⟨14, ![3, 5]⟩` with output oracle `p2`. -/
example : (some (⟨MvPolynomial.eval ![3, 5] p2.val, ![3, 5]⟩, fun _ => p2) :
      Option (Spec.StatementRound K 2 (Fin.last 2) × ∀ i, Spec.OracleStatement K 2 1 i)) =
      some (⟨14, ![3, 5]⟩, fun _ => p2) ∧
    ((⟨14, ![3, 5]⟩, fun _ => p2), ()) ∈ Spec.relationRound K 2 1 D₂ (Fin.last 2) :=
  ⟨by rw [eval_p2], (relationLast_iff_eval D₂ p2 14 ![3, 5]).2 eval_p2⟩

/-! ## Two rounds on a bilinear input -/

-- Migration rows: Sumcheck Interaction/Projection #7 (first-round relation), #8,
-- ProjectionTransport #2; Sequential #2, #4.

/-- The product of the two coordinates has individual degree at most one. -/
theorem XX_mem : (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) K) ∈
    MvPolynomial.restrictDegree (Fin 2) K 1 := by
  have h : (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) K) =
      MvPolynomial.monomial (Finsupp.single 0 1 + Finsupp.single 1 1) 1 := by
    simp [MvPolynomial.X]
  rw [h, MvPolynomial.mem_restrictDegree]
  intro s hs j
  rw [Finset.mem_singleton.1 (MvPolynomial.support_monomial_subset hs)]
  fin_cases j <;> simp

/-- The bilinear polynomial `1 + 2 X₀ + 3 X₁ + 4 X₀ X₁`, which sums to `1` over `{0, 1}²`. -/
def bilinear : Spec.OracleStatement K 2 1 () :=
  ⟨MvPolynomial.C 1 + MvPolynomial.C 2 * MvPolynomial.X 0 + MvPolynomial.C 3 * MvPolynomial.X 1 +
      MvPolynomial.C 4 * (MvPolynomial.X 0 * MvPolynomial.X 1), by
    simp only [MvPolynomial.C_mul']
    exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (C_mem 1)
      (Submodule.smul_mem _ _ (X_mem 0))) (Submodule.smul_mem _ _ (X_mem 1)))
      (Submodule.smul_mem _ _ XX_mem)⟩

/-- The bilinear polynomial satisfies its sum claim over the Boolean square. -/
theorem bilinear_relation :
    ((⟨1, Fin.elim0⟩, fun _ => bilinear), ()) ∈ Spec.relationRound K 2 1 D₂ 0 := by
  simpa [Spec.relationRound, bilinear, D₂, Fin.sum_univ_two] using (by decide :
    ∑ x ∈ Fintype.piFinset fun _ : Fin 2 => Finset.univ.map D₂,
      (1 + 2 * x 0 + 3 * x 1 + 4 * (x 0 * x 1)) = 1)

-- Migration rows: Sumcheck Interaction/Projection #1, #2, #4, #5, #6, ProjectionTransport #1;
-- Sequential #1, #3.

/-- The domain `{0, 1}` as a finite set. -/
theorem domain_points : Finset.univ.map D₂ = {0, 1} := by decide

/-- The one-coordinate suffixes over `{0, 1}`. -/
theorem suffix_points :
    Fintype.piFinset (fun _ : Fin 1 => Finset.univ.map D₂) = {![0], ![1]} := by decide

/-- The honest first message on `bilinear`. -/
abbrev firstMsg : K⦃≤ 1⦄[X] := honestMessage D₂ 1 (initState ⟨1, Fin.elim0⟩ fun _ => bilinear)

/-- The honest first message is `5 + 8 X`: `bilinear` with the second variable summed out. -/
theorem projected_eval (x : K) : firstMsg.val.eval x = 5 + 8 * x :=
  (Spec.SingleRound.relationRound_output_iff K 2 1 D₂ 0 ⟨1, Fin.elim0⟩ bilinear x
    (5 + 8 * x)).1 (by
      change ∑ y ∈ Fintype.piFinset fun _ : Fin 1 => Finset.univ.map D₂, _ = _
      rw [suffix_points, Finset.sum_pair (by decide)]
      simp [bilinear, Fin.append, Fin.addCases, Fin.snoc]
      ring)

/-- The honest first message passes the round-`0` sum check. -/
theorem projected_sum : ∑ x ∈ Finset.univ.map D₂, firstMsg.val.eval x = 1 := by
  rw [domain_points, Finset.sum_pair (by decide), projected_eval, projected_eval]
  decide

/-- The honest second message on `bilinear` after the first challenge `c`. -/
abbrev secondMsg (c : K) : K⦃≤ 1⦄[X] :=
  honestMessage D₂ 0
    (nextState (honestMessage D₂) 1 (initState ⟨1, Fin.elim0⟩ fun _ => bilinear) c)

/-- The honest second message is `bilinear` with the first variable fixed to `c`. -/
theorem second_eval (c x : K) : (secondMsg c).val.eval x = 1 + 2 * c + 3 * x + 4 * c * x :=
  (Spec.SingleRound.relationRound_output_iff K 2 1 D₂ 1
    ⟨firstMsg.val.eval c, Fin.snoc Fin.elim0 c⟩ bilinear x (1 + 2 * c + 3 * x + 4 * c * x)).1 (by
      refine (relationLast_iff_eval D₂ bilinear _ _).2 ?_
      simp [bilinear, Fin.snoc]
      ring)

/-- At every first challenge `c`, the honest second message sums to the first message at `c`. -/
theorem second_sum (c : K) :
    ∑ x ∈ Finset.univ.map D₂, (secondMsg c).val.eval x = firstMsg.val.eval c := by
  rw [domain_points, Finset.sum_pair (by decide), second_eval, second_eval, projected_eval]
  ring

/-- The honest first message on the bilinear input at the challenge `3`: the round-`0` check
accepts the claim `⟨12, ![3]⟩`, and that claim with the unchanged input is in the round-`1`
relation. -/
example : ∃ t, simulateQ (OracleInterface.simOracle0 _ (roundFullTranscript
        (honestMessage D₂ 1 (initState ⟨1, Fin.elim0⟩ fun _ => bilinear)) 3).messages)
      (roundCheck K 1 2 D₂ ambient 0 ⟨1, Fin.elim0⟩ (roundFullTranscript
        (honestMessage D₂ 1 (initState ⟨1, Fin.elim0⟩ fun _ => bilinear)) 3).challenges).run =
        some t ∧ t = ⟨12, ![3]⟩ ∧
      ((t, fun _ => bilinear), ()) ∈ Spec.relationRound K 2 1 D₂ 1 := by
  obtain ⟨t, ht, hrel⟩ := firstRound_relation D₂ ambient ⟨1, Fin.elim0⟩ bilinear
    bilinear_relation 3
  refine ⟨t, ht, ?_, hrel⟩
  have hsum := Spec.SingleRound.projected_sum_of_relationRound K 2 1 D₂ 0 ⟨1, Fin.elim0⟩ bilinear
    bilinear_relation
  rw [Finset.sum_map_toList] at hsum
  rw [roundCheck_eq_some 0 _ _ hsum] at ht
  cases Option.some.inj ht
  have key (m : K) (hm : (((⟨m, Fin.snoc (Fin.elim0 : Fin 0 → K) 3⟩ :
      Spec.StatementRound K 2 (Fin.succ 0)), fun _ => bilinear), ()) ∈
        Spec.relationRound K 2 1 D₂ (Fin.succ 0)) : m = 12 := by
    have h12 : ∑ x ∈ Fintype.piFinset fun _ : Fin 1 => Finset.univ.map D₂,
        (1 + 2 * (Fin.snoc (Fin.elim0 : Fin 0 → K) 3 : Fin 1 → K) 0 +
          3 * Fin.append (Fin.snoc (Fin.elim0 : Fin 0 → K) 3 : Fin 1 → K) x 1 +
          4 * ((Fin.snoc (Fin.elim0 : Fin 0 → K) 3 : Fin 1 → K) 0 *
            Fin.append (Fin.snoc (Fin.elim0 : Fin 0 → K) 3 : Fin 1 → K) x 1)) = 12 := by
      decide
    rw [← h12]
    simpa [Spec.relationRound, bilinear, D₂] using hm.symm
  have h12 : (honestMessage D₂ 1 (initState ⟨1, Fin.elim0⟩ fun _ => bilinear)).val.eval 3 = 12 :=
    key _ hrel
  change (⟨(honestMessage D₂ 1 (initState ⟨1, Fin.elim0⟩ fun _ => bilinear)).val.eval 3,
    Fin.snoc (Fin.elim0 : Fin 0 → K) 3⟩ : Spec.StatementRound K 2 (Fin.succ 0)) = _
  rw [h12]
  congr 1
  exact funext fun i => by fin_cases i; rfl

/-- The bilinear polynomial evaluates to fourteen at the chosen challenges. -/
theorem eval_bilinear : MvPolynomial.eval ![3, 5] bilinear.val = 14 := by
  simpa [bilinear] using (by decide : (1 + 2 * 3 + 3 * 5 + 4 * (3 * 5) : K) = 14)

/-- Two honest rounds on the claim that `bilinear` sums to `1`: the run queries the challenge
oracle at the first and then the second round's challenge node, and accepts `bilinear` evaluated
at the drawn challenges, with `bilinear` as output oracle. -/
theorem run_two_bilinear :
    (verifier K 1 2 D₂ ambient).run ⟨1, Fin.elim0⟩ (fun _ => bilinear)
        (honestProver D₂ ⟨1, Fin.elim0⟩ fun _ => bilinear) =
      (fun chals => (⟨honestTranscript D₂ ⟨1, Fin.elim0⟩ (fun _ => bilinear) chals,
        honestOutput D₂ ⟨1, Fin.elim0⟩ (fun _ => bilinear) chals,
        some (⟨MvPolynomial.eval chals bilinear.val, chals⟩, fun _ => bilinear)⟩ : Obs 2)) <$> (do
          let c₀ : K ← drawOf 2 (headNode 1)
          let c₁ : K ← tailDraw (drawOf 2) (headNode 0)
          pure ![c₀, c₁]) := by
  rw [run_honest_eval D₂ ambient _ bilinear bilinear_relation fun chals => funext fun i => by
    fin_cases i <;> rfl]
  rw [drawChallenges_two]

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

/-- The round of a challenge node: `1` for the first round's node, `2` for the second's. -/
def roundOf : ChallengeNode oracleSig (protocol K 1 2) → ℕ
  | ⟨.inr ⟨_, .inl _⟩, _⟩ => 1
  | _ => 2

/-- A handler that records the round of each challenge node it is asked for and answers `3` in
the first round and `5` in the second. The ambient oracle is never queried. -/
def recordChallenges :
    QueryImpl (ambient + challengeSpec oracleSig (protocol K 1 2)) (StateM (List ℕ))
  | .inl _ => pure ()
  | .inr c => do
      modify (· ++ [roundOf c])
      pure (cast (range_eq c).symm (if roundOf c = 1 then 3 else 5 : K))

/-- With the challenges `3` and then `5`, the run makes exactly two challenge queries, at the first
round's node and then at the second's, and accepts the claim `⟨14, ![3, 5]⟩` with `bilinear` as
output oracle. -/
example : (simulateQ recordChallenges ((fun obs => obs.2.2) <$>
    (verifier K 1 2 D₂ ambient).run ⟨1, Fin.elim0⟩ (fun _ => bilinear)
      (honestProver D₂ ⟨1, Fin.elim0⟩ fun _ => bilinear))).run [] =
      (some (⟨14, ![3, 5]⟩, fun _ => bilinear), [1, 2]) := by
  rw [run_two_bilinear, ← eval_bilinear]
  rfl

/-- The accepted claim `⟨14, ![3, 5]⟩` lies in the final relation. -/
example : ((⟨14, ![3, 5]⟩, fun _ => bilinear), ()) ∈
    Spec.relationRound K 2 1 D₂ (Fin.last 2) :=
  (relationLast_iff_eval D₂ bilinear 14 ![3, 5]).2 eval_bilinear

end

run_cmd
  for decl in [``Sumcheck.Core.RoundsTest.run_honest_eval, ``Sumcheck.Core.RoundsTest.run_three,
      ``Sumcheck.Core.RoundsTest.run_three_wrong, ``Sumcheck.Core.RoundsTest.run_two,
      ``Sumcheck.Core.RoundsTest.firstRound_relation,
      ``Sumcheck.Core.RoundsTest.run_two_bilinear, ``Sumcheck.Core.RoundsTest.range_eq,
      ``Sumcheck.Core.RoundsTest.relationLast_iff_eval, ``Sumcheck.Core.RoundsTest.bilinear,
      ``Sumcheck.Core.RoundsTest.bilinear_relation, ``Sumcheck.Core.RoundsTest.domain_points,
      ``Sumcheck.Core.RoundsTest.suffix_points, ``Sumcheck.Core.RoundsTest.projected_eval,
      ``Sumcheck.Core.RoundsTest.projected_sum, ``Sumcheck.Core.RoundsTest.second_eval,
      ``Sumcheck.Core.RoundsTest.second_sum] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected axiom {ax} in {decl}"

end Sumcheck.Core.RoundsTest
