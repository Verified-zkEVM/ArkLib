/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Core.Interval
public import ArkLib.Interaction.Core.Security.Implications

/-! # Sumcheck verification over indexed domains

Every occurrence of a domain point contributes to the sum, including repeated points.
-/

@[expose] public section

namespace Sumcheck.Core
open scoped ENNReal NNReal
open Polynomial MvPolynomial PFunctor FreeM Interaction.Core Interaction.TwoParty.Lens
  Interaction.Oracle
  OracleComp OracleSpec

variable {R : Type} [CommSemiring R] {deg n d : ℕ}

/-- The public claim with `k` rounds remaining in a full run: an interval claim that ends at the
last round. -/
abbrev IndexedClaim (R : Type) (n k : ℕ) := IntervalClaim R n (Fin.last n) k

/-- The initial claim has an empty challenge prefix. -/
def IndexedClaim.initial (stmt : RoundStatement R n 0) : IndexedClaim R n n :=
  ⟨0, Nat.zero_add n, stmt⟩

variable [DecidableEq R] (D : Fin d → R)

/-- The public update rejects a failed indexed sum check. -/
noncomputable def indexedNext {k : ℕ} (st : Option (IndexedClaim R n (k + 1)))
    (msg : R⦃≤ deg⦄[X]) (r : R) : Option (IndexedClaim R n k) :=
  st.bind fun st => if (∑ a : Fin d, msg.val.eval (D a)) = st.statement.target then
    some (st.next (msg.val.eval r) r) else none

/-- The verdict obtained by checking every round of a completed transcript: the interval verdict
to the last round, after a possible earlier rejection. -/
noncomputable def indexedVerdict (k : ℕ) (st : Option (IndexedClaim R n k))
    (tr : PathAlong oracleSig (protocol R deg k)) : Option (RoundStatement R n (Fin.last n)) :=
  st.bind fun st => intervalVerdict D k st tr

/-- Query the sent messages through the interval checks, after a possible earlier rejection. -/
def indexedDecision (k : ℕ) : Option (IndexedClaim R n k) →
    (p : Path (protocol R deg k)) → View (protocol R deg k) p →
    OracleComp (oracles (protocol R deg k) p) (Option (RoundStatement R n (Fin.last n)))
  | none, _, _ => pure none
  | some st, p, v => foldDecision (intervalCheck D) IntervalClaim.finish k st p v

/-- Lift the round-message queries into the verifier's final resource interface. -/
def indexedDecisionLift {ι : Type} (ambient : OracleSpec ι) (p : Path (protocol R deg n)) :
    QueryImpl (oracles (protocol R deg n) p)
      (OracleComp (ambient +
        (pathResources (polynomialFamily R n deg) (protocol R deg n) p).spec)) :=
  pathLift ambient (polynomialFamily R n deg) p

omit [DecidableEq R] in
/-- Answering the lifted message queries is a pure computation of the transcript payloads. -/
theorem simulateQ_indexedDecisionLift_monad {ι : Type} {ambient : OracleSpec ι}
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (impl : QueryImpl ambient m) (p : Path (protocol R deg n))
    (data : ∀ i, PolynomialData R n deg i) (pl : ∀ i, OracleData (protocol R deg n) p i)
    {α : Type} (oa : OracleComp (oracles (protocol R deg n) p) α) :
    simulateQ (QueryImpl.addLift impl ((pathResources (polynomialFamily R n deg) (protocol R deg n)
      p).answer (data, pl))) (simulateQ (indexedDecisionLift ambient p) oa) =
      (pure (simulateQ ((pathFamily (protocol R deg n) p).behaviorOfRealizations pl) oa) :
        m α) :=
  simulateQ_pathLift impl p data pl oa

/-- The passive Sumcheck verifier counts all domain indices in its final decision. -/
def indexedVerifier (R : Type) [CommSemiring R] [DecidableEq R] (deg n : ℕ)
    {d : ℕ} (D : Fin d → R) {ι : Type} (ambient : OracleSpec ι) :
    OracleVerifier ambient (protocol R deg n) (RoundStatement R n 0)
      (fun _ => RoundStatement R n (Fin.last n)) (polynomialFamily R n deg)
      (fun _ => polynomialFamily R n deg) where
  decide stmt p v := OptionT.mk (simulateQ (indexedDecisionLift ambient p)
    (indexedDecision D n (some (IndexedClaim.initial stmt)) p v))
  outputMap _ _ _ := OracleMap.fst _ _

/-- A rejected prefix stays rejected through every remaining round. -/
@[simp] theorem indexedVerdict_none : ∀ (k : ℕ)
    (tr : PathAlong oracleSig (protocol R deg k)), indexedVerdict (n := n) D k none tr = none :=
  fun _ _ => rfl

/-- One more round applies the public update to the head message and challenge. -/
theorem indexedVerdict_succ (k : ℕ) (st : Option (IndexedClaim R n (k + 1)))
    (tr : PathAlong oracleSig (protocol R deg (k + 1))) :
    indexedVerdict D (k + 1) st tr = indexedVerdict D k
      (indexedNext D st (Interpreted.message tr) (Interpreted.challenge tr))
      (Interpreted.tail tr) := by
  cases st with
  | none => rfl
  | some st =>
    change foldVerdict (intervalCheck D) IntervalClaim.finish (k + 1) st tr = _
    rw [foldVerdict_succ, roundVerdict_intervalCheck]
    unfold indexedNext
    dsimp only [Option.bind_some]
    split <;> rfl

/-- Answering the indexed decision from a transcript computes the indexed verdict. -/
theorem simulateQ_indexedDecision (k : ℕ) (st : Option (IndexedClaim R n k))
    (tr : PathAlong oracleSig (protocol R deg k)) :
    simulateQ (payloadImpl (protocol R deg k) tr)
      (indexedDecision D k st _ (toView _ tr)) = indexedVerdict D k st tr := by
  cases st with
  | none => rfl
  | some st => exact Interpreted.simulate_decision _ _ k st tr

omit [DecidableEq R] in
/-- A false current sum can become a true successor sum only at an agreement point of two
unequal degree-bounded polynomials. Repeated domain points retain their multiplicities. -/
theorem indexed_round_soundness [IsDomain R] [Fintype R] [SampleableType R]
    (i : Fin n) (stmt : RoundStatement R n i.castSucc)
    (p : R⦃≤ deg⦄[X Fin n]) (q : R⦃≤ deg⦄[X])
    (hfalse : ¬ indexedRelation D i.castSucc stmt p) :
    Pr{let r ← $ᵗ R}[(∑ a : Fin d, q.val.eval (D a)) = stmt.target ∧
      indexedRelation D i.succ ⟨q.val.eval r, Fin.snoc stmt.challenges r⟩ p] ≤
        (((deg : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞) := by
  classical
  by_cases hsum : (∑ a : Fin d, q.val.eval (D a)) = stmt.target
  · let honest := projectedRoundPolynomial D i stmt.challenges p
    have hne : ∃ a : Fin d, honest.val.eval (D a) ≠ q.val.eval (D a) := by
      by_contra! h
      apply hfalse
      change roundSum D i.castSucc stmt.challenges p.val = stmt.target
      rw [← sum_projectedRoundPolynomial D i stmt.challenges p]
      exact (Finset.sum_congr rfl (fun a _ => h a)).trans hsum
    obtain ⟨a, ha⟩ := hne
    have bound := Probability.prob_agreement_of_sum_ne ({D a}) honest q (by simpa using ha)
    simpa only [hsum, true_and, indexedRelation, roundSum_succ] using bound
  · simp [hsum]


section Prefix

variable {State : ℕ → Type}
  (Good : (k : ℕ) → State k → Prop)
  (next : (k : ℕ) → State (k + 1) → R⦃≤ deg⦄[X] → R → State k)

/-- The current truth predicate after interpreting every completed round in a full prefix. -/
def foldPrefix : (k : ℕ) → State k → {t : OracleProtocol} →
    (sp : Cursor.Spine (protocol R deg k) t) → PrefixMoves oracleSig sp → Prop
  | 0, st, _, sp, _ => by
      change Cursor.Spine (P := OraclePoly) (.pure PUnit.unit) _ at sp
      cases sp
      exact Good 0 st
  | k + 1, st, _, sp, history => by
      change Cursor.Spine (P := OraclePoly) (.liftBind (.oracle (R⦃≤ deg⦄[X]) inferInstance)
        (fun _ => .liftBind (.challenge R) (fun _ => protocol R deg k))) _ at sp
      cases sp with
      | root => exact Good (k + 1) st
      | down b tail =>
        cases b
        cases tail with
        | root => exact Good (k + 1) st
        | down b tail =>
          exact foldPrefix k (next k st history.1.val history.2.1.val) tail history.2.2

omit [DecidableEq R] in
/-- Sending a message does not change the current truth predicate. -/
theorem foldPrefix_send : ∀ (k : ℕ) (st : State k) {a : OraclePos}
    {rest : OraclePoly.B a → OracleProtocol} (sp : Cursor.Spine (protocol R deg k) (.liftBind a
      rest))
    (history : PrefixMoves oracleSig sp) (_h : owner oracleSig a = .sender)
    (x : Move oracleSig a),
    foldPrefix Good next k st
      (sp.comp (.down (oracleSig.toFunB a x) (.root _)))
      (PrefixMoves.snoc oracleSig sp history x) = foldPrefix Good next k st sp history := by
  intro k
  induction k with
  | zero => intro st a rest sp; cases sp
  | succ k ih =>
      intro st a rest sp history h x
      cases sp with
      | root => rfl
      | down b tail =>
        cases tail with
        | root => cases h
        | down b tail =>
          exact ih _ tail history.2.2 h x

end Prefix

/-- An unrejected current claim is true when its remaining indexed sum equals its target. -/
noncomputable def indexedGood (p : R⦃≤ deg⦄[X Fin n]) (k : ℕ)
    (st : Option (IndexedClaim R n k)) : Prop :=
  ∃ current, st = some current ∧ indexedRelation D current.round current.statement p

omit [DecidableEq R] in
/-- At the final round, truth of the current claim is exactly valid evaluation acceptance. -/
theorem indexedGood_zero (p : R⦃≤ deg⦄[X Fin n]) (st : Option (IndexedClaim R n 0)) :
    indexedGood D p 0 st ↔ ∃ t, st.map IntervalClaim.finish = some t ∧
      p.val.eval t.challenges = t.target := by
  cases st with
  | none => simp [indexedGood]
  | some st =>
    rcases st with ⟨round, ha, stmt⟩
    have heq : round = Fin.last n := Fin.ext (by simpa using ha)
    subst round
    simp [indexedGood, IntervalClaim.finish, indexedRelation_last]

/-- Truth at a terminal prefix is the indexed verdict's final evaluation claim. -/
theorem foldPrefix_indexed_leaf (p : R⦃≤ deg⦄[X Fin n]) :
    ∀ (k : ℕ) (st : Option (IndexedClaim R n k))
      (sp : Cursor.Spine (protocol R deg k) (.pure PUnit.unit))
      (history : PrefixMoves oracleSig sp),
    foldPrefix (indexedGood D p) (fun _ => indexedNext D) k st sp history ↔
      ∃ t, indexedVerdict D k st (PrefixMoves.complete oracleSig sp history) = some t ∧
        p.val.eval t.challenges = t.target := by
  intro k
  induction k with
  | zero =>
    intro st sp history
    change Cursor.Spine (P := OraclePoly) (.pure PUnit.unit) _ at sp
    cases sp
    cases st <;> exact indexedGood_zero D p _
  | succ k ih =>
    intro st sp history
    change Cursor.Spine (P := OraclePoly) (.liftBind (.oracle (R⦃≤ deg⦄[X]) inferInstance)
      (fun _ => .liftBind (.challenge R) (fun _ => protocol R deg k))) _ at sp
    cases sp with
    | down b tail =>
      cases b
      cases tail with
      | down b tail =>
        rw [indexedVerdict_succ]
        exact ih _ tail history.2.2

/-- An incorrect remaining claim becomes correct with probability at most `deg / |R|`. -/
theorem indexedGood_flip_le [IsDomain R] [Fintype R] [SampleableType R]
    (p : R⦃≤ deg⦄[X Fin n]) {k : ℕ} (st : Option (IndexedClaim R n (k + 1)))
    (msg : R⦃≤ deg⦄[X]) :
    Pr{let r ← $ᵗ R}[¬ indexedGood D p (k + 1) st ∧
      indexedGood D p k (indexedNext D st msg r)] ≤
        (((deg : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞) := by
  classical
  cases st with
  | none => simp [indexedGood, indexedNext]
  | some st =>
    by_cases ht : indexedRelation D st.round st.statement p
    · simp [indexedGood, ht]
    · have bound := indexed_round_soundness D st.index st.statement p msg ht
      by_cases hs : (∑ a : Fin d, msg.val.eval (D a)) = st.statement.target
      · have hevent : (fun r => ¬ indexedGood D p (k + 1) (some st) ∧
            indexedGood D p k (indexedNext D (some st) msg r)) =
            (fun r => (∑ a : Fin d, msg.val.eval (D a)) = st.statement.target ∧
              indexedRelation D st.index.succ
                ⟨msg.val.eval r, Fin.snoc st.statement.challenges r⟩ p) := by
          funext r
          simp [indexedGood, indexedNext, hs, ht, IntervalClaim.next]
        rw [hevent]
        exact bound
      · simp [indexedGood, indexedNext, hs]

/-- Uniform challenges for the indexed verifier use the protocol's canonical sampler. -/
def indexedDraw [SampleableType R] (k : ℕ) :
    QueryImpl (challengeSpec oracleSig (protocol R deg k)) ProbComp :=
  @challengeQueryImpl _ oracleSig (protocol R deg k) (challengeSampleable R deg k)

omit [DecidableEq R] in
/-- Sampling at a receiver in the remaining rounds is independent of earlier shape nodes. -/
theorem indexed_sampleAt_tail [SampleableType R] {k : ℕ} {a : OraclePos}
    {rest : OraclePoly.B a → OracleProtocol}
    (sp : Cursor.Spine (protocol R deg k) (.liftBind a rest))
    (h : owner oracleSig a = .receiver) :
    sampleAt oracleSig (indexedDraw (R := R) (deg := deg) (k + 1))
        (.down ⟨⟩ (.down ⟨⟩ sp)) h =
      sampleAt oracleSig (indexedDraw (R := R) (deg := deg) k) sp h := rfl

/-- Every receiver prefix satisfies the indexed Sumcheck flip bound. -/
theorem foldPrefix_indexed_flip_le [IsDomain R] [Fintype R] [SampleableType R]
    (p : R⦃≤ deg⦄[X Fin n]) :
    ∀ (k : ℕ) (st : Option (IndexedClaim R n k)) {a : OraclePos}
      {rest : OraclePoly.B a → OracleProtocol}
      (sp : Cursor.Spine (protocol R deg k) (.liftBind a rest))
      (h : owner oracleSig a = .receiver) (history : PrefixMoves oracleSig sp),
      letI : MeasurableSpace (Move oracleSig a) := ⊤
      𝒟[sampleAt oracleSig (indexedDraw (R := R) (deg := deg) k) sp h]
        {x | ¬ foldPrefix (indexedGood D p) (fun _ => indexedNext D) k st sp history ∧
          foldPrefix (indexedGood D p) (fun _ => indexedNext D) k st
            (sp.comp (.down (oracleSig.toFunB a x) (.root _)))
            (PrefixMoves.snoc oracleSig sp history x)} ≤
          (((deg : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞) := by
  intro k
  induction k with
  | zero => intro st a rest sp; cases sp
  | succ k ih =>
    intro st a rest sp h history
    cases sp with
    | root => cases h
    | down b tail =>
      cases b
      cases tail with
      | root =>
        have hs : sampleAt oracleSig
            (indexedDraw (R := R) (deg := deg) (k + 1))
            (.down ⟨⟩ (.root _)) h = ($ᵗ R) := by
          exact LawfulFunctor.id_map _
        rw [hs]
        let : MeasurableSpace (Move oracleSig (.challenge R)) := ⊤
        rw [← prEvent_eq_evalDist_of_discrete]
        change Pr{let x ← $ᵗ R}[¬ indexedGood D p (k + 1) st ∧
          foldPrefix (indexedGood D p) (fun _ => indexedNext D) k
            (indexedNext D st history.1.val x) (.root (protocol R deg k)) (PUnit.unit)] ≤ _
        cases k with
        | zero => exact indexedGood_flip_le D p st history.1.val
        | succ k => exact indexedGood_flip_le D p st history.1.val
      | down b tail =>
        cases b
        rw [indexed_sampleAt_tail]
        exact ih _ tail h history.2.2

/-- Resource answers make the indexed verifier's final decision a pure indexed verdict. -/
theorem simulateQ_indexedVerifier_decide {ι : Type} {ambient : OracleSpec ι}
    {m : Type → Type} [Monad m] [LawfulMonad m] (impl : QueryImpl ambient m)
    (stmt : RoundStatement R n 0) (data : ∀ i, PolynomialData R n deg i)
    (tr : PathAlong oracleSig (protocol R deg n)) :
    simulateQ (QueryImpl.addLift impl ((pathResources (polynomialFamily R n deg) (protocol R deg n)
      (projectPathAlong oracleSig _ tr)).answer (data, payloads _ tr)))
      ((indexedVerifier R deg n D ambient).decide stmt _ (toView _ tr)).run =
      (pure (indexedVerdict D n (some (IndexedClaim.initial stmt)) tr) : m _) := by
  change simulateQ _ (simulateQ (indexedDecisionLift ambient _) _) = _
  rw [simulateQ_indexedDecisionLift_monad]
  exact congrArg pure (simulateQ_indexedDecision D n _ tr)

/-- The actual core run records its transcript and applies the indexed verdict to its payloads. -/
theorem indexedVerifier_run {ι : Type} (ambient : OracleSpec ι)
    (stmt : RoundStatement R n 0) (data : ∀ i, PolynomialData R n deg i)
    {Out : PathAlong oracleSig (protocol R deg n) → Type}
    (prover : Prover oracleSig ambient (protocol R deg n) Out) :
    (indexedVerifier R deg n D ambient).run stmt data prover = (do
      let ⟨tr, out, _⟩ ← Interaction.TwoParty.Lens.run (protocol R deg n)
        (prover.simulate (fun q =>
          liftM ((ambient + challengeSpec oracleSig (protocol R deg n)).query (.inl q))))
        (sampler oracleSig (protocol R deg n) (fun c =>
          liftM ((ambient + challengeSpec oracleSig (protocol R deg n)).query (.inr c))))
      pure ⟨tr, out, (indexedVerdict D n (some (IndexedClaim.initial stmt)) tr).map
        (fun t => (t, data))⟩) := by
  rw [OracleVerifier.run_eq]
  refine bind_congr fun result => ?_
  rcases result with ⟨tr, out, u⟩
  dsimp only
  rw [simulateQ_indexedVerifier_decide]
  simp only [LawfulMonad.pure_bind]
  rfl

omit [DecidableEq R] in
/-- Sum the first message's query answers in the supplied list order. -/
def indexedSumQueries {k : ℕ} (domain : List R) (p : Path (protocol R deg (k + 1))) :
    OracleComp (oracles (protocol R deg (k + 1)) p) R := do
  let values ← domain.mapM (Interpreted.headQuery p)
  pure values.sum

omit [DecidableEq R] in
/-- Interpreting the scalar sum fragment computes the list sum, without equality decisions. -/
theorem simulateQ_indexedSumQueries {k : ℕ} (domain : List R)
    (tr : PathAlong oracleSig (protocol R deg (k + 1))) :
    simulateQ (payloadImpl (protocol R deg (k + 1)) tr)
      (indexedSumQueries domain (projectPathAlong oracleSig _ tr)) =
      (domain.map (fun x => (Interpreted.message tr).val.eval x)).sum := by
  rcases tr with ⟨msg, r, tail⟩
  unfold indexedSumQueries
  rw [simulateQ_bind, simulateQ_list_mapM]
  change ((domain.mapM (fun x => (pure (msg.val.eval x) : Id R))) >>= fun values =>
    pure values.sum) = _
  simp only [List.mapM_pure, LawfulMonad.pure_bind]
  rfl

omit [DecidableEq R] in
/-- The scalar sum fragment has the same pure interpretation in every lawful target monad. -/
theorem simulateQ_indexedSumQueries_monad {k : ℕ} (domain : List R)
    (tr : PathAlong oracleSig (protocol R deg (k + 1)))
    {m : Type → Type} [Monad m] [LawfulMonad m] :
    simulateQ ((payloadImpl (protocol R deg (k + 1)) tr).liftTarget m)
      (indexedSumQueries domain (projectPathAlong oracleSig _ tr)) =
      (pure (domain.map (fun x => (Interpreted.message tr).val.eval x)).sum : m R) := by
  rw [simulateQ_liftTarget, simulateQ_indexedSumQueries]
  rfl

/-- The initial indexed Sumcheck claim, with the polynomial supplied as oracle data. -/
def indexedInputProblem : StatementProblem
    (RoundStatement R n 0 × (∀ i, PolynomialData R n deg i)) where
  Witness _ _ := Unit
  admissible _ _ := True
  rel _ stmt _ := indexedRelation D 0 stmt.1 (stmt.2 ())
  rel_admissible _ _ _ _ := trivial

/-- The output problem checks the final evaluation claim against the same polynomial. -/
def indexedOutputProblem : PathProblem (protocol R deg n)
    (fun _ => RoundStatement R n (Fin.last n) ×
      (∀ i, PolynomialData R n deg i)) where
  Witness _ _ := Unit
  admissible _ _ := True
  rel _ stmt _ := (stmt.2 ()).val.eval stmt.1.challenges = stmt.1.target
  rel_admissible _ _ _ _ := trivial

/-- A valid accepting decision certifies truth at the completed indexed prefix. -/
theorem indexed_validAcceptance {ι σ : Type} {ambient : OracleSpec ι}
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (stmt : RoundStatement R n 0 × (∀ i, PolynomialData R n deg i))
    (tr : PathAlong oracleSig (protocol R deg n)) :
    (indexedVerifier R deg n D ambient).validAcceptance impl stmt tr
        ((indexedOutputProblem (R := R) (deg := deg) (n := n)).language
          (projectPathAlong oracleSig _ tr)) →
      ∃ t, indexedVerdict D n (some (IndexedClaim.initial stmt.1)) tr = some t ∧
        (stmt.2 ()).val.eval t.challenges = t.target := by
  unfold OracleVerifier.validAcceptance
  dsimp only
  rw [simulateQ_indexedVerifier_decide]
  intro h
  obtain ⟨state, hs⟩ := h
  classical
  by_contra hf
  simp [indexedVerifier, OracleMap.fst, indexedOutputProblem, Problem.language, hf] at hs

/-- The indexed verifier's soundness state follows the current remaining-sum claim. -/
noncomputable def indexedStateFunction {ι σ : Type} {ambient : OracleSpec ι}
    (impl : QueryImpl ambient (StateT σ ProbComp)) :
    StateFunction oracleSig (protocol R deg n)
      (RoundStatement R n 0 × (∀ i, PolynomialData R n deg i))
      ((indexedInputProblem D).admissible ()) ((indexedInputProblem D).language ())
      (fun stmt tr => (indexedVerifier R deg n D ambient).validAcceptance impl stmt tr
        ((indexedOutputProblem (R := R) (deg := deg) (n := n)).language
          (projectPathAlong oracleSig _ tr))) where
  toFun sp history stmt := foldPrefix (indexedGood D (stmt.2 ())) (fun _ => indexedNext D)
    n (some (IndexedClaim.initial stmt.1)) sp history
  root stmt _ h := by
    refine ⟨(), ?_⟩
    change indexedRelation D 0 stmt.1 (stmt.2 ())
    cases n with
    | zero => simpa [foldPrefix, indexedGood, IndexedClaim.initial] using h
    | succ n => simpa [foldPrefix, indexedGood, IndexedClaim.initial] using h
  send sp history stmt howner hfalse x := by
    rwa [foldPrefix_send _ _ _ _ _ _ howner x]
  leaf sp history stmt hfalse hacc :=
    hfalse ((foldPrefix_indexed_leaf D (stmt.2 ()) n _ sp history).mpr
      (indexed_validAcceptance D impl stmt _ hacc))

/-- Native round-by-round soundness holds over every finite indexed domain. -/
theorem indexedVerifier_rbrSoundness [IsDomain R] [Fintype R] [SampleableType R]
    {ι σ : Type} (ambient : OracleSpec ι) (impl : QueryImpl ambient (StateT σ ProbComp)) :
    (indexedVerifier R deg n D ambient).rbrSoundness impl
      (indexedInputProblem D) (indexedOutputProblem (R := R) (deg := deg) (n := n))
      (indexedDraw (R := R) (deg := deg) n)
      (fun _ => (((deg : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞)) := by
  refine ⟨indexedStateFunction D impl, fun stmt _ _ a rest sp h history => ?_⟩
  exact foldPrefix_indexed_flip_le D (stmt.2 ()) n _ sp h history

omit [DecidableEq R] in
/-- Every full Sumcheck path encounters exactly one challenge per round. -/
theorem card_challengeNodesOn_protocol : ∀ (k : ℕ) (path : Path (protocol R deg k)),
    (challengeNodesOn oracleSig (protocol R deg k) path).card = k := by
  intro k
  induction k with
  | zero => intro path; rfl
  | succ k ih =>
    rintro ⟨⟨⟩, ⟨⟨⟩, path⟩⟩
    simp only [challengeNodesOn, owner, oracleSig]
    refine (Finset.card_map _).trans ?_
    refine (Finset.card_cons _).trans ?_
    exact congrArg (· + 1) ((Finset.card_map _).trans (ih path))

/-- The actual indexed verifier run is sound with error `n * (deg / |R|)` over arbitrary domains.
The quantification includes every ambient-effectful prover and every prover output family. -/
theorem indexedVerifier_soundness [IsDomain R] [Fintype R] [SampleableType R]
    {ι σ : Type} (ambient : OracleSpec ι) (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp)) :
    (indexedVerifier R deg n D ambient).soundness init impl
      (indexedDraw (R := R) (deg := deg) n)
      (indexedInputProblem D) (indexedOutputProblem (R := R) (deg := deg) (n := n))
      ((n : ℝ≥0∞) * (((deg : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞)) := by
  simpa only [nsmul_eq_mul] using
    (OracleVerifier.soundness_of_rbrSoundness_uniform (init := init)
      (indexedVerifier_rbrSoundness D ambient impl) (fun _ => le_rfl)
      (fun path => (card_challengeNodesOn_protocol n path).le))

/-- Commit a polynomial before drawing the one-round challenge. -/
def committedProver {ι : Type} (ambient : OracleSpec ι) {R : Type} [CommSemiring R]
    {deg : ℕ} {Out : Type} (msg : R⦃≤ deg⦄[X]) (finish : R → Out) :
    Prover oracleSig ambient (protocol R deg 1) (fun _ => Out) :=
  pure ⟨msg, pure fun r => pure (finish r)⟩

/-- The complete one-round observation, retaining the original input polynomial data. -/
noncomputable def indexedRoundResult (data : ∀ i, PolynomialData R 1 deg i)
    (msg : R⦃≤ deg⦄[X]) (target r : R) :
    Observation oracleSig (protocol R deg 1) (fun _ => R × R)
      (fun _ => RoundStatement R 1 (Fin.last 1) × (∀ i, PolynomialData R 1 deg i)) :=
  ⟨roundTranscript msg r, (msg.val.eval r, r),
    if (∑ a : Fin d, msg.val.eval (D a)) = target then
      some (⟨msg.val.eval r, Fin.snoc Fin.elim0 r⟩, data) else none⟩

/-- The actual one-round run draws exactly one challenge and counts every domain index.
No distribution or sampling structure is required. -/
theorem indexedVerifier_run_one {ι : Type} (ambient : OracleSpec ι)
    (data : ∀ i, PolynomialData R 1 deg i) (msg : R⦃≤ deg⦄[X]) (target : R) :
    (indexedVerifier R deg 1 D ambient).run ⟨target, Fin.elim0⟩ data
      (committedProver ambient msg (fun r => (msg.val.eval r, r))) =
      indexedRoundResult D data msg target <$>
        (liftM ((ambient + challengeSpec oracleSig (protocol R deg 1)).query
          (.inr (roundChallengeNode (R := R) (deg := deg))))) := by
  rw [indexedVerifier_run]
  change (do
    let ⟨tr, out, _⟩ ← Interaction.TwoParty.Lens.run (round R deg)
      (roundProver msg (fun r => (msg.val.eval r, r)))
      (sampler oracleSig (round R deg) (fun c =>
        liftM ((ambient + challengeSpec oracleSig (protocol R deg 1)).query (.inr c))))
    pure (⟨tr, out, (indexedVerdict D 1
      (some (IndexedClaim.initial ⟨target, Fin.elim0⟩)) tr).map
      (fun t => (t, data))⟩ : Observation oracleSig (protocol R deg 1)
        (fun _ => R × R) (fun _ => RoundStatement R 1 (Fin.last 1) ×
          (∀ i, PolynomialData R 1 deg i)))) = _
  rw [run_roundProver]
  simp only [bind_map_left, LawfulMonad.pure_bind]
  rw [map_eq_bind_pure_comp]
  refine bind_congr fun r => ?_
  change R at r
  congr 2
  rw [indexedVerdict_succ]
  simp only [indexedVerdict, intervalVerdict, Interpreted.verdict, indexedNext,
    Interpreted.message, Interpreted.challenge, roundTranscript, IndexedClaim.initial,
    Option.bind_some]
  split <;> rename_i h <;> simp only [h, ite_true, ite_false] <;> rfl

/-- Answer the unique one-round challenge with a supplied computation. -/
def indexedRoundDraw {m : Type → Type} (challenge : m R) :
    QueryImpl (challengeSpec oracleSig (protocol R deg 1)) m := by
  rintro ⟨pos, h⟩
  rcases pos with ⟨⟩ | ⟨⟨⟩, pos⟩
  · cases h
  · rcases pos with ⟨⟩ | ⟨⟨⟩, pos⟩
    · exact challenge
    · cases pos

/-- Execute the actual indexed verifier with any challenge program, including a fixed value. -/
noncomputable def indexedExecute {ι : Type} (ambient : OracleSpec ι) {m : Type → Type} [Monad m]
    (impl : QueryImpl ambient m) (challenge : m R)
    (data : ∀ i, PolynomialData R 1 deg i) (msg : R⦃≤ deg⦄[X]) (target : R) :
    m (Observation oracleSig (protocol R deg 1) (fun _ => R × R)
      (fun _ => RoundStatement R 1 (Fin.last 1) × (∀ i, PolynomialData R 1 deg i))) :=
  simulateQ (QueryImpl.addLift (r := m) impl (indexedRoundDraw (deg := deg) challenge))
    ((indexedVerifier R deg 1 D ambient).run ⟨target, Fin.elim0⟩ data
      (committedProver ambient msg (fun r => (msg.val.eval r, r))))

/-- Execution transports the supplied challenge computation to complete native observations. -/
theorem indexedExecute_eq {ι : Type} (ambient : OracleSpec ι)
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (impl : QueryImpl ambient m) (challenge : m R)
    (data : ∀ i, PolynomialData R 1 deg i) (msg : R⦃≤ deg⦄[X]) (target : R) :
    indexedExecute D ambient impl challenge data msg target =
      indexedRoundResult D data msg target <$> challenge := by
  unfold indexedExecute
  rw [indexedVerifier_run_one, simulateQ_map]
  congr 1
  exact QueryImpl.simulateQ_add_query_right _ _ _

/-- Prescribing a challenge gives the full deterministic execution equation over arbitrary maps. -/
theorem indexedExecuteAt_eq {ι : Type} (ambient : OracleSpec ι)
    (data : ∀ i, PolynomialData R 1 deg i) (msg : R⦃≤ deg⦄[X]) (target r : R) :
    indexedExecute D ambient (QueryImpl.id' ambient) (pure r) data msg target =
      pure (indexedRoundResult D data msg target r) := by
  rw [indexedExecute_eq, LawfulApplicative.map_pure]

/-- A successful sum check gives an accepted deterministic observation at every challenge. -/
theorem indexedExecuteAt_accepted {ι : Type} (ambient : OracleSpec ι)
    (data : ∀ i, PolynomialData R 1 deg i) (msg : R⦃≤ deg⦄[X]) (target r : R)
    (h : (∑ a : Fin d, msg.val.eval (D a)) = target) :
    indexedExecute D ambient (QueryImpl.id' ambient) (pure r) data msg target =
      pure ⟨roundTranscript msg r, (msg.val.eval r, r),
        some (⟨msg.val.eval r, Fin.snoc Fin.elim0 r⟩, data)⟩ := by
  rw [indexedExecuteAt_eq]
  simp only [indexedRoundResult, ite_eq_left h]

/-- The arbitrary-list deterministic equation retains every occurrence of a domain point. -/
theorem indexedExecuteAt_list_eq {ι : Type} (ambient : OracleSpec ι) (domain : List R)
    (data : ∀ i, PolynomialData R 1 deg i) (msg : R⦃≤ deg⦄[X]) (target r : R) :
    indexedExecute domain.get ambient (QueryImpl.id' ambient) (pure r) data msg target =
      pure ⟨roundTranscript msg r, (msg.val.eval r, r),
        if (domain.map (fun x => msg.val.eval x)).sum = target then
          some (⟨msg.val.eval r, Fin.snoc Fin.elim0 r⟩, data) else none⟩ := by
  rw [indexedExecuteAt_eq]
  simp only [indexedRoundResult]
  rw [sum_domain_list domain (fun x => msg.val.eval x)]

/-- Accepted arbitrary-list execution needs only the list sum condition, with no sampler. -/
theorem indexedExecuteAt_list_accepted {ι : Type} (ambient : OracleSpec ι) (domain : List R)
    (data : ∀ i, PolynomialData R 1 deg i) (msg : R⦃≤ deg⦄[X]) (target r : R)
    (h : (domain.map (fun x => msg.val.eval x)).sum = target) :
    indexedExecute domain.get ambient (QueryImpl.id' ambient) (pure r) data msg target =
      pure ⟨roundTranscript msg r, (msg.val.eval r, r),
        some (⟨msg.val.eval r, Fin.snoc Fin.elim0 r⟩, data)⟩ := by
  rw [indexedExecuteAt_list_eq, ite_eq_left h]

/-- A failed sum check explicitly rejects while retaining the completed transcript and outputs. -/
theorem indexedRoundResult_rejects (data : ∀ i, PolynomialData R 1 deg i)
    (msg : R⦃≤ deg⦄[X]) (target r : R)
    (h : (∑ a : Fin d, msg.val.eval (D a)) ≠ target) :
    (indexedRoundResult D data msg target r).2.2 = none := by
  simp [indexedRoundResult, h]

/-- Executing a committed message preserves exactly the challenge computation's total mass. -/
theorem indexedExecute_failure {ι : Type} (ambient : OracleSpec ι)
    (impl : QueryImpl ambient ProbComp) (challenge : ProbComp R)
    (data : ∀ i, PolynomialData R 1 deg i) (msg : R⦃≤ deg⦄[X]) (target : R) :
    Pr{let _ ← indexedExecute D ambient impl challenge data msg target}[True] =
      Pr{let _ ← challenge}[True] := by
  rw [indexedExecute_eq, prEvent_map]

/-- A one-round output is true exactly when the check accepts and the retained input agrees
with the sent message at the challenge. -/
theorem indexedRoundResult_true_iff (data : ∀ i, PolynomialData R 1 deg i)
    (msg : R⦃≤ deg⦄[X]) (target r : R) :
    (indexedRoundResult D data msg target r).2.2.map
      (fun out => (out.2 ()).val.eval out.1.challenges = out.1.target) = some True ↔
      (∑ a : Fin d, msg.val.eval (D a)) = target ∧
        (data ()).val.eval (Fin.snoc Fin.elim0 r) = msg.val.eval r := by
  by_cases h : (∑ a : Fin d, msg.val.eval (D a)) = target
  · simp [indexedRoundResult, h]
  · simp [indexedRoundResult, h]

/-- The honest one-round message at an empty challenge prefix. -/
noncomputable def indexedHonestMessage (D : Fin d → R)
    (data : ∀ i, PolynomialData R 1 deg i) : R⦃≤ deg⦄[X] :=
  projectedRoundPolynomial D 0 Fin.elim0 (data ())

/-- Every challenge produces an accepted true output on an honest indexed input. -/
theorem indexedRoundResult_honest (data : ∀ i, PolynomialData R 1 deg i) (target r : R)
    (h : indexedRelation D 0 ⟨target, Fin.elim0⟩ (data ())) :
    (indexedRoundResult D data (indexedHonestMessage D data) target r).2.2.map
      (fun out => (out.2 ()).val.eval out.1.challenges = out.1.target) = some True := by
  apply (indexedRoundResult_true_iff D data _ target r).mpr
  constructor
  · exact (sum_projectedRoundPolynomial D 0 Fin.elim0 (data ())).trans h
  · have hs := roundSum_succ D (0 : Fin 1) Fin.elim0 (data ()) r
    have hl := (indexedRelation_last D
      (⟨(indexedHonestMessage D data).val.eval r, Fin.snoc Fin.elim0 r⟩ :
        RoundStatement R 1 (Fin.last 1)) (data ())).mp hs
    exact hl

/-- Honest execution with an arbitrary challenge program transports the complete observation. -/
theorem indexedExecute_honest_eq {ι : Type} (ambient : OracleSpec ι)
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (impl : QueryImpl ambient m) (challenge : m R)
    (data : ∀ i, PolynomialData R 1 deg i) (target : R)
    (h : indexedRelation D 0 ⟨target, Fin.elim0⟩ (data ())) :
    indexedExecute D ambient impl challenge data (indexedHonestMessage D data) target =
      (fun r => ⟨roundTranscript (indexedHonestMessage D data) r,
        ((indexedHonestMessage D data).val.eval r, r),
        some (⟨(indexedHonestMessage D data).val.eval r, Fin.snoc Fin.elim0 r⟩, data)⟩) <$>
          challenge := by
  rw [indexedExecute_eq]
  congr 1
  funext r
  unfold indexedRoundResult
  have hs : (∑ a : Fin d, (indexedHonestMessage D data).val.eval (D a)) = target :=
    (sum_projectedRoundPolynomial D 0 Fin.elim0 (data ())).trans h
  rw [ite_eq_left hs]

/-- Every supported honest execution satisfies the final evaluation relation. -/
theorem indexedExecute_honest_support {ι : Type} (ambient : OracleSpec ι)
    (impl : QueryImpl ambient ProbComp) (challenge : ProbComp R)
    (data : ∀ i, PolynomialData R 1 deg i) (target : R)
    (h : indexedRelation D 0 ⟨target, Fin.elim0⟩ (data ()))
    (obs : Observation oracleSig (protocol R deg 1) (fun _ => R × R)
      (fun _ => RoundStatement R 1 (Fin.last 1) × (∀ i, PolynomialData R 1 deg i)))
    (ho : obs ∈ support (indexedExecute D ambient impl challenge data
      (indexedHonestMessage D data) target)) :
    obs.2.2.map (fun out => (out.2 ()).val.eval out.1.challenges = out.1.target) =
      some True := by
  rw [indexedExecute_eq, _root_.support_map] at ho
  obtain ⟨r, _, rfl⟩ := ho
  exact indexedRoundResult_honest D data target r h

/-- Honest one-round completeness holds for every challenge computation, without sampling
assumptions on the semiring. -/
theorem indexedExecute_perfectCompleteness {ι : Type} (ambient : OracleSpec ι)
    (impl : QueryImpl ambient ProbComp) (challenge : ProbComp R)
    (data : ∀ i, PolynomialData R 1 deg i) (target : R)
    (h : indexedRelation D 0 ⟨target, Fin.elim0⟩ (data ())) :
    Pr{let obs ← (indexedExecute D ambient impl challenge data
      (indexedHonestMessage D data) target)}[
        obs.2.2.map (fun out => (out.2 ()).val.eval out.1.challenges = out.1.target) =
          some True] = 1 :=
  OracleComp.prEvent_eq_one_of_forall_mem_support _ _
    (indexedExecute_honest_support D ambient impl challenge data target h)

/-- The measure of honest valid accepted outputs is one for an arbitrary challenge program. -/
theorem indexedExecute_measureCompleteness {ι : Type} (ambient : OracleSpec ι)
    (impl : QueryImpl ambient ProbComp) (challenge : ProbComp R)
    (data : ∀ i, PolynomialData R 1 deg i) (target : R)
    (h : indexedRelation D 0 ⟨target, Fin.elim0⟩ (data ())) :
    𝒟[(fun obs => obs.2.2.map
      (fun out => (out.2 ()).val.eval out.1.challenges = out.1.target) = some True) <$>
        indexedExecute D ambient impl challenge data (indexedHonestMessage D data) target]
      {True} = 1 := by
  rw [← prEvent_eq_evalDist_map]
  exact indexedExecute_perfectCompleteness D ambient impl challenge data target h

/-- A degree-bounded message has degree at most its bound. -/
theorem message_degree {R : Type} [CommSemiring R] {deg : ℕ} (p : R⦃≤ deg⦄[X]) :
    p.val.degree ≤ deg :=
  Polynomial.mem_degreeLE.mp p.property

/-- Embed a degree-bounded univariate input into the native one-variable polynomial resource. -/
noncomputable def univariateData {R : Type} [CommSemiring R] {deg : ℕ} (p : R⦃≤ deg⦄[X]) :
    R⦃≤ deg⦄[X Fin 1] :=
  ⟨(MvPolynomial.uniqueAlgEquiv R (Fin 1)).symm p.val, by
    rw [MvPolynomial.mem_restrictDegree_iff_degreeOf_le]
    intro i
    change MvPolynomial.degreeOf i (Polynomial.aeval (MvPolynomial.X (0 : Fin 1)) p.val) ≤ deg
    exact (MvPolynomial.degreeOf_aeval_le i p.val _ (by
      rcases subsingleton_or_nontrivial R with hs | hn
      · let := hs
        rw [Subsingleton.elim (MvPolynomial.X (0 : Fin 1)) 0, MvPolynomial.degreeOf_zero]
        exact Nat.zero_le _
      · let := hn
        simp [Subsingleton.elim i 0])).trans
      (Polynomial.natDegree_le_of_degree_le (message_degree p))⟩
/-- The univariate adapter preserves evaluation at every challenge, with no sampling assumption. -/
theorem univariateData_eval {R : Type} [CommSemiring R] {deg : ℕ}
    (p : R⦃≤ deg⦄[X]) (r : R) :
    (univariateData p).val.eval (Fin.snoc Fin.elim0 r) = p.val.eval r := by
  change MvPolynomial.eval₂ (RingHom.id R) _
    ((MvPolynomial.uniqueAlgEquiv R (Fin 1)).symm p.val) = _
  rw [MvPolynomial.eval₂_uniqueAlgEquiv_symm]
  rfl

/-- Honest univariate execution over any list retains the original input and accepts every
prescribed challenge whenever the list sum claim holds. -/
theorem indexedExecuteAt_univariate_honest {ι : Type} (ambient : OracleSpec ι)
    (domain : List R) (p : R⦃≤ deg⦄[X]) (target r : R)
    (h : (domain.map (fun x => p.val.eval x)).sum = target) :
    indexedExecute domain.get ambient (QueryImpl.id' ambient) (pure r)
      (fun _ => univariateData p) p target =
      pure ⟨roundTranscript p r, (p.val.eval r, r),
        some (⟨p.val.eval r, Fin.snoc Fin.elim0 r⟩, fun _ => univariateData p)⟩ :=
  indexedExecuteAt_list_accepted ambient domain (fun _ => univariateData p) p target r h

/-- The full honest observation equation transports every lawful challenge program. -/
theorem indexedExecute_univariate_honest_eq {ι : Type} (ambient : OracleSpec ι)
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (impl : QueryImpl ambient m) (challenge : m R)
    (domain : List R) (p : R⦃≤ deg⦄[X]) (target : R)
    (h : (domain.map (fun x => p.val.eval x)).sum = target) :
    indexedExecute domain.get ambient impl challenge (fun _ => univariateData p) p target =
      (fun r => ⟨roundTranscript p r, (p.val.eval r, r),
        some (⟨p.val.eval r, Fin.snoc Fin.elim0 r⟩, fun _ => univariateData p)⟩) <$>
          challenge := by
  rw [indexedExecute_eq]
  congr 1
  funext r
  simp only [indexedRoundResult]
  rw [sum_domain_list domain (fun x => p.val.eval x), ite_eq_left h]

/-- An honest univariate normal form has a true closed evaluation output for every challenge. -/
theorem indexedRoundResult_univariate_honest (domain : List R) (p : R⦃≤ deg⦄[X])
    (target r : R) (h : (domain.map (fun x => p.val.eval x)).sum = target) :
    (indexedRoundResult domain.get (fun _ => univariateData p) p target r).2.2.map
      (fun out => (out.2 ()).val.eval out.1.challenges = out.1.target) = some True := by
  apply (indexedRoundResult_true_iff domain.get _ p target r).mpr
  exact ⟨(sum_domain_list domain (fun x => p.val.eval x)).trans h, univariateData_eval p r⟩

/-- Evaluating the actual honest output yields `some True`, preserving all challenge effects. -/
theorem indexedExecute_univariate_complete {ι : Type} (ambient : OracleSpec ι)
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (impl : QueryImpl ambient m) (challenge : m R)
    (domain : List R) (p : R⦃≤ deg⦄[X]) (target : R)
    (h : (domain.map (fun x => p.val.eval x)).sum = target) :
    (fun obs => obs.2.2.map
      (fun out => (out.2 ()).val.eval out.1.challenges = out.1.target)) <$>
        indexedExecute domain.get ambient impl challenge (fun _ => univariateData p) p target =
      (fun _ => some True) <$> challenge := by
  rw [indexedExecute_eq, Functor.map_map]
  congr 1
  funext r
  exact indexedRoundResult_univariate_honest domain p target r h

/-- The message degree bound and actual execution completeness hold together, preserving every
challenge effect. -/
theorem indexedExecute_univariate_degree_complete {ι : Type} (ambient : OracleSpec ι)
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (impl : QueryImpl ambient m) (challenge : m R)
    (domain : List R) (p : R⦃≤ deg⦄[X]) (target : R)
    (h : (domain.map (fun x => p.val.eval x)).sum = target) :
    p.val.degree ≤ deg ∧
      (fun obs => obs.2.2.map
        (fun out => (out.2 ()).val.eval out.1.challenges = out.1.target)) <$>
          indexedExecute domain.get ambient impl challenge (fun _ => univariateData p) p target =
        (fun _ => some True) <$> challenge :=
  ⟨message_degree p, indexedExecute_univariate_complete ambient impl challenge domain p target h⟩

/-- Every supported honest univariate run has a true accepted output, for an arbitrary list. -/
theorem indexedExecute_univariate_support {ι : Type} (ambient : OracleSpec ι)
    (impl : QueryImpl ambient ProbComp) (challenge : ProbComp R)
    (domain : List R) (p : R⦃≤ deg⦄[X]) (target : R)
    (h : (domain.map (fun x => p.val.eval x)).sum = target)
    (obs : Observation oracleSig (protocol R deg 1) (fun _ => R × R)
      (fun _ => RoundStatement R 1 (Fin.last 1) × (∀ i, PolynomialData R 1 deg i)))
    (ho : obs ∈ support (indexedExecute domain.get ambient impl challenge
      (fun _ => univariateData p) p target)) :
    obs.2.2.map (fun out => (out.2 ()).val.eval out.1.challenges = out.1.target) =
      some True := by
  rw [indexedExecute_eq, _root_.support_map] at ho
  obtain ⟨r, _, rfl⟩ := ho
  exact indexedRoundResult_univariate_honest domain p target r h

/-- The arbitrary-list honest univariate executor is perfectly complete for every challenge
program, without a sampling structure on the semiring. -/
theorem indexedExecute_univariate_perfectCompleteness {ι : Type} (ambient : OracleSpec ι)
    (impl : QueryImpl ambient ProbComp) (challenge : ProbComp R)
    (domain : List R) (p : R⦃≤ deg⦄[X]) (target : R)
    (h : (domain.map (fun x => p.val.eval x)).sum = target) :
    Pr{let obs ← (indexedExecute domain.get ambient impl challenge
      (fun _ => univariateData p) p target)}[
        obs.2.2.map (fun out => (out.2 ()).val.eval out.1.challenges = out.1.target) =
          some True] = 1 :=
  OracleComp.prEvent_eq_one_of_forall_mem_support _ _
    (indexedExecute_univariate_support ambient impl challenge domain p target h)

/-- The same honest arbitrary-list event has measure one in the actual run. -/
theorem indexedExecute_univariate_measureCompleteness {ι : Type} (ambient : OracleSpec ι)
    (impl : QueryImpl ambient ProbComp) (challenge : ProbComp R)
    (domain : List R) (p : R⦃≤ deg⦄[X]) (target : R)
    (h : (domain.map (fun x => p.val.eval x)).sum = target) :
    𝒟[(fun obs => obs.2.2.map
      (fun out => (out.2 ()).val.eval out.1.challenges = out.1.target) = some True) <$>
        indexedExecute domain.get ambient impl challenge (fun _ => univariateData p) p target]
      {True} = 1 := by
  rw [← prEvent_eq_evalDist_map]
  exact indexedExecute_univariate_perfectCompleteness ambient impl challenge domain p target h

end Sumcheck.Core
