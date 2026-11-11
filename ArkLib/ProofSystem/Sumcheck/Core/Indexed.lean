/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Core.Domain
public import ArkLib.ProofSystem.Sumcheck.Core.Tree
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

/-- The public claim with `k` rounds remaining. -/
structure IndexedClaim (R : Type) (n k : ℕ) where
  /-- The current round. -/
  round : Fin (n + 1)
  /-- The current round and remaining rounds partition the full run. -/
  round_add : round.val + k = n
  /-- The current target and challenge prefix. -/
  statement : RoundStatement R n round

/-- The next variable when a round remains. -/
def IndexedClaim.index {k : ℕ} (st : IndexedClaim R n (k + 1)) : Fin n :=
  ⟨st.round, by have := st.round_add; omega⟩

/-- Updating a claim with the evaluation of the sent message at the new challenge. -/
def IndexedClaim.next {k : ℕ} (st : IndexedClaim R n (k + 1)) (value r : R) :
    IndexedClaim R n k where
  round := st.index.succ
  round_add := by have := st.round_add; change st.round.val + 1 + k = n; omega
  statement := ⟨value, Fin.snoc st.statement.challenges r⟩

/-- Read the final evaluation claim after all variables have been fixed. -/
def IndexedClaim.finish (st : IndexedClaim R n 0) : RoundStatement R n (Fin.last n) :=
  ⟨st.statement.target, st.statement.challenges ∘ Fin.cast (by
    have := st.round_add; simp only [Fin.val_last]; omega)⟩

/-- The initial claim has an empty challenge prefix. -/
def IndexedClaim.initial (stmt : RoundStatement R n 0) : IndexedClaim R n n :=
  ⟨0, Nat.zero_add n, stmt⟩

variable [DecidableEq R] (D : Fin d → R)

/-- The public update rejects a failed indexed sum check. -/
noncomputable def indexedNext {k : ℕ} (st : Option (IndexedClaim R n (k + 1)))
    (msg : R⦃≤ deg⦄[X]) (r : R) : Option (IndexedClaim R n k) :=
  st.bind fun st => if (∑ a : Fin d, msg.val.eval (D a)) = st.statement.target then
    some (st.next (msg.val.eval r) r) else none

/-- The verdict obtained by checking every round of a completed transcript. -/
noncomputable def indexedVerdict : (k : ℕ) → Option (IndexedClaim R n k) →
    PathAlong oracleSig (protocol R deg k) → Option (RoundStatement R n (Fin.last n))
  | 0, st, _ => st.map IndexedClaim.finish
  | k + 1, st, tr => indexedVerdict k (indexedNext D st (headMessage tr) (headChallenge tr))
      (tailTranscript tr)

/-- Query the first round polynomial at a field or semiring element. -/
def indexedHeadQuery {k : ℕ} : (p : Path (protocol R deg (k + 1))) → R →
    OracleComp (oracles (protocol R deg (k + 1)) p) R
  | ⟨⟨⟩, ⟨⟨⟩, p⟩⟩, r => liftM
      ((oracles (protocol R deg (k + 1)) ⟨⟨⟩, ⟨⟨⟩, p⟩⟩).query ⟨.inl ⟨⟩, r⟩)

omit [DecidableEq R] in
/-- The transcript payload answers a query to the first round polynomial. -/
theorem simulateQ_indexedHeadQuery {k : ℕ}
    (tr : PathAlong oracleSig (protocol R deg (k + 1))) (r : R) :
    simulateQ (payloadImpl (protocol R deg (k + 1)) tr)
      (indexedHeadQuery (projectPathAlong oracleSig _ tr) r) = (headMessage tr).val.eval r := by
  rcases tr with ⟨msg, chal, tail⟩
  rfl

/-- The shape path of the remaining Sumcheck rounds. -/
def indexedTailPath {k : ℕ} : Path (protocol R deg (k + 1)) → Path (protocol R deg k)
  | ⟨⟨⟩, ⟨⟨⟩, p⟩⟩ => p

/-- Lift a query from the remaining rounds along a full Sumcheck shape path. -/
def indexedTailLift {k : ℕ} (p : Path (protocol R deg (k + 1))) :
    QueryImpl (oracles (protocol R deg k) (indexedTailPath p))
      (OracleComp (oracles (protocol R deg (k + 1)) p)) := by
  rcases p with ⟨⟨⟩, ⟨⟨⟩, p⟩⟩
  exact tailLift R deg k p

/-- Read the first challenge from a verifier view. -/
def indexedViewChallenge {k : ℕ} {p : Path (protocol R deg (k + 1))}
    (v : View (protocol R deg (k + 1)) p) : R := v.1.2.1

/-- Restrict a verifier view to the remaining rounds. -/
def indexedTailView {k : ℕ} {p : Path (protocol R deg (k + 1))}
    (v : View (protocol R deg (k + 1)) p) : View (protocol R deg k) (indexedTailPath p) :=
  ⟨v.1.2.2, (protocolPath_eq R deg k _).trans (protocolPath_eq R deg k _).symm⟩

omit [DecidableEq R] in
/-- Answering lifted suffix queries uses precisely the suffix transcript's payloads. -/
theorem simulateQ_indexedTailLift {k : ℕ}
    (tr : PathAlong oracleSig (protocol R deg (k + 1))) {α : Type}
    (oa : OracleComp (oracles (protocol R deg k)
      (indexedTailPath (projectPathAlong oracleSig _ tr))) α) :
    simulateQ (payloadImpl (protocol R deg (k + 1)) tr)
        (simulateQ (indexedTailLift (projectPathAlong oracleSig _ tr)) oa) =
      simulateQ (payloadImpl (protocol R deg k) (tailTranscript tr)) oa := by
  refine QueryImpl.simulateQ_simulateQ_eq_of_apply (fun q => ?_) oa
  rcases tr with ⟨msg, chal, tail⟩
  rfl

/-- Query the sent message at every domain index before continuing to the next round. -/
def indexedDecision : (k : ℕ) → Option (IndexedClaim R n k) →
    (p : Path (protocol R deg k)) → View (protocol R deg k) p →
    OracleComp (oracles (protocol R deg k) p) (Option (RoundStatement R n (Fin.last n)))
  | 0, st, _, _ => pure (st.map IndexedClaim.finish)
  | k + 1, st, p, v => do
      match st with
      | none => return none
      | some st =>
        let values ← (List.finRange d).mapM fun a => indexedHeadQuery p (D a)
        if values.sum = st.statement.target then
          let r := indexedViewChallenge v
          let value ← indexedHeadQuery p r
          simulateQ (indexedTailLift p) (indexedDecision k (some (st.next value r))
            (indexedTailPath p) (indexedTailView v))
        else return none

/-- Lift the round-message queries into the verifier's final resource interface. -/
def indexedDecisionLift {ι : Type} (ambient : OracleSpec ι) (p : Path (protocol R deg n)) :
    QueryImpl (oracles (protocol R deg n) p)
      (OracleComp (ambient + (pathResources (polyFamily R deg n) (protocol R deg n) p).spec)) :=
  fun q => liftM ((ambient +
    (pathResources (polyFamily R deg n) (protocol R deg n) p).spec).query (.inr (.inr q)))

omit [DecidableEq R] in
/-- Answering the lifted message queries is a pure computation of the transcript payloads. -/
theorem simulateQ_indexedDecisionLift_monad {ι : Type} {ambient : OracleSpec ι}
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (impl : QueryImpl ambient m) (p : Path (protocol R deg n))
    (data : ∀ i, PolynomialData R n deg i) (pl : ∀ i, OracleData (protocol R deg n) p i)
    {α : Type} (oa : OracleComp (oracles (protocol R deg n) p) α) :
    simulateQ (QueryImpl.addLift impl ((pathResources (polyFamily R deg n) (protocol R deg n)
      p).answer (data, pl))) (simulateQ (indexedDecisionLift ambient p) oa) =
      (pure (simulateQ ((pathFamily (protocol R deg n) p).behaviorOfRealizations pl) oa) :
        m α) := by
  refine (QueryImpl.simulateQ_simulateQ_eq_of_apply
    (impl := ((pathFamily (protocol R deg n) p).behaviorOfRealizations pl).liftTarget m)
    (fun t => ?_) oa).trans ?_
  · simp only [QueryImpl.addLift_def]
    exact QueryImpl.simulateQ_add_query_right _ _ _
  · rw [simulateQ_liftTarget]
    rfl

/-- The passive Sumcheck verifier counts all domain indices in its final decision. -/
def indexedVerifier (R : Type) [CommSemiring R] [DecidableEq R] (deg n : ℕ)
    {d : ℕ} (D : Fin d → R) {ι : Type} (ambient : OracleSpec ι) :
    OracleVerifier ambient (protocol R deg n) (RoundStatement R n 0)
      (fun _ => RoundStatement R n (Fin.last n)) (polyFamily R deg n)
      (fun _ => polyFamily R deg n) where
  decide stmt p v := OptionT.mk (simulateQ (indexedDecisionLift ambient p)
    (indexedDecision D n (some (IndexedClaim.initial stmt)) p v))
  outputMap _ p _ :=
    { f := fun x => x.1
      impl := fun q => liftM
        ((pathResources (polyFamily R deg n) (protocol R deg n) p).spec.query (.inl q))
      law := fun _ _ => rfl }

/-- A rejected prefix stays rejected through every remaining round. -/
@[simp] theorem indexedVerdict_none : ∀ (k : ℕ)
    (tr : PathAlong oracleSig (protocol R deg k)), indexedVerdict (n := n) D k none tr = none := by
  intro k
  induction k with
  | zero => intro tr; rfl
  | succ k ih => intro tr; exact ih (tailTranscript tr)

/-- Answering the indexed decision from a transcript computes the indexed verdict. -/
theorem simulateQ_indexedDecision : ∀ (k : ℕ) (st : Option (IndexedClaim R n k))
    (tr : PathAlong oracleSig (protocol R deg k)),
    simulateQ (payloadImpl (protocol R deg k) tr)
      (indexedDecision D k st _ (toView _ tr)) = indexedVerdict D k st tr := by
  intro k
  induction k with
  | zero => intro st tr; rfl
  | succ k ih =>
      intro st tr
      rcases tr with ⟨msg, chal, tail⟩
      cases st with
      | none =>
        change (none : Option (RoundStatement R n (Fin.last n))) =
          indexedVerdict D (k + 1) none _
        simp only [indexedVerdict_none]
      | some st =>
        rw [indexedDecision]
        simp only [simulateQ_bind, simulateQ_list_mapM]
        change ((List.finRange d).mapM (fun a => (pure (msg.val.eval (D a)) : Id R)) >>= _) = _
        simp only [List.mapM_pure, LawfulMonad.pure_bind]
        by_cases hs : (∑ a : Fin d, msg.val.eval (D a)) = st.statement.target
        · have hl : (List.map (fun a => msg.val.eval (D a)) (List.finRange d)).sum =
              st.statement.target := by
            rwa [← List.ofFn_eq_map, List.sum_ofFn]
          simp only [hl, ite_true]
          rw [simulateQ_bind, simulateQ_indexedHeadQuery]
          change simulateQ _ (simulateQ
            (indexedTailLift (projectPathAlong oracleSig _ ⟨msg, chal, tail⟩))
            (indexedDecision D k (some (st.next (msg.val.eval chal) chal)) _
              (indexedTailView (toView (protocol R deg (k + 1)) ⟨msg, chal, tail⟩)))) = _
          rw [simulateQ_indexedTailLift (R := R) (deg := deg) (k := k)
            (⟨msg, chal, tail⟩ : PathAlong oracleSig (protocol R deg (k + 1)))]
          change simulateQ (payloadImpl (protocol R deg k) tail)
            (indexedDecision D k (some (st.next (msg.val.eval chal) chal))
              (projectPathAlong oracleSig (protocol R deg k) tail)
              (toView (protocol R deg k) tail)) = _
          rw [ih _ tail]
          simp [indexedVerdict, indexedNext, hs, headMessage, headChallenge, tailTranscript]
        · have hl : (List.map (fun a => msg.val.eval (D a)) (List.finRange d)).sum ≠
              st.statement.target := by
            rwa [← List.ofFn_eq_map, List.sum_ofFn]
          simp only [hl, ite_false, simulateQ_pure]
          simp [indexedVerdict, indexedNext, hs, headMessage]
          rfl

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
    indexedGood D p 0 st ↔ ∃ t, st.map IndexedClaim.finish = some t ∧
      p.val.eval t.challenges = t.target := by
  cases st with
  | none => simp [indexedGood]
  | some st =>
    rcases st with ⟨round, ha, stmt⟩
    have heq : round = Fin.last n := Fin.ext (by simpa using ha)
    subst round
    simp [indexedGood, IndexedClaim.finish, indexedRelation_last]

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
    exact indexedGood_zero D p st
  | succ k ih =>
    intro st sp history
    change Cursor.Spine (P := OraclePoly) (.liftBind (.oracle (R⦃≤ deg⦄[X]) inferInstance)
      (fun _ => .liftBind (.challenge R) (fun _ => protocol R deg k))) _ at sp
    cases sp with
    | down b tail =>
      cases b
      cases tail with
      | down b tail => exact ih _ tail history.2.2

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
          simp [indexedGood, indexedNext, hs, ht, IndexedClaim.next]
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
    simulateQ (QueryImpl.addLift impl ((pathResources (polyFamily R deg n) (protocol R deg n)
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
  unfold Interaction.Core.OracleVerifier.run
  refine bind_congr fun result => ?_
  rcases result with ⟨tr, out, u⟩
  dsimp only
  rw [simulateQ_indexedVerifier_decide]
  simp only [LawfulMonad.pure_bind]
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
  simp [indexedVerifier, indexedOutputProblem, Problem.language, hf] at hs

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

end Sumcheck.Core
