/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Core.Interval
public import VCVio.OracleComp.EvalDist.Measure

/-! # Completeness of arbitrary Sumcheck intervals

The honest prover preserves the indexed remaining-sum relation for every challenge. Stateful
challenge handlers may depend on the reached statement and all previous challenges.
-/

@[expose] public section

namespace Sumcheck.Core
open Polynomial MvPolynomial PFunctor FreeM Interaction.Core Interaction.TwoParty.Lens
  Interaction.Oracle
  OracleComp OracleSpec

variable {R : Type} [CommSemiring R] [DecidableEq R] {deg n d : ℕ}
  (D : Fin d → R) {stop : Fin (n + 1)}
  (p : R⦃≤ deg⦄[X Fin n])

/-- The honest message is the indexed sum over all remaining variables after the free one. -/
noncomputable def intervalMessage (k : ℕ) (st : IntervalClaim R n stop (k + 1)) :
    R⦃≤ deg⦄[X] := projectedRoundPolynomial D st.index st.statement.challenges p

/-- The honest successor extends the prefix by the received challenge. -/
noncomputable def intervalNext (k : ℕ) (st : IntervalClaim R n stop (k + 1)) (r : R) :
    IntervalClaim R n stop k := st.next ((intervalMessage D p k st).val.eval r) r

/-- The honest interval prover sends its projected polynomial at every round. -/
noncomputable def intervalProver {m : Type → Type} [Monad m] (k : ℕ)
    (st : IntervalClaim R n stop k) :
    Focal oracleSig m (protocol R deg k) (fun _ => RoundStatement R n stop) :=
  foldRounds (intervalMessage D p) (intervalNext D p) IntervalClaim.finish k st

/-- Every honest round accepts and preserves the indexed remaining-sum claim. -/
theorem interval_honest_step (k : ℕ) (st : IntervalClaim R n stop (k + 1))
    (h : indexedRelation D st.round st.statement p) (r : R) :
    roundVerdict (intervalCheck D k) st (intervalMessage D p k st) r =
      some (intervalNext D p k st r) ∧
    indexedRelation D (intervalNext D p k st r).round
      (intervalNext D p k st r).statement p := by
  constructor
  · rw [roundVerdict_intervalCheck]
    have hs := sum_projectedRoundPolynomial D st.index st.statement.challenges p
    change (if _ = st.statement.target then _ else _) = _
    rw [show (∑ a : Fin d, (intervalMessage D p k st).val.eval (D a)) =
      st.statement.target from hs.trans h]
    simp only [ite_true]
    rfl
  · exact roundSum_succ D st.index st.statement.challenges p r

omit [DecidableEq R] in
/-- At the endpoint the finish operation preserves the remaining-sum relation. -/
theorem interval_finish_relation (st : IntervalClaim R n stop 0)
    (h : indexedRelation D st.round st.statement p) :
    indexedRelation D stop st.finish p := by
  rcases st with ⟨i, hi, stmt⟩
  have heq : i = stop := Fin.ext (by simpa using hi)
  subst i
  exact h

/-- Every honest transcript is accepted, including empty intervals and nonzero starts. -/
theorem intervalVerdict_honest : ∀ (k : ℕ) (st : IntervalClaim R n stop k)
    (_h : indexedRelation D st.round st.statement p) (chals : Fin k → R),
    intervalVerdict D k st (foldTranscript (intervalMessage D p) (intervalNext D p) k st chals) =
      some (foldState (intervalNext D p) k st chals).finish ∧
    indexedRelation D stop (foldState (intervalNext D p) k st chals).finish p := by
  intro k
  induction k with
  | zero => intro st h chals; exact ⟨rfl, interval_finish_relation D p st h⟩
  | succ k ih =>
    intro st h chals
    obtain ⟨hcheck, hnext⟩ := interval_honest_step D p k st h (chals 0)
    obtain ⟨haccept, hrel⟩ := ih _ hnext (Fin.tail chals)
    refine ⟨?_, hrel⟩
    unfold intervalVerdict
    rw [foldTranscript, foldVerdict, headMessage_consTranscript, headChallenge_consTranscript,
      tailTranscript_consTranscript, hcheck]
    exact haccept

/-- The actual honest run is a map of all challenge draws, retaining its prover output. -/
theorem intervalVerifier_honest_run {ι : Type} (ambient : OracleSpec ι)
    (start count : ℕ) (bound : start + count ≤ n)
    (stmt : RoundStatement R n ⟨start, by omega⟩)
    (h : indexedRelation D _ stmt p) :
    let st := intervalInitial start count bound stmt
    (intervalVerifier R deg n D ambient start count bound).run stmt (fun _ => p)
      (intervalProver D p count st) =
      (fun chals => (⟨foldTranscript (intervalMessage D p) (intervalNext D p) count st chals,
        (foldState (intervalNext D p) count st chals).finish,
        some ((foldState (intervalNext D p) count st chals).finish, fun _ => p)⟩ :
          Observation oracleSig (protocol R deg count) (fun _ => RoundStatement R n
            ⟨count + start, by omega⟩)
            (fun _ => RoundStatement R n ⟨count + start, by omega⟩ ×
              (∀ i, PolynomialData R n deg i)))) <$>
        drawChallenges count (fun c => liftM
          ((ambient + challengeSpec oracleSig (protocol R deg count)).query (.inr c))) := by
  dsimp only
  rw [intervalVerifier_run, foldVerifier_run]
  unfold intervalProver
  rw [simulate_foldRounds, run_foldRounds]
  rw [bind_map_left]
  rw [← LawfulMonad.bind_pure_comp]
  refine bind_congr fun chals => ?_
  dsimp only
  change pure (⟨_, _, (intervalVerdict D count _ _).map (fun t => (t, fun _ => p))⟩ :
    Observation oracleSig (protocol R deg count) (fun _ => RoundStatement R n
      ⟨count + start, by omega⟩) (fun _ => RoundStatement R n ⟨count + start, by omega⟩ ×
        (∀ i, PolynomialData R n deg i))) = _
  rw [(intervalVerdict_honest D p count _ h chals).1]
  rfl

/-- Interpret the actual run with shared state for ambient effects and adaptive challenges. -/
def intervalExperiment {ι σ α : Type} {spec : OracleSpec ι}
    (init : ProbComp σ) (impl : QueryImpl spec (StateT σ ProbComp))
    (program : OracleComp spec α) : ProbComp α := do
  (simulateQ impl program).run' (← init)

/-- Interpreting a mapped program maps the resulting experiment. -/
theorem intervalExperiment_map {ι σ α β : Type} {spec : OracleSpec ι}
    (init : ProbComp σ) (impl : QueryImpl spec (StateT σ ProbComp))
    (f : α → β) (program : OracleComp spec α) :
    intervalExperiment init impl (f <$> program) = f <$> intervalExperiment init impl program := by
  simp only [intervalExperiment, simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map,
    _root_.map_bind]

/-- Every supported actual honest interval run accepts a true endpoint claim. The handler may
keep the reached statement in shared state and choose challenges from that entire history. -/
theorem intervalVerifier_supportCompleteness {ι σ : Type} (ambient : OracleSpec ι)
    (init : ProbComp σ)
    (start count : ℕ) (bound : start + count ≤ n)
    (impl : QueryImpl (ambient + challengeSpec oracleSig (protocol R deg count))
      (StateT σ ProbComp))
    (stmt : RoundStatement R n ⟨start, by omega⟩)
    (h : indexedRelation D _ stmt p) :
    ∀ result ∈ support (intervalExperiment init impl
      ((intervalVerifier R deg n D ambient start count bound).run stmt (fun _ => p)
        (intervalProver D p count (intervalInitial start count bound stmt)))),
      ∃ t, result.2.2 = some (t, fun _ => p) ∧ indexedRelation D _ t p := by
  rw [intervalVerifier_honest_run D p ambient start count bound stmt h, intervalExperiment_map,
    MonadAttach.support_map]
  rintro result ⟨chals, _, rfl⟩
  exact ⟨_, rfl, (intervalVerdict_honest D p count _ h chals).2⟩

/-- The actual honest interval run accepts a true endpoint claim with probability one. -/
theorem intervalVerifier_perfectCompleteness {ι σ : Type} (ambient : OracleSpec ι)
    (init : ProbComp σ)
    (start count : ℕ) (bound : start + count ≤ n)
    (impl : QueryImpl (ambient + challengeSpec oracleSig (protocol R deg count))
      (StateT σ ProbComp))
    (stmt : RoundStatement R n ⟨start, by omega⟩)
    (h : indexedRelation D _ stmt p) :
    Pr{let result ← (intervalExperiment init impl
      ((intervalVerifier R deg n D ambient start count bound).run stmt (fun _ => p)
        (intervalProver D p count (intervalInitial start count bound stmt))))}[
      ∃ t, result.2.2 = some (t, fun _ => p) ∧ indexedRelation D _ t p] = 1 :=
  prEvent_eq_one_of_forall_mem_support _ _
    (intervalVerifier_supportCompleteness D p ambient init start count bound impl stmt h)

/-- At a suffix endpoint the accepted relation is evaluation at the full challenge prefix. -/
theorem intervalVerifier_evaluation {ι σ : Type} (ambient : OracleSpec ι)
    (init : ProbComp σ) (start count : ℕ) (finish : start + count = n)
    (impl : QueryImpl (ambient + challengeSpec oracleSig (protocol R deg count))
      (StateT σ ProbComp))
    (stmt : RoundStatement R n ⟨start, by omega⟩)
    (h : indexedRelation D _ stmt p) :
    ∀ result ∈ support (intervalExperiment init impl
      ((intervalVerifier R deg n D ambient start count finish.le).run stmt (fun _ => p)
        (intervalProver D p count (intervalInitial start count finish.le stmt)))),
      ∃ t, result.2.2 = some (t, fun _ => p) ∧
        p.val.eval (t.challenges ∘ Fin.cast (by change n = count + start; omega)) = t.target := by
  have hn : n = count + start := by omega
  subst hn
  intro result hr
  obtain ⟨t, ht, hrel⟩ := intervalVerifier_supportCompleteness D p ambient init start count
    (by omega) impl stmt h result hr
  exact ⟨t, ht, (indexedRelation_last D t p).mp hrel⟩

/-- The measure of valid acceptance is one for every bounded honest interval. -/
theorem intervalVerifier_measureCompleteness {ι σ : Type} (ambient : OracleSpec ι)
    (init : ProbComp σ) (start count : ℕ) (bound : start + count ≤ n)
    (impl : QueryImpl (ambient + challengeSpec oracleSig (protocol R deg count))
      (StateT σ ProbComp))
    (stmt : RoundStatement R n ⟨start, by omega⟩)
    (h : indexedRelation D _ stmt p) :
    𝒟[(fun result => ∃ t, result.2.2 = some (t, fun _ => p) ∧ indexedRelation D _ t p) <$>
      intervalExperiment init impl
        ((intervalVerifier R deg n D ambient start count bound).run stmt (fun _ => p)
          (intervalProver D p count (intervalInitial start count bound stmt)))] {True} = 1 := by
  rw [← prEvent_eq_evalDist_map]
  exact intervalVerifier_perfectCompleteness D p ambient init start count bound impl stmt h

/-- Perfect completeness for any list domain retains every occurrence of every point. -/
theorem intervalVerifier_perfectCompleteness_list (domain : List R)
    {ι σ : Type} (ambient : OracleSpec ι) (init : ProbComp σ)
    (start count : ℕ) (bound : start + count ≤ n)
    (impl : QueryImpl (ambient + challengeSpec oracleSig (protocol R deg count))
      (StateT σ ProbComp))
    (stmt : RoundStatement R n ⟨start, by omega⟩)
    (h : indexedRelation domain.get _ stmt p) :
    Pr{let result ← (intervalExperiment init impl
      ((intervalVerifier R deg n domain.get ambient start count bound).run stmt (fun _ => p)
        (intervalProver domain.get p count (intervalInitial start count bound stmt))))}[
      ∃ t, result.2.2 = some (t, fun _ => p) ∧ indexedRelation domain.get _ t p] = 1 :=
  intervalVerifier_perfectCompleteness domain.get p ambient init start count bound impl stmt h

/-- The injective-domain completeness theorem specializes the indexed-domain theorem. -/
theorem intervalVerifier_perfectCompleteness_injective (embedding : Fin d ↪ R)
    {ι σ : Type} (ambient : OracleSpec ι) (init : ProbComp σ)
    (start count : ℕ) (bound : start + count ≤ n)
    (impl : QueryImpl (ambient + challengeSpec oracleSig (protocol R deg count))
      (StateT σ ProbComp))
    (stmt : RoundStatement R n ⟨start, by omega⟩)
    (h : indexedRelation (⇑embedding) _ stmt p) :
    Pr{let result ← (intervalExperiment init impl
      ((intervalVerifier R deg n (⇑embedding) ambient start count bound).run stmt (fun _ => p)
        (intervalProver (⇑embedding) p count (intervalInitial start count bound stmt))))}[
      ∃ t, result.2.2 = some (t, fun _ => p) ∧ indexedRelation (⇑embedding) _ t p] = 1 :=
  intervalVerifier_perfectCompleteness (⇑embedding) p ambient init start count bound impl stmt h

end Sumcheck.Core
