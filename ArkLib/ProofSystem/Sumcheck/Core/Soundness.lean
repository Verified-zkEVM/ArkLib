/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Core.Indexed

/-! # Native Sumcheck soundness over indexed domains

The verifier counts each domain index, including repeated evaluation points. A false current
sum becomes true only at an agreement point of unequal degree-bounded polynomials. The core
round-by-round implication bounds the actual run of every prover by `n * (deg / |R|)`.
-/

@[expose] public section

namespace Sumcheck.Core
open Polynomial MvPolynomial PFunctor FreeM Interaction.Core Interaction.TwoParty.Lens
  Interaction.Oracle OracleComp OracleSpec
open scoped ENNReal NNReal

variable {R : Type} [CommSemiring R] [DecidableEq R] [SampleableType R] [IsDomain R]
  [Fintype R] {deg n d : ℕ} (D : Fin d → R) {ι σ : Type} (ambient : OracleSpec ι)
  (init : ProbComp σ) (impl : QueryImpl ambient (StateT σ ProbComp))

/-- Native soundness of the actual Sumcheck run against every prover, with one error per round. -/
theorem verifier_soundness :
    (indexedVerifier R deg n D ambient).soundness init impl
      (indexedDraw (R := R) (deg := deg) n)
      (indexedInputProblem D) (indexedOutputProblem (R := R) (deg := deg) (n := n))
      (n • (((deg : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞)) := by
  simpa only [nsmul_eq_mul] using indexedVerifier_soundness D ambient init impl

/-- The full-run error is `n * (deg / |R|)`, without any distinctness hypothesis on the domain. -/
theorem verifier_soundness_rounds :
    (indexedVerifier R deg n D ambient).soundness init impl
      (indexedDraw (R := R) (deg := deg) n)
      (indexedInputProblem D) (indexedOutputProblem (R := R) (deg := deg) (n := n))
      ((n : ℝ≥0∞) * (((deg : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞)) :=
  indexedVerifier_soundness D ambient init impl

/-- A list domain retains all occurrences of each point in the actual verifier run. -/
theorem verifier_soundness_list (domain : List R) :
    (indexedVerifier R deg n domain.get ambient).soundness init impl
      (indexedDraw (R := R) (deg := deg) n)
      (indexedInputProblem domain.get) (indexedOutputProblem (R := R) (deg := deg) (n := n))
      ((n : ℝ≥0∞) * (((deg : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞)) :=
  indexedVerifier_soundness domain.get ambient init impl

/-- The injective-domain corollary uses exactly the same native verifier and proof. -/
theorem verifier_soundness_injective (embedding : Fin d ↪ R) :
    (indexedVerifier R deg n (⇑embedding) ambient).soundness init impl
      (indexedDraw (R := R) (deg := deg) n)
      (indexedInputProblem (⇑embedding)) (indexedOutputProblem (R := R) (deg := deg) (n := n))
      ((n : ℝ≥0∞) * (((deg : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞)) :=
  indexedVerifier_soundness (⇑embedding) ambient init impl

/-- The native bound is a probability statement about the accepted verdict of the actual run. -/
theorem verifier_run_soundness
    {Out : PathAlong oracleSig (protocol R deg n) → Type}
    (stmt : RoundStatement R n 0) (data : ∀ i, PolynomialData R n deg i)
    (hfalse : ¬ indexedRelation D 0 stmt (data ()))
    (prover : Prover oracleSig ambient (protocol R deg n) Out) :
    Pr{let obs ← (experiment init impl (indexedDraw (R := R) (deg := deg) n)
      ((indexedVerifier R deg n D ambient).run stmt data prover))}[
        ∃ t, obs.2.2 = some t ∧ (t.2 ()).val.eval t.1.challenges = t.1.target] ≤
      ((n : ℝ≥0∞) * (((deg : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞)) := by
  have h := ((indexedVerifier R deg n D ambient).soundness_iff_soundnessUsing init impl
    (indexedDraw (R := R) (deg := deg) n) (indexedInputProblem D)
    (indexedOutputProblem (R := R) (deg := deg) (n := n)) _).mp
      (verifier_soundness_rounds D ambient init impl)
  have bound := h Out (stmt, data) trivial
    (by simpa [indexedInputProblem, Problem.language] using hfalse) prover
  simpa [indexedOutputProblem, Problem.language] using bound

/-- Sample a possibly failing commitment before the fresh receiver challenge. -/
def randomizedProver {ι : Type} (ambient : OracleSpec ι) {R : Type} [CommSemiring R]
    {deg : ℕ} {Out : Type} (commit : OracleComp ambient (R⦃≤ deg⦄[X]))
    (finish : R → Out) : Prover oracleSig ambient (protocol R deg 1) (fun _ => Out) :=
  commit >>= fun msg => committedProver ambient msg finish

/-- A committed message satisfies the native one-round bound over every indexed domain. -/
theorem committed_soundness {Out : Type} (msg : R⦃≤ deg⦄[X]) (finish : R → Out)
    (stmt : RoundStatement R 1 0) (data : ∀ i, PolynomialData R 1 deg i)
    (hfalse : ¬ indexedRelation D 0 stmt (data ())) :
    Pr{let obs ← (experiment init impl (indexedDraw (R := R) (deg := deg) 1)
      ((indexedVerifier R deg 1 D ambient).run stmt data (committedProver ambient msg finish)))}[
        ∃ t, obs.2.2 = some t ∧ (t.2 ()).val.eval t.1.challenges = t.1.target] ≤
      (((deg : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞) := by
  simpa only [Nat.cast_one, one_mul] using
    verifier_run_soundness D ambient init impl stmt data hfalse (committedProver ambient msg finish)

/-- An ambient randomized commitment satisfies the same native actual-run bound.
The commitment may fail and may change shared state before the fresh challenge is drawn. -/
theorem randomized_soundness {Out : Type} (commit : OracleComp ambient (R⦃≤ deg⦄[X]))
    (finish : R → Out) (stmt : RoundStatement R 1 0) (data : ∀ i, PolynomialData R 1 deg i)
    (hfalse : ¬ indexedRelation D 0 stmt (data ())) :
    Pr{let obs ← (experiment init impl (indexedDraw (R := R) (deg := deg) 1)
      ((indexedVerifier R deg 1 D ambient).run stmt data
        (randomizedProver ambient commit finish)))}[
        ∃ t, obs.2.2 = some t ∧ (t.2 ()).val.eval t.1.challenges = t.1.target] ≤
      (((deg : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞) := by
  simpa only [Nat.cast_one, one_mul] using
    verifier_run_soundness D ambient init impl stmt data hfalse
      (randomizedProver ambient commit finish)

/-- The committed-message bound also holds for the measure of valid accepted outputs. -/
theorem committed_measureSoundness {Out : Type} (msg : R⦃≤ deg⦄[X]) (finish : R → Out)
    (stmt : RoundStatement R 1 0) (data : ∀ i, PolynomialData R 1 deg i)
    (hfalse : ¬ indexedRelation D 0 stmt (data ())) :
    letI : MeasurableSpace (Observation oracleSig (protocol R deg 1) (fun _ => Out)
      (fun _ => RoundStatement R 1 (Fin.last 1) × (∀ i, PolynomialData R 1 deg i))) := ⊤
    𝒟[experiment init impl (indexedDraw (R := R) (deg := deg) 1)
      ((indexedVerifier R deg 1 D ambient).run stmt data (committedProver ambient msg finish))]
      {obs | ∃ t, obs.2.2 = some t ∧ (t.2 ()).val.eval t.1.challenges = t.1.target} ≤
        (((deg : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞) := by
  let : MeasurableSpace (Observation oracleSig (protocol R deg 1) (fun _ => Out)
    (fun _ => RoundStatement R 1 (Fin.last 1) × (∀ i, PolynomialData R 1 deg i))) := ⊤
  rw [← prEvent_eq_evalDist_of_discrete]
  exact committed_soundness D ambient init impl msg finish stmt data hfalse

/-- A randomized commitment has the same measure bound, including ambient failure and state. -/
theorem randomized_measureSoundness {Out : Type} (commit : OracleComp ambient (R⦃≤ deg⦄[X]))
    (finish : R → Out) (stmt : RoundStatement R 1 0) (data : ∀ i, PolynomialData R 1 deg i)
    (hfalse : ¬ indexedRelation D 0 stmt (data ())) :
    letI : MeasurableSpace (Observation oracleSig (protocol R deg 1) (fun _ => Out)
      (fun _ => RoundStatement R 1 (Fin.last 1) × (∀ i, PolynomialData R 1 deg i))) := ⊤
    𝒟[experiment init impl (indexedDraw (R := R) (deg := deg) 1)
      ((indexedVerifier R deg 1 D ambient).run stmt data (randomizedProver ambient commit finish))]
      {obs | ∃ t, obs.2.2 = some t ∧ (t.2 ()).val.eval t.1.challenges = t.1.target} ≤
        (((deg : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞) := by
  let : MeasurableSpace (Observation oracleSig (protocol R deg 1) (fun _ => Out)
    (fun _ => RoundStatement R 1 (Fin.last 1) × (∀ i, PolynomialData R 1 deg i))) := ⊤
  rw [← prEvent_eq_evalDist_of_discrete]
  exact randomized_soundness D ambient init impl commit finish stmt data hfalse

end Sumcheck.Core
