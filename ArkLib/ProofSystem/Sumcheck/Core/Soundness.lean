/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Core.Indexed

/-! # Interaction-layer Sumcheck soundness over indexed domains

Every theorem here concerns the interaction-layer verifier `indexedVerifier`. The compatibility
`verifier` of `Execution` has separate, transferred results in `LegacySoundness`,
`RoundByRound` and `Knowledge`.

The success event is that the run returns a claim satisfying the final evaluation relation: the
retained input polynomial evaluated at the returned challenges equals the returned target.
Soundness bounds the probability of this event from a false input claim. A message can pass
every sum check and still yield a returned claim that fails the final relation, so a returned
claim alone is not the success event.

The argument is the sum-check analysis of [LFKN92], as presented in [Thaler2023], §4.1
(Proposition 4.1, with Remark 4.1 for sums over a finite subset in place of `{0, 1}`). The proof
first checks the remaining sum. A false claim can pass a sum check only when the sent polynomial
differs from the honest one, and the next claim is then true only at an agreement point of two
distinct degree-bounded polynomials. The specialization here differs from the textbook statement
as follows:

* the domain is a map `D : Fin d → R`, so repeated points count with multiplicity;
* the message type `R⦃≤ deg⦄[X]` enforces the degree bound, so the verifier makes no degree check;
* the output relation `indexedOutputProblem` performs the final evaluation check;
* the error denominator is the size of the uniformly sampled challenge type `R`, which is a finite
  commutative semiring with `IsDomain`.

The length `d` of the indexed sum changes the verifier's queries, one per domain index in each
attempted sum check, but not the error `n * (deg / |R|)`.

## References

* [Lund, C., Fortnow, L., Karloff, H., and Nisan, N., *Algebraic methods for interactive
    proof systems*][LFKN92]
* [Thaler, J., *Proofs, Arguments, and Zero-Knowledge*][Thaler2023]
-/

@[expose] public section

namespace Sumcheck.Core
open Polynomial MvPolynomial PFunctor FreeM Interaction.Core Interaction.TwoParty.Lens
  Interaction.Oracle OracleComp OracleSpec
open scoped ENNReal NNReal

variable {R : Type} [CommSemiring R] [DecidableEq R] [SampleableType R] [IsDomain R]
  [Fintype R] {deg n d : ℕ} (D : Fin d → R) {ι σ : Type} (ambient : OracleSpec ι)
  (init : ProbComp σ) (impl : QueryImpl ambient (StateT σ ProbComp))

/-- Soundness of `indexedVerifier` against every prover, with the error written as one
`deg / |R|` per round. `indexedVerifier_soundness` states the same bound as
`n * (deg / |R|)`. -/
theorem indexedVerifier_soundness_nsmul :
    (indexedVerifier R deg n D ambient).soundness init impl
      (indexedDraw (R := R) (deg := deg) n)
      (indexedInputProblem D) (indexedOutputProblem (R := R) (deg := deg) (n := n))
      (n • (((deg : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞)) := by
  simpa only [nsmul_eq_mul] using indexedVerifier_soundness D ambient init impl

/-- Soundness of `indexedVerifier` over a list domain, which keeps every occurrence of each
point. -/
theorem indexedVerifier_soundness_list (domain : List R) :
    (indexedVerifier R deg n domain.get ambient).soundness init impl
      (indexedDraw (R := R) (deg := deg) n)
      (indexedInputProblem domain.get) (indexedOutputProblem (R := R) (deg := deg) (n := n))
      ((n : ℝ≥0∞) * (((deg : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞)) :=
  indexedVerifier_soundness domain.get ambient init impl

/-- Soundness of `indexedVerifier` over an injective domain: the same verifier and proof. -/
theorem indexedVerifier_soundness_injective (embedding : Fin d ↪ R) :
    (indexedVerifier R deg n (⇑embedding) ambient).soundness init impl
      (indexedDraw (R := R) (deg := deg) n)
      (indexedInputProblem (⇑embedding)) (indexedOutputProblem (R := R) (deg := deg) (n := n))
      ((n : ℝ≥0∞) * (((deg : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞)) :=
  indexedVerifier_soundness (⇑embedding) ambient init impl

/-- The `indexedVerifier` bound as a probability on the actual run: from a false input claim, the
run returns a claim satisfying the final evaluation relation with probability at most
`n * (deg / |R|)`, for every prover. -/
theorem indexedVerifier_run_soundness
    {Out : Transcript oracleSig (protocol R deg n) → Type}
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
      (indexedVerifier_soundness D ambient init impl)
  have bound := h Out (stmt, data) trivial
    (by simpa [indexedInputProblem, Problem.language] using hfalse) prover
  simpa [indexedOutputProblem, Problem.language] using bound

/-- Sample a possibly failing commitment before the fresh receiver challenge. -/
def randomizedProver {ι : Type} (ambient : OracleSpec ι) {R : Type} [CommSemiring R]
    {deg : ℕ} {Out : Type} (commit : OracleComp ambient (R⦃≤ deg⦄[X]))
    (finish : R → Out) : Prover oracleSig ambient (protocol R deg 1) (fun _ => Out) :=
  commit >>= fun msg => committedProver ambient msg finish

/-- One round of `indexedVerifier` against a committed message, over every indexed domain. -/
theorem indexedVerifier_committed_soundness {Out : Type}
    (msg : R⦃≤ deg⦄[X]) (finish : R → Out)
    (stmt : RoundStatement R 1 0) (data : ∀ i, PolynomialData R 1 deg i)
    (hfalse : ¬ indexedRelation D 0 stmt (data ())) :
    Pr{let obs ← (experiment init impl (indexedDraw (R := R) (deg := deg) 1)
      ((indexedVerifier R deg 1 D ambient).run stmt data (committedProver ambient msg finish)))}[
        ∃ t, obs.2.2 = some t ∧ (t.2 ()).val.eval t.1.challenges = t.1.target] ≤
      (((deg : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞) := by
  simpa only [Nat.cast_one, one_mul] using
    indexedVerifier_run_soundness D ambient init impl stmt data hfalse
      (committedProver ambient msg finish)

/-- One round of `indexedVerifier` against an ambient randomized commitment. The commitment may
fail and may change shared state before the fresh challenge is drawn. -/
theorem indexedVerifier_randomized_soundness {Out : Type}
    (commit : OracleComp ambient (R⦃≤ deg⦄[X]))
    (finish : R → Out) (stmt : RoundStatement R 1 0) (data : ∀ i, PolynomialData R 1 deg i)
    (hfalse : ¬ indexedRelation D 0 stmt (data ())) :
    Pr{let obs ← (experiment init impl (indexedDraw (R := R) (deg := deg) 1)
      ((indexedVerifier R deg 1 D ambient).run stmt data
        (randomizedProver ambient commit finish)))}[
        ∃ t, obs.2.2 = some t ∧ (t.2 ()).val.eval t.1.challenges = t.1.target] ≤
      (((deg : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞) := by
  simpa only [Nat.cast_one, one_mul] using
    indexedVerifier_run_soundness D ambient init impl stmt data hfalse
      (randomizedProver ambient commit finish)

/-- The committed-message bound for `indexedVerifier`, stated for the measure of the success
event. -/
theorem indexedVerifier_committed_measureSoundness {Out : Type}
    (msg : R⦃≤ deg⦄[X]) (finish : R → Out)
    (stmt : RoundStatement R 1 0) (data : ∀ i, PolynomialData R 1 deg i)
    (hfalse : ¬ indexedRelation D 0 stmt (data ())) :
    letI : MeasurableSpace (Outcome oracleSig (protocol R deg 1) (fun _ => Out)
      (fun _ => RoundStatement R 1 (Fin.last 1) × (∀ i, PolynomialData R 1 deg i))) := ⊤
    𝒟[experiment init impl (indexedDraw (R := R) (deg := deg) 1)
      ((indexedVerifier R deg 1 D ambient).run stmt data (committedProver ambient msg finish))]
      {obs | ∃ t, obs.2.2 = some t ∧ (t.2 ()).val.eval t.1.challenges = t.1.target} ≤
        (((deg : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞) := by
  let : MeasurableSpace (Outcome oracleSig (protocol R deg 1) (fun _ => Out)
    (fun _ => RoundStatement R 1 (Fin.last 1) × (∀ i, PolynomialData R 1 deg i))) := ⊤
  rw [← prEvent_eq_evalDist_of_discrete]
  exact indexedVerifier_committed_soundness D ambient init impl msg finish stmt data hfalse

/-- The randomized-commitment bound for `indexedVerifier`, stated for the measure of the success
event, including ambient failure and state. -/
theorem indexedVerifier_randomized_measureSoundness {Out : Type}
    (commit : OracleComp ambient (R⦃≤ deg⦄[X]))
    (finish : R → Out) (stmt : RoundStatement R 1 0) (data : ∀ i, PolynomialData R 1 deg i)
    (hfalse : ¬ indexedRelation D 0 stmt (data ())) :
    letI : MeasurableSpace (Outcome oracleSig (protocol R deg 1) (fun _ => Out)
      (fun _ => RoundStatement R 1 (Fin.last 1) × (∀ i, PolynomialData R 1 deg i))) := ⊤
    𝒟[experiment init impl (indexedDraw (R := R) (deg := deg) 1)
      ((indexedVerifier R deg 1 D ambient).run stmt data
        (randomizedProver ambient commit finish))]
      {obs | ∃ t, obs.2.2 = some t ∧ (t.2 ()).val.eval t.1.challenges = t.1.target} ≤
        (((deg : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞) := by
  let : MeasurableSpace (Outcome oracleSig (protocol R deg 1) (fun _ => Out)
    (fun _ => RoundStatement R 1 (Fin.last 1) × (∀ i, PolynomialData R 1 deg i))) := ⊤
  rw [← prEvent_eq_evalDist_of_discrete]
  exact indexedVerifier_randomized_soundness D ambient init impl commit finish stmt data hfalse

end Sumcheck.Core
