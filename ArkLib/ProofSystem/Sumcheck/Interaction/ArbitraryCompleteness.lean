/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Sumcheck.Interaction.ArbitraryRounds

/-!
# Perfect completeness of arbitrary sampled Sumcheck rounds

The common ordered executor propagates a relation invariant through the actual closed claims.
Challenge programs may depend on each reached statement. Explicit losslessness hypotheses rule
out missing probability mass; verifier rejection and failed challenge computations remain distinct.
-/

namespace Sumcheck.Interaction.MultivariateRound

open OracleComp OracleSpec
open _root_.Interaction.Oracle
open SingleRound

noncomputable section

variable (R : Type) [CommSemiring R] (n deg : ℕ)

/-- Lossless history-dependent receiver programs give perfect honest completeness. -/
theorem executeRoundsSampled_perfect_completeness [DecidableEq R] {m : ℕ} (D : Fin m ↪ R)
    (start count : ℕ) (bound : start + count ≤ n)
    (stmt : Spec.StatementRound R n ⟨start, by omega⟩)
    (p : Spec.OracleStatement R n deg ())
    (challenges : (i : Fin n) → Spec.StatementRound R n i.castSucc → ProbComp R)
    (lossless : ∀ i current, Pr[⊥ | challenges i current] = 0)
    (h : ((stmt, fun _ => p), ()) ∈ Spec.relationRound R n deg D _) :
    Pr[fun result => result.map (closedRelation R n deg D ⟨start + count, by omega⟩) =
      some True | executeRoundsSampled R n deg unifSpec start count bound
        (Finset.univ.map D).toList ⟨stmt, (family R n deg).answerData (fun _ => p)⟩
        (honestMessages R n deg D p) challenges] = 1 := by
  let I := roundInterfaces R n deg start count bound
  let stages := roundStages R n deg unifSpec start count bound (Finset.univ.map D).toList
    (honestMessages R n deg D p) challenges
  let Inv : (j : Fin (count + 1)) → (I j).State → Prop := fun _ state =>
    state.1.oracles = (family R n deg).answerData (fun _ => p) ∧
      ((state.1.stmt, fun _ => p), ()) ∈ Spec.relationRound R n deg D _
  have preserves : ∀ (j : Fin count) (input : (I j.castSucc).State), Inv j.castSucc input →
      Pr[fun result => ∃ output, result = some output ∧ Inv j.succ output |
        (stages j).run input] = 1 := by
    intro j input hin
    rcases hin with ⟨himpl, hcurrent⟩
    change Pr[fun result => ∃ output, result = some output ∧ Inv j.succ output |
      (roundStages R n deg unifSpec start count bound (Finset.univ.map D).toList
        (honestMessages R n deg D p) challenges j).run input] = 1
    rw [roundStages_honest R n deg unifSpec D start count bound p challenges j input hcurrent]
    apply probEvent_eq_one_iff.mpr
    constructor
    · rw [probFailure_map]
      exact lossless _ _
    · intro result hresult
      rw [support_map] at hresult
      obtain ⟨r, _, rfl⟩ := hresult
      refine ⟨_, rfl, himpl, ?_⟩
      exact relationRound_projected_output R n deg D ⟨start + j, by omega⟩ input.1.stmt p r
  have hrun := OrderedExecution.run_preserves_prob count I stages Inv preserves
    (⟨stmt, (family R n deg).answerData (fun _ => p)⟩, ()) ⟨rfl, h⟩
  obtain ⟨hfailure, hsupport⟩ := probEvent_eq_one_iff.mp hrun
  apply probEvent_eq_one_iff.mpr
  constructor
  · change Pr[⊥ | Option.map Prod.fst <$> OrderedExecution.run count I stages _] = 0
    rw [probFailure_map]
    exact hfailure
  · intro result hresult
    change result ∈ support
      (Option.map Prod.fst <$> OrderedExecution.run count I stages _) at hresult
    rw [support_map] at hresult
    obtain ⟨full, hfull, rfl⟩ := hresult
    obtain ⟨output, rfl, horacles, hrelation⟩ := hsupport full hfull
    simp only [Option.map_some]
    congr 1
    apply propext
    constructor
    · intro _
      trivial
    · intro _
      rcases output with ⟨⟨last, impl⟩, payload⟩
      change impl = (family R n deg).answerData (fun _ => p) at horacles
      subst impl
      exact hrelation

/-- Measure-valued perfect completeness for the actual arbitrary-round sampled executor. -/
theorem executeRoundsSampled_measure_complete [DecidableEq R] {m : ℕ} (D : Fin m ↪ R)
    (start count : ℕ) (bound : start + count ≤ n)
    (stmt : Spec.StatementRound R n ⟨start, by omega⟩)
    (p : Spec.OracleStatement R n deg ())
    (challenges : (i : Fin n) → Spec.StatementRound R n i.castSucc → ProbComp R)
    (lossless : ∀ i current, discreteEvalDist (challenges i current) Set.univ = 1)
    (h : ((stmt, fun _ => p), ()) ∈ Spec.relationRound R n deg D _) :
    discreteEvalDist (executeRoundsSampled R n deg unifSpec start count bound
      (Finset.univ.map D).toList ⟨stmt, (family R n deg).answerData (fun _ => p)⟩
      (honestMessages R n deg D p) challenges)
      {result | result.map (closedRelation R n deg D ⟨start + count, by omega⟩) = some True} =
        1 := by
  let : MeasurableSpace R := ⊤
  have hfailure : ∀ i current, Pr[⊥ | challenges i current] = 0 := by
    intro i current
    have hmass : Pr[fun _ => True | challenges i current] = 1 := by
      rw [probEvent_eq_evalSPMF_toMeasure]
      exact lossless i current
    exact (probEvent_eq_one_iff.mp hmass).1
  let : MeasurableSpace
      (Option (ClosedClaim (Spec.StatementRound R n ⟨start + count, by omega⟩)
        (family R n deg))) := ⊤
  have hprob := executeRoundsSampled_perfect_completeness R n deg D start count bound stmt p
    challenges hfailure h
  rw [probEvent_eq_evalSPMF_toMeasure] at hprob
  exact hprob

/-- Independent uniform receiver challenges satisfy the lossless measure contract. -/
theorem executeRounds_uniform_measure_complete [DecidableEq R] [SampleableType R]
    {m : ℕ} (D : Fin m ↪ R) (start count : ℕ) (bound : start + count ≤ n)
    (stmt : Spec.StatementRound R n ⟨start, by omega⟩)
    (p : Spec.OracleStatement R n deg ())
    (h : ((stmt, fun _ => p), ()) ∈ Spec.relationRound R n deg D _) :
    discreteEvalDist (executeRoundsSampled R n deg unifSpec start count bound
      (Finset.univ.map D).toList ⟨stmt, (family R n deg).answerData (fun _ => p)⟩
      (honestMessages R n deg D p) (fun _ _ => $ᵗ R))
      {result | result.map (closedRelation R n deg D ⟨start + count, by omega⟩) = some True} =
        1 := by
  apply executeRoundsSampled_measure_complete R n deg D start count bound stmt p _ _ h
  intro i current
  let : MeasurableSpace R := ⊤
  have hmass : Pr[fun _ => True | $ᵗ R] = 1 :=
    probEvent_eq_one_iff.mpr ⟨probFailure_uniformSample R, fun _ _ => trivial⟩
  rw [probEvent_eq_evalSPMF_toMeasure] at hmass
  exact hmass

end
end Sumcheck.Interaction.MultivariateRound
