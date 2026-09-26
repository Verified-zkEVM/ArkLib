/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.OrderedSoundness
public import ArkLib.ProofSystem.Sumcheck.Interaction.AdaptiveRounds
public import ArkLib.ProofSystem.Sumcheck.Interaction.MultivariateSoundness

/-!
# Soundness against adaptive randomized Sumcheck messages

Each message kernel sees the current challenge prefix and carried private state, samples its
message and next private state, then the verifier draws a fresh uniform challenge. The actual
ordered executor has error at most `count * (deg / |F|)` from a false initial relation. Rejection
is excluded from the successful event. The input behavior is tied to an original multivariate
polynomial of individual degree at most `deg` and is retained at every actual stage boundary.
-/

@[expose] public section

namespace Sumcheck.Interaction.MultivariateRound

open OracleComp OracleSpec
open _root_.Interaction.Oracle

noncomputable section

variable (n deg : ℕ) (F : Type) [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable (σ : Type) {m : ℕ} (D : Fin m ↪ F)
variable (start count : ℕ) (bound : start + count ≤ n)

/-- Marking oracle mismatch as true makes the stage hypothesis applicable to every state.
An actual stage from matching behavior never produces mismatch. -/
private def guardedRelation (p : Spec.OracleStatement F n deg ())
    (j : Fin (count + 1))
    (state : (adaptiveInterfaces F n deg σ start count bound j).State) : Prop :=
  state.1.oracles ≠ (polynomialFamily F n deg).behaviorOfRealizations (fun _ => p) ∨
    closedRelation F n deg D ⟨start + j, by omega⟩ state.1

private theorem adaptiveStages_soundness
    (p : Spec.OracleStatement F n deg ())
    (messages : (i : Fin n) → Spec.StatementRound F n i.castSucc → σ →
      ProbComp (SingleRound.Message F deg × σ))
    (j : Fin count)
    (input : (adaptiveInterfaces F n deg σ start count bound j.castSucc).State)
    (hfalse : ¬ guardedRelation n deg F σ D start count bound p j.castSucc input) :
    Pr{let result ← (adaptiveStages F n deg σ start count bound
      (Finset.univ.map D).toList messages j).run input}[
      ∃ output, result = some output ∧
        guardedRelation n deg F σ D start count bound p j.succ output] ≤
      (deg : ENNReal) / Fintype.card F := by
  have himpl : input.1.oracles = (polynomialFamily F n deg).behaviorOfRealizations (fun _ => p) :=
    not_not.mp (not_or.mp hfalse).1
  have hrel : ¬ closedRelation F n deg D ⟨start + j, by omega⟩ input.1 :=
    (not_or.mp hfalse).2
  rw [adaptiveStages_run]
  apply prEvent_bind_le_of_forall_le
  intro chosen
  have h := executeCore_sampled_soundness n deg F D ⟨start + j, by omega⟩ input.1.stmt p
    input.1.oracles chosen.1 himpl hrel
  rw [executeCore_sampled_closed_eq, prEvent_map] at h
  simp only [bind_assoc, pure_bind]
  rw [executeCore_sampled_closed_eq, prEvent_map]
  refine (prEvent_congr ($ᵗ F) _ _ ?_).trans_le h
  intro r
  by_cases hcheck : ((Finset.univ.map D).toList.map
      (fun x => chosen.1.val.eval x)).sum = input.1.stmt.target
  · simp only [hcheck, ↓reduceIte, Option.map_some, Option.some.injEq,
      guardedRelation, himpl, eq_iff_iff, iff_true]
    constructor
    · rintro ⟨output, rfl, hbad | htrue⟩
      · exact False.elim (hbad rfl)
      · exact htrue
    · intro htrue
      exact ⟨_, rfl, Or.inr htrue⟩
  · simp only [hcheck, ↓reduceIte, Option.map_none, reduceCtorEq, false_and,
      exists_false]

/-- Every adaptive randomized prover kernel obeys the accumulated error bound.
No soundness assumption on the kernel or intermediate claims is supplied by the caller. -/
theorem executeAdaptiveRounds_soundness
    (p : Spec.OracleStatement F n deg ())
    (input : ClosedClaim (Spec.StatementRound F n ⟨start, by omega⟩) (polynomialFamily F n deg))
    (privateState : σ)
    (messages : (i : Fin n) → Spec.StatementRound F n i.castSucc → σ →
      ProbComp (SingleRound.Message F deg × σ))
    (himpl : input.oracles = (polynomialFamily F n deg).behaviorOfRealizations (fun _ => p))
    (hfalse : ¬ closedRelation F n deg D ⟨start, by omega⟩ input) :
    Pr{let result ← (executeAdaptiveRounds F n deg σ start count bound
      (Finset.univ.map D).toList input privateState messages)}[
      ∃ output, result = some output ∧
        closedRelation F n deg D ⟨start + count, by omega⟩ output.1] ≤
      (count : ENNReal) * ((deg : ENNReal) / Fintype.card F) := by
  let I := adaptiveInterfaces F n deg σ start count bound
  let stages := adaptiveStages F n deg σ start count bound (Finset.univ.map D).toList messages
  let Rel := guardedRelation n deg F σ D start count bound p
  let : ∀ j, MeasurableSpace (I j).State := fun _ => ⊤
  let : ∀ j, DiscreteMeasurableSpace (I j).State := fun _ => ⟨fun _ => trivial⟩
  have hsound : ∀ (j : Fin count) (state : (I j.castSucc).State), ¬ Rel j.castSucc state →
      𝒟[(stages j).run state] {result | ∃ output, result = some output ∧ Rel j.succ output} ≤
        (deg : ENNReal) / Fintype.card F := by
    intro j state hf
    rw [← prEvent_eq_evalDist_of_discrete]
    exact adaptiveStages_soundness n deg F σ D start count bound p messages j state hf
  have h := OrderedExecution.run_soundness_measure count I stages Rel
    (fun _ => (deg : ENNReal) / Fintype.card F) hsound (input, privateState)
    (by simp only [Rel, guardedRelation, himpl, ne_eq, not_true_eq_false, false_or]; exact hfalse)
  rw [← prEvent_eq_evalDist_of_discrete] at h
  refine (prEvent_mono _ _ _ ?_).trans (h.trans_eq ?_)
  · intro result hresult
    obtain ⟨output, rfl, hrel⟩ := hresult
    exact ⟨output, rfl, Or.inr hrel⟩
  · simp [Finset.sum_const, nsmul_eq_mul]

private theorem prEvent_eq_evalDist_map_unifSpec {α : Type} (mx : OracleComp unifSpec α)
    (event : α → Prop) : Pr{let x ← mx}[event x] = 𝒟[event <$> mx] {True} :=
  prEvent_eq_evalDist_map mx event

/-- Native measure formulation of adaptive arbitrary-round soundness, with no countability
requirement on function-valued closed oracle behavior or private state. -/
theorem executeAdaptiveRounds_measureSoundness
    (p : Spec.OracleStatement F n deg ())
    (input : ClosedClaim (Spec.StatementRound F n ⟨start, by omega⟩) (polynomialFamily F n deg))
    (privateState : σ)
    (messages : (i : Fin n) → Spec.StatementRound F n i.castSucc → σ →
      ProbComp (SingleRound.Message F deg × σ))
    (himpl : input.oracles = (polynomialFamily F n deg).behaviorOfRealizations (fun _ => p))
    (hfalse : ¬ closedRelation F n deg D ⟨start, by omega⟩ input) :
    𝒟[(fun result : Option (ClosedClaim (Spec.StatementRound F n ⟨start + count, by omega⟩)
        (polynomialFamily F n deg) × σ) =>
      ∃ output, result = some output ∧
        closedRelation F n deg D ⟨start + count, by omega⟩ output.1) <$>
      executeAdaptiveRounds F n deg σ start count bound
        (Finset.univ.map D).toList input privateState messages] {True} ≤
      (count : ENNReal) * ((deg : ENNReal) / Fintype.card F) := by
  rw [← prEvent_eq_evalDist_map_unifSpec]
  exact executeAdaptiveRounds_soundness n deg F σ D start count bound p input privateState
    messages himpl hfalse

end
end Sumcheck.Interaction.MultivariateRound
