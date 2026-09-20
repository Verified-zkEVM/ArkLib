/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Interaction.ArbitraryRounds
public import VCVio.OracleComp.EvalDist.Measure
public import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure

/-!
# Perfect completeness of arbitrary sampled Sumcheck rounds

The common ordered executor propagates a relation invariant through the actual closed claims.
Challenge programs may depend on each reached statement. Completeness is an operational fact:
every possible output of the honest execution is an accepted closed claim, whatever the challenge
programs return. Its probability-one reading follows from the native measure semantics, under
which probabilistic computations never lose mass; verifier rejection remains a returned outcome.
-/

@[expose] public section

namespace Sumcheck.Interaction.MultivariateRound

open OracleComp OracleSpec
open _root_.Interaction.Oracle
open SingleRound

noncomputable section

variable (R : Type) [CommSemiring R] (n deg : ℕ)

/-- Every possible output of the honest sampled execution is an accepted closed claim. -/
theorem executeRoundsSampled_support_completeness [DecidableEq R] {m : ℕ} (D : Fin m ↪ R)
    (start count : ℕ) (bound : start + count ≤ n)
    (stmt : Spec.StatementRound R n ⟨start, by omega⟩)
    (p : Spec.OracleStatement R n deg ())
    (challenges : (i : Fin n) → Spec.StatementRound R n i.castSucc → ProbComp R)
    (h : ((stmt, fun _ => p), ()) ∈ Spec.relationRound R n deg D _) :
    ∀ result ∈ support (executeRoundsSampled R n deg unifSpec start count bound
        (Finset.univ.map D).toList
        ⟨stmt, (polynomialFamily R n deg).behaviorOfRealizations (fun _ => p)⟩
        (honestMessages R n deg D p) challenges),
      result.map (closedRelation R n deg D ⟨start + count, by omega⟩) = some True := by
  let I := roundInterfaces R n deg start count bound
  let stages := roundStages R n deg unifSpec start count bound (Finset.univ.map D).toList
    (honestMessages R n deg D p) challenges
  let Inv : (j : Fin (count + 1)) → (I j).State → Prop := fun _ state =>
    state.1.oracles = (polynomialFamily R n deg).behaviorOfRealizations (fun _ => p) ∧
      ((state.1.stmt, fun _ => p), ()) ∈ Spec.relationRound R n deg D _
  have preserves : ∀ (j : Fin count) (input : (I j.castSucc).State), Inv j.castSucc input →
      ∀ result ∈ support ((stages j).run input),
        ∃ output, result = some output ∧ Inv j.succ output := by
    intro j input hin result hresult
    rcases hin with ⟨himpl, hcurrent⟩
    change result ∈ support ((roundStages R n deg unifSpec start count bound
      (Finset.univ.map D).toList (honestMessages R n deg D p) challenges j).run input) at hresult
    rw [roundStages_honest R n deg unifSpec D start count bound p challenges j input hcurrent,
      support_map] at hresult
    obtain ⟨r, _, rfl⟩ := hresult
    refine ⟨_, rfl, himpl, ?_⟩
    exact relationRound_projected_output R n deg D ⟨start + j, by omega⟩ input.1.stmt p r
  have hrun := OrderedExecution.run_preserves_support count I stages Inv preserves
    (⟨stmt, (polynomialFamily R n deg).behaviorOfRealizations (fun _ => p)⟩, ()) ⟨rfl, h⟩
  intro result hresult
  change result ∈ support
    (Option.map Prod.fst <$> OrderedExecution.run count I stages _) at hresult
  rw [support_map] at hresult
  obtain ⟨full, hfull, rfl⟩ := hresult
  obtain ⟨output, rfl, horacles, hrelation⟩ := hrun full hfull
  simp only [Option.map_some]
  congr 1
  apply propext
  constructor
  · intro _
    trivial
  · intro _
    rcases output with ⟨⟨last, impl⟩, payload⟩
    change impl = (polynomialFamily R n deg).behaviorOfRealizations (fun _ => p) at horacles
    subst impl
    exact hrelation

/-- Perfect completeness of the honest sampled execution: the accepted closed claim is returned
with probability one, for any history-dependent challenge programs. -/
theorem executeRoundsSampled_perfectCompleteness [DecidableEq R] {m : ℕ} (D : Fin m ↪ R)
    (start count : ℕ) (bound : start + count ≤ n)
    (stmt : Spec.StatementRound R n ⟨start, by omega⟩)
    (p : Spec.OracleStatement R n deg ())
    (challenges : (i : Fin n) → Spec.StatementRound R n i.castSucc → ProbComp R)
    (h : ((stmt, fun _ => p), ()) ∈ Spec.relationRound R n deg D _) :
    Pr{let result ← executeRoundsSampled R n deg unifSpec start count bound
        (Finset.univ.map D).toList
        ⟨stmt, (polynomialFamily R n deg).behaviorOfRealizations (fun _ => p)⟩
        (honestMessages R n deg D p) challenges}[
      result.map (closedRelation R n deg D ⟨start + count, by omega⟩) = some True] = 1 :=
  OracleComp.prEvent_eq_one_of_forall_mem_support _ _
    (executeRoundsSampled_support_completeness R n deg D start count bound stmt p challenges h)

/-- Independent uniform receiver challenges are one instance of the sampled executor. -/
theorem executeRounds_uniform_perfectCompleteness [DecidableEq R] [SampleableType R]
    {m : ℕ} (D : Fin m ↪ R) (start count : ℕ) (bound : start + count ≤ n)
    (stmt : Spec.StatementRound R n ⟨start, by omega⟩)
    (p : Spec.OracleStatement R n deg ())
    (h : ((stmt, fun _ => p), ()) ∈ Spec.relationRound R n deg D _) :
    Pr{let result ← executeRoundsSampled R n deg unifSpec start count bound
        (Finset.univ.map D).toList
        ⟨stmt, (polynomialFamily R n deg).behaviorOfRealizations (fun _ => p)⟩
        (honestMessages R n deg D p) (fun _ _ => $ᵗ R)}[
      result.map (closedRelation R n deg D ⟨start + count, by omega⟩) = some True] = 1 :=
  executeRoundsSampled_perfectCompleteness R n deg D start count bound stmt p _ h

end
end Sumcheck.Interaction.MultivariateRound
