/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Core.IntervalExecution
public import VCVio.OracleComp.EvalDist.Measure

/-! # Soundness of one interval round at an arbitrary variable -/

@[expose] public section

namespace Sumcheck.Core
open scoped ENNReal NNReal
open Polynomial MvPolynomial PFunctor FreeM Interaction.Core Interaction.TwoParty.Lens
  Interaction.Oracle OracleComp OracleSpec
variable {R : Type} [CommSemiring R] [DecidableEq R] {deg n d : ℕ} (D : Fin d → R)

/-- A one-round interval accepts exactly when its indexed message sum is consistent. -/
theorem intervalVerdict_one (i : Fin n) (stmt : RoundStatement R n i.castSucc)
    (q : R⦃≤ deg⦄[X]) (r : R) :
    intervalVerdict D 1 (intervalInitial i.val 1 (by omega) stmt) (roundTranscript q r) =
      if (∑ a : Fin d, q.val.eval (D a)) = stmt.target then
        some (⟨q.val.eval r, Fin.snoc stmt.challenges r ∘ Fin.cast (by
          change 1 + i.val = i.val + 1; omega)⟩ :
          RoundStatement R n ⟨1 + i.val, by omega⟩) else none := by
  unfold intervalVerdict
  dsimp only [roundTranscript]
  rw [foldVerdict_succ]
  dsimp only [headMessage, headChallenge]
  rw [roundVerdict_intervalCheck]
  dsimp only [intervalInitial]
  split <;> rename_i h <;> simp only [h, ite_true, ite_false] <;> rfl

omit [DecidableEq R] in
/-- Truth of an accepted successor is precisely agreement with the honest projection. -/
theorem interval_successor_iff (i : Fin n) (stmt : RoundStatement R n i.castSucc)
    (p : R⦃≤ deg⦄[X Fin n]) (q : R⦃≤ deg⦄[X]) (r : R) :
    indexedRelation D i.succ ⟨q.val.eval r, Fin.snoc stmt.challenges r⟩ p ↔
      (projectedRoundPolynomial D i stmt.challenges p).val.eval r = q.val.eval r := by
  exact iff_of_eq (congrArg (· = q.val.eval r) (roundSum_succ D i stmt.challenges p r))

/-- Close the actual one-round interval run with an explicit challenge implementation. -/
noncomputable def intervalRoundExecute {ι : Type} (ambient : OracleSpec ι)
    {m : Type → Type} [Monad m] (impl : QueryImpl ambient m) (challenge : m R)
    (i : Fin n) (stmt : RoundStatement R n i.castSucc)
    (data : ∀ j, PolynomialData R n deg j) (q : R⦃≤ deg⦄[X]) :
    m (Option (RoundStatement R n ⟨1 + i.val, by omega⟩ ×
      (∀ j, PolynomialData R n deg j))) :=
  (fun obs => obs.2.2) <$> simulateQ (QueryImpl.addLift impl
    (indexedRoundDraw (deg := deg) challenge))
    ((intervalVerifier R deg n D ambient i.val 1 (by omega)).run stmt data
      (committedProver ambient q (fun _ => PUnit.unit)))

/-- The closed run retains the original data in both acceptance and rejection cases. -/
theorem intervalRoundExecute_eq {ι : Type} (ambient : OracleSpec ι)
    {m : Type → Type} [Monad m] [LawfulMonad m] (impl : QueryImpl ambient m) (challenge : m R)
    (i : Fin n) (stmt : RoundStatement R n i.castSucc)
    (data : ∀ j, PolynomialData R n deg j) (q : R⦃≤ deg⦄[X]) :
    intervalRoundExecute D ambient impl challenge i stmt data q =
      (fun r => (intervalVerdict D 1 (intervalInitial i.val 1 (by omega) stmt)
        (roundTranscript q r)).map (fun t => (t, data))) <$> challenge := by
  unfold intervalRoundExecute
  rw [intervalVerifier_run_one, simulateQ_map]
  simp only [Functor.map_map]
  congr 1
  exact QueryImpl.simulateQ_add_query_right _ _ _

/-- Every variable position has the native false-to-true one-round bound. -/
theorem intervalRoundExecute_soundness [IsDomain R] [Fintype R] [SampleableType R]
    (i : Fin n) (stmt : RoundStatement R n i.castSucc)
    (data : ∀ j, PolynomialData R n deg j) (q : R⦃≤ deg⦄[X])
    (hfalse : ¬ indexedRelation D i.castSucc stmt (data ())) :
    Pr{let result ← (intervalRoundExecute D unifSpec (QueryImpl.id' unifSpec) ($ᵗ R)
      i stmt data q)}[result.map (fun t => indexedRelation D _ t.1 (t.2 ())) = some True] ≤
        (((deg : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞) := by
  rw [intervalRoundExecute_eq, prEvent_map]
  refine (prEvent_congr ($ᵗ R) _ _ (fun r => ?_)).trans_le
    (indexed_round_soundness D i stmt (data ()) q hfalse)
  rw [intervalVerdict_one]
  split <;> rename_i h
  · simp only [Option.map_some, Option.some.injEq, h, true_and]
    simp only [eq_iff_iff, iff_true]
    have hi : (⟨1 + i.val, by omega⟩ : Fin (n + 1)) = i.succ := Fin.ext (by
      change 1 + i.val = i.val + 1; omega)
    exact indexedRelation_transport D hi.symm
      (⟨q.val.eval r, Fin.snoc stmt.challenges r⟩ : RoundStatement R n i.succ) (data ())
  · simp only [Option.map_none, reduceCtorEq, h, false_and]

/-- Measure semantics gives the same one-round bound for the actual closed output. -/
theorem intervalRoundExecute_measureSoundness [IsDomain R] [Fintype R] [SampleableType R]
    (i : Fin n) (stmt : RoundStatement R n i.castSucc)
    (data : ∀ j, PolynomialData R n deg j) (q : R⦃≤ deg⦄[X])
    (hfalse : ¬ indexedRelation D i.castSucc stmt (data ())) :
    𝒟[(fun result => result.map (fun t => indexedRelation D _ t.1 (t.2 ())) = some True) <$>
      intervalRoundExecute D unifSpec (QueryImpl.id' unifSpec) ($ᵗ R) i stmt data q] {True} ≤
        (((deg : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞) := by
  rw [← prEvent_eq_evalDist_map]
  exact intervalRoundExecute_soundness D i stmt data q hfalse

end Sumcheck.Core
