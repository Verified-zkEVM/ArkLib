/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Sumcheck.Core.BehaviorComposition
import ArkLib.ProofSystem.Sumcheck.Core.ComputableSoundness
import ArkLib.ProofSystem.Sumcheck.Core.IntervalRoundSoundness
import ArkLib.ProofSystem.Sumcheck.Core.IntervalExecution
import ArkLib.ProofSystem.Sumcheck.Core.IntervalCompleteness
import ArkLib.ProofSystem.Sumcheck.Core.IntervalSoundness
import ArkLib.ProofSystem.Sumcheck.Core.FoldComposition
import ArkLib.ProofSystem.Sumcheck.Core.Projection
import ArkLib.ProofSystem.Sumcheck.Core.IntervalAdaptive
import ArkLib.ProofSystem.Sumcheck.Core.Behavior
import ArkLib.ProofSystem.Sumcheck.Core.InterpretedExecution

/-! # Native interval boundary and security regressions -/

namespace Sumcheck.Core.IntervalTest
open Polynomial MvPolynomial PFunctor FreeM Interaction.Core Interaction.TwoParty.Lens
  Interaction.Oracle OracleComp OracleSpec

noncomputable section

/-- An unused ambient oracle for deterministic native executions. -/
abbrev ambient : OracleSpec Unit := Unit →ₒ Unit

/-- A repeated indexed domain, with both occurrences retained. -/
def repeated : Fin 2 → ℕ := fun _ => 0

/-- A constant honest message over the natural numbers. -/
def zeroMessage : ℕ⦃≤ 0⦄[X] := ⟨0, by simp⟩

/-- The zero input polynomial in three variables. -/
def zeroInput : ℕ⦃≤ 0⦄[X Fin 3] := ⟨0, by simp⟩

/-- A nonzero starting round with its earlier challenge preserved. -/
def initial : RoundStatement ℕ 3 1 := ⟨0, ![7]⟩

/-- A deterministic one-round handler answers with `3` and never samples uniformly. -/
def oneHandler : QueryImpl (ambient + challengeSpec oracleSig (protocol ℕ 0 1)) Id :=
  QueryImpl.addLift (fun _ => (pure () : Id Unit)) (indexedRoundDraw (deg := 0) (pure 3 : Id ℕ))

/-- The nonzero-start transcript accepts and appends its challenge to the earlier prefix. -/
theorem nonzero_verdict :
    intervalVerdict repeated 1 (intervalInitial 1 1 (by decide : 1 + 1 ≤ 3) initial)
      (roundTranscript zeroMessage 3) = some ⟨0, ![7, 3]⟩ := by
  unfold intervalVerdict
  rw [foldVerdict, roundVerdict_intervalCheck]
  simp [repeated, zeroMessage, headMessage, headChallenge, roundTranscript, foldVerdict,
    IntervalClaim.finish, IntervalClaim.next, IntervalClaim.index, intervalInitial, initial]

/-- The actual interval run preserves its private output and the earlier challenge. -/
theorem nonzero_run :
    simulateQ oneHandler ((intervalVerifier ℕ 0 3 repeated ambient 1 1 (by decide)).run
      initial (fun _ => zeroInput) (committedProver ambient zeroMessage (fun _ => 37))) =
      ⟨roundTranscript zeroMessage 3, 37, some (⟨0, ![7, 3]⟩, fun _ => zeroInput)⟩ := by
  rw [intervalVerifier_run_one, simulateQ_map]
  change (⟨roundTranscript zeroMessage 3, 37,
    (intervalVerdict repeated 1 (intervalInitial 1 1 (by decide) initial)
      (roundTranscript zeroMessage 3)).map (fun t => (t, fun _ => zeroInput))⟩ :
      Observation oracleSig (protocol ℕ 0 1) (fun _ => ℕ)
        (fun _ => RoundStatement ℕ 3 2 × (∀ i, PolynomialData ℕ 3 0 i))) = _
  rw [nonzero_verdict]
  rfl

/-- A bad claim at a nonzero start rejects even with a correct degree-bounded message. -/
theorem nonzero_rejects :
    intervalVerdict repeated 1 (intervalInitial 1 1 (by decide : 1 + 1 ≤ 3)
      (⟨1, ![7]⟩ : RoundStatement ℕ 3 1)) (roundTranscript zeroMessage 3) = none := by
  unfold intervalVerdict
  rw [foldVerdict, roundVerdict_intervalCheck]
  simp [repeated, zeroMessage, headMessage, roundTranscript, intervalInitial]

/-- Zero rounds accept the unchanged endpoint claim without issuing a challenge. -/
theorem zero_count :
    (intervalVerdict repeated (deg := 0) 0
      (intervalInitial 1 0 (by decide : 1 + 0 ≤ 3) initial) PUnit.unit).map
        (fun t => (t.target, t.challenges 0)) = some (0, 7) := rfl

/-- The actual empty interval executes its terminal prover action and accepts the same claim. -/
theorem zero_run :
    ((fun obs => (obs.2.1, obs.2.2.map (fun t => (t.1.target, t.1.challenges 0)))) <$>
      (intervalVerifier ℕ 0 3 repeated ambient 1 0 (by decide)).run (Out := fun _ => ℕ)
        initial (fun _ => zeroInput)
        (pure 43 : OracleComp ambient ℕ)) = pure (43, some (0, 7)) := by
  rw [intervalVerifier_run_zero]
  simp only [simulateQ_pure, LawfulApplicative.map_pure]
  rfl

/-- Generic native suffix soundness retains arbitrary nonzero starts and zero counts. -/
example {R : Type} [CommSemiring R] [DecidableEq R] [IsDomain R] [Fintype R]
    [SampleableType R] {n deg d : ℕ} (D : Fin d → R) {ι σ : Type} (a : OracleSpec ι)
    (init : ProbComp σ) (impl : QueryImpl a (StateT σ ProbComp))
    (start count : ℕ) (finish : start + count = n) :
    (intervalVerifier R deg n D a start count finish.le).soundness init impl
      (indexedDraw (R := R) (deg := deg) count)
      (intervalInputProblem D ⟨start, by omega⟩)
      (intervalOutputProblem D ⟨count + start, by omega⟩ count)
      ((count : ENNReal) * (((deg : NNReal) / Fintype.card R : NNReal) : ENNReal)) :=
  intervalVerifier_soundness D a init impl start count finish

end

run_cmd
  for decl in [``Sumcheck.Core.intervalVerifier, ``Sumcheck.Core.intervalVerifier_rbrSoundness,
      ``Sumcheck.Core.intervalVerifier_soundness, ``Sumcheck.Core.intervalVerifier_soundness_list,
      ``Sumcheck.Core.intervalVerifier_soundness_injective,
      ``Sumcheck.Core.intervalVerifier_supportCompleteness,
      ``Sumcheck.Core.intervalVerifier_perfectCompleteness,
      ``Sumcheck.Core.Computable.interpret_intervalHonestProver,
      ``Sumcheck.Core.Computable.execute_perfectCompleteness,
      ``Sumcheck.Core.Computable.execute_soundness,
      ``Sumcheck.Core.intervalRoundExecute_soundness,
      ``Sumcheck.Core.intervalRoundExecute_measureSoundness,
      ``Sumcheck.Core.run_append_behaviorIntervalVerifier,
      ``Sumcheck.Core.intervalVerifier_full_run, ``Sumcheck.Core.run_append_intervalVerifier,
      ``Sumcheck.Core.run_append_public_intervalVerifier,
      ``Sumcheck.Core.intervalVerifier_measureCompleteness,
      ``Sumcheck.Core.intervalVerifier_adaptive_perfectCompleteness,
      ``Sumcheck.Core.intervalVerifier_evaluation,
      ``Sumcheck.Core.behaviorRoundRelation_last,
      ``Sumcheck.Core.behaviorIntervalVerifier_run_zero,
      ``Sumcheck.Core.Interpreted.run_transport,
      ``Sumcheck.Core.projectedMap, ``Sumcheck.Core.simulateQ_projectedQuery,
      ``Sumcheck.Core.projectedExecute_honest_eq, ``Sumcheck.Core.projectedExecute_closed,
      ``Sumcheck.Core.projectedExecute_related, ``Sumcheck.Core.simulateQ_projectedInput,
      ``Sumcheck.Core.IntervalTest.nonzero_run,
      ``Sumcheck.Core.IntervalTest.nonzero_rejects, ``Sumcheck.Core.IntervalTest.zero_run] do
    for ax in ← Lean.collectAxioms decl do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "unexpected axiom {ax} in {decl}"

end Sumcheck.Core.IntervalTest
