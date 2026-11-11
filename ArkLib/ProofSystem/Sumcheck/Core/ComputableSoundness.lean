/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Core.ComputableInterval
public import ArkLib.ProofSystem.Sumcheck.Core.IntervalSoundness

/-! # Native suffix soundness for computable message carriers -/

@[expose] public section

namespace Sumcheck.Core
open Polynomial MvPolynomial PFunctor FreeM Interaction.Core Interaction.TwoParty.Lens
  Interaction.Oracle OracleComp OracleSpec
open scoped ENNReal NNReal
variable {R : Type} [CommSemiring R] [DecidableEq R] {deg n d : ℕ}

omit [DecidableEq R] in
/-- Uniform interpreted draws agree with the native mathematical sampler at every node. -/
theorem indexedDraw_eq_interpreted [SampleableType R] (k : ℕ) :
    indexedDraw (R := R) (deg := deg) k =
      Interpreted.draw (evaluate := fun (q : R⦃≤ deg⦄[X]) r => q.val.eval r) ($ᵗ R) k := by
  induction k with
  | zero => funext ⟨node, _⟩; cases node
  | succ k ih =>
    funext ⟨node, h⟩
    rcases node with ⟨⟩ | ⟨⟨⟩, node⟩
    · cases h
    · rcases node with ⟨⟩ | ⟨⟨⟩, node⟩
      · rfl
      · exact congrFun ih ⟨node, h⟩

omit [CommSemiring R] [DecidableEq R] in
/-- Lifting the explicit challenge action lifts the whole fixed-shape draw family. -/
theorem interpretedDraw_lift {M : Type} {evaluate : M → R → R}
    {σ : Type} (next : ProbComp R) (k : ℕ) :
    (fun c => (liftM (Interpreted.draw (evaluate := evaluate) next k c) : StateT σ ProbComp _)) =
      Interpreted.draw (liftM next : StateT σ ProbComp R) k := by
  induction k with
  | zero => funext ⟨node, _⟩; cases node
  | succ k ih =>
    funext ⟨node, h⟩
    rcases node with ⟨⟩ | ⟨⟨⟩, node⟩
    · cases h
    · rcases node with ⟨⟩ | ⟨⟨⟩, node⟩
      · rfl
      · exact congrFun ih ⟨node, h⟩

/-- The closed mathematical executor is the actual interval experiment with transcript erased. -/
theorem interval_closed_execute [SampleableType R] (D : Fin d → R)
    {ι σ Out : Type} (ambient : OracleSpec ι) (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp)) (start count : ℕ) (bound : start + count ≤ n)
    (stmt : RoundStatement R n ⟨start, by omega⟩) (data : ∀ j, PolynomialData R n deg j)
    (prover : Prover oracleSig ambient (protocol R deg count) (fun _ => Out)) :
    (fun obs => (obs.2.1, obs.2.2)) <$> experiment init impl
      (indexedDraw (R := R) (deg := deg) count)
      ((intervalVerifier R deg n D ambient start count bound).run stmt data prover) = (do
        (Interpreted.execute (liftM ($ᵗ R) : StateT σ ProbComp R) (intervalCheck D)
          IntervalClaim.finish count (intervalInitial start count bound stmt) data
          (Prover.simulate impl prover)).run' (← init)) := by
  rw [← experiment_map, intervalVerifier_run]
  unfold experiment
  rw [indexedDraw_eq_interpreted]
  have h := Interpreted.execute_eq_verifier
    (evaluate := fun (q : R⦃≤ deg⦄[X]) r => q.val.eval r) ambient (polynomialFamily R n deg) impl
    (liftM ($ᵗ R) : StateT σ ProbComp R) (intervalCheck D) IntervalClaim.finish count
    (intervalInitial start count bound stmt) data prover
  simp only [simulateQ_map]
  have hh : QueryImpl.addLift (r := StateT σ ProbComp) impl
      (Interpreted.draw (evaluate := fun (q : R⦃≤ deg⦄[X]) r => q.val.eval r) ($ᵗ R) count) =
      QueryImpl.addLift (r := StateT σ ProbComp) impl
        (Interpreted.draw (evaluate := fun (q : R⦃≤ deg⦄[X]) r => q.val.eval r)
          (liftM ($ᵗ R) : StateT σ ProbComp R) count) := by
    funext q
    rcases q with a | c
    · rfl
    · exact congrFun (interpretedDraw_lift
        (evaluate := fun (q : R⦃≤ deg⦄[X]) r => q.val.eval r) ($ᵗ R) count) c
  rw [hh, h]

end Sumcheck.Core

namespace Sumcheck.Core.Computable
open Polynomial MvPolynomial PFunctor FreeM Interaction.Core Interaction.TwoParty.Lens
  Interaction.Oracle OracleComp OracleSpec
open scoped ENNReal NNReal
variable {R : Type} [CommSemiring R] [DecidableEq R] [SampleableType R] {deg n d : ℕ}

/-- Run the interpreted-message executor with shared ambient state and fresh uniform coins. -/
noncomputable def executeExperiment (D : Fin d → R) {ι σ Out : Type} (ambient : OracleSpec ι)
    (init : ProbComp σ) (impl : QueryImpl ambient (StateT σ ProbComp))
    (start count : ℕ) (bound : start + count ≤ n)
    (stmt : RoundStatement R n ⟨start, by omega⟩) (data : ∀ j, PolynomialData R n deg j)
    (prover : Prover oracleSig ambient (Interpreted.protocol R (Impl.Representation.Message R deg)
      (Impl.Representation.evaluate R deg) count) (fun _ => Out)) :
    ProbComp (Out × Option (RoundStatement R n ⟨count + start, by omega⟩ ×
      (∀ j, PolynomialData R n deg j))) := do
  (Interpreted.execute (liftM ($ᵗ R) : StateT σ ProbComp R) (intervalCheck D)
    IntervalClaim.finish count (intervalInitial start count bound stmt) data
    (Prover.simulate impl prover)).run' (← init)

/-- Interpreting every computational message preserves the actual closed interval experiment. -/
theorem executeExperiment_eq_native [BEq R] [LawfulBEq R] (D : Fin d → R)
    {ι σ Out : Type} (ambient : OracleSpec ι) (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp)) (start count : ℕ) (bound : start + count ≤ n)
    (stmt : RoundStatement R n ⟨start, by omega⟩) (data : ∀ j, PolynomialData R n deg j)
    (prover : Prover oracleSig ambient (Interpreted.protocol R (Impl.Representation.Message R deg)
      (Impl.Representation.evaluate R deg) count) (fun _ => Out)) :
    executeExperiment D ambient init impl start count bound stmt data prover =
      (fun obs => (obs.2.1, obs.2.2)) <$> experiment init impl
        (indexedDraw (R := R) (deg := deg) count)
        ((intervalVerifier R deg n D ambient start count bound).run stmt data
          (Interpreted.transportProver (Impl.Representation.toMessage R deg) count prover)) := by
  rw [interval_closed_execute]
  unfold executeExperiment
  rw [Interpreted.simulate_transport]
  have h := Interpreted.execute_transport
    (evaluateN := fun (q : R⦃≤ deg⦄[X]) r => q.val.eval r)
    (liftM ($ᵗ R) : StateT σ ProbComp R) (intervalCheck D) IntervalClaim.finish
    (Impl.Representation.toMessage R deg)
    (fun q r => (Impl.Representation.evaluate_eq R deg q r).symm)
    count (intervalInitial start count bound stmt) data (Prover.simulate impl prover)
  rw [h]

/-- Every suffix has native soundness against arbitrary computational-message provers. The
original oracle data, all prover effects and private continuations are retained by the bridge. -/
theorem execute_soundness [BEq R] [LawfulBEq R] [IsDomain R] [Fintype R] (D : Fin d → R)
    {ι σ Out : Type} (ambient : OracleSpec ι) (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp)) (start count : ℕ) (finish : start + count = n)
    (stmt : RoundStatement R n ⟨start, by omega⟩) (data : ∀ j, PolynomialData R n deg j)
    (prover : Prover oracleSig ambient (Interpreted.protocol R (Impl.Representation.Message R deg)
      (Impl.Representation.evaluate R deg) count) (fun _ => Out))
    (hfalse : ¬ indexedRelation D _ stmt (data ())) :
    Pr{let result ← (executeExperiment D ambient init impl start count finish.le stmt data prover)}[
      ∃ t, result.2 = some t ∧ indexedRelation D _ t.1 (t.2 ())] ≤
        ((count : ℝ≥0∞) * (((deg : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞)) := by
  rw [executeExperiment_eq_native, prEvent_map]
  have h := ((intervalVerifier R deg n D ambient start count finish.le).soundness_iff_soundnessUsing
    init impl (indexedDraw (R := R) (deg := deg) count)
      (intervalInputProblem D ⟨start, by omega⟩)
      (intervalOutputProblem D ⟨count + start, by omega⟩ count) _).mp
        (intervalVerifier_soundness D ambient init impl start count finish)
  have bound := h (fun _ => Out) (stmt, data) trivial
    (by simpa [intervalInputProblem, Problem.language] using hfalse)
    (Interpreted.transportProver (Impl.Representation.toMessage R deg) count prover)
  simpa [intervalOutputProblem, Problem.language] using bound

end Sumcheck.Core.Computable
