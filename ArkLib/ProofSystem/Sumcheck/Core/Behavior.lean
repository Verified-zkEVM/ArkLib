/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Core.IntervalExecution

/-! # Retained arbitrary input behavior at interval boundaries -/

@[expose] public section

namespace Sumcheck.Core
open Polynomial MvPolynomial PFunctor FreeM Interaction.Core Interaction.TwoParty.Lens
  Interaction.Oracle OracleComp OracleSpec

variable {R : Type} [CommSemiring R] {n d deg : ℕ}

/-- The evaluation interface whose data is an arbitrary total function, with no polynomial
realization assumption. -/
def evaluationFamily (R : Type) (X : Type) : OracleFamily Unit (fun _ => X → R) where
  interface _ := { Query := X, toOC := { spec := X →ₒ R, impl x := do return (← read) x } }

/-- The remaining indexed sum of arbitrary original evaluation behavior. -/
noncomputable def behaviorRoundSum (D : Fin d → R) (i : Fin (n + 1)) (c : Fin i → R)
    (evaluate : (Fin n → R) → R) : R :=
  ∑ x : Fin (n - i) → Fin d, evaluate
    (Fin.append c (D ∘ x) ∘ Fin.cast (by have := i.isLt; omega))

/-- A remaining-sum claim for arbitrary total input behavior. -/
def behaviorRoundRelation (D : Fin d → R) (i : Fin (n + 1))
    (stmt : RoundStatement R n i) (evaluate : (Fin n → R) → R) : Prop :=
  behaviorRoundSum D i stmt.challenges evaluate = stmt.target

/-- At the final endpoint an arbitrary-behavior remaining sum is exactly evaluation of that
same behavior at the full prefix. -/
theorem behaviorRoundRelation_last (D : Fin d → R)
    (stmt : RoundStatement R n (Fin.last n)) (evaluate : (Fin n → R) → R) :
    behaviorRoundRelation D (Fin.last n) stmt evaluate ↔
      evaluate stmt.challenges = stmt.target := by
  let : Unique (Fin (n - (Fin.last n).val) → Fin d) := by
    simpa using (show Unique (Fin 0 → Fin d) from
      ⟨⟨Fin.elim0⟩, fun _ => funext fun j => j.elim0⟩)
  unfold behaviorRoundRelation behaviorRoundSum
  rw [Fintype.sum_unique]
  have h : Fin.append stmt.challenges (D ∘ (default : Fin (n - (Fin.last n).val) → Fin d)) ∘
      Fin.cast (show n = n + (n - n) by omega) = stmt.challenges := by
    funext j
    change Fin.append stmt.challenges _ (Fin.cast _ j) = _
    exact Fin.append_left_of_lt j.val (by omega) j.isLt
  change _ = stmt.target ↔ _ = stmt.target
  rw [h]

/-- The mathematical polynomial relation is a specialization of the behavior relation. -/
theorem behaviorRoundRelation_polynomial (D : Fin d → R) (i : Fin (n + 1))
    (stmt : RoundStatement R n i) (p : R⦃≤ deg⦄[X Fin n]) :
    behaviorRoundRelation D i stmt (fun point => p.val.eval point) ↔
      indexedRelation D i stmt p := Iff.rfl

variable [DecidableEq R]

/-- An interval verifier can retain arbitrary original evaluation behavior as its input and
output oracle, because its checks query only the sent messages. -/
def behaviorIntervalVerifier (D : Fin d → R) {ι : Type} (ambient : OracleSpec ι)
    (start count : ℕ) (bound : start + count ≤ n) :
    OracleVerifier ambient (protocol R deg count) (RoundStatement R n ⟨start, by omega⟩)
      (fun _ => RoundStatement R n ⟨count + start, by omega⟩)
      (evaluationFamily R (Fin n → R)) (fun _ => evaluationFamily R (Fin n → R)) where
  decide stmt p v :=
    (foldVerifier R deg ambient (evaluationFamily R (Fin n → R))
      (intervalCheck D) IntervalClaim.finish count).decide
      (intervalInitial start count bound stmt) p v
  outputMap _ _ _ := OracleMap.fst _ _

/-- The arbitrary-behavior interval is the same native passive fold with its original data
retained, without assuming that those answers have a polynomial realization. -/
theorem behaviorIntervalVerifier_run (D : Fin d → R) {ι : Type} (ambient : OracleSpec ι)
    (start count : ℕ) (bound : start + count ≤ n)
    (stmt : RoundStatement R n ⟨start, by omega⟩) (evaluate : (Fin n → R) → R)
    {Out : PathAlong oracleSig (protocol R deg count) → Type}
    (prover : Prover oracleSig ambient (protocol R deg count) Out) :
    (behaviorIntervalVerifier (deg := deg) D ambient start count bound).run stmt
      (fun _ => evaluate) prover =
      (foldVerifier R deg ambient (evaluationFamily R (Fin n → R))
        (intervalCheck D) IntervalClaim.finish count).run
        (intervalInitial start count bound stmt) (fun _ => evaluate) prover := rfl

/-- A one-round interval draws once and retains its original polynomial and private output. -/
theorem behaviorIntervalVerifier_run_one (D : Fin d → R) {ι : Type} (ambient : OracleSpec ι)
    (start : ℕ) (bound : start + 1 ≤ n)
    (stmt : RoundStatement R n ⟨start, by omega⟩) (evaluate : (Fin n → R) → R)
    (msg : R⦃≤ deg⦄[X]) {Out : Type} (finish : R → Out) :
    (behaviorIntervalVerifier (deg := deg) D ambient start 1 bound).run stmt (fun _ => evaluate)
      (committedProver ambient msg finish) =
      (fun r => (⟨roundTranscript msg r, finish r,
        (intervalVerdict D 1 (intervalInitial start 1 bound stmt) (roundTranscript msg r)).map
          (fun t => (t, fun _ => evaluate))⟩ :
          Observation oracleSig (protocol R deg 1) (fun _ => Out)
            (fun _ => RoundStatement R n ⟨1 + start, by omega⟩ ×
              (∀ _ : Unit, (Fin n → R) → R)))) <$>
        (liftM ((ambient + challengeSpec oracleSig (protocol R deg 1)).query
          (.inr (roundChallengeNode (R := R) (deg := deg))))) := by
  rw [behaviorIntervalVerifier_run, Interpreted.verifier_run]
  change (do
    let ⟨tr, out, _⟩ ← Interaction.TwoParty.Lens.run (round R deg)
      (roundProver msg finish) (sampler oracleSig (round R deg) (fun c =>
        liftM ((ambient + challengeSpec oracleSig (protocol R deg 1)).query (.inr c))))
    pure (⟨tr, out, (intervalVerdict D 1 (intervalInitial start 1 bound stmt) tr).map
      (fun t => (t, fun _ => evaluate))⟩ :
          Observation oracleSig (protocol R deg 1) (fun _ => Out)
        (fun _ => RoundStatement R n ⟨1 + start, by omega⟩ ×
          (∀ _ : Unit, (Fin n → R) → R)))) = _
  rw [run_roundProver]
  simp only [bind_map_left, LawfulMonad.pure_bind]
  rw [map_eq_bind_pure_comp]
  rfl

/-- An empty actual run retains arbitrary original behavior, accepts, and executes the prover's
terminal effects and private output. -/
theorem behaviorIntervalVerifier_run_zero (D : Fin d → R) {ι : Type} (ambient : OracleSpec ι)
    (start : ℕ) (bound : start + 0 ≤ n)
    (stmt : RoundStatement R n ⟨start, by omega⟩) (evaluate : (Fin n → R) → R)
    {Out : Type} (prover : OracleComp ambient Out) :
    (behaviorIntervalVerifier (deg := deg) D ambient start 0 bound).run
      (Out := fun _ => Out) stmt (fun _ => evaluate) prover =
      (fun out => (⟨PUnit.unit, out,
        some ((intervalInitial start 0 bound stmt).finish, fun _ => evaluate)⟩ :
          Observation oracleSig (protocol R deg 0) (fun _ => Out)
            (fun _ => RoundStatement R n ⟨0 + start, by omega⟩ ×
              (∀ _ : Unit, (Fin n → R) → R)))) <$>
        simulateQ (fun q => liftM
          ((ambient + challengeSpec oracleSig (protocol R deg 0)).query (.inl q))) prover := by
  rw [behaviorIntervalVerifier_run, Interpreted.verifier_run]
  change (do
    let ⟨tr, out, _⟩ ← Interaction.TwoParty.Lens.run (OutP := fun _ => Out) (OutC := fun _ => PUnit)
      (.pure PUnit.unit) (simulateQ _ prover) (pure PUnit.unit)
    pure (⟨tr, out, some ((intervalInitial start 0 bound stmt).finish, fun _ => evaluate)⟩ :
      Observation oracleSig (protocol R deg 0) (fun _ => Out)
        (fun _ => RoundStatement R n ⟨0 + start, by omega⟩ ×
          (∀ _ : Unit, (Fin n → R) → R)))) = _
  erw [run_done]
  rw [map_eq_bind_pure_comp]
  simp only [LawfulMonad.bind_assoc, LawfulMonad.pure_bind]
  rfl

end Sumcheck.Core
