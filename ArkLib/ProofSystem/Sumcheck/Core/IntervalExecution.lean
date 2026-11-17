/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Core.Indexed

/-! # Boundary execution equations for Sumcheck intervals -/

@[expose] public section

namespace Sumcheck.Core
open Polynomial MvPolynomial PFunctor FreeM Interaction.Core Interaction.TwoParty.Lens
  Interaction.Oracle OracleComp OracleSpec
variable {R : Type} [CommSemiring R] [DecidableEq R] {deg n d : ℕ} (D : Fin d → R)

/-- A one-round interval draws once and retains its original polynomial and private output. -/
theorem intervalVerifier_run_one {ι : Type} (ambient : OracleSpec ι)
    (start : ℕ) (bound : start + 1 ≤ n)
    (stmt : RoundStatement R n ⟨start, by omega⟩) (data : ∀ i, PolynomialData R n deg i)
    (msg : R⦃≤ deg⦄[X]) {Out : Type} (finish : R → Out) :
    (intervalVerifier R deg n D ambient start 1 bound).run stmt data
      (committedProver ambient msg finish) =
      (fun r => (⟨roundTranscript msg r, finish r,
        (intervalVerdict D 1 (intervalInitial start 1 bound stmt) (roundTranscript msg r)).map
          (fun t => (t, data))⟩ : Observation oracleSig (protocol R deg 1) (fun _ => Out)
            (fun _ => RoundStatement R n ⟨1 + start, by omega⟩ ×
              (∀ i, PolynomialData R n deg i)))) <$>
        (liftM ((ambient + challengeSpec oracleSig (protocol R deg 1)).query
          (.inr (roundChallengeNode (R := R) (deg := deg))))) := by
  rw [intervalVerifier_run, Interpreted.verifier_run]
  change (do
    let ⟨tr, out, _⟩ ← Interaction.TwoParty.Lens.run (round R deg)
      (roundProver msg finish) (sampler oracleSig (round R deg) (fun c =>
        liftM ((ambient + challengeSpec oracleSig (protocol R deg 1)).query (.inr c))))
    pure (⟨tr, out, (intervalVerdict D 1 (intervalInitial start 1 bound stmt) tr).map
      (fun t => (t, data))⟩ : Observation oracleSig (protocol R deg 1) (fun _ => Out)
        (fun _ => RoundStatement R n ⟨1 + start, by omega⟩ ×
          (∀ i, PolynomialData R n deg i)))) = _
  rw [run_roundProver]
  simp only [bind_map_left, LawfulMonad.pure_bind]
  rw [map_eq_bind_pure_comp]
  rfl

/-- An empty interval executes the prover's terminal effects, accepts, and retains the input. -/
theorem intervalVerifier_run_zero {ι : Type} (ambient : OracleSpec ι)
    (start : ℕ) (bound : start + 0 ≤ n)
    (stmt : RoundStatement R n ⟨start, by omega⟩) (data : ∀ i, PolynomialData R n deg i)
    {Out : Type} (prover : OracleComp ambient Out) :
    (intervalVerifier R deg n D ambient start 0 bound).run (Out := fun _ => Out) stmt data prover =
      (fun out => (⟨PUnit.unit, out,
        some ((intervalInitial start 0 bound stmt).finish, data)⟩ :
          Observation oracleSig (protocol R deg 0) (fun _ => Out)
            (fun _ => RoundStatement R n ⟨0 + start, by omega⟩ ×
              (∀ i, PolynomialData R n deg i)))) <$>
        simulateQ (fun q => liftM
          ((ambient + challengeSpec oracleSig (protocol R deg 0)).query (.inl q))) prover := by
  rw [intervalVerifier_run, Interpreted.verifier_run]
  change (do
    let ⟨tr, out, _⟩ ← Interaction.TwoParty.Lens.run (OutP := fun _ => Out) (OutC := fun _ => PUnit)
      (.pure PUnit.unit)
      (simulateQ _ prover) (pure PUnit.unit)
    pure (⟨tr, out, some ((intervalInitial start 0 bound stmt).finish, data)⟩ :
      Observation oracleSig (protocol R deg 0) (fun _ => Out)
        (fun _ => RoundStatement R n ⟨0 + start, by omega⟩ ×
          (∀ i, PolynomialData R n deg i)))) = _
  erw [run_done]
  rw [map_eq_bind_pure_comp]
  simp only [LawfulMonad.bind_assoc, LawfulMonad.pure_bind]
  rfl

end Sumcheck.Core
