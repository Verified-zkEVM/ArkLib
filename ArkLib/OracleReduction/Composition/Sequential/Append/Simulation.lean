/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.OracleReduction.Composition.Sequential.Append.Execution

/-!
# Simulation of sequential composition

The explicit left and right challenge inclusions preserve simulation exactly. These identities
include any oracle state: no reset or assumption that the oracle is stateless is needed.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec

variable {ι : Type} {oSpec : OracleSpec ι}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, SampleableType (pSpec₁.Challenge i)]
  [∀ i, SampleableType (pSpec₂.Challenge i)]
  {M : Type → Type} [Monad M] [LawfulMonad M]
  [MonadLiftT ProbComp M] [LawfulMonadLiftT ProbComp M]

namespace ProtocolSpec

/-- Simulating a left-component computation after its challenge inclusion is exactly the
component simulation, including all effects of the shared oracle implementation. -/
theorem simulateQ_liftAppendLeft (impl : QueryImpl oSpec M) {α : Type}
    (oa : OracleComp (oSpec + [pSpec₁.Challenge]ₒ) α) :
    simulateQ (impl.addLift (challengeQueryImpl (pSpec := pSpec₁ ++ₚ pSpec₂)) :
      QueryImpl _ M) (liftAppendLeft pSpec₂ oa) =
    simulateQ (impl.addLift (challengeQueryImpl (pSpec := pSpec₁)) : QueryImpl _ M) oa := by
  unfold liftAppendLeft
  apply QueryImpl.simulateQ_liftM_eq_of_query
  intro t
  rcases t with t | ⟨i, ⟨⟩⟩
  · change simulateQ _ (liftM ((oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).query
        (Sum.inl t))) = impl t
    simp
  · change simulateQ _ (cast (challenge_append_inl (pSpec₂ := pSpec₂) i) <$>
        (liftM ((oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).query
          (Sum.inr ⟨ChallengeIdx.inl i, ()⟩)))) = liftM ($ᵗ (pSpec₁.Challenge i))
    rw [simulateQ_map]
    trans cast (challenge_append_inl (pSpec₂ := pSpec₂) i) <$>
      (liftM ($ᵗ ((pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inl i))) : M _)
    · congr 1
      exact simulateQ_spec_query
        (impl.addLift (challengeQueryImpl (pSpec := pSpec₁ ++ₚ pSpec₂)) : QueryImpl _ M)
        (Sum.inr ⟨ChallengeIdx.inl i, ()⟩)
    · rw [← liftM_map, uniformSample_challenge_append_inl]

/-- Simulating a right-component computation after its challenge inclusion is exactly the
component simulation. The inclusion is pinned explicitly, even when both protocols coincide. -/
theorem simulateQ_liftAppendRight (impl : QueryImpl oSpec M) {α : Type}
    (oa : OracleComp (oSpec + [pSpec₂.Challenge]ₒ) α) :
    simulateQ (impl.addLift (challengeQueryImpl (pSpec := pSpec₁ ++ₚ pSpec₂)) :
      QueryImpl _ M) (liftAppendRight pSpec₁ oa) =
    simulateQ (impl.addLift (challengeQueryImpl (pSpec := pSpec₂)) : QueryImpl _ M) oa := by
  unfold liftAppendRight
  apply QueryImpl.simulateQ_liftM_eq_of_query
  intro t
  rcases t with t | ⟨i, ⟨⟩⟩
  · change simulateQ _ (liftM ((oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).query
        (Sum.inl t))) = impl t
    simp
  · change simulateQ _ (cast (challenge_append_inr (pSpec₁ := pSpec₁) i) <$>
        (liftM ((oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).query
          (Sum.inr ⟨ChallengeIdx.inr i, ()⟩)))) = liftM ($ᵗ (pSpec₂.Challenge i))
    rw [simulateQ_map]
    trans cast (challenge_append_inr (pSpec₁ := pSpec₁) i) <$>
      (liftM ($ᵗ ((pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr i))) : M _)
    · congr 1
      exact simulateQ_spec_query
        (impl.addLift (challengeQueryImpl (pSpec := pSpec₁ ++ₚ pSpec₂)) : QueryImpl _ M)
        (Sum.inr ⟨ChallengeIdx.inr i, ()⟩)
    · rw [← liftM_map, uniformSample_challenge_append_inr]

end ProtocolSpec

namespace Prover

variable {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}

/-- Simulating an appended prover factors into its two component simulations in the same
monad. For stateful implementations, the second component receives the first component's
final oracle state. The seam condition permits effectful left output when the second
protocol is empty or begins with a prover message. -/
theorem simulateQ_append_run_of_seam
    (P₁ : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (P₂ : Prover oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (hSeam : ∀ hn : 0 < n, P₁.OutputIsPure ∨ pSpec₂.dir ⟨0, hn⟩ = .P_to_V)
    (impl : QueryImpl oSpec M) (stmt : Stmt₁) (wit : Wit₁) :
    simulateQ (impl.addLift (challengeQueryImpl (pSpec := pSpec₁ ++ₚ pSpec₂)) :
      QueryImpl _ M) ((P₁.append P₂).run stmt wit) = (do
        let ⟨tr₁, stmt₂, wit₂⟩ ← simulateQ
          (impl.addLift (challengeQueryImpl (pSpec := pSpec₁)) : QueryImpl _ M)
          (P₁.run stmt wit)
        let ⟨tr₂, stmt₃, wit₃⟩ ← simulateQ
          (impl.addLift (challengeQueryImpl (pSpec := pSpec₂)) : QueryImpl _ M)
          (P₂.run stmt₂ wit₂)
        return ⟨tr₁ ++ₜ tr₂, stmt₃, wit₃⟩) := by
  rw [append_run_of_seam hSeam]
  simp only [simulateQ_bind, simulateQ_pure, simulateQ_liftAppendLeft,
    simulateQ_liftAppendRight]

/-- Pure left output suffices to factor the simulated prover execution for every second
protocol, preserving the shared oracle state across the two phases. -/
theorem simulateQ_append_run
    (P₁ : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (P₂ : Prover oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    [P₁.OutputIsPure] (impl : QueryImpl oSpec M) (stmt : Stmt₁) (wit : Wit₁) :
    simulateQ (impl.addLift (challengeQueryImpl (pSpec := pSpec₁ ++ₚ pSpec₂)) :
      QueryImpl _ M) ((P₁.append P₂).run stmt wit) = (do
        let ⟨tr₁, stmt₂, wit₂⟩ ← simulateQ
          (impl.addLift (challengeQueryImpl (pSpec := pSpec₁)) : QueryImpl _ M)
          (P₁.run stmt wit)
        let ⟨tr₂, stmt₃, wit₃⟩ ← simulateQ
          (impl.addLift (challengeQueryImpl (pSpec := pSpec₂)) : QueryImpl _ M)
          (P₂.run stmt₂ wit₂)
        return ⟨tr₁ ++ₜ tr₂, stmt₃, wit₃⟩) :=
  simulateQ_append_run_of_seam P₁ P₂ (fun _ => Or.inl inferInstance) impl stmt wit

variable {σ : Type}

/-- Equality of simulated prover programs at every input and deterministic shared state.
The result includes both transcripts, the output statement and witness, and final state. -/
def SimulatedAppendFactorization
    (P₁ : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (P₂ : Prover oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) : Prop :=
  ∀ stmt wit s,
    (simulateQ (impl.addLift (challengeQueryImpl (pSpec := pSpec₁ ++ₚ pSpec₂)) :
      QueryImpl _ (StateT σ ProbComp)) ((P₁.append P₂).run stmt wit)).run s = (do
        let r₁ ← simulateQ
          (impl.addLift (challengeQueryImpl (pSpec := pSpec₁)) :
            QueryImpl _ (StateT σ ProbComp)) (P₁.run stmt wit)
        let r₂ ← simulateQ
          (impl.addLift (challengeQueryImpl (pSpec := pSpec₂)) :
            QueryImpl _ (StateT σ ProbComp)) (P₂.run r₁.2.1 r₁.2.2)
        pure (r₁.1 ++ₜ r₂.1, r₂.2)).run s

/-- Simulated prover execution factors when the suffix is empty, starts with a prover message,
or follows a prover with pure output. -/
theorem simulatedAppendFactorization_of_seam
    (P₁ : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (P₂ : Prover oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (hSeam : ∀ hn : 0 < n, P₁.OutputIsPure ∨ pSpec₂.dir ⟨0, hn⟩ = .P_to_V)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) :
    P₁.SimulatedAppendFactorization P₂ impl := by
  intro stmt wit s
  rw [simulateQ_append_run_of_seam P₁ P₂ hSeam]

end Prover
