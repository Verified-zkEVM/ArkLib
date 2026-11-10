/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.OracleReduction.Execution

/-!
# Challenge handlers for non-interactive execution

A one-message protocol has no verifier challenges. Its challenge handler is unique,
independently of the ambient oracle handler and the target monad.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec

namespace ProtocolSpec

/-- The challenge handler of a one-message, prover-only protocol. -/
def emptyChallengeImpl (Message : Type) (μ : Type → Type) :
    QueryImpl
      ([(⟨!v[.P_to_V], !v[Message]⟩ : ProtocolSpec 1).Challenge]ₒ'challengeOracleInterface) μ :=
  fun q => isEmptyElim q.1

/-- Lifting a random challenge handler adds no behavior to a one-message protocol. -/
theorem addLift_challengeQueryImpl_eq_add_empty
    {ι : Type} {oSpec : OracleSpec ι} {μ : Type → Type} [MonadLiftT ProbComp μ]
    (handler : QueryImpl oSpec μ) (Message : Type)
    [∀ i, SampleableType ((⟨!v[.P_to_V], !v[Message]⟩ : ProtocolSpec 1).Challenge i)] :
    (handler.addLift challengeQueryImpl : QueryImpl
      (oSpec +
        [(⟨!v[.P_to_V], !v[Message]⟩ : ProtocolSpec 1).Challenge]ₒ'challengeOracleInterface) μ) =
      handler + emptyChallengeImpl Message μ := by
  funext q
  rcases q with q | q
  · rfl
  · exact isEmptyElim q.1

end ProtocolSpec
