/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.FiatShamir.LegacyExecution
public import ArkLib.Interaction.Oracle.Security.StateRestorationQueryBound
public import VCVio.OracleComp.QueryTracking.QueryBound.Simulation

/-!
# Query budgets across the legacy Fiat–Shamir bridge

The legacy prover's challenge calls occupy the left summand; its ambient base oracle is empty.
Private uniform samples occupy the right summand and do not consume the hash budget. The concrete
translation preserves this structural cap, so the native distinct-query estimate can be used with
an ordinary query-budget hypothesis on the original legacy prover.
-/

@[expose] public section

namespace Interaction.Oracle.FiatShamir

open OracleComp OracleSpec ProtocolSpec Security.StateRestoration

/-- Concrete legacy-to-native prover translation preserves the structural hash-query cap. -/
theorem simulateLegacyProver_queryBound {Input W : Type} (rounds : List Round)
    (prover : Prover.StateRestoration.KnowledgeSoundnessWithCoins
      (OracleSpec.ofPFunctor 0) Input W (legacySpec rounds) unifSpec)
    (Q : ℕ) (hbound : prover.IsQueryBoundP (fun q => q.isLeft) Q) :
    (simulateLegacyProver rounds prover).IsQueryBoundP (fun q => q.isRight) Q := by
  unfold simulateLegacyProver simulateLegacyProverWith
  rw [isQueryBoundP_map_iff]
  apply hbound.simulateQ_of_step
  · intro t ht
    cases t with
    | inl t =>
      cases t with
      | inl impossible => nomatch impossible
      | inr key =>
        obtain ⟨native, rfl⟩ := (keyEquiv Input rounds).surjective key
        simp [legacyProverRoute, restorationQueries]
    | inr coin => simp at ht
  · intro t ht
    cases t with
    | inl t => simp at ht
    | inr coin =>
      simp [legacyProverRoute]

/-- A legacy prover hash-query cap bounds the expected number of translated distinct keys. -/
theorem simulateLegacyProver_expectedKeys_le {Input W : Type} [DecidableEq Input]
    (rounds : List Round)
    (prover : Prover.StateRestoration.KnowledgeSoundnessWithCoins
      (OracleSpec.ofPFunctor 0) Input W (legacySpec rounds) unifSpec)
    (Q : ℕ) (hbound : prover.IsQueryBoundP (fun q => q.isLeft) Q) :
    expectedAdversaryFreshKeys rounds (simulateLegacyProver rounds prover) ≤ Q :=
  expectedAdversaryFreshKeys_le_of_queryBound rounds (simulateLegacyProver rounds prover) Q
    (simulateLegacyProver_queryBound rounds prover Q hbound)

end Interaction.Oracle.FiatShamir
