/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Core.LegacyEquivalence
public import ArkLib.Interaction.Core.Legacy.OracleSecurity

/-!
# Perfect completeness of the embedded legacy honest Sumcheck prover

The embedded legacy honest Sumcheck prover, `legacyProver`, is accepted by the interaction-layer
Sumcheck verifier with probability one on every input in the round-`0` relation, with uniformly
sampled challenges. The prover's output statement equals the accepted statement, and the prover's
output statement and witness lie in the final relation.

The result is transferred from the legacy `Spec.oracleReduction_perfectCompleteness` through the
equivalence of `LegacyEquivalence` and `oracleCompleteness_iff`. It differs from
`perfectCompleteness`, which is proved directly for the interaction-layer honest prover
`honestProver`, for every challenge implementation, and judges only the accepted statement; this
file concerns the legacy honest prover and judges the output witness as well.
-/

@[expose] public section

namespace Sumcheck.Core
open scoped ENNReal NNReal
open Polynomial PFunctor FreeM Interaction.Core Interaction.TwoParty.Lens Interaction.Oracle
  OracleComp OracleSpec ProtocolSpec Interaction.Core.Legacy

variable (R : Type) [CommSemiring R] [DecidableEq R] [SampleableType R] (deg n : ℕ)
  {d : ℕ} (D : Fin d ↪ R) {ι : Type} (ambient : OracleSpec ι) [∀ t, Inhabited (ambient.Range t)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl ambient (StateT σ ProbComp))

/-- Perfect completeness of the embedded legacy honest Sumcheck prover against the
interaction-layer Sumcheck verifier, with uniformly sampled challenges. -/
theorem legacyProver_perfectCompleteness :
    letI : MeasurableSpace (Observation oracleSig (protocol R deg n)
      (fun _ => (Spec.StatementRound R n (Fin.last n) × (∀ i, Spec.OracleStatement R n deg i)) ×
        Unit) (Spec.StatementRound R n (Fin.last n) × (∀ i, Spec.OracleStatement R n deg i))) := ⊤
    completeness ((verifier R deg n D ambient).classicalModel init impl
        (challengeQueryImpl oracleSig (protocol R deg n)))
      (relProblem (Spec.relationRound R n deg D 0))
      (relProblem (Spec.relationRound R n deg D (Fin.last n)))
      (knowledgeJudgement (protocol R deg n) (Spec.relationRound R n deg D (Fin.last n)))
      (legacyProver R deg n D ambient) ((0 : ℝ≥0) : ℝ≥0∞) := by
  rw [challengeQueryImpl_eq_legacy]
  refine ((verifier_agrees R deg n D ambient).completeness_iff (mObs := ⊤) init impl _ _ _ _ _
    _).mpr ?_
  refine (completeness_cast _ _ _ _ _ _ _
    (fun stmt wit => embedOracleProver (Spec.oracleReduction R deg D n ambient).prover
      stmt.1 stmt.2 wit) _).mpr ?_
  exact (oracleCompleteness_iff init impl (Spec.oracleReduction R deg D n ambient) _ _ _).mpr
    (Spec.oracleReduction_perfectCompleteness R deg D n ambient)

end Sumcheck.Core
