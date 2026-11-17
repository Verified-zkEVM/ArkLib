/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Core.LegacyEquivalence
public import ArkLib.Interaction.Core.Legacy.OracleKnowledge

/-!
# Knowledge soundness of Sumcheck in the interaction layer

The interaction-layer Sumcheck verifier is knowledge sound for the Sumcheck relations, against
every prover, with the legacy error: the sum over the challenges of `deg / |R|`. The result is
transferred from the legacy `Spec.oracleVerifier_knowledgeSoundness` through the equivalence of
`LegacyEquivalence` and the oracle knowledge transfer `oracleKnowledgeSoundness_iff`, with no
loss. The model samples challenges uniformly and the straight-line extractor reads the prover's
output witness.
-/

@[expose] public section

namespace Sumcheck.Core
open scoped ENNReal NNReal
open Polynomial PFunctor FreeM Interaction.Core Interaction.TwoParty.Lens Interaction.Oracle
  OracleComp OracleSpec ProtocolSpec Interaction.Core.Legacy

variable (R : Type) [CommSemiring R] [DecidableEq R] [SampleableType R] (deg n : ℕ)
  {d : ℕ} (D : Fin d ↪ R) {ι : Type} (ambient : OracleSpec ι)
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl ambient (StateT σ ProbComp))

/-- Knowledge soundness of the interaction-layer Sumcheck verifier, with the error of the legacy
Sumcheck: `deg / |R|` for each challenge. -/
theorem verifier_knowledgeSoundness [Fintype R] [IsDomain R] :
    letI : MeasurableSpace (Observation oracleSig (protocol R deg n)
      (fun _ => (Spec.StatementRound R n (Fin.last n) × (∀ i, Spec.OracleStatement R n deg i)) ×
        Unit) (fun _ => Spec.StatementRound R n (Fin.last n) × (∀ i, Spec.OracleStatement R n deg
          i))) := ⊤
    letI : MeasurableSpace Unit := ⊤
    knowledgeSoundness ((verifier R deg n D ambient).classicalModel init impl
        (challengeQueryImpl oracleSig (protocol R deg n)))
      (relProblem (Spec.relationRound R n deg D 0))
      (relProblem (Spec.relationRound R n deg D (Fin.last n)))
      (knowledgeJudgementOn (protocol R deg n) (Spec.relationRound R n deg D (Fin.last n)))
      ((verifier R deg n D ambient).classicalStraightline (fun _ => Unit) init impl
        (challengeQueryImpl oracleSig (protocol R deg n))
        (fun _ (o : (Spec.StatementRound R n (Fin.last n) ×
          (∀ i, Spec.OracleStatement R n deg i)) × Unit) => o.2))
      ((∑ _ : (Spec.pSpec R deg n).ChallengeIdx, (deg : ℝ≥0) / Fintype.card R : ℝ≥0) :
        ℝ≥0∞) := by
  let : ∀ t, Inhabited (ambient.Range t) := fun t => ⟨supportedAnswer init impl t⟩
  rw [challengeQueryImpl_eq_legacy]
  refine ((verifier_agrees R deg n D ambient).knowledgeSoundness_iff (mObs := ⊤)
    (mWit := fun _ => (⊤ : MeasurableSpace Unit)) init impl _ _
    (relProblem (Spec.relationRound R n deg D 0)) _ _ _).mpr ?_
  exact (knowledgeSoundness_cast _ _ _ _ _ _ _ _).mpr
    ((oracleKnowledgeSoundness_iff init impl (Spec.oracleVerifier R deg D n ambient) _ _ _).mpr
      (Spec.oracleVerifier_knowledgeSoundness R deg D n ambient))

end Sumcheck.Core
