/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Core.LegacyEquivalence
public import ArkLib.Interaction.Core.Legacy.OracleSecurity

/-!
# Round-by-round soundness of Sumcheck in the interaction layer

The interaction-layer Sumcheck verifier is round-by-round knowledge sound and round-by-round sound
for the Sumcheck relations, with error `deg / |R|` at every challenge node, against every prover.
Both results are transferred from the legacy `Spec.oracleVerifier_rbrKnowledgeSoundness` (and,
for soundness, its legacy consequence `Verifier.rbrSoundness_of_rbrKnowledgeSoundness`) through
the equivalence of `LegacyEquivalence` and the round-by-round transfers
`embedOracleVerifier_rbrKnowledgeSoundness` and `embedOracleVerifier_rbrSoundness`, with no loss.

A round-by-round transfer into the interaction layer needs a terminal certificate for every state
function. For soundness, on a full transcript where the state function is false, the legacy
verifier accepts into no output of the output language. For knowledge soundness, if the legacy
verifier can accept an output related to an output witness, then the knowledge state function
holds at the full transcript of the extracted witness. Neither certificate asks the verifier to
reject every false terminal state. The legacy Sumcheck verifier has a guarded form,
`Spec.oracleVerifierGuardedForm`, so the certificates are the guarded ones,
`StateTerminalCertificate.of_guarded` and `KnowledgeTerminalCertificate.of_guarded`.

The statements need no inhabitance assumption on the ambient oracle: the proofs answer the
embedding's dropped ambient queries with `supportedAnswer`, an answer that `impl` can give.
-/

@[expose] public section

namespace Sumcheck.Core
open scoped ENNReal NNReal
open Polynomial PFunctor FreeM Interaction.Core Interaction.TwoParty.Lens Interaction.Oracle
  OracleComp OracleSpec ProtocolSpec Interaction.Core.Legacy

variable (R : Type) [CommSemiring R] [DecidableEq R] [SampleableType R] (deg n : ℕ)
  {d : ℕ} (D : Fin d ↪ R) {ι : Type} (ambient : OracleSpec ι)
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl ambient (StateT σ ProbComp))

include init in
/-- Round-by-round knowledge soundness of the interaction-layer Sumcheck verifier, with error
`deg / |R|` at every challenge node. -/
theorem verifier_rbrKnowledgeSoundness [Fintype R] [IsDomain R] :
    (verifier R deg n D ambient).rbrKnowledgeSoundness impl (fun _ => True)
      (fun stmt w => (stmt, w) ∈ Spec.relationRound R n deg D 0)
      (fun _ t w => (t, w) ∈ Spec.relationRound R n deg D (Fin.last n))
      (challengeQueryImpl oracleSig (protocol R deg n))
      (fun _ => (((deg : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞)) := by
  let : ∀ t, Inhabited (ambient.Range t) := fun t => ⟨supportedAnswer init impl t⟩
  rw [challengeQueryImpl_eq_legacy, ← OracleVerifier.eqRec_const (protocol_eq R deg n).symm,
    (verifier_agrees R deg n D ambient).rbrKnowledgeSoundness_iff]
  refine (OracleVerifier.rbrKnowledgeSoundness_cast _ _ _ _ _ _ _ _).mpr ?_
  exact embedOracleVerifier_rbrKnowledgeSoundness init impl (Spec.oracleVerifier R deg D n ambient)
    _ _ _ (fun _ _ K => KnowledgeTerminalCertificate.of_guarded
      (Spec.oracleVerifierGuardedForm R deg D n ambient) K)
    (Spec.oracleVerifier_rbrKnowledgeSoundness R deg D n ambient)

include init in
/-- Round-by-round soundness of the interaction-layer Sumcheck verifier, with error `deg / |R|`
at every challenge node. -/
theorem verifier_rbrSoundness [Fintype R] [IsDomain R] :
    (verifier R deg n D ambient).rbrSoundness impl
      (langProblem (Spec.relationRound R n deg D 0).language)
      (langProblem (Spec.relationRound R n deg D (Fin.last n)).language)
      (challengeQueryImpl oracleSig (protocol R deg n))
      (fun _ => (((deg : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞)) := by
  let : ∀ t, Inhabited (ambient.Range t) := fun t => ⟨supportedAnswer init impl t⟩
  rw [challengeQueryImpl_eq_legacy, ← OracleVerifier.eqRec_const (protocol_eq R deg n).symm,
    (verifier_agrees R deg n D ambient).rbrSoundness_iff]
  refine (OracleVerifier.rbrSoundness_cast _ _ _ _ _ _ _).mpr ?_
  simpa only [OracleVerifier.langProblem_cast, Spec.polynomialFamily, family] using
    embedOracleVerifier_rbrSoundness init impl (Spec.oracleVerifier R deg D n ambient)
    _ _ _ (fun S => StateTerminalCertificate.of_guarded
      (Spec.oracleVerifierGuardedForm R deg D n ambient) S)
    (_root_.Verifier.rbrSoundness_of_rbrKnowledgeSoundness (init := init) (impl := impl)
      (Spec.oracleVerifier_rbrKnowledgeSoundness R deg D n ambient))

end Sumcheck.Core
