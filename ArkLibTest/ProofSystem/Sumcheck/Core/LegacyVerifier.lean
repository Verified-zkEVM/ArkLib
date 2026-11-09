/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLibTest.ProofSystem.Sumcheck.Core.SingleRound
import ArkLib.ProofSystem.Sumcheck.Core.LegacyEquivalence

/-!
# Legacy verifier regressions through the interaction-core bridge

The wrong-target, zero-message, rejected-sum and nonconstant-message cases are checked on both
the Sumcheck core verifier `verifier` and the embedded legacy verifier `legacyVerifier`, using
the same completed interaction. The legacy-layer test of the same cases remains separate.
All challenges are arbitrary elements of `ZMod 5`, so evaluating a nonconstant message at the
wrong point is observable. The final relation reads the retained input, rather than the message.
-/

namespace Sumcheck.Core.LegacyVerifierTest

open Polynomial PFunctor FreeM Interaction.Core Interaction.TwoParty.Lens Interaction.Oracle
  OracleComp OracleSpec ProtocolSpec SingleRoundTest

noncomputable section

/-- The field of the legacy verifier regressions. -/
abbrev F := ZMod 5

/-- Answer a verifier's decision from its input and the completed round's message. -/
def answered {deg : ℕ}
    (V : OracleVerifier ambient (protocol F deg 1) (Spec.StatementRound F 1 0)
      (Spec.StatementRound F 1 (Fin.last 1)) (Spec.polynomialFamily F 1 deg)
      (Spec.polynomialFamily F 1 deg)) (target : F) (msg : F⦃≤ deg⦄[X]) (r : F) :=
  V.decideWith (claim target) _ (toView _ (tr1 msg r))
    (sumData (fun _ => poly0 deg) (payloads _ (tr1 msg r)))

/-- Both decisions give the legacy fold's verdict on this completed round, as open ambient
programs. This exercises the public bridge on the actual message and input resources. -/
theorem answered_pair {deg : ℕ} (target : F) (msg : F⦃≤ deg⦄[X]) (r : F) :
    answered (verifier F deg 1 D₁ ambient) target msg r =
        pure (legacyVerdict F deg 1 D₁ ambient (claim target) (decodeTranscript 1 (tr1 msg r))) ∧
      answered (legacyVerifier F deg 1 D₁ ambient) target msg r =
        pure (legacyVerdict F deg 1 D₁ ambient (claim target) (decodeTranscript 1 (tr1 msg r))) :=
  decide_ambient_trace F deg 1 D₁ ambient (QueryImpl.id' ambient) (claim target)
    (fun _ => poly0 deg) (tr1 msg r)

/-- A constant message one passes the false claim about input zero. Both decisions return one
at every challenge, rather than the input's evaluation zero. -/
theorem sent_target (r : F) :
    answered (verifier F 0 1 D₁ ambient) 1 (msgOne 0) r =
        pure (some ⟨1, Fin.snoc Fin.elim0 r⟩) ∧
      answered (legacyVerifier F 0 1 D₁ ambient) 1 (msgOne 0) r =
        pure (some ⟨1, Fin.snoc Fin.elim0 r⟩) := by
  have h := answered_pair 1 (msgOne 0) r
  rw [verdict_pass ambient D₁ (claim 1) (msgOne 0) r (by simp [msgOne, claim])] at h
  simpa [msgOne, claim] using h

/-- Changing the target to zero rejects the same message in both verifiers. -/
theorem inconsistent_sum_rejected (r : F) :
    answered (verifier F 0 1 D₁ ambient) 0 (msgOne 0) r = pure none ∧
      answered (legacyVerifier F 0 1 D₁ ambient) 0 (msgOne 0) r = pure none := by
  have h := answered_pair 0 (msgOne 0) r
  rw [verdict_fail ambient D₁ (claim 0) (msgOne 0) r
    (by simpa [msgOne, claim] using (by decide : (1 : F) ≠ 0))] at h
  exact h

/-- The zero message on the true zero claim is accepted by both verifiers. -/
theorem honest_zero_accepted (r : F) :
    answered (verifier F 0 1 D₁ ambient) 0 (0 : F⦃≤ 0⦄[X]) r =
        pure (some ⟨0, Fin.snoc Fin.elim0 r⟩) ∧
      answered (legacyVerifier F 0 1 D₁ ambient) 0 (0 : F⦃≤ 0⦄[X]) r =
        pure (some ⟨0, Fin.snoc Fin.elim0 r⟩) := by
  have h := answered_pair (deg := 0) 0 (0 : F⦃≤ 0⦄[X]) r
  rw [verdict_pass ambient D₁ (claim 0) 0 r (by simp [claim])] at h
  simpa [claim] using h

/-- The degree-one message `X + 1`. -/
def linearMessage : F⦃≤ 1⦄[X] :=
  ⟨X + 1, Submodule.add_mem _ (mem_degreeLE.mpr degree_X_le) (msgOne 1).property⟩

/-- Both decisions evaluate `X + 1` at the supplied challenge, returning `r + 1`. -/
theorem linear_sent_target (r : F) :
    answered (verifier F 1 1 D₁ ambient) 1 linearMessage r =
        pure (some ⟨r + 1, Fin.snoc Fin.elim0 r⟩) ∧
      answered (legacyVerifier F 1 1 D₁ ambient) 1 linearMessage r =
        pure (some ⟨r + 1, Fin.snoc Fin.elim0 r⟩) := by
  have hD (i : Fin 1) : D₁ i = (0 : F) := rfl
  have h := answered_pair (deg := 1) 1 linearMessage r
  rw [verdict_pass (deg := 1) ambient D₁ (claim 1) linearMessage r
    (by simp [linearMessage, hD, claim])] at h
  simpa [linearMessage, claim] using h

/-- In both full runs, acceptance of the cheating constant message produces a false final
relation on the retained zero input. The test reads the verdict returned by each run itself. -/
theorem run_false_relation :
    let read := fun obs : Obs1 (R := F) (deg := 0) F => obs.2.2.map fun out =>
      ((out, ()) ∈ Spec.relationRound F 1 0 D₁ (Fin.last 1))
    let prover := oneRound ambient (msgOne 0) id 0
    read <$> (verifier F 0 1 D₁ ambient).run (claim 1) (fun _ => poly0 0) prover =
        (fun _ => some False) <$> drawChallenges 1 (fun c =>
          liftM ((ambient + challengeSpec oracleSig (protocol F 0 1)).query (.inr c))) ∧
      read <$> (legacyVerifier F 0 1 D₁ ambient).run (claim 1) (fun _ => poly0 0) prover =
        (fun _ => some False) <$> drawChallenges 1 (fun c =>
          liftM ((ambient + challengeSpec oracleSig (protocol F 0 1)).query (.inr c))) := by
  intro read prover
  rw [← (verifier_agrees F 0 1 D₁ ambient).run_eq (claim 1) (fun _ => poly0 0) prover]
  suffices h : read <$> (verifier F 0 1 D₁ ambient).run (claim 1) (fun _ => poly0 0) prover =
      (fun _ => some False) <$> drawChallenges 1 (fun c =>
          liftM ((ambient + challengeSpec oracleSig (protocol F 0 1)).query (.inr c))) from ⟨h, h⟩
  rw [run_oneRound, Functor.map_map]
  refine congrArg (· <$> _) (funext fun chals => ?_)
  dsimp [read, obs1]
  rw [verdict_pass ambient D₁ (claim 1) (msgOne 0) _ (by simp [msgOne, claim])]
  simp only [msgOne, Polynomial.eval_one, Option.map_some]
  congr 1
  apply propext
  exact (Spec.relationRound_last_iff F 1 0 D₁ _ _).trans
    (by simpa [poly0] using (by decide : ¬ (0 : F) = 1))

end

run_cmd
  for decl in [``Sumcheck.Core.LegacyVerifierTest.answered_pair,
      ``Sumcheck.Core.LegacyVerifierTest.sent_target,
      ``Sumcheck.Core.LegacyVerifierTest.inconsistent_sum_rejected,
      ``Sumcheck.Core.LegacyVerifierTest.honest_zero_accepted,
      ``Sumcheck.Core.LegacyVerifierTest.linear_sent_target,
      ``Sumcheck.Core.LegacyVerifierTest.run_false_relation] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected axiom {ax} in {decl}"

end Sumcheck.Core.LegacyVerifierTest
