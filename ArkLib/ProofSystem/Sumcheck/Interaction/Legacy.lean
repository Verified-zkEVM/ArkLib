/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Sumcheck.Interaction.Closing

/-! # Two-way single-round legacy relation correspondence -/

namespace Sumcheck.Interaction.SingleRound

open Polynomial OracleComp OracleSpec
open _root_.Interaction.Oracle

noncomputable section

variable (R : Type) [CommSemiring R] (deg : ℕ)

local instance : ∀ i, OracleInterface ((Spec.SingleRound.pSpec R deg).Challenge i) :=
  ProtocolSpec.challengeOracleInterface

/-- Both directions of the concrete legacy output relation agree with the behavior boundary. -/
theorem legacy_output_iff (p : Message R deg) (stmt : R × R) :
    ((stmt, (fun _ : Unit => p)), ()) ∈ Spec.SingleRound.Simple.outputRelation R deg ↔
      closedOutputRelation R deg
        (DataClaim.toClosed (⟨stmt, fun _ => p⟩ : DataClaim (R × R) (outputFamily R deg))) :=
  Iff.rfl

/-- Both directions of the legacy input relation agree, using the same finite domain. -/
theorem legacy_input_iff {m : ℕ} (D : Fin m ↪ R) (p : Message R deg) (target : R) :
    ((target, (fun _ : Unit => p)), ()) ∈ Spec.SingleRound.Simple.inputRelation R deg D ↔
      closedInputRelation R deg (Finset.univ.map D).toList
        (DataClaim.toClosed (⟨target, fun _ => p⟩ : DataClaim R (outputFamily R deg))) := by
  change (∑ x ∈ Finset.univ.map D, p.val.eval x) = target ↔
    ((Finset.univ.map D).toList.map (fun x => p.val.eval x)).sum = target
  rw [Finset.sum_map_toList]

/-- The legacy two-message transcript corresponding to the typed concrete path. -/
def legacyTranscript (p : Message R deg) (r : R) :
    (Spec.SingleRound.pSpec R deg).FullTranscript :=
  fun i => Fin.cases p (fun j => Fin.cases r (fun k => Fin.elim0 k) j) i

@[simp]
theorem legacyTranscript_message (p : Message R deg) (r : R) :
    legacyTranscript R deg p r 0 = p := rfl

@[simp]
theorem legacyTranscript_challenge (p : Message R deg) (r : R) :
    legacyTranscript R deg p r 1 = r := rfl

/-- Run the actual legacy prover with its challenge query answered by the chosen challenge. -/
theorem legacy_prover_run {ι : Type} (ambient : OracleSpec ι)
    (p : Message R deg) (target r : R) :
    simulateQ (OracleInterface.simOracle ambient
      (T := (Spec.SingleRound.pSpec R deg).Challenge) (legacyTranscript R deg p r).challenges)
      ((Spec.SingleRound.Simple.prover R deg ambient).run (target, fun _ => p) ()) =
      pure (legacyTranscript R deg p r, ((p.val.eval r, r), fun _ : Unit => p), ()) := by
  have hfirst : (Spec.SingleRound.Simple.prover R deg ambient).runToRound (1 : Fin 3)
      (target, fun _ => p) () =
      pure (ProtocolSpec.Transcript.concat (m := (0 : Fin 2))
        (pSpec := Spec.SingleRound.pSpec R deg) p (fun i => Fin.elim0 i), p) := by
    erw [Prover.runToRound_succ (0 : Fin 2)]
    erw [Prover.processRound_of_dir_eq_P_to_V 0 rfl]
    simp [Spec.SingleRound.Simple.prover]
    rfl
  have hsecond : simulateQ
      (OracleInterface.simOracle ambient (T := (Spec.SingleRound.pSpec R deg).Challenge)
        (legacyTranscript R deg p r).challenges)
      ((Spec.SingleRound.Simple.prover R deg ambient).runToRound (2 : Fin 3)
        (target, fun _ => p) ()) =
      pure (ProtocolSpec.Transcript.concat (m := (1 : Fin 2)) r
        (ProtocolSpec.Transcript.concat (m := (0 : Fin 2))
          (pSpec := Spec.SingleRound.pSpec R deg) p (fun i => Fin.elim0 i)),
        (p, r)) := by
    erw [Prover.runToRound_succ (1 : Fin 2)]
    erw [Prover.processRound_of_dir_eq_V_to_P 1 rfl, hfirst]
    simp only [Spec.SingleRound.Simple.prover, pure_bind, monadLift_pure,
      ProtocolSpec.getChallenge, map_pure, bind_pure_comp, simulateQ_map, HasQuery.query]
    erw [simulateQ_query]
    rfl
  simp only [Prover.run, simulateQ_bind]
  change (simulateQ _ ((Spec.SingleRound.Simple.prover R deg ambient).runToRound
    (2 : Fin 3) (target, fun _ => p) ()) >>= _) = _
  rw [hsecond]
  have ht : ProtocolSpec.Transcript.concat (m := (1 : Fin 2)) r
      (ProtocolSpec.Transcript.concat (m := (0 : Fin 2))
        (pSpec := Spec.SingleRound.pSpec R deg) p (fun i => Fin.elim0 i)) =
      legacyTranscript R deg p r := by
    funext i
    fin_cases i <;> rfl
  simp only [Spec.SingleRound.Simple.prover, pure_bind, monadLift_pure, simulateQ_pure]
  erw [ht]

/-- Honest legacy verifier execution agrees with the typed executor's scalar output. -/
theorem legacy_verifier_correspondence [DecidableEq R] [SampleableType R]
    {ι : Type} (ambient : OracleSpec ι) {m : ℕ} (D : Fin m ↪ R)
    (p : Message R deg) (target r : R)
    (h : ((target, (fun _ : Unit => p)), ()) ∈
      Spec.SingleRound.Simple.inputRelation R deg D) :
    (Option.map Prod.fst) <$>
      ((Spec.SingleRound.Simple.oracleVerifier R deg D ambient).toVerifier.verify
        (target, fun _ => p) (legacyTranscript R deg p r)).run =
      (fun result => result.2.2) <$>
        executeAt R deg ambient p p (Finset.univ.map D).toList target r := by
  rw [executeAt_honest R deg ambient p _ target r (legacy_input_sum R deg D p target h)]
  rw [Spec.SingleRound.Simple.oracleVerifier_eq_verifier]
  have hs : (∑ x, p.val.eval (D x)) = target := by
    simpa [Spec.SingleRound.Simple.inputRelation] using h
  simp [Spec.SingleRound.Simple.verifier, hs]


end
end Sumcheck.Interaction.SingleRound
