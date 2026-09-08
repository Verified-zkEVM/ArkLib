/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLibTest.ProofSystem.Binius.ConcreteCommitment
import ArkLib.ProofSystem.Binius.FRIBinius.CoreInteractionPhase
import ArkLib.OracleReduction.Composition.Sequential.General

/-! # Actual FRI-Binius final-check execution over an inhabited rank-four GF16 fixture

The runtime check needs no basis normalization hypothesis. These tests preserve the actual
folded-oracle family and do not assert a full folding input relation or downstream FRI security.
-/

open OracleSpec OracleComp ProtocolSpec Sumcheck.Structured RingSwitching
open Binius Binius.ConcreteCommitment MvPolynomial

noncomputable section
namespace Binius.FRIBinius.ProductionFinalTest

abbrev L := PackedField
abbrev K := ZMod 2
local instance : Fintype L := Fintype.ofFinite L
local instance : DecidableEq L := Classical.decEq L
local instance : Fact (Nat.Prime (ringChar K)) :=
  ⟨by simpa only [ZMod.ringChar_zmod_n] using Nat.prime_two⟩
local instance : Fact (Fintype.card K = 2) := ⟨ZMod.card 2⟩
local instance : Fact (1 ∣ 2) := ⟨one_dvd 2⟩

abbrev profile := FRIBinius.CoreInteractionPhase.biniusProfile 2 L K binaryBasis
abbrev Stmt := Statement (L := L) (ℓ := 2)
  (RingSwitchingBaseContext 2 L K 4 profile) (Fin.last 2)
abbrev Out := BinaryBasefold.FinalSumcheckStatementOut (L := L) (ℓ := 2)
abbrev O := BinaryBasefold.OracleStatement K binaryBasis
  (h_ℓ_add_R_rate := show 2 + 1 < 2 ^ 2 by decide) 1 (Fin.last 2)
abbrev spec := BinaryBasefold.pSpecFinalSumcheckStep (L := L)
abbrev V := FRIBinius.CoreInteractionPhase.finalSumcheckVerifier
  2 L K binaryBasis 4 2 1 1 (by decide) rfl

def oracle : ∀ j, O j := fun _ _ => 1
def ctx : RingSwitchingBaseContext 2 L K 4 profile := ⟨⟨0, 1⟩, 0, 0⟩
def statement (target : L) : Stmt := ⟨target, 1, ctx⟩
def transcript (msg : L) : FullTranscript spec := fun | ⟨0, _⟩ => msg

def sent (tr : FullTranscript spec) : L := tr.messages ⟨0, rfl⟩

def multiplier (s : Stmt) : L := compute_final_eq_value 2 L K profile 4 2 rfl
  s.ctx.t_eval_point s.challenges s.ctx.r_batching

def accepted (s : Stmt) (msg : L) : Out where
  sumcheck_target := s.sumcheck_target
  challenges := s.challenges
  ctx := ⟨getEvaluationPointSuffix 2 L 4 2 rfl s.ctx.t_eval_point, s.ctx.original_claim⟩
  final_constant := msg

/-- The production equation applies to arbitrary statements, actual oracles, and messages. -/
theorem runtime (s : Stmt) (o : ∀ j, O j) (tr : FullTranscript spec) :
    V.toVerifier.verify (s, o) tr =
      (if s.sumcheck_target = multiplier s * sent tr then
        pure (accepted s (sent tr), o) else failure) := by
  apply FRIBinius.CoreInteractionPhase.finalSumcheckVerifier_verify

theorem multiplier_zero (target : L) : multiplier (statement target) = 0 := by
  simp [multiplier, statement, ctx, compute_final_eq_value, compute_final_eq_tensor,
    eqTilde, eqWeightedCoordSum]

/-- The false target cannot yield an ordinary dummy statement. -/
theorem failed_check_aborts :
    V.toVerifier.verify (statement 1, oracle) (transcript 0) = failure := by
  rw [runtime]
  simp [statement, transcript, sent, FullTranscript.messages]

theorem zero_multiplier_forwards_one :
    V.toVerifier.verify (statement 0, oracle) (transcript 1) =
      pure (accepted (statement 0) 1, oracle) := by
  rw [runtime]
  simp only [show sent (transcript 1) = 1 from rfl, multiplier_zero, zero_mul,
    show (statement 0).sumcheck_target = 0 from rfl, ite_true]

/-- The forwarded constant is nonzero even though its multiplier vanishes. -/
theorem accepted_constant_nonzero : (accepted (statement 0) 1).final_constant ≠ 0 := one_ne_zero

/-- Accepted output preserves the source context and the supplied challenge prefix. -/
theorem accepted_fields :
    (accepted (statement 0) 1).ctx.original_claim = 1 ∧
      (accepted (statement 0) 1).challenges = 1 ∧
      (accepted (statement 0) 1).sumcheck_target = 0 := ⟨rfl, rfl, rfl⟩

/-- No actual oracle suffix can revive the rejected final equation. -/
theorem rejects_before_oracle_suffix {n : ℕ} {p : ProtocolSpec n}
    [∀ i, OracleInterface (p.Message i)] {T J : Type} {O' : J → Type}
    [∀ i, OracleInterface (O' i)]
    (W : OracleVerifier []ₒ Out O T O' p) (tr : FullTranscript p) :
    (OracleVerifier.append V W).toVerifier.verify (statement 1, oracle)
        (transcript 0 ++ₜ tr) = failure := by
  apply FRIBinius.CoreInteractionPhase.finalSumcheckVerifier_append_failure
  simp [statement, transcript, FullTranscript.messages]

/-- A concrete suffix marks that execution reached it. -/
def markerSuffix : Verifier []ₒ (Out × (∀ j, O j)) Nat ProtocolSpec.empty where
  verify := fun _ _ => pure 37

theorem rejects_before_marker :
    (V.toVerifier.append markerSuffix).run (statement 1, oracle)
      (transcript 0 ++ₜ (fun i => Fin.elim0 i)) = failure := by
  rw [Verifier.append_run]
  simp only [FullTranscript.append_fst, FullTranscript.append_snd, Verifier.run]
  rw [failed_check_aborts]
  simp [markerSuffix]

end Binius.FRIBinius.ProductionFinalTest
