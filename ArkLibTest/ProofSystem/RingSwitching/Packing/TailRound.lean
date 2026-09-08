/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.RingSwitching.Packing.Tail.RoundSecurity
import ArkLibTest.ProofSystem.RingSwitching.Packing.PackedCommitment

/-!
# Adversarial roots at the actual sumcheck challenge

For p=X and multiplier one over ZMod5, the forged message X² passes the Boolean sum check.
It matches the true residual precisely at 0 and 1. The actual knowledge state must allow
those sampled roots after the challenge while rejecting the false global message before it.
-/

noncomputable section

namespace RingSwitching.Packing.Tests.TailRound

open Polynomial MvPolynomial OracleSpec OracleComp ProtocolSpec
open NonfunctionalCommitment
open scoped NNReal

local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

abbrev F := ZMod 5
abbrev exactPC := ExactPackedCommitment.polynomialOracle F 1
abbrev pc : PackedCommitment F 1 := exactPC.toPackedCommitment

def p : F⦃≤ 1⦄[X Fin 1] := ⟨X 0, by simp [mem_restrictDegree_iff_degreeOf_le]⟩
def ost := pc.commit p
def multiplier : Unit → F⦃≤ 1⦄[X Fin 1] := fun _ => constant 1 1
def stmt : Tail.Statement Unit F (0 : Fin 1).castSucc := ⟨(), Fin.elim0, 1⟩
def forged : F⦃≤ 2⦄[X] :=
  ⟨Polynomial.X ^ 2, Polynomial.mem_degreeLE.mpr (by simp)⟩

/-- The production round message query requests the whole polynomial as clear data. -/
theorem clear_message_query :
    ((inferInstance : ∀ j, OracleInterface ((Tail.Round.pSpec F).Message j)) ⟨0, rfl⟩).Query =
      Unit := rfl

/-- That query returns the degree-bounded polynomial itself, using the production interface. -/
theorem clear_message_answer :
    @OracleInterface.answer ((Tail.Round.pSpec F).Message ⟨0, rfl⟩)
      ((inferInstance : ∀ j, OracleInterface ((Tail.Round.pSpec F).Message j)) ⟨0, rfl⟩)
      forged () = forged := rfl

/-- The forged quadratic satisfies the actual local Boolean-sum check. -/
theorem forged_check : Tail.Round.check 0 stmt forged := by
  simp [Tail.Round.check, forged, stmt]

/-- Every challenge gives an accepted transcript with the original commitment oracle. -/
theorem forged_verifier_accept (c : F) :
    (Tail.Round.verifier pc 0).toVerifier.verify (stmt, ost) (FullTranscript.mk2 forged c) =
      pure (Tail.Round.nextStatement 0 stmt forged c, ost) := by
  rw [Tail.Round.verifier_verify]
  exact if_pos forged_check

/-- The true next residual relation sees only agreement at the actually sampled coordinate. -/
theorem forged_output_iff (c : F) :
    ((Tail.Round.nextStatement 0 stmt forged c, ost), p) ∈
      Tail.rel multiplier pc (0 : Fin 1).succ ↔ c ^ 2 = c := by
  change ((Tail.Round.nextStatement 0 stmt forged c, ost), p) ∈
    Tail.rel multiplier pc (Fin.last 1) ↔ _
  rw [Tail.rel_last]
  simp [Tail.Round.nextStatement, stmt, multiplier, constant, forged, p, ost,
    pc.commitsTo_commit, Fin.snoc]

/-- A zero challenge is a real accidental root, so post-challenge knowledge holds. -/
theorem forged_after_zero : Tail.Round.afterChallenge multiplier pc 0 stmt ost forged 0 p :=
  ⟨forged_check, (forged_output_iff 0).mpr (by decide)⟩

/-- One is the second real accidental root. -/
theorem forged_after_one : Tail.Round.afterChallenge multiplier pc 0 stmt ost forged 1 p :=
  ⟨forged_check, (forged_output_iff 1).mpr (by decide)⟩

/-- At two the same accepted message no longer satisfies the committed residual relation. -/
theorem forged_not_after_two :
    ¬ Tail.Round.afterChallenge multiplier pc 0 stmt ost forged 2 p := by
  intro h
  exact (by decide : (2 : F) ^ 2 ≠ 2) ((forged_output_iff 2).mp h.2)

/-- Before the challenge, the forged message is not the global committed residual polynomial. -/
theorem forged_not_before : ¬ Tail.Round.beforeChallenge multiplier pc 0 stmt ost forged p := by
  intro h
  have he := congrArg (fun g : F⦃≤ 2⦄[X] => g.val.eval 2) h.2.2
  rw [Tail.Round.honestMessage, Tail.roundMessage_eval] at he
  have hh : (2 : F) ^ 2 = 2 := by
    simpa [forged, hypercubeSum_last, Tail.productPoly_eval, multiplier, constant, stmt, p,
      Fin.snoc] using he
  exact (by decide : (2 : F) ^ 2 ≠ 2) hh

/-- The actual one-message prefix fixes the forged polynomial before sampling. -/
def beforeTranscript : Transcript (1 : Fin 3) (Tail.Round.pSpec F) :=
  fun | ⟨0, _⟩ => forged

/-- The exact production KSF exposes the same false-before/true-after challenge transition. -/
theorem actual_knowledge_transition {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    ¬ (Tail.Round.knowledgeStateFunction multiplier pc 0 init impl).toFun 1
        (stmt, ost) beforeTranscript p ∧
      (Tail.Round.knowledgeStateFunction multiplier pc 0 init impl).toFun 2
        (stmt, ost) (FullTranscript.mk2 forged (0 : F)) p :=
  ⟨forged_not_before, forged_after_zero⟩

/-- The probability theorem uses the real polynomial oracle's binding and actual KSF. -/
theorem actual_worstCase {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    Verifier.rbrKnowledgeSoundnessWorstCaseWith init impl
      (Tail.rel multiplier pc (0 : Fin 1).castSucc) (Tail.rel multiplier pc (0 : Fin 1).succ)
      (Tail.Round.verifier pc 0).toVerifier (Tail.Round.WitMid (P := F) (m := 1))
      (Tail.Round.extractor (C := F) (Context := Unit) pc 0)
      (Tail.Round.knowledgeStateFunction multiplier pc 0 init impl) Tail.Round.rbrError :=
  Tail.Round.rbrKnowledgeSoundnessWorstCaseWith multiplier pc 0
    exactPC.commitsTo_functional init impl

/-- The degree-two root bound is the concrete nonzero value two fifths. -/
theorem actual_error (i : (Tail.Round.pSpec F).ChallengeIdx) :
    Tail.Round.rbrError i = (2 / 5 : ℝ≥0) := by
  simp [Tail.Round.rbrError]

/-- A second forged message can hide a false old target at one sampled root. -/
def linearForged : F⦃≤ 2⦄[X] :=
  ⟨Polynomial.X, Polynomial.mem_degreeLE.mpr (by simp)⟩

/-- Claiming one for the committed zero polynomial gives a false input relation. -/
theorem false_old_target :
    ((stmt, pc.commit 0), (0 : F⦃≤ 1⦄[X Fin 1])) ∉ Tail.rel multiplier pc (0 : Fin 1).castSucc := by
  simp [Tail.rel, stmt, Tail.productPoly, hypercubeSum]

/-- The malicious linear message passes the local guard and repairs the residual at zero. -/
theorem false_target_after_zero :
    Tail.Round.afterChallenge multiplier pc 0 stmt (pc.commit 0) linearForged 0 0 := by
  refine ⟨?_, ?_⟩
  · simp [Tail.Round.check, stmt, linearForged]
  · change ((Tail.Round.nextStatement 0 stmt linearForged 0, pc.commit 0), 0) ∈
      Tail.rel multiplier pc (Fin.last 1)
    rw [Tail.rel_last]
    exact ⟨by simp [Tail.Round.nextStatement, linearForged], pc.commitsTo_commit 0⟩

/-- Knowledge before this repair is false; it cannot retain old-target truth after sampling. -/
theorem false_target_not_before :
    ¬ Tail.Round.beforeChallenge multiplier pc 0 stmt (pc.commit 0) linearForged 0 :=
  fun h => false_old_target
    (Tail.Round.readback multiplier pc 0 stmt (pc.commit 0) linearForged 0 h)

end RingSwitching.Packing.Tests.TailRound

end
