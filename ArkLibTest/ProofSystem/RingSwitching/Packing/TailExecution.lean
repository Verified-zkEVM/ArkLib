/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.RingSwitching.Packing.Tail.Knowledge
import ArkLibTest.ProofSystem.RingSwitching.Packing.TailTerminal
import ArkLibTest.ProofSystem.RingSwitching.Packing.TailRound

/-!
# finite-loop and terminal seams

The empty loop reaches the same terminal over a product ring and list-valued oracle. One
round checks the forged-root boundary. Two rounds accept a constant witness and
retain rejection from the middle guard through the terminal seam.
-/

noncomputable section

namespace RingSwitching.Packing.Tests.TailExecution

open Polynomial MvPolynomial OracleSpec OracleComp ProtocolSpec
open NonfunctionalCommitment
open scoped NNReal

open TailTerminal in
/-- The empty loop forwards to the zero-multiplier terminal on the same list oracle. -/
theorem empty_loop_forwards_one :
    (Tail.verifier (multiplier 0) pc).toVerifier.run (stmt 0, ost)
      ((fun i => Fin.elim0 i : FullTranscript (Tail.loopSpec R 0)) ++ₜ
        Tail.Terminal.transcript (1 : R)) =
      pure ((Fin.elim0, 1), ost) := by
  erw [Tail.verifier_toVerifier, Verifier.append_run, Tail.loopVerifier_toVerifier]
  simp only [Verifier.seqCompose, FullTranscript.append_fst, FullTranscript.append_snd,
    Verifier.run, Verifier.id, pure_bind]
  exact zero_multiplier_forwards_one

open TailTerminal in
/-- The empty-loop reduction is state-uniformly complete for this nonfunctional oracle. -/
theorem empty_loop_complete {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (Tail.reduction (multiplier 0) pc).perfectCompleteness init impl
      (Tail.rel (multiplier 0) pc 0) pc.evalRel :=
  Tail.perfectCompleteness (multiplier 0) pc init impl

local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

private theorem snoc_empty {A : Type} (a : A) :
    Fin.snoc (fun i : Fin 0 => i.elim0) a = (fun _ : Fin 1 => a) := by
  funext i
  fin_cases i
  rfl

private theorem snoc_two {A : Type} (a b : A) :
    Fin.snoc (Fin.snoc (fun i : Fin 0 => i.elim0) a) b =
      (fun i : Fin 2 => if i = 0 then a else b) := by
  funext i
  fin_cases i <;> rfl

open TailRound in
set_option backward.isDefEq.respectTransparency false in
/-- The accepted accidental root reaches a valid packed opening through the full tail. -/
theorem one_round_root_accepts :
    (Tail.verifier multiplier pc).toVerifier.run (stmt, ost)
      ((FullTranscript.seqCompose (fun _ : Fin 1 => FullTranscript.mk2 forged (0 : F))) ++ₜ
        Tail.Terminal.transcript (0 : F)) = pure (((fun _ => (0 : F)), 0), ost) := by
  erw [Tail.verifier_toVerifier, Verifier.append_run, Tail.loopVerifier_toVerifier]
  dsimp only [Tail.loopSpec, Tail.Round.pSpec, Tail.Terminal.pSpec] at *
  simp [Verifier.seqCompose, Verifier.append, FullTranscript.seqCompose_succ_eq_append,
    FullTranscript.append_fst, FullTranscript.append_snd,
    Verifier.run, Verifier.id,
    Tail.Round.verifier_verify (C := F) (Context := Unit) pc (0 : Fin 1), Tail.Round.check,
    Tail.Round.nextStatement, Tail.Terminal.verifier_verify multiplier pc, Tail.Terminal.check,
    Tail.Terminal.nextStatement, Tail.Terminal.transcript, FullTranscript.messages,
    FullTranscript.challenges, FullTranscript.mk2, forged, stmt, multiplier, constant, snoc_empty]

open TailRound in
set_option backward.isDefEq.respectTransparency false in
/-- At a non-root, the terminal rejects the packed value although the round guard passes. -/
theorem one_round_nonroot_rejected :
    (Tail.verifier multiplier pc).toVerifier.run (stmt, ost)
      ((FullTranscript.seqCompose (fun _ : Fin 1 => FullTranscript.mk2 forged (2 : F))) ++ₜ
        Tail.Terminal.transcript (2 : F)) = failure := by
  erw [Tail.verifier_toVerifier, Verifier.append_run, Tail.loopVerifier_toVerifier]
  dsimp only [Tail.loopSpec, Tail.Round.pSpec, Tail.Terminal.pSpec] at *
  simp [Verifier.seqCompose, Verifier.append, FullTranscript.seqCompose_succ_eq_append,
    FullTranscript.append_fst, FullTranscript.append_snd,
    Verifier.run, Verifier.id,
    Tail.Round.verifier_verify (C := F) (Context := Unit) pc (0 : Fin 1), Tail.Round.check,
    Tail.Round.nextStatement, Tail.Terminal.verifier_verify multiplier pc, Tail.Terminal.check,
    Tail.Terminal.transcript, FullTranscript.messages,
    FullTranscript.challenges, FullTranscript.mk2, forged, stmt, multiplier, constant, snoc_empty,
    show (2 : F) ^ 2 ≠ 2 by decide]

abbrev F := ZMod 5
abbrev exactPC := ExactPackedCommitment.polynomialOracle F 2
abbrev pc : PackedCommitment F 2 := exactPC.toPackedCommitment

def p : F⦃≤ 1⦄[X Fin 2] := constant 2 1
def ost := pc.commit p
def multiplier : Unit → F⦃≤ 1⦄[X Fin 2] := fun _ => constant 2 1
def stmt : Tail.Statement Unit F (0 : Fin 3) := ⟨(), Fin.elim0, 4⟩
def msg (a : F) : F⦃≤ 2⦄[X] :=
  ⟨Polynomial.C a, Polynomial.mem_degreeLE.mpr (Polynomial.degree_C_le.trans (by decide))⟩
def rounds (second : F) : FullTranscript (Tail.loopSpec F 2) :=
  FullTranscript.seqCompose (fun i : Fin 2 =>
    FullTranscript.mk2 (msg (if i = 0 then 2 else second)) (if i = 0 then 3 else 4 : F))

/-- The two-round fixture starts from a true Boolean cube sum on its committed witness. -/
theorem two_round_source_related : ((stmt, ost), p) ∈ Tail.rel multiplier pc 0 := by
  change ((⟨(), Fin.elim0, 4⟩, ost), p) ∈ Tail.rel multiplier pc 0
  rw [Tail.rel_zero]
  exact ⟨by simp [multiplier, p, constant], pc.commitsTo_commit p⟩

set_option backward.isDefEq.respectTransparency false in
/-- Both scalar rounds and the terminal accept, retaining the ordered challenge point and oracle. -/
theorem two_round_accepts :
    (Tail.verifier multiplier pc).toVerifier.run (stmt, ost)
      (rounds 1 ++ₜ Tail.Terminal.transcript (1 : F)) =
      pure (((fun i : Fin 2 => if i = 0 then (3 : F) else 4), 1), ost) := by
  erw [Tail.verifier_toVerifier, Verifier.append_run, Tail.loopVerifier_toVerifier]
  dsimp only [Tail.loopSpec, Tail.Round.pSpec, Tail.Terminal.pSpec] at *
  simp [Verifier.seqCompose, Verifier.append, FullTranscript.seqCompose_succ_eq_append,
    FullTranscript.append_fst, FullTranscript.append_snd,
    Verifier.run, Verifier.id, Tail.Round.verifier_verify (C := F) (Context := Unit) pc (0 : Fin 2),
    Tail.Round.verifier_verify (C := F) (Context := Unit) pc (1 : Fin 2), Tail.Round.check,
    Tail.Round.nextStatement, Tail.Terminal.verifier_verify multiplier pc, Tail.Terminal.check,
    Tail.Terminal.nextStatement, Tail.Terminal.transcript, FullTranscript.messages,
    FullTranscript.challenges, FullTranscript.mk2, rounds, msg, stmt, multiplier, constant,
    snoc_two,
    show (2 : F) + 2 = 4 by decide, show (1 : F) + 1 = 2 by decide]

set_option backward.isDefEq.respectTransparency false in
/-- Replacing only the second message by zero rejects despite a subsequently valid zero terminal. -/
theorem middle_guard_rejected :
    (Tail.verifier multiplier pc).toVerifier.run (stmt, ost)
      (rounds 0 ++ₜ Tail.Terminal.transcript (0 : F)) = failure := by
  erw [Tail.verifier_toVerifier, Verifier.append_run, Tail.loopVerifier_toVerifier]
  dsimp only [Tail.loopSpec, Tail.Round.pSpec, Tail.Terminal.pSpec] at *
  simp [Verifier.seqCompose, Verifier.append, FullTranscript.seqCompose_succ_eq_append,
    FullTranscript.append_fst, FullTranscript.append_snd,
    Verifier.run, Verifier.id, Tail.Round.verifier_verify (C := F) (Context := Unit) pc (0 : Fin 2),
    Tail.Round.verifier_verify (C := F) (Context := Unit) pc (1 : Fin 2), Tail.Round.check,
    Tail.Round.nextStatement,
    FullTranscript.challenges, FullTranscript.mk2, rounds, msg, stmt,
    show (2 : F) + 2 = 4 by decide, show (0 : F) ≠ 2 by decide]

/-- The two-round extractor/KSF satisfy the fixed-prefix contract on this live commitment. -/
theorem two_round_worst_case {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    Verifier.rbrKnowledgeSoundnessWorstCaseWith init impl
      (Tail.rel multiplier pc 0) pc.evalRel (Tail.verifier multiplier pc).toVerifier
      (Tail.Witness (P := F) (m := 2)) (Tail.extractor (C := F) (Context := Unit) pc)
      (Tail.knowledgeStateFunction multiplier pc init impl) (Tail.rbrError (C := F) (m := 2)) :=
  Tail.rbrKnowledgeSoundnessWorstCaseWith multiplier pc exactPC.commitsTo_functional init impl

end RingSwitching.Packing.Tests.TailExecution

end
