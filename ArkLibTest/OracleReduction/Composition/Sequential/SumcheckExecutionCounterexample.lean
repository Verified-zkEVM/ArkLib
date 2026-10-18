/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Sumcheck.Spec.SingleRound

/-!
# The legacy simple Sumcheck verifier repairs a false claim

The input oracle is zero, the claimed singleton sum is one, and the prover sends one.
Every challenge passes the check. The legacy next-target computation made the output true;
the corrected implementation keeps it false. Degree zero makes the advertised error zero.
-/

open Sumcheck.Spec Sumcheck.Spec.SingleRound
open scoped Polynomial

namespace SumcheckExecutionCounterexample

noncomputable section

def domain : Fin 1 ↪ ZMod 2 := ⟨fun _ => 0, fun _ _ _ => Subsingleton.elim _ _⟩

def input : Simple.StmtIn (ZMod 2) × (∀ i, Simple.OStmtIn (ZMod 2) 0 i) :=
  (1, fun _ => 0)

def transcript (challenge : ZMod 2) : (pSpec (ZMod 2) 0).FullTranscript :=
  fun i => Fin.cases
    (show (pSpec (ZMod 2) 0).Type 0 from
      ⟨1, by simp [Polynomial.mem_degreeLE]⟩)
    (fun j => Fin.cases challenge (fun k => Fin.elim0 k) j) i

theorem false_input : (input, ()) ∉ Simple.inputRelation (ZMod 2) 0 domain := by
  simp [Simple.inputRelation, input, domain]

theorem passes_every_challenge (challenge : ZMod 2) :
    (Simple.verifierGuardedForm (ZMod 2) 0 domain []ₒ).check
      input (transcript challenge) = true := by
  simp [Simple.verifierGuardedForm, input, transcript, domain]

def legacyOutput (challenge : ZMod 2) :
    Simple.StmtOut (ZMod 2) × (∀ i, Simple.OStmtOut (ZMod 2) 0 i) :=
  (((input.2 ()).val.eval challenge, challenge), input.2)

theorem legacy_true_output (challenge : ZMod 2) :
    (legacyOutput challenge, ()) ∈ Simple.outputRelation (ZMod 2) 0 := by
  rfl

theorem corrected_false_output (challenge : ZMod 2) :
    ((Simple.verifierGuardedForm (ZMod 2) 0 domain []ₒ).out
      input (transcript challenge), ()) ∉ Simple.outputRelation (ZMod 2) 0 := by
  simp [Simple.verifierGuardedForm, Simple.outputRelation, input, transcript]

/-- info: 'SumcheckExecutionCounterexample.corrected_false_output'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms corrected_false_output

end

end SumcheckExecutionCounterexample
