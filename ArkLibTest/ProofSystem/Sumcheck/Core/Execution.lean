/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Sumcheck.Core.Execution
import Mathlib.Algebra.Field.ZMod

/-!
# Sumcheck verification and execution in the interaction layer

Every round runs even after a failed check, zero rounds accepts at once, an honest run on a
satisfied claim accepts, and challenges never select shape.
-/

namespace Sumcheck.Core.ExecutionTest

open Polynomial PFunctor FreeM Interaction.Core Interaction.TwoParty.Lens OracleComp OracleSpec
  ProtocolSpec

abbrev F := ZMod 5

variable {ι : Type} (ambient : OracleSpec ι)

/-- The uniform draws of the verifier in an execution. -/
abbrev drawOf (n : ℕ) :=
  fun c : ChallengeNode oracleSig (protocol F 1 n) =>
    (liftM ((ambient + challengeSpec oracleSig (protocol F 1 n)).query (.inr c)) :
      OracleComp (ambient + challengeSpec oracleSig (protocol F 1 n)) _)

/-! ## A bad round followed by good rounds -/

/-- Messages that are bad in the first of two rounds and honest afterwards. -/
noncomputable def badFirst {d : ℕ} (D : Fin d ↪ F) (bad : F⦃≤ 1⦄[X]) :
    (k : ℕ) → RoundState F 1 2 (k + 1) → F⦃≤ 1⦄[X]
  | 0, st => honestMessage D 0 st
  | _ + 1, _ => bad

/-- The prover that sends `bad` first and honest messages afterwards. -/
noncomputable def badFirstProver {d : ℕ} (D : Fin d ↪ F) (bad : F⦃≤ 1⦄[X])
    (stmt : Spec.StatementRound F 2 0) (oStmt : ∀ i, Spec.OracleStatement F 2 1 i) :
    Prover oracleSig ambient (protocol F 1 2) (fun _ => HonestOutput F 1 2) :=
  foldRounds (badFirst D bad) (nextState (badFirst D bad)) finishState 2 (initState stmt oStmt)

/-- A first message whose sum over `D` misses the target: the execution still draws both
challenges and records both rounds, and the verdict rejects. -/
theorem run_badFirstProver {d : ℕ} (D : Fin d ↪ F) (bad : F⦃≤ 1⦄[X])
    (stmt : Spec.StatementRound F 2 0) (oStmt : ∀ i, Spec.OracleStatement F 2 1 i)
    (hbad : ∑ x ∈ Finset.univ.map D, bad.val.eval x ≠ stmt.target) :
    (verifier F 1 2 D ambient).run stmt oStmt (badFirstProver ambient D bad stmt oStmt) =
      (fun chals => (⟨foldTranscript (badFirst D bad) (nextState (badFirst D bad)) 2
          (initState stmt oStmt) chals,
        finishState (foldState (nextState (badFirst D bad)) 2 (initState stmt oStmt) chals),
        none⟩ : Observation oracleSig (protocol F 1 2) (fun _ => HonestOutput F 1 2)
          (Spec.StatementRound F 2 (Fin.last 2) × ∀ i, Spec.OracleStatement F 2 1 i))) <$>
        drawChallenges 2 (drawOf ambient 2) := by
  rw [badFirstProver, run_verifier_foldRounds]
  refine congrArg (· <$> _) (funext fun chals => ?_)
  have hv : legacyVerdict F 1 2 D ambient stmt (decodeTranscript 2 (foldTranscript (badFirst D bad)
      (nextState (badFirst D bad)) 2 (initState stmt oStmt) chals)) = none :=
    legacyVerdict_eq_none (k := 1) stmt (roundFullTranscript bad (chals 0))
      (legacyTranscript 1 _ _) hbad
  rw [hv]
  rfl

/-- The run records both rounds of the bad prover, with the drawn challenges in order. -/
example {d : ℕ} (D : Fin d ↪ F) (bad : F⦃≤ 1⦄[X]) (stmt : Spec.StatementRound F 2 0)
    (oStmt : ∀ i, Spec.OracleStatement F 2 1 i) (chals : Fin 2 → F) :
    let tr := foldTranscript (badFirst D bad) (nextState (badFirst D bad)) 2
      (initState stmt oStmt) chals
    headMessage tr = bad ∧ headChallenge tr = chals 0 ∧
      headMessage (tailTranscript tr) =
        honestMessage D 0 (nextState (badFirst D bad) 1 (initState stmt oStmt) (chals 0)) ∧
      headChallenge (tailTranscript tr) = chals 1 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The evaluation domain `{0, 1}`. -/
def D₂ : Fin 2 ↪ F := ⟨fun i => (i.val : F), by decide⟩

/-- The constant polynomial one. -/
noncomputable def one : F⦃≤ 1⦄[X] := ⟨C 1, mem_degreeLE.2 (degree_C_le.trans (by decide))⟩

/-- A concrete bad first message: the constant one sums to two over `{0, 1}`, not to zero. -/
example (stmt : Spec.StatementRound F 2 0) (oStmt : ∀ i, Spec.OracleStatement F 2 1 i)
    (htarget : stmt.target = 0) :
    (verifier F 1 2 D₂ ambient).run stmt oStmt (badFirstProver ambient D₂ one stmt oStmt) =
      (fun chals => (⟨foldTranscript (badFirst D₂ one) (nextState (badFirst D₂ one)) 2
          (initState stmt oStmt) chals,
        finishState (foldState (nextState (badFirst D₂ one)) 2 (initState stmt oStmt) chals),
        none⟩ : Observation oracleSig (protocol F 1 2) (fun _ => HonestOutput F 1 2)
          (Spec.StatementRound F 2 (Fin.last 2) × ∀ i, Spec.OracleStatement F 2 1 i))) <$>
        drawChallenges 2 (drawOf ambient 2) := by
  refine run_badFirstProver ambient _ _ stmt oStmt ?_
  rw [htarget, Finset.sum_map]
  simpa [one] using (by decide : (2 : F) ≠ 0)

/-! ## Zero rounds -/

/-- With zero rounds the execution draws nothing and accepts the input claim at once. -/
example {d : ℕ} (D : Fin d ↪ F) (stmt : Spec.StatementRound F 0 0)
    (oStmt : ∀ i, Spec.OracleStatement F 0 1 i) :
    (verifier F 1 0 D ambient).run stmt oStmt (honestProver D stmt oStmt) =
      pure ⟨⟨⟩, finishState (initState stmt oStmt), some (stmt, oStmt)⟩ := by
  rw [run_verifier_honestProver]
  rfl

/-! ## Accepting honest runs -/

/-- One honest round on a satisfied claim accepts, with the next target the honest message at
the challenge. -/
theorem legacyVerdict_honest_one {d : ℕ} (D : Fin d ↪ F) (stmt : Spec.StatementRound F 1 0)
    (oStmt : ∀ i, Spec.OracleStatement F 1 1 i)
    (h : ((stmt, oStmt), ()) ∈ Spec.relationRound F 1 1 D 0) (chal : F) :
    legacyVerdict F 1 1 D ambient stmt
        (decodeTranscript 1 (honestTranscript D stmt oStmt fun _ => chal)) =
      some ⟨(honestMessage D 0 (initState stmt oStmt)).val.eval chal,
        Fin.snoc stmt.challenges chal⟩ := by
  refine (simulateQ_oracleVerifierProgram_succ 0 _ _ stmt
    (roundFullTranscript (honestMessage D 0 (initState stmt oStmt)) chal)
    (legacyTranscript 0 Fin.elim0 Fin.elim0)).trans ?_
  rw [roundCheck_eq_some 0 stmt _ ?_]
  · rfl
  · rw [← Finset.sum_map_toList]
    exact Spec.SingleRound.projected_sum_of_relationRound F 1 1 D 0 stmt (oStmt ()) h

/-- The honest execution of one round on a satisfied claim accepts on every challenge, and its
output oracle is the input polynomial. -/
theorem run_honest_one {d : ℕ} (D : Fin d ↪ F) (stmt : Spec.StatementRound F 1 0)
    (oStmt : ∀ i, Spec.OracleStatement F 1 1 i)
    (h : ((stmt, oStmt), ()) ∈ Spec.relationRound F 1 1 D 0) :
    (verifier F 1 1 D ambient).run stmt oStmt (honestProver D stmt oStmt) =
      (fun chals => (⟨honestTranscript D stmt oStmt chals, honestOutput D stmt oStmt chals,
        some (⟨(honestMessage D 0 (initState stmt oStmt)).val.eval (chals 0),
          Fin.snoc stmt.challenges (chals 0)⟩, oStmt)⟩ :
          Observation oracleSig (protocol F 1 1) (fun _ => HonestOutput F 1 1)
            (Spec.StatementRound F 1 (Fin.last 1) × ∀ i, Spec.OracleStatement F 1 1 i))) <$>
        drawChallenges 1 (drawOf ambient 1) := by
  rw [run_verifier_honestProver]
  refine congrArg (· <$> _) (funext fun chals => ?_)
  have hc : chals = fun _ => chals 0 := funext fun j => by rw [Subsingleton.elim j 0]
  have hv := legacyVerdict_honest_one ambient D stmt oStmt h (chals 0)
  rw [← hc] at hv
  rw [hv]
  rfl

/-! ## Shape independence -/

/-- The verifier view of any two runs differs only in the challenges it records. -/
example (tr₁ tr₂ : PathAlong oracleSig (protocol F 1 2))
    (h : transcriptChallenges 2 tr₁ = transcriptChallenges 2 tr₂) :
    viewChallenges (toView (protocol F 1 2) tr₁) =
      viewChallenges (toView (protocol F 1 2) tr₂) := by
  unfold viewChallenges
  rw [viewChallengeList_toView, viewChallengeList_toView, h]

/-- The decoded challenges are those recorded in the view, whatever the messages. -/
example (tr : PathAlong oracleSig (protocol F 1 3)) :
    (decodeTranscript 3 tr).challenges = viewChallenges (toView (protocol F 1 3) tr) :=
  (viewChallenges_toView 3 tr).symm

end Sumcheck.Core.ExecutionTest

run_cmd do
  for decl in [``Sumcheck.Core.simulateQ_route, ``Sumcheck.Core.viewChallenges_toView,
      ``Sumcheck.Core.simulateQ_decide, ``Sumcheck.Core.simulateQ_legacy_verify,
      ``Sumcheck.Core.run_verifier_foldRounds, ``Sumcheck.Core.run_verifier_honestProver,
      ``Sumcheck.Core.simulateQ_oracleVerifierProgram_succ, ``Sumcheck.Core.roundCheck_eq_none,
      ``Sumcheck.Core.roundCheck_eq_some, ``Sumcheck.Core.legacyVerdict_eq_none,
      ``Sumcheck.Core.ExecutionTest.run_badFirstProver,
      ``Sumcheck.Core.ExecutionTest.run_honest_one] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected axiom {ax} in {decl}"
