/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.FiatShamir.SingleSaltSecurity
public import ArkLib.ProofSystem.Sumcheck.Interaction.StoppedSoundness

/-!
# Native single-salt Fiat–Shamir for Sumcheck

The verifier checks each polynomial sum before hashing its challenge, then checks the final
closed claim using the explicitly supplied stateless source handler. The statement relation
ignores the global salt. This is ordinary false-claim soundness, with a Unit terminal seed.
-/

@[expose] public section

open Interaction Interaction.Oracle Interaction.Oracle.Security OracleComp OracleSpec
open scoped ENNReal

namespace Sumcheck.Interaction.Restoration

open SingleRound MultivariateRound
open Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir

variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable (n deg : ℕ)
variable {Input Salt : Type}
variable {m : ℕ} (D : Fin m ↪ F)
variable (A : PFunctor)
variable (stmt : Input → Spec.StatementRound F n ⟨0, by omega⟩)
variable (p : Input → Spec.OracleStatement F n deg ())
variable (originalOracle : Input →
  VirtualOracle (OracleSpec.ofPFunctor A) (polynomialFamily F n deg))
variable (impl : Input → QueryImpl (OracleSpec.ofPFunctor A) Id)

/-- The actual terminal source check; reconstruction or source rejection returns false. -/
noncomputable def singleSaltSumcheckAccepts (z : Input × Salt)
    (path : (Security.StateRestoration.protocol (rounds F deg n)).tree.ExecutionPath) : Bool :=
  match nativeObservedOutput F n deg D A stmt originalOracle impl z.1 path with
  | none => false
  | some output =>
      decide ((show F from output.oracles ⟨(), output.stmt.challenges⟩) = output.stmt.target)

/-- Terminal acceptance is exactly a returned closed native claim satisfying its output relation. -/
theorem singleSaltSumcheckAccepts_iff (z : Input × Salt)
    (path : (Security.StateRestoration.protocol (rounds F deg n)).tree.ExecutionPath) :
    singleSaltSumcheckAccepts F n deg D A stmt originalOracle impl z path = true ↔
      ∃ output, nativeObservedOutput F n deg D A stmt originalOracle impl z.1 path = some output ∧
        Native.outputRelation F n deg output := by
  unfold singleSaltSumcheckAccepts
  cases h : nativeObservedOutput F n deg D A stmt originalOracle impl z.1 path with
  | none => simp
  | some output =>
      simp [Native.outputRelation, Native.Core.outputRelation]
      rfl

/-- The compiled native experiment includes both prefix checks and the final source check. -/
noncomputable def singleSaltSumcheckExecution
    (adversary : SingleSaltAdversary Input Salt Unit (rounds F deg n)) :=
  singleSaltAcceptedExecution (rounds F deg n)
    (sumcheckGuards F n deg D n 0 (by omega) (fun z : Input × Salt => stmt z.1))
    (singleSaltSumcheckAccepts F n deg D A stmt originalOracle impl) adversary

/-- A returned compiled proof is bad exactly when its original Sumcheck claim is false. -/
def singleSaltSumcheckFalseClaim :
    Option ((Input × Salt) ×
      (Security.StateRestoration.protocol (rounds F deg n)).tree.ExecutionPath × Unit) → Prop
  | none => False
  | some (z, _, _) => ¬ initialClaimTrue F n deg D stmt p z.1

/-- The actual compiled terminal check validates the explicit Sumcheck terminal seed. -/
theorem singleSaltSumcheck_terminal_seed_valid
    (sourceLaw : ∀ z, (originalOracle z).eval (impl z) =
      (polynomialFamily F n deg).behaviorOfRealizations (fun _ => p z))
    (z : Input × Salt)
    (path : (Security.StateRestoration.protocol (rounds F deg n)).tree.ExecutionPath)
    (accepted : singleSaltSumcheckAccepts F n deg D A stmt originalOracle impl z path = true) :
    ((certificate F n deg D (p z.1) n 0 (by omega) (stmt z.1) True).terminalState path).holds
      (terminalWitnessEquiv F n deg D (p z.1) n 0 (by omega) (stmt z.1) True path ()) := by
  exact (terminal_certificate_holds_iff_native F n deg D A stmt p originalOracle impl
    sourceLaw z.1 path ()).mpr
      ((singleSaltSumcheckAccepts_iff F n deg D A stmt originalOracle impl z path).mp accepted)

/-- False-claim soundness of the actual compiled Sumcheck verifier, charged to the distinct
keys in its joint lazy-oracle run. The retained source oracle is interpreted by `sourceLaw`. -/
theorem singleSaltSumcheck_soundness [DecidableEq Input] [DecidableEq Salt]
    (sourceLaw : ∀ z, (originalOracle z).eval (impl z) =
      (polynomialFamily F n deg).behaviorOfRealizations (fun _ => p z))
    (adversary : SingleSaltAdversary Input Salt Unit (rounds F deg n)) :
    Pr{let joint ← (randomOracleLoggedRun
      (singleSaltSumcheckExecution F n deg D A stmt originalOracle impl adversary) ∅)}[
      singleSaltSumcheckFalseClaim F n deg D stmt p joint.1.1.1] ≤
    expectedFreshQueryCharge
      (singleSaltSumcheckExecution F n deg D A stmt originalOracle impl adversary)
      (keyError (fun _ : Fin (rounds F deg n).length => fieldError F deg)) := by
  let state := fun z : Input × Salt =>
    claimState F n deg D ⟨0, by omega⟩ (stmt z.1) (p z.1) True
  let extractor := fun z : Input × Salt =>
    certificate F n deg D (p z.1) n 0 (by omega) (stmt z.1) True
  let Rin := fun z : Input × Salt => fun _ : Unit => initialClaimTrue F n deg D stmt p z.1
  let Rout := fun (_ : Input × Salt)
      (_ : (Security.StateRestoration.protocol (rounds F deg n)).tree.ExecutionPath)
      (_ : Unit) => True
  let seed := fun (z : Input × Salt) path (w : Unit) =>
    terminalWitnessEquiv F n deg D (p z.1) n 0 (by omega) (stmt z.1) True path w
  have security := singleSalt_knowledge_soundness
    (sumcheckGuards F n deg D n 0 (by omega) (fun z : Input × Salt => stmt z.1))
    (singleSaltSumcheckAccepts F n deg D A stmt originalOracle impl)
    (fun _ => fieldError F deg) adversary state extractor Set.univ
    (by intro z _; exact certificate_preserving F n deg D (p z.1) n 0 (by omega) (stmt z.1) True)
    (by intro z _; exact certificate_bounded_constant F n deg D (p z.1) (stmt z.1))
    Rin Rout seed
    (by intro z w; exact initial_certificate_holds_iff F n deg D stmt p z.1 w)
    (by
      intro z path w accepted _
      cases w
      exact singleSaltSumcheck_terminal_seed_valid F n deg D A stmt p originalOracle impl
        sourceLaw z path accepted)
  have events := prEvent_congr
    (randomOracleLoggedRun
      (singleSaltSumcheckExecution F n deg D A stmt originalOracle impl adversary) ∅)
    (fun joint => singleSaltSumcheckFalseClaim F n deg D stmt p joint.1.1.1)
    (fun joint => badStoppedRelation state extractor Rin Rout seed Set.univ joint.1.1.1)
    (by
      intro joint
      cases joint.1.1.1 with
      | none => rfl
      | some selected =>
          rcases selected with ⟨z, path, w⟩
          simp [singleSaltSumcheckFalseClaim, badStoppedRelation, Rin, Rout])
  exact events.le.trans security

/-- The compiled Sumcheck bound charges only verifier rounds reached before rejection. -/
theorem singleSaltSumcheck_expected_round_bound [DecidableEq Input] [DecidableEq Salt]
    (sourceLaw : ∀ z, (originalOracle z).eval (impl z) =
      (polynomialFamily F n deg).behaviorOfRealizations (fun _ => p z))
    (adversary : SingleSaltAdversary Input Salt Unit (rounds F deg n)) :
    Pr{let joint ← (randomOracleLoggedRun
      (singleSaltSumcheckExecution F n deg D A stmt originalOracle impl adversary) ∅)}[
      singleSaltSumcheckFalseClaim F n deg D stmt p joint.1.1.1] ≤
      fieldError F deg * expectedSingleSaltAdversaryKeys adversary +
        expectedSingleSaltVerifierCost
          (sumcheckGuards F n deg D n 0 (by omega) (fun z : Input × Salt => stmt z.1))
          (singleSaltSumcheckAccepts F n deg D A stmt originalOracle impl)
          (fun _ => fieldError F deg) adversary := by
  have cost := (singleSalt_query_cost
    (sumcheckGuards F n deg D n 0 (by omega) (fun z : Input × Salt => stmt z.1))
    (singleSaltSumcheckAccepts F n deg D A stmt originalOracle impl)
    (fun _ => fieldError F deg) adversary).1
  have maximum : Finset.univ.sup
      (fun _ : Fin (rounds F deg n).length => fieldError F deg) ≤ fieldError F deg :=
    Finset.sup_le fun _ _ => le_rfl
  apply ((singleSaltSumcheck_soundness F n deg D A stmt p originalOracle impl
    sourceLaw adversary).trans cost).trans
  gcongr

/-- The concrete compiled verifier satisfies the usual `(Q + n) * degree/field-size` bound.
The cap counts the adversary's actual distinct hash keys, including failed proof selections. -/
theorem singleSaltSumcheck_query_bound [DecidableEq Input] [DecidableEq Salt]
    (sourceLaw : ∀ z, (originalOracle z).eval (impl z) =
      (polynomialFamily F n deg).behaviorOfRealizations (fun _ => p z))
    (adversary : SingleSaltAdversary Input Salt Unit (rounds F deg n)) (Q : ℕ)
    (queryBound : ∀ phase ∈ support (randomOracleLoggedRun adversary.withQueryLog ∅),
      (freshKeysOfLog phase.1.2).card ≤ Q) :
    Pr{let joint ← (randomOracleLoggedRun
      (singleSaltSumcheckExecution F n deg D A stmt originalOracle impl adversary) ∅)}[
      singleSaltSumcheckFalseClaim F n deg D stmt p joint.1.1.1] ≤
      (Q + n : ℕ) * fieldError F deg := by
  apply (singleSaltSumcheck_soundness F n deg D A stmt p originalOracle impl
    sourceLaw adversary).trans
  simpa only [rounds_length, singleSaltSumcheckExecution] using singleSalt_uniform_query_cost
    (sumcheckGuards F n deg D n 0 (by omega) (fun z : Input × Salt => stmt z.1))
    (singleSaltSumcheckAccepts F n deg D A stmt originalOracle impl)
    (fieldError F deg) adversary Q queryBound

end Sumcheck.Interaction.Restoration
