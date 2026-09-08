/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.RingSwitching.Packing.Tail.RoundSecurity
import ArkLib.ProofSystem.RingSwitching.Packing.Tail.Terminal
import ArkLib.OracleReduction.Composition.Sequential.OracleCompleteness

/-!
# The actual generic product-sumcheck tail

The m scalar rounds are the library's actual sequential oracle reduction, followed by the
terminal opening check. The empty sequence is the identity, so m=0 directly reaches the same
terminal check. Every component keeps the original packed polynomial and its actual oracles.
-/

noncomputable section
namespace RingSwitching.Packing.Tail
open OracleSpec OracleComp ProtocolSpec MvPolynomial
variable {P C Context : Type} [CommRing P] [CommRing C] [Algebra P C] {m : ℕ}
  (multiplier : Context → C⦃≤ 1⦄[X Fin m]) (pc : PackedCommitment P m)

/-- The m actual scalar round protocols, including the empty protocol at m=0. -/
def loopSpec (C : Type) [CommRing C] (m : ℕ) :
    ProtocolSpec (Fin.vsum (fun _ : Fin m => 2)) :=
  ProtocolSpec.seqCompose (fun _ : Fin m => Round.pSpec C)

instance : ∀ j, OracleInterface ((loopSpec C m).Message j) :=
  inferInstanceAs (∀ j, OracleInterface
    ((ProtocolSpec.seqCompose (fun _ : Fin m => Round.pSpec C)).Message j))

instance [Fintype C] : ∀ j, SampleableType ((loopSpec C m).Challenge j) :=
  inferInstanceAs (∀ j, SampleableType
    ((ProtocolSpec.seqCompose (fun _ : Fin m => Round.pSpec C)).Challenge j))

/-- Sequentially run each actual scalar verifier with the same commitment oracle family. -/
def loopVerifier : OracleVerifier []ₒ (Statement Context C (0 : Fin (m + 1))) pc.OStmt
    (Statement Context C (Fin.last m)) pc.OStmt (loopSpec C m) :=
  OracleVerifier.seqCompose (Statement Context C) (fun _ => pc.OStmt)
    (Round.verifier (C := C) (Context := Context) pc)

/-- The m-round reduction preserves the original P-polynomial as its witness. -/
def loopReduction : OracleReduction []ₒ (Statement Context C (0 : Fin (m + 1))) pc.OStmt
    P⦃≤ 1⦄[X Fin m] (Statement Context C (Fin.last m)) pc.OStmt P⦃≤ 1⦄[X Fin m]
    (loopSpec C m) :=
  OracleReduction.seqCompose (Statement Context C) (fun _ => pc.OStmt)
    (fun _ => P⦃≤ 1⦄[X Fin m]) (Round.reduction multiplier pc)

omit [Algebra P C] in
/-- Materialization commutes with the actual finite sequential verifier. -/
theorem loopVerifier_toVerifier :
    (loopVerifier (C := C) (Context := Context) pc).toVerifier =
      Verifier.seqCompose (fun i => Statement Context C i × (∀ j, pc.OStmt j))
        (fun i => (Round.verifier (C := C) (Context := Context) pc i).toVerifier) := by
  apply OracleVerifier.seqCompose_toVerifier

/-- The loop retains every component guard, including the identity base case. -/
def loopGuardedForm : (loopVerifier (C := C) (Context := Context) pc).toVerifier.GuardedForm := by
  rw [loopVerifier_toVerifier]
  exact Verifier.GuardedForm.seqCompose
    (fun i => Statement Context C i × (∀ j, pc.OStmt j))
    (fun i => (Round.verifier (C := C) (Context := Context) pc i).toVerifier)
    (fun i => Round.guardedForm pc i)

instance : (loopReduction multiplier pc).prover.OutputIsPure :=
  Prover.OutputIsPure.seqCompose
    (fun i => Statement Context C i × (∀ j, pc.OStmt j))
    (fun _ => P⦃≤ 1⦄[X Fin m]) (Round.prover multiplier pc) (fun _ => inferInstance)

/-- All scalar challenges followed by the final packed-value message. -/
def pSpec (C : Type) [CommRing C] (m : ℕ) :
    ProtocolSpec (Fin.vsum (fun _ : Fin m => 2) + 1) :=
  loopSpec C m ++ₚ Terminal.pSpec C

instance : ∀ j, OracleInterface ((pSpec C m).Message j) :=
  inferInstanceAs (∀ j, OracleInterface ((loopSpec C m ++ₚ Terminal.pSpec C).Message j))

instance [Fintype C] : ∀ j, SampleableType ((pSpec C m).Challenge j) :=
  inferInstanceAs (∀ j, SampleableType ((loopSpec C m ++ₚ Terminal.pSpec C).Challenge j))

/-- The actual verifier composition ends at the packed opening point and value. -/
def verifier : OracleVerifier []ₒ (Statement Context C (0 : Fin (m + 1))) pc.OStmt
    ((Fin m → C) × C) pc.OStmt (pSpec C m) :=
  (loopVerifier pc).append (Terminal.verifier multiplier pc)

/-- The actual same-oracle product-sumcheck tail, including its terminal opening message. -/
def reduction : OracleReduction []ₒ (Statement Context C (0 : Fin (m + 1))) pc.OStmt
    P⦃≤ 1⦄[X Fin m] ((Fin m → C) × C) pc.OStmt P⦃≤ 1⦄[X Fin m] (pSpec C m) :=
  (loopReduction multiplier pc).append (Terminal.reduction multiplier pc)

omit [Algebra P C] in
set_option backward.isDefEq.respectTransparency false in
/-- Materialization preserves the actual loop-to-terminal verifier composition. -/
theorem verifier_toVerifier : (verifier multiplier pc).toVerifier =
    (loopVerifier pc).toVerifier.append (Terminal.verifier multiplier pc).toVerifier := by
  apply OracleVerifier.append_toVerifier

set_option backward.isDefEq.respectTransparency false in
/-- The complete tail preserves failure from every scalar round and the terminal check. -/
def guardedForm : (verifier multiplier pc).toVerifier.GuardedForm := by
  rw [verifier, OracleVerifier.append_toVerifier]
  exact (loopGuardedForm pc).append (Terminal.guardedForm multiplier pc)

instance : (reduction multiplier pc).prover.OutputIsPure :=
  Prover.OutputIsPure.append _ _ inferInstance
    (show (Terminal.prover (C := C) (Context := Context) pc).OutputIsPure from inferInstance)

/-- Universal-state completeness of the actual finite loop over a finite commutative ring. -/
theorem loop_perfectCompleteness [Fintype C] {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (loopReduction multiplier pc).perfectCompleteness init impl
      (rel multiplier pc 0) (rel multiplier pc (Fin.last m)) := by
  exact OracleReduction.seqCompose_perfectCompleteness_of_guarded_verifiers
    (Statement Context C) (fun _ => pc.OStmt) (fun _ => P⦃≤ 1⦄[X Fin m])
    init impl (rel multiplier pc) (Round.reduction multiplier pc)
    (fun i => show (Round.prover multiplier pc i).OutputIsPure from inferInstance)
    (fun i => Round.guardedForm pc i)
    (fun i s => Round.perfectCompleteness multiplier pc i (pure s) impl)

/-- The full tail is perfectly complete on the actual same-commitment opening relation. -/
theorem perfectCompleteness [Fintype C] {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (reduction multiplier pc).perfectCompleteness init impl (rel multiplier pc 0) pc.evalRel := by
  exact OracleReduction.append_perfectCompleteness_of_guarded_verifiers
    (loopReduction multiplier pc) (Terminal.reduction multiplier pc)
    (loopGuardedForm pc) (Terminal.guardedForm multiplier pc) (fun _ => Or.inl inferInstance)
    (loop_perfectCompleteness multiplier pc init impl)
    (fun s => Terminal.perfectCompleteness multiplier pc (pure s) impl)

end RingSwitching.Packing.Tail
