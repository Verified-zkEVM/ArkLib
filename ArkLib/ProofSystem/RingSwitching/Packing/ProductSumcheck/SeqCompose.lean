/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.ProofSystem.RingSwitching.Packing.ProductSumcheck.RoundSecurity
public import ArkLib.ProofSystem.RingSwitching.Packing.ProductSumcheck.Terminal
public import ArkLib.OracleReduction.Composition.Sequential.OracleCompleteness

/-!
# The generic product-sumcheck tail

The m scalar rounds are the sequential oracle reduction, followed by the
terminal opening check. The empty sequence is the identity, so m=0 directly reaches the same
terminal check. Every component keeps the original packed polynomial and its oracles.
-/

@[expose] public section

variable {ιₒ : Type} {oSpec : OracleSpec ιₒ}

noncomputable section
namespace RingSwitching.Packing.ProductSumcheck
open OracleSpec OracleComp ProtocolSpec MvPolynomial
variable {P C Context : Type} [CommRing P] [CommRing C] [Algebra P C] {m : ℕ}
  (multiplier : Multiplier Context C m) (pc : PackedCommitment P m)

/-- The scalar-round protocol sequence, empty when there are no retained variables. -/
def loopSpec (C : Type) [CommRing C] (m : ℕ) :
    ProtocolSpec (Fin.vsum (fun _ : Fin m => 2)) :=
  ProtocolSpec.seqCompose (fun _ : Fin m => Round.pSpec C)

instance : ∀ j, OracleInterface ((loopSpec C m).Message j) :=
  inferInstanceAs (∀ j, OracleInterface
    ((ProtocolSpec.seqCompose (fun _ : Fin m => Round.pSpec C)).Message j))

instance [SampleableType C] : ∀ j, SampleableType ((loopSpec C m).Challenge j) :=
  inferInstanceAs (∀ j, SampleableType
    ((ProtocolSpec.seqCompose (fun _ : Fin m => Round.pSpec C)).Challenge j))

/-- Sequential composition of scalar verifiers preserving the commitment oracle family. -/
def loopVerifier : OracleVerifier oSpec (Statement Context C (0 : Fin (m + 1))) pc.OStmt
    (Statement Context C (Fin.last m)) pc.OStmt (loopSpec C m) :=
  OracleVerifier.seqCompose (Statement Context C) (fun _ => pc.OStmt)
    (Round.verifier (oSpec := oSpec) (C := C) (Context := Context) pc)

/-- The m-round reduction preserves the original P-polynomial as its witness. -/
def loopReduction : OracleReduction oSpec (Statement Context C (0 : Fin (m + 1))) pc.OStmt
    P⦃≤ 1⦄[X Fin m] (Statement Context C (Fin.last m)) pc.OStmt P⦃≤ 1⦄[X Fin m]
    (loopSpec C m) :=
  OracleReduction.seqCompose (Statement Context C) (fun _ => pc.OStmt)
    (fun _ => P⦃≤ 1⦄[X Fin m]) (Round.reduction (oSpec := oSpec) multiplier pc)

omit [Algebra P C] in
/-- Materialization commutes with the finite verifier sequence. -/
theorem loopVerifier_toVerifier :
    (loopVerifier (oSpec := oSpec) (C := C) (Context := Context) pc).toVerifier =
      Verifier.seqCompose (fun i => Statement Context C i × (∀ j, pc.OStmt j))
        (fun i => (Round.verifier (oSpec := oSpec) (C := C)
          (Context := Context) pc i).toVerifier) := by
  apply OracleVerifier.seqCompose_toVerifier

/-- The loop retains every component guard, including the identity base case. -/
def loopGuardedForm : (loopVerifier (oSpec := oSpec) (C := C)
  (Context := Context) pc).toVerifier.GuardedForm := by
  rw [loopVerifier_toVerifier]
  exact Verifier.GuardedForm.seqCompose
    (fun i => Statement Context C i × (∀ j, pc.OStmt j))
    (fun i => (Round.verifier (oSpec := oSpec) (C := C) (Context := Context) pc i).toVerifier)
    (fun i => Round.guardedForm (oSpec := oSpec) pc i)

instance : (loopReduction (oSpec := oSpec) multiplier pc).prover.OutputIsPure :=
  Prover.OutputIsPure.seqCompose
    (fun i => Statement Context C i × (∀ j, pc.OStmt j))
    (fun _ => P⦃≤ 1⦄[X Fin m]) (Round.prover
      (oSpec := oSpec) multiplier pc) (fun _ => inferInstance)

/-- All scalar challenges followed by the final packed-value message. -/
def pSpec (C : Type) [CommRing C] (m : ℕ) :
    ProtocolSpec (Fin.vsum (fun _ : Fin m => 2) + 1) :=
  loopSpec C m ++ₚ Terminal.pSpec C

instance : ∀ j, OracleInterface ((pSpec C m).Message j) :=
  inferInstanceAs (∀ j, OracleInterface ((loopSpec C m ++ₚ Terminal.pSpec C).Message j))

instance [SampleableType C] : ∀ j, SampleableType ((pSpec C m).Challenge j) :=
  inferInstanceAs (∀ j, SampleableType ((loopSpec C m ++ₚ Terminal.pSpec C).Challenge j))

/-- The complete-tail verifier ends at the packed evaluation point and value. -/
def verifier : OracleVerifier oSpec (Statement Context C (0 : Fin (m + 1))) pc.OStmt
    (Context × ((Fin m → C) × C)) pc.OStmt (pSpec C m) :=
  (loopVerifier (oSpec := oSpec) pc).append (Terminal.verifier (oSpec := oSpec) multiplier pc)

/--
The product-sumcheck tail preserving the commitment oracle and ending with an opening message.
-/
def reduction : OracleReduction oSpec (Statement Context C (0 : Fin (m + 1))) pc.OStmt
    P⦃≤ 1⦄[X Fin m] (Context × ((Fin m → C) × C)) pc.OStmt P⦃≤ 1⦄[X Fin m] (pSpec C m) :=
  (loopReduction (oSpec := oSpec) multiplier pc).append (Terminal.reduction
    (oSpec := oSpec) multiplier pc)

omit [Algebra P C] in
-- Match the oracle-interface instances produced by loop/terminal append materialization.
set_option backward.isDefEq.respectTransparency false in
/-- Materialization commutes with loop-to-terminal composition. -/
theorem verifier_toVerifier : (verifier (oSpec := oSpec) multiplier pc).toVerifier =
    (loopVerifier (oSpec := oSpec) pc).toVerifier.append (Terminal.verifier
      (oSpec := oSpec) multiplier pc).toVerifier := by
  apply OracleVerifier.append_toVerifier

-- Match the oracle-interface instances produced by loop/terminal append materialization.
set_option backward.isDefEq.respectTransparency false in
/-- The complete tail preserves failure from every scalar round and the terminal check. -/
def guardedForm : (verifier (oSpec := oSpec) multiplier pc).toVerifier.GuardedForm := by
  rw [verifier, OracleVerifier.append_toVerifier]
  exact (loopGuardedForm (oSpec := oSpec) pc).append (Terminal.guardedForm
    (oSpec := oSpec) multiplier pc)

instance : (reduction (oSpec := oSpec) multiplier pc).prover.OutputIsPure :=
  Prover.OutputIsPure.append _ _ inferInstance
    (show (Terminal.prover (oSpec := oSpec) (C := C)
      (Context := Context) pc).OutputIsPure from inferInstance)

/--
Perfect completeness of the finite loop over a commutative ring, from every initial
state.
-/
theorem loop_perfectCompleteness [SampleableType C] {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) :
    (loopReduction (oSpec := oSpec) multiplier pc).perfectCompleteness init impl
      (rel multiplier pc 0) (rel multiplier pc (Fin.last m)) := by
  exact OracleReduction.seqCompose_perfectCompleteness_of_guarded_verifiers
    (Statement Context C) (fun _ => pc.OStmt) (fun _ => P⦃≤ 1⦄[X Fin m])
    init impl (rel multiplier pc) (Round.reduction (oSpec := oSpec) multiplier pc)
    (fun i => show (Round.prover (oSpec := oSpec) multiplier pc i).OutputIsPure from inferInstance)
    (fun i => Round.guardedForm (oSpec := oSpec) pc i)
    (fun i s => Round.perfectCompleteness multiplier pc i (pure s) impl)

/-- Perfect completeness of the complete tail on the same commitment opening relation. -/
theorem perfectCompleteness [SampleableType C] {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) :
    (reduction (oSpec := oSpec) multiplier pc).perfectCompleteness init impl (rel multiplier pc 0)
      (pc.evalRelWithContext Context) := by
  exact OracleReduction.append_perfectCompleteness_of_guarded_verifiers
    (loopReduction (oSpec := oSpec) multiplier pc) (Terminal.reduction
      (oSpec := oSpec) multiplier pc)
    (loopGuardedForm (oSpec := oSpec) pc) (Terminal.guardedForm
      (oSpec := oSpec) multiplier pc) (fun _ => Or.inl inferInstance)
    (loop_perfectCompleteness multiplier pc init impl)
    (fun s => Terminal.perfectCompleteness multiplier pc (pure s) impl)

end RingSwitching.Packing.ProductSumcheck
