/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.RingSwitching.Packing.Tail.FullFamilyInput
import ArkLib.ProofSystem.RingSwitching.Packing.Tail.Knowledge

/-!
# The full-family batched claim to its original commitment opening

The zero-round input adapter is followed by every scalar round and the terminal value
message. The output is precisely the original commitment's evaluation relation over C, on the
same P-polynomial and oracle family. No downstream opening proof is assumed by this reduction.
-/

noncomputable section
namespace RingSwitching.Packing.FullFamilyTail
open OracleSpec OracleComp ProtocolSpec MvPolynomial
open scoped NNReal
variable {B : Type} [CommRing B] (data : PackingData B) (m : ℕ)
  {C : Type} [CommRing C] [Algebra B C] [Algebra data.P C]
  (bat : BatchingStrategy C data.ιE) (pc : PackedCommitment data.P m)

/-- Reformat the input, then run the product-sumcheck tail. -/
def pSpec : ProtocolSpec (0 + (Fin.vsum (fun _ : Fin m => 2) + 1)) :=
  !p[] ++ₚ Tail.pSpec C m

instance : ∀ j, OracleInterface ((pSpec (C := C) m).Message j) :=
  ProtocolSpec.instOracleInterfaceMessageAppend (pSpec₁ := !p[]) (pSpec₂ := Tail.pSpec C m)

instance [Fintype C] : ∀ j, SampleableType ((pSpec (C := C) m).Challenge j) :=
  ProtocolSpec.instSampleableTypeChallengeAppend (pSpec₁ := !p[]) (pSpec₂ := Tail.pSpec C m)

/-- The oracle verifier from a batched family claim to a packed evaluation. -/
def verifier : OracleVerifier []ₒ (FullFamily.Output data m bat) pc.OStmt
    ((Fin m → C) × C) pc.OStmt (pSpec (C := C) m) :=
  (adapterVerifier data m bat pc).append (Tail.verifier (multiplier data m bat) pc)

/-- The batched-family reduction preserving the packed witness and oracle family. -/
def reduction : OracleReduction []ₒ (FullFamily.Output data m bat) pc.OStmt
    data.P⦃≤ 1⦄[X Fin m] ((Fin m → C) × C) pc.OStmt data.P⦃≤ 1⦄[X Fin m]
    (pSpec (C := C) m) :=
  (adapterReduction data m bat pc).append (Tail.reduction (multiplier data m bat) pc)

omit [Algebra data.P C] in
/-- Materialization commutes with the input-adapter append. -/
theorem verifier_toVerifier : (verifier data m bat pc).toVerifier =
    (adapterVerifier data m bat pc).toVerifier.append
      (Tail.verifier (multiplier data m bat) pc).toVerifier :=
  OracleVerifier.append_toVerifier _ _

/-- Guarded form of the input adapter followed by the complete tail. -/
def guardedForm : (verifier data m bat pc).toVerifier.GuardedForm := by
  let G := (adapterGuardedForm data m bat pc).append (Tail.guardedForm (multiplier data m bat) pc)
  exact {
    check := G.check
    out := G.out
    verify_eq := fun stmt tr => by
      rw [verifier_toVerifier]
      exact G.verify_eq stmt tr }

instance : (reduction data m bat pc).prover.OutputIsPure :=
  Prover.OutputIsPure.append _ _
    (show (adapterProver data m bat pc).OutputIsPure from inferInstance)
    (show (Tail.reduction (multiplier data m bat) pc).prover.OutputIsPure from inferInstance)

/-- Perfect completeness of the batched-claim reduction over a finite commutative challenge ring. -/
theorem perfectCompleteness [Fintype C] {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (reduction data m bat pc).perfectCompleteness init impl
      (FullFamily.relOut data m bat pc) pc.evalRel := by
  exact OracleReduction.append_perfectCompleteness_of_guarded_verifiers
    (adapterReduction data m bat pc) (Tail.reduction (multiplier data m bat) pc)
    (adapterGuardedForm data m bat pc) (Tail.guardedForm (multiplier data m bat) pc)
    (fun _ => Or.inl (show (adapterProver data m bat pc).OutputIsPure from inferInstance))
    (adapter_perfectCompleteness data m bat pc init impl)
    (fun s => Tail.perfectCompleteness (multiplier data m bat) pc (pure s) impl)

/-- The input-adapter witness followed by the tail intermediate witness family. -/
abbrev Witness : Fin (0 + (Fin.vsum (fun _ : Fin m => 2) + 1) + 1) → Type :=
  Verifier.KnowledgeAppend.Witness (AdapterWitness data m)
    (Tail.Witness (P := data.P) (m := m))

/-- The exact append extractor transports the original P-polynomial across the format seam. -/
def extractor : Extractor.RoundByRound []ₒ
    (FullFamily.Output data m bat × (∀ j, pc.OStmt j)) data.P⦃≤ 1⦄[X Fin m]
    data.P⦃≤ 1⦄[X Fin m] (pSpec (C := C) m) (Witness data m) :=
  (adapterExtractor data m bat pc).append
    (Tail.extractor (C := C) (Context := (Fin m → data.E) × bat.Challenge) pc)
    (adapterGuardedForm data m bat pc).out

/-- The error function selecting the tail challenge after the zero-round adapter. -/
def rbrError [Fintype C] : (pSpec (C := C) m).ChallengeIdx → ℝ≥0 :=
  Sum.elim (fun _ => 0) (Tail.rbrError (C := C) (m := m)) ∘ ChallengeIdx.sumEquiv.symm

set_option backward.isDefEq.respectTransparency false in
/-- Every challenge carries the scalar-round error. -/
theorem rbrError_eq [Fintype C] (i : (pSpec (C := C) m).ChallengeIdx) :
    rbrError m i = 2 / Fintype.card C := by
  obtain ⟨j, rfl⟩ := ChallengeIdx.sumEquiv.surjective i
  rcases j with j | j
  · exact Fin.elim0 j.1
  · simp only [rbrError, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr]
    exact Tail.rbrError_eq j

/-- The knowledge state after materialization of the input adapter and tail. -/
def knowledgeStateFunction [Fintype C] {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (verifier data m bat pc).toVerifier.KnowledgeStateFunction init impl
      (FullFamily.relOut data m bat pc) pc.evalRel (extractor data m bat pc) := by
  let K := Verifier.KnowledgeStateFunction.appendGuarded (adapterGuardedForm data m bat pc)
    (adapterKnowledgeStateFunction data m bat pc init impl)
    (Tail.knowledgeStateFunction (multiplier data m bat) pc init impl)
  exact {
    toFun := K.toFun
    toFun_empty := K.toFun_empty
    toFun_next := K.toFun_next
    toFun_full := fun stmt tr p h => K.toFun_full stmt tr p (by
      simpa only [Verifier.run, verifier_toVerifier] using h) }

/-- Worst-case knowledge soundness for a challenge-algebra evaluation on the same commitment. -/
theorem rbrKnowledgeSoundnessWorstCaseWith [IsDomain C] [Fintype C]
    (hfunctional : pc.Functional) {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    Verifier.rbrKnowledgeSoundnessWorstCaseWith init impl
      (FullFamily.relOut data m bat pc) pc.evalRel (verifier data m bat pc).toVerifier
      (Witness data m) (extractor data m bat pc)
      (knowledgeStateFunction data m bat pc init impl) (rbrError (C := C) m) := by
  exact Verifier.append_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_first
    (adapterGuardedForm data m bat pc) (adapterKnowledgeStateFunction data m bat pc init impl)
    (Tail.knowledgeStateFunction (multiplier data m bat) pc init impl)
    (adapter_rbrKnowledgeSoundnessWorstCaseWith data m bat pc init impl)
    (Tail.rbrKnowledgeSoundnessWorstCaseWith (multiplier data m bat) pc hfunctional init impl)

end RingSwitching.Packing.FullFamilyTail
