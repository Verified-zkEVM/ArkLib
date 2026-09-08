/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.RingSwitching.Packing.Tail.SeqCompose
import ArkLib.OracleReduction.Composition.Sequential.KnowledgeNary

/-!
# Exact knowledge security of the product-sumcheck tail

The finite loop uses the proved guarded sequence constructor. Its extractor and knowledge state
then compose with the terminal leaf through append. Every sampled bad event is
bounded directly at a fixed prefix; averaging is only a consequence of that proved contract.
-/

noncomputable section
namespace RingSwitching.Packing.Tail
open OracleSpec OracleComp ProtocolSpec MvPolynomial
open scoped NNReal
variable {P C Context : Type} [CommRing P] [CommRing C] [Algebra P C] {m : ℕ}
  (multiplier : Context → C⦃≤ 1⦄[X Fin m]) (pc : PackedCommitment P m)

/-- The scalar-round sequence's intermediate witness family. -/
abbrev LoopWitness : Fin (Fin.vsum (fun _ : Fin m => 2) + 1) → Type :=
  Verifier.KnowledgeSeqCompose.Witness (fun _ : Fin (m + 1) => P⦃≤ 1⦄[X Fin m])
    (fun _ : Fin m => Round.WitMid (P := P) (m := m))

/-- The recursive append extractor for the scalar-round sequence. -/
def loopExtractor : Extractor.RoundByRound []ₒ
    (Statement Context C (0 : Fin (m + 1)) × (∀ j, pc.OStmt j))
    P⦃≤ 1⦄[X Fin m] P⦃≤ 1⦄[X Fin m] (loopSpec C m) (LoopWitness (P := P) (m := m)) :=
  Verifier.KnowledgeSeqCompose.extractor
    (fun i => Statement Context C i × (∀ j, pc.OStmt j))
    (fun _ => P⦃≤ 1⦄[X Fin m])
    (fun i => (Round.verifier (C := C) (Context := Context) pc i).toVerifier)
    (fun i => Round.guardedForm pc i) (fun _ => Round.WitMid (P := P) (m := m))
    (Round.extractor (C := C) (Context := Context) pc)

/-- The loop error by component and local challenge index. -/
def loopRbrError [Fintype C] : (loopSpec C m).ChallengeIdx → ℝ≥0 :=
  Verifier.KnowledgeSeqCompose.error (fun _ : Fin m => Round.rbrError (C := C))

/-- Every loop challenge belongs to a degree-two scalar round. -/
theorem loopRbrError_eq [Fintype C] (i : (loopSpec C m).ChallengeIdx) :
    loopRbrError (C := C) i = 2 / Fintype.card C := by
  rw [loopRbrError, Verifier.KnowledgeSeqCompose.error_eq_sigma]
  rfl

/-- Materializing the loop preserves its knowledge-state values. -/
def loopKnowledgeStateFunction [Fintype C] {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (loopVerifier (C := C) (Context := Context) pc).toVerifier.KnowledgeStateFunction init impl
      (rel multiplier pc 0) (rel multiplier pc (Fin.last m))
      (loopExtractor (C := C) (Context := Context) pc) := by
  let K := Verifier.KnowledgeSeqCompose.state
    (fun i => Statement Context C i × (∀ j, pc.OStmt j))
    (fun _ => P⦃≤ 1⦄[X Fin m]) init impl (rel multiplier pc)
    (fun i => (Round.verifier (C := C) (Context := Context) pc i).toVerifier)
    (fun i => Round.guardedForm pc i) (fun _ => Round.WitMid (P := P) (m := m))
    (Round.extractor (C := C) (Context := Context) pc)
    (fun i => Round.knowledgeStateFunction multiplier pc i init impl)
  exact {
    toFun := K.toFun
    toFun_empty := K.toFun_empty
    toFun_next := K.toFun_next
    toFun_full := fun stmt tr p h => K.toFun_full stmt tr p (by
      simpa only [Verifier.run, loopVerifier_toVerifier] using h) }

/-- Each fixed loop prefix has the exact degree-two component bound. -/
theorem loop_rbrKnowledgeSoundnessWorstCaseWith [IsDomain C] [Fintype C]
    (hfunctional : pc.Functional) {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    Verifier.rbrKnowledgeSoundnessWorstCaseWith init impl
      (rel multiplier pc 0) (rel multiplier pc (Fin.last m)) (loopVerifier pc).toVerifier
      (LoopWitness (P := P) (m := m)) (loopExtractor (C := C) (Context := Context) pc)
      (loopKnowledgeStateFunction multiplier pc init impl) (loopRbrError (C := C) (m := m)) := by
  exact Verifier.seqCompose_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_verifiers
    (fun i => Statement Context C i × (∀ j, pc.OStmt j))
    (fun _ => P⦃≤ 1⦄[X Fin m]) init impl (rel multiplier pc)
    (fun i => (Round.verifier (C := C) (Context := Context) pc i).toVerifier)
    (fun i => Round.guardedForm pc i) (fun _ => Round.WitMid (P := P) (m := m))
    (Round.extractor (C := C) (Context := Context) pc)
    (fun i => Round.knowledgeStateFunction multiplier pc i init impl)
    (fun _ => Round.rbrError (C := C))
    (fun i => Round.rbrKnowledgeSoundnessWorstCaseWith multiplier pc i hfunctional init impl)

/-- Append preserves the loop's intermediate witnesses and the terminal packed witness. -/
abbrev Witness : Fin (Fin.vsum (fun _ : Fin m => 2) + 1 + 1) → Type :=
  Verifier.KnowledgeAppend.Witness (LoopWitness (P := P) (m := m))
    (Terminal.WitMid (P := P) (m := m))

/-- The complete-tail extractor using the loop's passing output at the seam. -/
def extractor : Extractor.RoundByRound []ₒ
    (Statement Context C (0 : Fin (m + 1)) × (∀ j, pc.OStmt j))
    P⦃≤ 1⦄[X Fin m] P⦃≤ 1⦄[X Fin m] (pSpec C m) (Witness (P := P) (m := m)) :=
  (loopExtractor (C := C) (Context := Context) pc).append
    (Terminal.extractor (C := C) (Context := Context) pc) (loopGuardedForm pc).out

/-- The tail error selects the scalar challenges; the terminal contributes zero. -/
def rbrError [Fintype C] : (pSpec C m).ChallengeIdx → ℝ≥0 :=
  Sum.elim (loopRbrError (C := C) (m := m)) (fun _ => 0) ∘ ChallengeIdx.sumEquiv.symm

set_option backward.isDefEq.respectTransparency false in
/-- Each tail challenge has degree-two error. -/
theorem rbrError_eq [Fintype C] (i : (pSpec C m).ChallengeIdx) :
    rbrError (C := C) i = 2 / Fintype.card C := by
  obtain ⟨j, rfl⟩ := ChallengeIdx.sumEquiv.surjective i
  rcases j with j | j
  · simp only [rbrError, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl]
    exact loopRbrError_eq j
  · rcases j with ⟨⟨j, hj⟩, hdir⟩
    have : j = 0 := by omega
    subst j
    contradiction

/-- The exact complete-tail state retains every preceding guard across the terminal seam. -/
def knowledgeStateFunction [Fintype C] {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (verifier multiplier pc).toVerifier.KnowledgeStateFunction init impl
      (rel multiplier pc 0) pc.evalRel (extractor (C := C) (Context := Context) pc) := by
  let K := Verifier.KnowledgeStateFunction.appendGuarded (loopGuardedForm pc)
    (loopKnowledgeStateFunction multiplier pc init impl)
    (Terminal.knowledgeStateFunction multiplier pc init impl)
  exact {
    toFun := K.toFun
    toFun_empty := K.toFun_empty
    toFun_next := K.toFun_next
    toFun_full := fun stmt tr p h => K.toFun_full stmt tr p (by
      simpa only [Verifier.run, verifier_toVerifier] using h) }

/-- Worst-case knowledge soundness of the complete tail on the same commitment opening. -/
theorem rbrKnowledgeSoundnessWorstCaseWith [IsDomain C] [Fintype C]
    (hfunctional : pc.Functional) {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    Verifier.rbrKnowledgeSoundnessWorstCaseWith init impl
      (rel multiplier pc 0) pc.evalRel (verifier multiplier pc).toVerifier
      (Witness (P := P) (m := m)) (extractor (C := C) (Context := Context) pc)
      (knowledgeStateFunction multiplier pc init impl) (rbrError (C := C) (m := m)) := by
  exact Verifier.append_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_first
    (loopGuardedForm pc) (loopKnowledgeStateFunction multiplier pc init impl)
    (Terminal.knowledgeStateFunction multiplier pc init impl)
    (loop_rbrKnowledgeSoundnessWorstCaseWith multiplier pc hfunctional init impl)
    (Terminal.rbrKnowledgeSoundnessWorstCaseWith multiplier pc init impl)

/-- The tail extractor and knowledge state satisfy the prover-averaged contract. -/
theorem rbrKnowledgeSoundnessWith [IsDomain C] [Fintype C]
    (hfunctional : pc.Functional) {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    Verifier.rbrKnowledgeSoundnessWith init impl
      (rel multiplier pc 0) pc.evalRel (verifier multiplier pc).toVerifier
      (Witness (P := P) (m := m)) (extractor (C := C) (Context := Context) pc)
      (knowledgeStateFunction multiplier pc init impl) (rbrError (C := C) (m := m)) :=
  Verifier.rbrKnowledgeSoundnessWorstCaseWith_implies_rbrKnowledgeSoundnessWith init impl
    (rbrKnowledgeSoundnessWorstCaseWith multiplier pc hfunctional init impl)

end RingSwitching.Packing.Tail
