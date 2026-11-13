/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.ProofSystem.RingSwitching.Packing.ProductSumcheck.SeqCompose
public import ArkLib.OracleReduction.Composition.Sequential.GuardedRoundByRound

/-!
# Knowledge security of the product-sumcheck tail

The guarded finite-composition theorem combines the concrete polynomial-preserving
round extractors. Appending the terminal same-commitment opening preserves every preceding
guard. Every challenge has the degree-two collision bound; the terminal adds no challenge.
-/

@[expose] public section

noncomputable section
namespace RingSwitching.Packing.ProductSumcheck
open OracleSpec OracleComp ProtocolSpec MvPolynomial
open scoped NNReal
variable {P C Context : Type} [CommRing P] [CommRing C] [Algebra P C] {m : ℕ}
  (multiplier : Multiplier Context C m) (pc : PackedCommitment P m)

/-- Decode the component round to assign its degree-two error. -/
def loopRbrError [Fintype C] : (loopSpec C m).ChallengeIdx → ℝ≥0 :=
  fun combinedIdx =>
    let ij := seqComposeChallengeIdxToSigma combinedIdx
    Round.rbrError (C := C) ij.2

/-- Every loop challenge belongs to one scalar round. -/
theorem loopRbrError_eq [Fintype C] (i : (loopSpec C m).ChallengeIdx) :
    loopRbrError (C := C) i = 2 / Fintype.card C := rfl

/-- The finite loop is round-by-round knowledge sound. -/
theorem loop_rbrKnowledgeSoundness [NoZeroDivisors C] [Fintype C] [SampleableType C]
    (hfunctional : pc.Functional) {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (loopVerifier pc).toVerifier.rbrKnowledgeSoundness init impl
      (rel multiplier pc 0) (rel multiplier pc (Fin.last m))
      (loopRbrError (C := C) (m := m)) := by
  apply OracleVerifier.seqCompose_rbrKnowledgeSoundness_of_guarded
    (Statement Context C) (fun _ => pc.OStmt) (fun _ => P⦃≤ 1⦄[X Fin m])
    (rel multiplier pc) (Round.verifier pc) (Round.guardedForm pc)
    (fun _ => Round.rbrError (C := C))
  intro i
  apply (Verifier.rbrKnowledgeSoundness_iff_exists_with init impl _ _ _ _).mpr
  exact ⟨_, _, _, Round.rbrKnowledgeSoundnessWith multiplier pc i hfunctional init impl⟩

/-- The scalar challenges retain their component error; the terminal contributes none. -/
def rbrError [Fintype C] : (pSpec C m).ChallengeIdx → ℝ≥0 :=
  Sum.elim (loopRbrError (C := C) (m := m)) (fun _ => 0) ∘ ChallengeIdx.sumEquiv.symm

-- Unfold the appended specification when transporting challenge indices through sumEquiv.
set_option backward.isDefEq.respectTransparency false in
/-- Every challenge of the complete tail has degree-two error. -/
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

/-- Round-by-round knowledge soundness on the original commitment opening. -/
theorem rbrKnowledgeSoundness [NoZeroDivisors C] [Fintype C] [SampleableType C]
    (hfunctional : pc.Functional) {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (verifier multiplier pc).toVerifier.rbrKnowledgeSoundness init impl
      (rel multiplier pc 0) (pc.evalRelWithContext Context) (rbrError (C := C) (m := m)) := by
  rw [verifier_toVerifier]
  apply Verifier.append_rbrKnowledgeSoundness_of_guarded_first
    _ _ (loopGuardedForm pc)
    (loop_rbrKnowledgeSoundness multiplier pc hfunctional init impl)
  apply (Verifier.rbrKnowledgeSoundness_iff_exists_with init impl _ _ _ _).mpr
  exact ⟨_, _, _, Terminal.rbrKnowledgeSoundnessWith multiplier pc init impl⟩

end RingSwitching.Packing.ProductSumcheck
