/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.General

/-!
# Full Binary Basefold composition controls

The certified full verifier is the core-and-query append. These clients check its
transcript, error transport, rejecting behavior, and standard-axiom security headlines.
-/

open OracleSpec OracleComp ProtocolSpec AdditiveNTT Probability
open Binius.BinaryBasefold Binius.BinaryBasefold.CoreInteraction
open Binius.BinaryBasefold.QueryPhase Binius.BinaryBasefold.FullBinaryBasefold
open scoped NNReal

namespace Binius.BinaryBasefold.FullProtocolTests
noncomputable section
variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L]
  [SampleableType L]
variable (𝔽q : Type) [Field 𝔽q]
local instance [Finite 𝔽q] : Fact (Nat.Prime (ringChar 𝔽q)) := ⟨CharP.prime_ringChar 𝔽q⟩
variable [Fintype 𝔽q] [DecidableEq 𝔽q] [Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [Fact (LinearIndependent 𝔽q β)] [Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} (γ : ℕ) [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ]
variable {h_rate : ℓ + 𝓡 < r} [Fact (ϑ ∣ ℓ)] {𝓑 : Fin 2 ↪ L}

-- The zero codewords and canonical witness inhabit the full completeness premise.
def zeroStmt : Statement (L := L) (ℓ := ℓ) (SumcheckBaseContext L ℓ) 0 where
  sumcheck_target := 0
  challenges := fun _ => 0
  ctx := ⟨fun _ => 0, 0⟩

def zeroWit : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_rate) (ℓ := ℓ) 0 where
  t := 0
  H := 0
  f := getMidCodewords 𝔽q β (h_ℓ_add_R_rate := h_rate) 0
    (zeroStmt (L := L) (ℓ := ℓ)).challenges

def zeroOracles : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_rate) (0 : Fin (ℓ + 1)) j := fun _ _ => 0

omit [DecidableEq 𝔽q] [SampleableType L] [Fact (β 0 = 1)] in
theorem zero_initial_strict :
    ((zeroStmt (L := L) (ℓ := ℓ), zeroOracles 𝔽q β (ϑ := ϑ)
      (h_rate := h_rate)), zeroWit 𝔽q β (h_rate := h_rate)) ∈
    strictRoundRelation (multpoly := multiplier) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_rate) (𝓑 := 𝓑) 0 := by
  classical
  dsimp only [strictRoundRelation, StrictRoundRelated, StrictOracleWitnessConsistent]
  refine ⟨?_, ⟨?_, rfl⟩, ?_⟩
  · simp only [sumcheckConsistencyProp, zeroStmt, zeroWit]
    symm
    apply Finset.sum_eq_zero
    intro x hx
    exact (MvPolynomial.eval x).map_zero
  · apply Subtype.ext
    change (0 : MvPolynomial (Fin ℓ) L) = fixFirstVariablesOfMQP ℓ 0
      (computeInitialSumcheckPoly ℓ 0 (multiplier (zeroStmt (L := L) (ℓ := ℓ)).ctx)).val
      (zeroStmt (L := L) (ℓ := ℓ)).challenges
    rw [Sumcheck.Structured.coe_computeInitialSumcheckPoly]
    have hch : (zeroStmt (L := L) (ℓ := ℓ)).challenges = (Fin.elim0 : Fin 0 → L) := by
      funext i
      have hi := i.isLt
      simp at hi
    rw [hch, MvPolynomial.fixFirstVariablesOfMQP_zero]
    simp only [ZeroMemClass.coe_zero, mul_zero]
  · dsimp only [StrictOracleFoldingConsistent]
    intro j
    have hp : (polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega)
        (fun ω => (zeroWit 𝔽q β (h_rate := h_rate)).t.val.eval (bitsOfIndex ω))).val = 0 := by
      simp [zeroWit, polynomialFromNovelCoeffsF₂, polynomialFromNovelCoeffs]
    simp only [hp]
    rw [iteratedFold_eq_matrix_form]
    funext y
    simp [zeroOracles, polyToOracleFunc, iteratedFoldMatrixForm,
      pointFoldMatrixForm, fiberEvaluations, Matrix.mulVec, dotProduct]

/-- The sampled full honest protocol accepts the exhibited initial strict zero input. -/
example {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    let R := OracleReduction.toReduction (Oₛₒ := fun i : Empty => nomatch i)
      (fullOracleReduction 𝔽q β γ (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) (𝓑 := 𝓑))
    let pImpl : QueryImpl ([]ₒ + [(fullPSpec 𝔽q β γ (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_rate)).Challenge]ₒ'challengeOracleInterface)
      (StateT σ ProbComp) := QueryImpl.addLift impl challengeQueryImpl
    Pr{let out ← OptionT.mk do
      let st ← init
      (simulateQ pImpl (R.run (zeroStmt (L := L) (ℓ := ℓ),
        zeroOracles 𝔽q β (ϑ := ϑ) (h_rate := h_rate))
        (zeroWit 𝔽q β (h_rate := h_rate))).run).run' st}[
          (out.2, out.1.2.2) ∈ acceptRejectOracleRel ∧ out.1.2.1 = out.2] = 1 := by
  have h := fullOracleReduction_perfectCompleteness 𝔽q β γ (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_rate) (𝓑 := 𝓑) (init := init) (impl := impl)
  change Reduction.perfectCompleteness init impl
    (strictRoundRelation (multpoly := multiplier) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_rate) (𝓑 := 𝓑) 0) acceptRejectOracleRel
    (OracleReduction.toReduction (Oₛₒ := fun i : Empty => nomatch i)
      (fullOracleReduction 𝔽q β γ (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) (𝓑 := 𝓑))) at h
  rw [Reduction.perfectCompleteness_eq_prob_one] at h
  exact h
    (zeroStmt (L := L) (ℓ := ℓ), zeroOracles 𝔽q β (ϑ := ϑ) (h_rate := h_rate))
    (zeroWit 𝔽q β (h_rate := h_rate)) (zero_initial_strict 𝔽q β)

-- The honest reduction and the certified verifier contain the same append.
example :
    (fullOracleReduction 𝔽q β γ (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate)
      (𝓑 := 𝓑)).toOracleVerifier =
    fullOracleVerifier 𝔽q β γ (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) (𝓑 := 𝓑) := rfl

-- The full protocol is exactly the core transcript followed by the query transcript.
example :
    fullPSpec 𝔽q β γ (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) =
      pSpecCoreInteraction 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) ++ₚ
        pSpecQuery 𝔽q β γ (h_ℓ_add_R_rate := h_rate) := rfl

-- Challenge-index transport does not replace either component's error by zero.
example (j : (pSpecCoreInteraction 𝔽q β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_rate)).ChallengeIdx) :
    fullRbrKnowledgeError 𝔽q β γ (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate)
      (ChallengeIdx.sumEquiv (Sum.inl j)) =
    coreInteractionOracleRbrKnowledgeError 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_rate) j := by
  simp only [fullRbrKnowledgeError, Equiv.symm_apply_apply, Sum.elim_inl]

example (j : (pSpecQuery 𝔽q β γ (h_ℓ_add_R_rate := h_rate)).ChallengeIdx) :
    fullRbrKnowledgeError 𝔽q β γ (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate)
      (ChallengeIdx.sumEquiv (Sum.inr j)) =
    queryRbrKnowledgeError 𝔽q β γ (h_ℓ_add_R_rate := h_rate) j := by
  simp only [fullRbrKnowledgeError, Equiv.symm_apply_apply, Sum.elim_inr]

-- The final scalar message is a checked message, so it contributes no challenge/error slot.
example : IsEmpty (pSpecFinalSumcheckStep (L := L)).ChallengeIdx := inferInstance

-- The smallest block has a sumcheck message/challenge, a final scalar, and query challenges.
local instance : Fact ((1 : ℕ) ∣ 1) := ⟨by decide⟩

example {h_small : 1 + 1 < r} :
    Fintype.card (fullPSpec 𝔽q β γ (ℓ := 1) (𝓡 := 1) (ϑ := 1)
      (h_ℓ_add_R_rate := h_small)).MessageIdx = 2 := by
  change Fintype.card {i : Fin 4 //
    ![Direction.P_to_V, .V_to_P, .P_to_V, .V_to_P] i = .P_to_V} = 2
  decide

example {h_small : 1 + 1 < r} :
    Fintype.card (fullPSpec 𝔽q β γ (ℓ := 1) (𝓡 := 1) (ϑ := 1)
      (h_ℓ_add_R_rate := h_small)).ChallengeIdx = 2 := by
  change Fintype.card {i : Fin 4 //
    ![Direction.P_to_V, .V_to_P, .P_to_V, .V_to_P] i = .V_to_P} = 2
  decide

-- A rejected core transcript aborts the full converted verifier before query.
example (input : Statement (L := L) (SumcheckBaseContext L ℓ) 0 ×
      (∀ j, OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) 0 j))
    (tr : (fullPSpec 𝔽q β γ (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate)).FullTranscript)
    (hcore : (coreInteractionOracleVerifier 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_rate) (𝓑 := 𝓑)).toVerifier.run input tr.fst = failure) :
    ((fullOracleVerifier 𝔽q β γ (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate)
      (𝓑 := 𝓑)).toVerifier (Oₛₒ := fun i : Empty => nomatch i)).run input tr = failure := by
  unfold fullOracleVerifier
  rw [OracleVerifier.append_toVerifier (Oₛ₃ := fun i : Empty => nomatch i),
    Verifier.append_run, hcore]
  simp

-- The scalar display is usefully below one for an admissible field size and parameters.
example (hcard : Fintype.card L = 16) :
    concreteBinaryBasefoldKnowledgeError L 1 1 4 = (177 / 256 : ℝ≥0) ∧
    concreteBinaryBasefoldKnowledgeError L 1 1 4 < 1 := by
  norm_num [concreteBinaryBasefoldKnowledgeError, hcard]


/--
info: 'Binius.BinaryBasefold.FullBinaryBasefold.strictRoundRelation_subset_roundRelation_zero'
depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms strictRoundRelation_subset_roundRelation_zero
/--
info: 'Binius.BinaryBasefold.FullBinaryBasefold.fullOracleReduction_perfectCompleteness'
depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fullOracleReduction_perfectCompleteness
/--
info: 'Binius.BinaryBasefold.FullBinaryBasefold.fullOracleVerifier_rbrKnowledgeSoundness'
depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fullOracleVerifier_rbrKnowledgeSoundness
/--
info: 'Binius.BinaryBasefold.FullBinaryBasefold.fullRbrKnowledgeError_sum_le_concrete'
depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fullRbrKnowledgeError_sum_le_concrete

end
end Binius.BinaryBasefold.FullProtocolTests
