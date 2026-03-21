/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
import ArkLib.ProofSystem.Binius.RingSwitching.Prelude
import ArkLib.ProofSystem.Binius.BinaryBasefold.Spec
import ArkLib.ToVCVio.Oracle

namespace Binius.RingSwitching
open Binius.BinaryBasefold

/-! ## Protocol Specs for Ring-Switching

This module defines the protocol specs, and the following instance types:

- **Protocol specs**: `pSpecBatching`, `pSpecSumcheckRound`, `pSpecSumcheckLoop`,
  `pSpecFinalSumcheck`, `pSpecCoreInteraction`, `pSpecLargeFieldReduction`, `fullPspec`.

- **OracleInterface**: For every `(pSpec ...).Message j` and `(pSpec ...).Challenge j` in the
  protocol. Challenge oracles should use `ProtocolSpec.challengeOracleInterface`.

- **SampleableType**: For all challenge types in batching, sumcheck, core interaction,
  large-field reduction, and full protocol.

- **OracleSpec.Inhabited**: For `[]ₒ` and for `[(pSpec ...).Message]ₒ` for every pSpec above.

- **OracleSpec.Fintype**: For `[]ₒ`, and for various `[pSpec.Challenge]ₒ` specs.

- **Fintype / Inhabited**: For individual `(pSpec ...).Challenge i` types where needed.

**NOTE**: For `∀ i, OracleInterface ((pSpec ...).Challenge i)`, use
  `ProtocolSpec.challengeOracleInterface` to avoid conflict.
-/

noncomputable section
open OracleSpec OracleComp ProtocolSpec Finset Polynomial MvPolynomial
open scoped NNReal

variable (κ : ℕ) [NeZero κ]
variable (L : Type) [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [SampleableType L]
variable (K : Type) [Field K] [Fintype K] [DecidableEq K]
variable [Algebra K L]
variable (β : Fin κ → L) [hβ_lin_indep : Fact (LinearIndependent K β)]
variable (h_dim : Module.finrank K L = κ)
variable (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
variable (h_l : ℓ = ℓ' + κ)
variable (mlIOPCS : MLIOPCS L ℓ')
section Pspec

@[reducible]
def pSpecBatching : ProtocolSpec 2 :=
  ⟨![Direction.P_to_V, Direction.V_to_P],
   ![TensorAlgebra K L, Fin κ → L]⟩

@[reducible]
-- Note, this one is same as pSpecFold in BinaryBasefold
def pSpecSumcheckRound : ProtocolSpec 2 := ⟨![Direction.P_to_V, Direction.V_to_P], ![L⦃≤ 2⦄[X], L]⟩

def pSpecSumcheckLoop := ProtocolSpec.seqCompose (fun (_: Fin ℓ') => pSpecSumcheckRound L)

@[reducible]
def pSpecFinalSumcheck := pSpecFinalSumcheckStep (L := L)

@[reducible]
def pSpecCoreInteraction := (pSpecSumcheckLoop L ℓ') ++ₚ (pSpecFinalSumcheck L)

@[reducible]
def pSpecLargeFieldReduction := (pSpecBatching κ L K) ++ₚ (pSpecCoreInteraction (L:=L) (ℓ':=ℓ'))

@[reducible]
def fullPspec := (pSpecLargeFieldReduction κ (L:=L) (K:=K) (ℓ':=ℓ')) ++ₚ (mlIOPCS.pSpec)

/-! ## Oracle Interface instances for Messages-/

instance : OracleInterface (TensorAlgebra K L) := OracleInterface.instDefault
instance : OracleInterface (Fin κ → L) := OracleInterface.instDefault

instance : ∀ j, OracleInterface ((pSpecBatching κ L K).Message j)
  | ⟨0, _⟩ => OracleInterface.instDefault -- ŝ ∈ A
  | ⟨1, _⟩ => OracleInterface.instDefault -- r'' ∈ L^κ

instance : ∀ j, OracleInterface ((pSpecBatching κ L K).Challenge j) :=
  fun _ => OracleInterface.instDefault
  -- NOTE: this is same as ProtocolSpec.challengeOracleInterface (pSpec := pSpecBatching κ L K)

instance instOracleInterfaceMessagePSpecSumcheckRound :
  ∀ j, OracleInterface ((pSpecSumcheckRound (L:=L)).Message j) :=
  fun _ => OracleInterface.instDefault

instance : ∀ j, OracleInterface ((pSpecSumcheckRound (L:=L)).Challenge j) :=
  ProtocolSpec.challengeOracleInterface

instance : ∀ j, OracleInterface ((pSpecSumcheckLoop (L:=L) ℓ').Message j)
  := instOracleInterfaceMessageSeqCompose

instance : ∀ i, OracleInterface ((pSpecCoreInteraction (L:=L) (ℓ':=ℓ')).Message i) :=
  instOracleInterfaceMessageAppend

instance : ∀ i, OracleInterface ((pSpecLargeFieldReduction κ (L:=L) (K:=K) (ℓ':=ℓ')).Message i) :=
  instOracleInterfaceMessageAppend

instance : ∀ i, OracleInterface (mlIOPCS.pSpec.Message i) := fun i => mlIOPCS.Oₘ i

instance : ∀ i, OracleInterface ((fullPspec κ (L:=L) (K:=K) (ℓ':=ℓ') mlIOPCS).Message i) :=
  instOracleInterfaceMessageAppend

/-! ## SampleableType instances -/

instance : ∀ j, SampleableType ((pSpecBatching κ L K).Challenge j)
  | ⟨0, h0⟩ => by nomatch h0
  | ⟨1, _⟩ => by
    simp only [Challenge, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    exact instSampleableTypeFinFunc (α := L)

instance : ∀ j, SampleableType ((pSpecSumcheckRound (L:=L)).Challenge j)
  | ⟨0, h0⟩ => by nomatch h0
  | ⟨1, _⟩ => by
    simp only [Challenge, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    infer_instance

instance : ∀ j, SampleableType ((pSpecSumcheckLoop (L:=L) ℓ').Challenge j)
  := instSampleableTypeChallengeSeqCompose

instance : ∀ i, SampleableType ((pSpecCoreInteraction (L:=L) (ℓ':=ℓ')).Challenge i) :=
  instSampleableTypeChallengeAppend

instance : ∀ i, SampleableType ((pSpecLargeFieldReduction κ (L:=L) (K:=K) (ℓ':=ℓ')).Challenge i) :=
  instSampleableTypeChallengeAppend

instance : ∀ i, SampleableType (mlIOPCS.pSpec.Challenge i) := mlIOPCS.O_challenges

instance : ∀ i, SampleableType ((fullPspec κ (L:=L) (K:=K) (ℓ':=ℓ') mlIOPCS).Challenge i) :=
  instSampleableTypeChallengeAppend

/-! ## Fintype & Inhabited instances for oracle specifications -/

instance instInhabitedOracleSpecEmpty : (([]ₒ : OracleSpec PEmpty).Inhabited) where
  inhabited_B i := nomatch i

instance instFintypeOracleSpecEmpty : (([]ₒ : OracleSpec PEmpty).Fintype) where
  fintype_B i := nomatch i

/-! ## OracleSpec.Inhabited for all pSpec.Message -/

instance instInhabitedPSpecBatchingMessage : [(pSpecBatching κ L K).Message]ₒ.Inhabited := by
  refine { inhabited_B := ?_ }
  intro x
  rcases x with ⟨⟨i, hi⟩, q⟩
  have h0 : i = 0 := by
    fin_cases i
    · rfl
    · simp [pSpecBatching] at hi
  subst h0
  cases q
  change Inhabited (TensorAlgebra K L)
  exact ⟨0⟩

instance instInhabitedPSpecSumcheckRoundMessage :
    [(pSpecSumcheckRound (L:=L)).Message]ₒ.Inhabited := by
  letI : Inhabited L := ⟨0⟩
  refine { inhabited_B := ?_ }
  intro x
  rcases x with ⟨⟨i, hi⟩, q⟩
  have h0 : i = 0 := by
    fin_cases i
    · rfl
    · simp [pSpecSumcheckRound] at hi
  subst h0
  cases q
  change Inhabited (L⦃≤ 2⦄[X])
  infer_instance

instance instInhabitedPSpecFinalSumcheckMessage :
    [(pSpecFinalSumcheck (L:=L)).Message]ₒ.Inhabited := by
  letI : Inhabited L := ⟨0⟩
  refine { inhabited_B := ?_ }
  intro x
  rcases x with ⟨⟨i, hi⟩, q⟩
  have h0 : i = 0 := Fin.eq_zero i
  subst h0
  cases q
  change Inhabited L
  infer_instance

/-! ## OracleSpec.Fintype for challenge specs -/

instance instFintypePSpecSumcheckRoundChallenge :
    ([(pSpecSumcheckRound (L:=L)).Challenge]ₒ).Fintype := by
  refine { fintype_B := ?_ }
  intro x
  rcases x with ⟨⟨i, hi⟩, q⟩
  have h1 : i = 1 := by
    fin_cases i
    · simp [pSpecSumcheckRound] at hi
    · rfl
  subst h1
  cases q
  change Fintype L
  infer_instance

instance instInhabitedPSpecSumcheckRoundChallenge :
    ([(pSpecSumcheckRound (L:=L)).Challenge]ₒ).Inhabited := by
  refine { inhabited_B := ?_ }
  intro x
  rcases x with ⟨⟨i, hi⟩, q⟩
  have h1 : i = 1 := by
    fin_cases i
    · simp [pSpecSumcheckRound] at hi
    · rfl
  subst h1
  cases q
  change Inhabited L
  exact ⟨0⟩

instance instFintypePSpecBatching_AllChallenges :
    ∀ i, Fintype ((pSpecBatching (κ := κ) (L := L) (K := K)).Challenge i)
  | ⟨0, h0⟩ => nomatch h0
  | ⟨1, _⟩ => by
    simp only [Challenge, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    infer_instance

instance instInhabitedPSpecBatching_AllChallenges :
    ∀ i, Inhabited ((pSpecBatching (κ := κ) (L := L) (K := K)).Challenge i)
  | ⟨0, h0⟩ => nomatch h0
  | ⟨1, _⟩ => ⟨fun _ => 0⟩

instance instFintypePSpecBatchingChallenge :
    ([(pSpecBatching κ L K).Challenge]ₒ).Fintype := by
  refine { fintype_B := ?_ }
  intro x
  rcases x with ⟨⟨i, hi⟩, q⟩
  have h1 : i = 1 := by
    fin_cases i
    · simp [pSpecBatching] at hi
    · rfl
  subst h1
  cases q
  change Fintype (Fin κ → L)
  infer_instance

instance instInhabitedPSpecBatchingChallenge :
    ([(pSpecBatching κ L K).Challenge]ₒ).Inhabited := by
  refine { inhabited_B := ?_ }
  intro x
  rcases x with ⟨⟨i, hi⟩, q⟩
  have h1 : i = 1 := by
    fin_cases i
    · simp [pSpecBatching] at hi
    · rfl
  subst h1
  cases q
  change Inhabited (Fin κ → L)
  exact ⟨fun _ => 0⟩



instance instFintypePSpecFinalSumcheck_AllChallenges : ∀ i, Fintype ((pSpecFinalSumcheck (L:=L)).Challenge i)
  | ⟨0, h0⟩ => nomatch h0

instance instInhabitedPSpecFinalSumcheck_AllChallenges : ∀ i, Inhabited ((pSpecFinalSumcheck (L:=L)).Challenge i)
  | ⟨0, h0⟩ => nomatch h0

instance instFintypePSpecFinalSumcheckChallenge :
    ([(pSpecFinalSumcheck (L:=L)).Challenge]ₒ).Fintype := by
  infer_instance

instance instInhabitedPSpecFinalSumcheckChallenge :
    ([(pSpecFinalSumcheck (L:=L)).Challenge]ₒ).Inhabited := by
  infer_instance

end Pspec

end
end Binius.RingSwitching
