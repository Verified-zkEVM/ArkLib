/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
import ArkLib.ProofSystem.Binius.RingSwitching.Prelude
import ArkLib.ToVCVio.Oracle

namespace Binius.RingSwitching

/-! ## Protocol Specs for Ring-Switching
This module contains the protocol specs, oracle index bounds,
instances of OracleInterface and SelectableType for the Ring Switching protocol.
-/

noncomputable section
open OracleSpec OracleComp ProtocolSpec Finset Polynomial MvPolynomial
open scoped NNReal

variable (κ : ℕ) [NeZero κ]
variable (L : Type) [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [SelectableType L]
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
def pSpecSumcheckRound : ProtocolSpec 2 := ⟨![Direction.P_to_V, Direction.V_to_P], ![L⦃≤ 2⦄[X], L]⟩

def pSpecSumcheckLoop := ProtocolSpec.seqCompose (fun (_: Fin ℓ') => pSpecSumcheckRound L)

def pSpecFinalSumcheck : ProtocolSpec 1 := ⟨![Direction.P_to_V], ![L]⟩

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

instance : ∀ j, OracleInterface ((pSpecSumcheckRound (L:=L)).Message j)
  | ⟨0, _⟩ => OracleInterface.instDefault -- h_i(X) polynomial
  | ⟨1, _⟩ => OracleInterface.instDefault -- challenge r'_i

instance : ∀ j, OracleInterface ((pSpecSumcheckLoop (L:=L) ℓ').Message j)
  := instOracleInterfaceMessageSeqCompose

instance : ∀ i, OracleInterface ((pSpecFinalSumcheck (L:=L)).Message i)
  | ⟨0, _⟩ => OracleInterface.instDefault -- final constant c

instance : ∀ i, OracleInterface ((pSpecCoreInteraction (L:=L) (ℓ':=ℓ')).Message i) :=
  instOracleInterfaceMessageAppend

instance : ∀ i, OracleInterface ((pSpecLargeFieldReduction κ (L:=L) (K:=K) (ℓ':=ℓ')).Message i) :=
  instOracleInterfaceMessageAppend

instance : ∀ i, OracleInterface (mlIOPCS.pSpec.Message i) := fun i => mlIOPCS.Oₘ i

instance : ∀ i, OracleInterface ((fullPspec κ (L:=L) (K:=K) (ℓ':=ℓ') mlIOPCS).Message i) :=
  instOracleInterfaceMessageAppend

/-! ## SelectableType instances -/

instance : ∀ j, SelectableType ((pSpecBatching κ L K).Challenge j)
  | ⟨0, h0⟩ => by nomatch h0
  | ⟨1, _⟩ => by
    simp only [Challenge, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    exact instSelectableTypeFinFunc (α := L)

instance : ∀ j, SelectableType ((pSpecSumcheckRound (L:=L)).Challenge j)
  | ⟨0, h0⟩ => by nomatch h0
  | ⟨1, _⟩ => by
    simp only [Challenge, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    infer_instance

instance : ∀ j, SelectableType ((pSpecSumcheckLoop (L:=L) ℓ').Challenge j)
  := instSelectableTypeChallengeSeqCompose

instance : ∀ i, SelectableType ((pSpecFinalSumcheck (L:=L)).Challenge i)
  | ⟨0, h0⟩ => by nomatch h0 -- P->V message has no challenge

instance : ∀ i, SelectableType ((pSpecCoreInteraction (L:=L) (ℓ':=ℓ')).Challenge i) :=
  instSelectableTypeChallengeAppend

instance : ∀ i, SelectableType ((pSpecLargeFieldReduction κ (L:=L) (K:=K) (ℓ':=ℓ')).Challenge i) :=
  instSelectableTypeChallengeAppend

instance : ∀ i, SelectableType (mlIOPCS.pSpec.Challenge i) := mlIOPCS.O_challenges

instance : ∀ i, SelectableType ((fullPspec κ (L:=L) (K:=K) (ℓ':=ℓ') mlIOPCS).Challenge i) :=
  instSelectableTypeChallengeAppend

end Pspec

end
end Binius.RingSwitching
