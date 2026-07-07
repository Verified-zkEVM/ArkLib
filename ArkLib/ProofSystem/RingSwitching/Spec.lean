/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
import ArkLib.ProofSystem.RingSwitching.Prelude
import ArkLib.ProofSystem.Sumcheck.Structured.SingleRound

namespace RingSwitching

/-! ## Protocol Specs for Ring-Switching
This module contains the protocol specs, oracle index bounds,
instances of OracleInterface and SampleableType for the Ring Switching protocol.
-/

noncomputable section
open OracleSpec OracleComp ProtocolSpec Finset Polynomial MvPolynomial
open scoped NNReal
open Sumcheck.Structured

variable (κ : ℕ) [NeZero κ]
variable (L : Type) [CommRing L] [Fintype L] [DecidableEq L]
  [SampleableType L]
variable (K : Type) [CommRing K] [Fintype K] [DecidableEq K]
variable [Algebra K L]
variable (P : RingSwitchingProfile K L κ)
variable (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
variable (h_l : ℓ = ℓ' + κ)
variable (mlIOPCS : MLIOPCS L ℓ')

section Pspec

@[reducible]
def pSpecBatching : ProtocolSpec 2 :=
  ⟨![Direction.P_to_V, Direction.V_to_P],
   ![P.A, Fin κ → L]⟩

-- `pSpecSumcheckRound` was lifted to `ArkLib.ProofSystem.Sumcheck.Structured.SingleRound` as a
-- degree-neutral spec. The `WithDegree` names expose the reusable protocol shape; the historical
-- Binius ring-switching names below pin `d := 2`.
abbrev pSpecSumcheckRoundWithDegree (L : Type) [Semiring L] (d : ℕ) : ProtocolSpec 2 :=
  Sumcheck.Structured.pSpecSumcheckRound L d

abbrev pSpecSumcheckRound (L : Type) [Semiring L] : ProtocolSpec 2 :=
  pSpecSumcheckRoundWithDegree L 2

@[reducible]
def pSpecSumcheckLoopWithDegree (d : ℕ) :=
  ProtocolSpec.seqCompose (fun (_: Fin ℓ') => pSpecSumcheckRoundWithDegree L d)

@[reducible]
def pSpecSumcheckLoop := pSpecSumcheckLoopWithDegree L ℓ' 2

def pSpecFinalSumcheck : ProtocolSpec 1 := ⟨![Direction.P_to_V], ![L]⟩

@[reducible]
def pSpecCoreInteractionWithDegree (d : ℕ) :=
  (pSpecSumcheckLoopWithDegree L ℓ' d) ++ₚ (pSpecFinalSumcheck L)

@[reducible]
def pSpecCoreInteraction := pSpecCoreInteractionWithDegree L ℓ' 2

@[reducible]
def pSpecLargeFieldReduction :=
  (pSpecBatching κ L K P) ++ₚ (pSpecCoreInteraction (L:=L) (ℓ':=ℓ'))

@[reducible]
def fullPspec := (pSpecLargeFieldReduction κ (L:=L) (K:=K) P (ℓ':=ℓ')) ++ₚ (mlIOPCS.pSpec)

/-! ## Oracle Interface instances for Messages-/

instance : OracleInterface P.A := OracleInterface.instDefault
instance : OracleInterface (Fin κ → L) := OracleInterface.instDefault

instance : ∀ j, OracleInterface ((pSpecBatching κ L K P).Message j)
  | ⟨0, _⟩ => OracleInterface.instDefault -- ŝ ∈ A
  | ⟨1, _⟩ => OracleInterface.instDefault -- r'' ∈ L^κ

-- The `OracleInterface` instance for `pSpecSumcheckRound.Message` was lifted to
-- `ArkLib.ProofSystem.Sumcheck.Structured.SingleRound` along with the spec itself.
-- Anonymous instances are looked up globally regardless of namespace, so no shim is needed.

instance {d : ℕ} : ∀ j, OracleInterface ((pSpecSumcheckLoopWithDegree (L:=L) ℓ' d).Message j)
  := instOracleInterfaceMessageSeqCompose

instance : ∀ j, OracleInterface ((pSpecSumcheckLoop (L:=L) ℓ').Message j)
  := instOracleInterfaceMessageSeqCompose

instance : ∀ i, OracleInterface ((pSpecFinalSumcheck (L:=L)).Message i)
  | ⟨0, _⟩ => OracleInterface.instDefault -- final constant c

instance {d : ℕ} : ∀ i,
    OracleInterface ((pSpecCoreInteractionWithDegree (L:=L) (ℓ':=ℓ') d).Message i) :=
  instOracleInterfaceMessageAppend

instance : ∀ i, OracleInterface ((pSpecCoreInteraction (L:=L) (ℓ':=ℓ')).Message i) :=
  instOracleInterfaceMessageAppend

instance : ∀ i, OracleInterface
    ((pSpecLargeFieldReduction κ (L:=L) (K:=K) P (ℓ':=ℓ')).Message i) :=
  instOracleInterfaceMessageAppend

instance : ∀ i, OracleInterface (mlIOPCS.pSpec.Message i) := fun i => mlIOPCS.Oₘ i

instance : ∀ i, OracleInterface ((fullPspec κ (L:=L) (K:=K) P (ℓ':=ℓ') mlIOPCS).Message i) :=
  instOracleInterfaceMessageAppend

/-! ## SampleableType instances -/

instance : ∀ j, SampleableType ((pSpecBatching κ L K P).Challenge j)
  | ⟨0, h0⟩ => by nomatch h0
  | ⟨1, _⟩ => by
    simp only [Challenge, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    exact instSampleableTypeFinFunc (α := L)

-- The `SampleableType` instance for `pSpecSumcheckRound.Challenge` was lifted to
-- `ArkLib.ProofSystem.Sumcheck.Structured.SingleRound`. Anonymous instances are looked up
-- globally, so no shim is needed.

instance {d : ℕ} : ∀ j,
    SampleableType ((pSpecSumcheckLoopWithDegree (L:=L) ℓ' d).Challenge j)
  := instSampleableTypeChallengeSeqCompose

instance : ∀ j, SampleableType ((pSpecSumcheckLoop (L:=L) ℓ').Challenge j)
  := instSampleableTypeChallengeSeqCompose

instance : ∀ i, SampleableType ((pSpecFinalSumcheck (L:=L)).Challenge i)
  | ⟨0, h0⟩ => by nomatch h0 -- P->V message has no challenge

instance {d : ℕ} : ∀ i,
    SampleableType ((pSpecCoreInteractionWithDegree (L:=L) (ℓ':=ℓ') d).Challenge i) :=
  instSampleableTypeChallengeAppend

instance : ∀ i, SampleableType ((pSpecCoreInteraction (L:=L) (ℓ':=ℓ')).Challenge i) :=
  instSampleableTypeChallengeAppend

instance : ∀ i, SampleableType
    ((pSpecLargeFieldReduction κ (L:=L) (K:=K) P (ℓ':=ℓ')).Challenge i) :=
  instSampleableTypeChallengeAppend

instance : ∀ i, SampleableType (mlIOPCS.pSpec.Challenge i) := mlIOPCS.O_challenges

instance : ∀ i, SampleableType ((fullPspec κ (L:=L) (K:=K) P (ℓ':=ℓ') mlIOPCS).Challenge i) :=
  instSampleableTypeChallengeAppend

end Pspec

end
end RingSwitching
