/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
import ArkLib.ProofSystem.Binius.BinaryBasefold.Steps.Fold
import ArkLib.Data.FieldTheory.AdditiveNTT.Impl

namespace Binius.BinaryBasefold.CoreInteraction.Comp

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
open Binius.BinaryBasefold

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [SampleableType L]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}
variable {𝓑 : Fin 2 ↪ L}
variable [hdiv : Fact (ϑ ∣ ℓ)]
variable {Context : Type}

/-- Executable witness carrier for fold-round migration.

`HComp` and `tComp` use computable multivariate polynomials (`CPoly.CMvPolynomial`), and
`fComp` is index-native on the loose `Fin` carrier. -/
structure WitnessComp (i : Fin (ℓ + 1)) where
  tComp : CPoly.CMvPolynomial ℓ L
  HComp : CPoly.CMvPolynomial (ℓ - i) L
  fComp : Fin (2 ^ (ℓ + 𝓡 - i.val)) → L

section FoldStep

variable [BEq L] [LawfulBEq L]

/-- Executable projection of `Hᵢ` to `Hᵢ₊₁` by fixing the first variable to challenge `ρ`. -/
def projectToNextHComp (i : Fin ℓ) (H : CPoly.CMvPolynomial (ℓ - i) L) (ρ : L) :
    CPoly.CMvPolynomial (ℓ - i.succ) L :=
  CPoly.CMvPolynomial.bind₁ (n := ℓ - i) (m := ℓ - i.succ) (R := L)
    (f := fun j =>
      if h0 : j.val = 0 then
        CPoly.CMvPolynomial.C (n := ℓ - i.succ) (R := L) ρ
      else
        CPoly.CMvPolynomial.X (n := ℓ - i.succ) (R := L) ⟨j.val - 1, by
          have hj_pos : 0 < j.val := Nat.pos_of_ne_zero h0
          have hj_lt : j.val < ℓ - i := j.isLt
          simp only [Fin.val_succ] at hj_lt ⊢
          omega⟩)
    H

/-- Executable fold-message function from computable `Hᵢ`. -/
def foldMessageFromHComp (i : Fin ℓ) (H : CPoly.CMvPolynomial (ℓ - i) L) :
    FoldMessageComp (L := L) :=
  fun ρ =>
    ∑ x ∈ (univ.map 𝓑) ^ᶠ (ℓ - i.succ),
      CPoly.CMvPolynomial.eval
        (Fin.cons ρ x ∘ Fin.cast (by
          simp only [Fin.val_succ]
          omega))
        H

/-- Single-step executable fold update over loose index carriers. -/
def foldFunctionComp (i : Fin ℓ)
    (fIn : Fin (2 ^ (ℓ + 𝓡 - i.val)) → L) (ρ : L) :
    Fin (2 ^ (ℓ + 𝓡 - (i.val + 1))) → L :=
  fun v =>
    let src0Raw : Fin (2 ^ ((ℓ + 𝓡 - (i.val + 1)) + 1)) :=
      Nat.joinBits (low := (0 : Fin (2 ^ 1))) (high := v)
    let src1Raw : Fin (2 ^ ((ℓ + 𝓡 - (i.val + 1)) + 1)) :=
      Nat.joinBits (low := (1 : Fin (2 ^ 1))) (high := v)
    let src0 : Fin (2 ^ (ℓ + 𝓡 - i.val)) :=
      cast (by
        have h_size : ((ℓ + 𝓡 - (i.val + 1)) + 1) = (ℓ + 𝓡 - i.val) := by omega
        simp [h_size]) src0Raw
    let src1 : Fin (2 ^ (ℓ + 𝓡 - i.val)) :=
      cast (by
        have h_size : ((ℓ + 𝓡 - (i.val + 1)) + 1) = (ℓ + 𝓡 - i.val) := by omega
        simp [h_size]) src1Raw
    (1 - ρ) * fIn src0 + ρ * fIn src1

/-- Advance executable witness state across one fold round. -/
def advanceWitnessComp (i : Fin ℓ)
    (witIn : WitnessComp (L := L) (ℓ := ℓ) (𝓡 := 𝓡) i.castSucc)
    (ρ : L) :
    WitnessComp (L := L) (ℓ := ℓ) (𝓡 := 𝓡) i.succ :=
  {
    tComp := witIn.tComp
    HComp := projectToNextHComp
      (r := r) (L := L) (ℓ := ℓ) (𝓡 := 𝓡) (i := i) witIn.HComp ρ
    fComp := foldFunctionComp (r := r) (L := L) (ℓ := ℓ) (𝓡 := 𝓡) (i := i) witIn.fComp ρ
  }

/-- Prover state for the executable fold companion. -/
def foldPrvStateComp (i : Fin ℓ) : Fin (2 + 1) → Type := fun
  | ⟨0, _⟩ => Statement (L := L) Context i.castSucc ×
    (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j) ×
    WitnessComp (L := L) (ℓ := ℓ) (𝓡 := 𝓡) i.castSucc
  | ⟨1, _⟩ => Statement (L := L) Context i.castSucc ×
    (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j) ×
    WitnessComp (L := L) (ℓ := ℓ) (𝓡 := 𝓡) i.castSucc ×
      FoldMessageComp (L := L)
  | _ => Statement (L := L) Context i.castSucc ×
    (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j) ×
    WitnessComp (L := L) (ℓ := ℓ) (𝓡 := 𝓡) i.castSucc ×
      FoldMessageComp (L := L) × L

/-- Final prover-state projection for the executable fold companion. -/
def getFoldProverFinalOutputComp (i : Fin ℓ)
    (finalPrvState : foldPrvStateComp (L := L) 𝔽q β
      (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Context := Context) i 2) :
  ((Statement (L := L) Context i.succ × ((j : Fin (toOutCodewordsCount ℓ ϑ i.castSucc)) →
    OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j))
      × WitnessComp (L := L) (ℓ := ℓ) (𝓡 := 𝓡) i.succ) :=
  let (stmtIn, oStmtIn, witIn, h_i, r_i') := finalPrvState
  let stmtOut := foldVerifierStmtOutComp (L := L) i stmtIn h_i r_i'
  let oStmtOut : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j :=
    oStmtIn
  let witOut := advanceWitnessComp
    (r := r) (L := L) (ℓ := ℓ) (𝓡 := 𝓡) (i := i) witIn r_i'
  ⟨⟨stmtOut, oStmtOut⟩, witOut⟩

/-- Executable fold-round prover over `pSpecFoldComp` and `WitnessComp`. -/
def foldOracleProverComp (i : Fin ℓ) :
  OracleProver (oSpec := []ₒ)
    (StmtIn := Statement (L := L) Context i.castSucc)
    (OStmtIn := OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (WitIn := WitnessComp (L := L) (ℓ := ℓ) (𝓡 := 𝓡) i.castSucc)
    (StmtOut := Statement (L := L) Context i.succ)
    (OStmtOut := OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (WitOut := WitnessComp (L := L) (ℓ := ℓ) (𝓡 := 𝓡) i.succ)
    (pSpec := pSpecFoldComp (L := L)) where
  PrvState := foldPrvStateComp (L := L) 𝔽q β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
  input := fun ⟨⟨stmtIn, oStmtIn⟩, witIn⟩ => (stmtIn, oStmtIn, witIn)
  sendMessage
  | ⟨0, _⟩ => fun ⟨stmtIn, oStmtIn, witIn⟩ => do
    let h_i := foldMessageFromHComp
      (r := r) (L := L) (ℓ := ℓ) (𝓡 := 𝓡) (𝓑 := 𝓑) (i := i) witIn.HComp
    pure ⟨h_i, (stmtIn, oStmtIn, witIn, h_i)⟩
  | ⟨1, _⟩ => by contradiction
  receiveChallenge
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => fun ⟨stmtIn, oStmtIn, witIn, h_i⟩ => do
    pure (fun r_i' => (stmtIn, oStmtIn, witIn, h_i, r_i'))
  output := fun finalPrvState =>
    pure (getFoldProverFinalOutputComp (L := L) 𝔽q β
      (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Context := Context) i finalPrvState)

/-- Executable fold-round reduction over computable companion witness/message carriers. -/
def foldOracleReductionComp (i : Fin ℓ) :
  OracleReduction (oSpec := []ₒ)
    (StmtIn := Statement (L := L) Context i.castSucc)
    (OStmtIn := OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (WitIn := WitnessComp (L := L) (ℓ := ℓ) (𝓡 := 𝓡) i.castSucc)
    (StmtOut := Statement (L := L) Context i.succ)
    (OStmtOut := OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (WitOut := WitnessComp (L := L) (ℓ := ℓ) (𝓡 := 𝓡) i.succ)
    (pSpec := pSpecFoldComp (L := L)) where
  prover := foldOracleProverComp (L := L) 𝔽q β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (Context := Context) i
  verifier := Binius.BinaryBasefold.CoreInteraction.foldOracleVerifierComp (L := L) 𝔽q β
    (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (Context := Context) i

end FoldStep

end Binius.BinaryBasefold.CoreInteraction.Comp
