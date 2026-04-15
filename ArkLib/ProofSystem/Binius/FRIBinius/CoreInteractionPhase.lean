/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.CoreInteractionPhase
import ArkLib.ProofSystem.Binius.BinaryBasefold.ReductionLogic
import ArkLib.ProofSystem.Binius.FRIBinius.Prelude

/-!
# Core Interaction Phase of FRI-Binius IOPCS
This module implements the Core Interaction Phase of the FRI-Binius IOPCS.

This phase combines sumcheck and FRI folding using shared challenges r'ᵢ:

6. `P` and `V` both abbreviate `f^(0) := f`, and execute the following loop:
   for `i ∈ {0, ..., ℓ' - 1}` do
     `P` sends `V` the polynomial
        `h_i(X) := Σ_{w ∈ {0,1}^{ℓ'-i-1}} h(r_0', ..., r_{i-1}', X, w_0, ..., w_{ℓ'-i-2})`.
     `V` requires `s_i ?= h_i(0) + h_i(1)`. `V` samples `r_i' ← T_τ`, sets `s_{i+1} := h_i(r_i')`,
     and sends `P` `r_i'`.
     `P` defines `f^(i+1): S^(i+1) → T_τ` as the function `fold(f^(i), r_i')` of Definition 4.6.
     if `i + 1 = ℓ'` then `P` sends `c := f^(ℓ')(0, ..., 0)` to `V`.
     else if `ϑ | i + 1` then `P` submits `(submit, ℓ' + R - i - 1, f^(i+1))` to the oracle.
7. `P` sends `c := f^(ℓ')(0, ..., 0)` to `V`.
  `V` sets `e := eqTilde(φ_0(r_κ), ..., φ_0(r_{ℓ-1}), φ_1(r'_0), ..., φ_1(r'_{ℓ'-1}))`
    and decomposes `e =: Σ_{u ∈ {0,1}^κ} β_u ⊗ e_u`.
  `V` requires `s_{ℓ'} ?= (Σ_{u ∈ {0,1}^κ} eqTilde(u_0, ..., u_{κ-1},`
                                  `r''_0, ..., r''_{κ-1}) * e_u) * c`.

## Oracle reduction composition

Inside this file, `coreInteractionOracleReduction` is the composition of:
1. `LiftContext(sumcheckFoldOracleReduction)` (the lifted Binary Basefold
  sumcheck-fold reduction), then
2. `finalSumcheckOracleReduction`.

`LiftContext` here is only the bridge from batching-output shape to Binary Basefold sumcheck-fold
input shape. Concretely, it maps
`SumcheckWitness (t', H)` to `BinaryBasefold.Witness (t, H, f₀)`, where
`f₀ := getMidCodewords t challenges`, and keeps the output witness unchanged (`toFunB` is
identity on `innerWitOut`).
-/

namespace Binius.FRIBinius.CoreInteractionPhase
section

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial
  MvPolynomial TensorProduct Module Binius.BinaryBasefold Binius.RingSwitching
open scoped NNReal

-- TODO: how to make params cleaner while can explicitly reuse across sections?
variable (κ : ℕ) [NeZero κ]
variable (L : Type) [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [SampleableType L]
variable (K : Type) [Field K] [Fintype K] [DecidableEq K]
variable [h_Fq_char_prime : Fact (Nat.Prime (ringChar K))] [hF₂ : Fact (Fintype.card K = 2)]
variable [Algebra K L]
variable (β : Basis (Fin (2 ^ κ)) K L)
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable (ℓ ℓ' 𝓡 ϑ γ_repetitions : ℕ) [NeZero ℓ] [NeZero ℓ'] [NeZero 𝓡] [NeZero ϑ]
variable (h_ℓ_add_R_rate : ℓ' + 𝓡 < 2 ^ κ)
variable (h_l : ℓ = ℓ' + κ)
variable {𝓑 : Fin 2 ↪ L}
variable [hdiv : Fact (ϑ ∣ ℓ')]

section SumcheckFold

/-- Statement lens that projects SumcheckStmt to BinaryBasefold.Statement and lifts back -/
def sumcheckFoldStmtLens : OracleStatement.Lens
    (OuterStmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) 0)
    (OuterStmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ'))
    (InnerStmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) 0)
    (InnerStmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ'))
    (OuterOStmtIn := BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (OuterOStmtOut := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (InnerOStmtIn := BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (InnerOStmtOut := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ')) where
  -- Stmt and OStmt are same as in outer context, only witness changes
  toFunA := fun ⟨outerStmtIn, outerOStmtIn⟩ => ⟨outerStmtIn, outerOStmtIn⟩
  toFunB := fun ⟨_, _⟩ ⟨innerStmtOut, innerOStmtOut⟩ => ⟨innerStmtOut, innerOStmtOut⟩

/-- Executable statement lens over explicit basis values. -/
private def sumcheckFoldStmtLensExec
    (βfun : Fin (2 ^ κ) → L)
    [Fact (LinearIndependent K βfun)] [Fact (βfun 0 = 1)] : OracleStatement.Lens
    (OuterStmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) 0)
    (OuterStmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ'))
    (InnerStmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) 0)
    (InnerStmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ'))
    (OuterOStmtIn := BinaryBasefold.OracleStatement K βfun (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (OuterOStmtOut := BinaryBasefold.OracleStatement K βfun
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (InnerOStmtIn := BinaryBasefold.OracleStatement K βfun (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (InnerOStmtOut := BinaryBasefold.OracleStatement K βfun
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ')) where
  toFunA := fun ⟨outerStmtIn, outerOStmtIn⟩ => ⟨outerStmtIn, outerOStmtIn⟩
  toFunB := fun ⟨_, _⟩ ⟨innerStmtOut, innerOStmtOut⟩ => ⟨innerStmtOut, innerOStmtOut⟩

/-- Oracle context lens for sumcheck fold lifting over explicit basis values. -/
def sumcheckFoldCtxLens
    (βfun : Fin (2 ^ κ) → L)
    [Fact (LinearIndependent K βfun)] [Fact (βfun 0 = 1)] : OracleContext.Lens
    (OuterStmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) 0)
    (OuterStmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ'))
    (InnerStmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) 0)
    (InnerStmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ'))
    (OuterOStmtIn := BinaryBasefold.OracleStatement K βfun (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (OuterOStmtOut := BinaryBasefold.OracleStatement K βfun
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (InnerOStmtIn := BinaryBasefold.OracleStatement K βfun (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (InnerOStmtOut := BinaryBasefold.OracleStatement K βfun
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (OuterWitIn := RingSwitching.SumcheckWitness L ℓ' 0)
    (OuterWitOut := BinaryBasefold.Witness K βfun
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') (Fin.last ℓ'))
    (InnerWitIn := BinaryBasefold.Witness K βfun (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') 0)
    (InnerWitOut := BinaryBasefold.Witness K βfun
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') (Fin.last ℓ')) where
  wit := {
    toFunA := fun ⟨⟨outerStmtIn, _outerOStmtIn⟩, outerWitIn⟩ => by
      let t : BinaryBasefold.MultilinearPoly L ℓ' :=
        BinaryBasefold.MultilinearPoly.ofCMvPoly outerWitIn.t'
      let H : BinaryBasefold.MultiquadraticPoly L (ℓ' - 0) :=
        BinaryBasefold.MultiquadraticPoly.ofCMvPoly outerWitIn.H
      let f₀ : OracleFunction K βfun (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        ⟨0, by omega⟩ :=
        BinaryBasefold.getMidCodewords K βfun (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := (0 : Fin (ℓ' + 1))) (t := t) (challenges := outerStmtIn.challenges)
      exact { t := t, H := H, f := f₀ }
    toFunB := fun ⟨⟨_outerStmtIn, _outerOStmtIn⟩, _outerWitIn⟩
      ⟨⟨_innerStmtOut, _innerOStmtOut⟩, innerWitOut⟩ => innerWitOut
  }
  stmt := sumcheckFoldStmtLensExec (κ := κ) (L := L) (K := K) (ℓ := ℓ) (ℓ' := ℓ')
    (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) βfun

/-- Extractor lens for sumcheck fold lifting -/
def sumcheckFoldExtractorLens : Extractor.Lens
    (OuterStmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) 0 ×
      (∀ j, OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0 j))
    (OuterStmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ')
      ×(∀ j, OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ') j))
    (InnerStmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) 0 ×
      (∀ j, OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0 j))
    (InnerStmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ')
      × (∀ j, OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ') j))
    (OuterWitIn := RingSwitching.SumcheckWitness L ℓ' 0)
    (OuterWitOut := BinaryBasefold.Witness K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (ℓ:=ℓ') (Fin.last ℓ'))
    (InnerWitIn := Witness K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') 0)
    (InnerWitOut := Witness K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') (Fin.last ℓ')) where
  stmt := sumcheckFoldStmtLens κ L K β ℓ ℓ' 𝓡 ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  wit := {
    toFunA := fun ⟨⟨outerStmtIn, outerOStmtIn⟩, outerWitOut⟩ => outerWitOut
    toFunB := fun ⟨⟨outerStmtIn, outerOStmtIn⟩, outerWitOut⟩ innerWitIn => by
      let outerWitIn : SumcheckWitness L ℓ' 0 := {
        t' := MultilinearPoly.toCMvPoly innerWitIn.t
        H := innerWitIn.H
      }
      exact outerWitIn
  }

private def sumcheckFoldOracleVerifierExec
    (βfun : Fin (2 ^ κ) → L)
    [Fact (LinearIndependent K βfun)] [Fact (βfun 0 = 1)]
    (mp : SumcheckMultiplierParam L ℓ' (RingSwitchingBaseContext κ L K ℓ)) :=
  (BinaryBasefold.CoreInteraction.sumcheckFoldOracleVerifier K βfun (ϑ := ϑ)
    (mp := mp) (𝓑 := 𝓑) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).liftContext
      (lens := sumcheckFoldStmtLensExec (κ := κ) (L := L) (K := K) (ℓ := ℓ) (ℓ' := ℓ')
        (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) βfun)

private def sumcheckFoldOracleReductionExec
    (βfun : Fin (2 ^ κ) → L)
    [Fact (LinearIndependent K βfun)] [Fact (βfun 0 = 1)]
    (mp : SumcheckMultiplierParam L ℓ' (RingSwitchingBaseContext κ L K ℓ)) :=
  (BinaryBasefold.CoreInteraction.sumcheckFoldOracleReduction K βfun (ϑ := ϑ)
    (mp := mp) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)).liftContext
      (lens := sumcheckFoldCtxLens (κ := κ) (L := L) (K := K) (ℓ := ℓ) (ℓ' := ℓ')
        (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_l := h_l) βfun)

@[reducible]
def sumcheckFoldOracleVerifier
    (βfun : Fin (2 ^ κ) → L)
    [Fact (LinearIndependent K βfun)] [Fact (βfun 0 = 1)]
    (mp : SumcheckMultiplierParam L ℓ' (RingSwitchingBaseContext κ L K ℓ)) :=
  sumcheckFoldOracleVerifierExec (κ := κ) (L := L) (K := K) (ℓ := ℓ) (ℓ' := ℓ')
    (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
    βfun mp

@[reducible]
def sumcheckFoldOracleReduction
    (βfun : Fin (2 ^ κ) → L)
    [Fact (LinearIndependent K βfun)] [Fact (βfun 0 = 1)]
    (mp : SumcheckMultiplierParam L ℓ' (RingSwitchingBaseContext κ L K ℓ)) :=
  sumcheckFoldOracleReductionExec (κ := κ) (L := L) (K := K) (ℓ := ℓ) (ℓ' := ℓ')
    (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_l := h_l) (𝓑 := 𝓑)
    βfun mp

-- Security properties for the lifted oracle reduction

section Security

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

instance sumcheckFoldBetaFun_linearIndependent :
    Fact (LinearIndependent K (fun i => β i)) := by
  exact ⟨β.linearIndependent⟩

instance sumcheckFoldBetaFun_zero_eq_one :
    Fact ((fun i => β i) 0 = 1) := by
  exact h_β₀_eq_1

-- Completeness instance for the context lens
instance sumcheckFoldCtxLens_complete :
  (sumcheckFoldCtxLens (κ := κ) (L := L) (K := K) (ℓ := ℓ) (ℓ' := ℓ')
    (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_l := h_l)
    (βfun := fun i => β i)).toContext.IsComplete
    (OuterStmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) 0 ×
      (∀ i, BinaryBasefold.OracleStatement K (⇑β) ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 i))
    (OuterStmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ') ×
      (∀ i, BinaryBasefold.OracleStatement K (⇑β) ϑ
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ') i))
    (InnerStmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) 0 ×
      (∀ i, BinaryBasefold.OracleStatement K (⇑β) ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 i))
    (InnerStmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ') ×
      (∀ i, BinaryBasefold.OracleStatement K (⇑β) ϑ
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ') i))
    (OuterWitIn := RingSwitching.SumcheckWitness L ℓ' 0)
    (OuterWitOut := BinaryBasefold.Witness K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') (Fin.last ℓ'))
    (InnerWitIn := Witness K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') 0)
    (InnerWitOut := Witness K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') (Fin.last ℓ'))
    (outerRelIn := RingSwitching.strictSumcheckRoundRelation κ L K
      (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l (𝓑 := 𝓑)
      (aOStmtIn := BinaryBasefoldAbstractOStmtIn
        (κ := κ) (L := L) (K := K) (β := β)
        (ℓ' := ℓ') (𝓡 := 𝓡) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) 0)
    (outerRelOut :=
      BinaryBasefold.strictRoundRelation (mp := RingSwitching_SumcheckMultParam κ L K
        (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l) K β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) (Fin.last ℓ')
    )
    (innerRelIn :=
      BinaryBasefold.strictRoundRelation (mp := RingSwitching_SumcheckMultParam κ L K
        (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l) K β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) 0
    )
    (innerRelOut :=
      BinaryBasefold.strictRoundRelation (mp := RingSwitching_SumcheckMultParam κ L K
        (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l) K β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) (Fin.last ℓ')
    )
    (compat :=
      let originalReduction := (CoreInteraction.sumcheckFoldOracleReduction K β (ϑ:=ϑ)
        (mp := RingSwitching_SumcheckMultParam κ L K (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)).toReduction
      Reduction.compatContext (oSpec := []ₒ) (pSpec :=
        pSpecSumcheckFold K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
        (sumcheckFoldCtxLens (κ := κ) (L := L) (K := K) (ℓ := ℓ) (ℓ' := ℓ')
          (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_l := h_l)
          (βfun := fun i => β i)).toContext originalReduction
    ) := by
  sorry

omit [NeZero κ] [NeZero ℓ] in
-- Perfect completeness for the lifted oracle reduction
theorem sumcheckFoldOracleReduction_perfectCompleteness (hInit : NeverFail init) :
  OracleReduction.perfectCompleteness
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) 0)
    (OStmtIn := BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (WitIn := RingSwitching.SumcheckWitness L ℓ' 0)
    (StmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ'))
    (OStmtOut := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (WitOut := BinaryBasefold.Witness K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') (Fin.last ℓ'))
    (pSpec := BinaryBasefold.pSpecSumcheckFold K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (relIn := RingSwitching.strictSumcheckRoundRelation κ L K
      (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l (𝓑 := 𝓑)
      (aOStmtIn := BinaryBasefoldAbstractOStmtIn (β := β) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) 0)
    (relOut :=
      BinaryBasefold.strictRoundRelation (mp := RingSwitching_SumcheckMultParam κ L K
        (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l) K β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) (Fin.last ℓ')
    )
    (oracleReduction := sumcheckFoldOracleReduction (κ := κ) (L := L) (K := K)
      (ℓ := ℓ) (ℓ' := ℓ') (𝓡 := 𝓡) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_l := h_l) (𝓑 := 𝓑)
      (βfun := fun i => β i)
      (mp := RingSwitching_SumcheckMultParam κ L K
        (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l))
    (init := init)
    (impl := impl) := by
  sorry

/-- Knowledge soundness instance for the extractor lens. This one is compatStmt-agnostic -/
instance sumcheckFoldExtractorLens_rbr_knowledge_soundness
    {compatStmt :
      (Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) 0 ×
        (∀ i, BinaryBasefold.OracleStatement K (⇑β) ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 i)) →
      (Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ') ×
        (∀ i, BinaryBasefold.OracleStatement K (⇑β) ϑ
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ') i)) → Prop} :
    Extractor.Lens.IsKnowledgeSound
      (OuterStmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) 0 ×
        (∀ i, BinaryBasefold.OracleStatement K (⇑β) ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 i))
      (OuterStmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ)
        (Fin.last ℓ') × (∀ i, BinaryBasefold.OracleStatement K (⇑β) ϑ
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ') i))
      (InnerStmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) 0 ×
        (∀ i, BinaryBasefold.OracleStatement K (⇑β) ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 i))
      (InnerStmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ)
        (Fin.last ℓ') × (∀ i, BinaryBasefold.OracleStatement K (⇑β) ϑ
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ') i))
      (OuterWitIn := RingSwitching.SumcheckWitness L ℓ' 0)
      (OuterWitOut := BinaryBasefold.Witness K β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') (Fin.last ℓ'))
      (InnerWitIn := Witness K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') 0)
      (InnerWitOut := Witness K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') (Fin.last ℓ'))
      (outerRelIn := RingSwitching.sumcheckRoundRelation κ L K
        (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l (𝓑 := 𝓑)
        (BinaryBasefoldAbstractOStmtIn
          (κ := κ) (L := L) (K := K) (β := β)
          (ℓ' := ℓ') (𝓡 := 𝓡) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) 0)
      (outerRelOut :=
        BinaryBasefold.roundRelation (mp := RingSwitching_SumcheckMultParam κ L K
          (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l) K β (ϑ:=ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑)  (Fin.last ℓ')
      )
      (innerRelIn :=
        BinaryBasefold.roundRelation (mp := RingSwitching_SumcheckMultParam κ L K
          (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l) K β (ϑ:=ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑)  0
      )
      (innerRelOut :=
        BinaryBasefold.roundRelation (mp := RingSwitching_SumcheckMultParam κ L K
          (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l) K β (ϑ:=ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑)  (Fin.last ℓ')
      )
      (compatStmt := compatStmt)
      (compatWit := fun _ _ => True)
      (lens := sumcheckFoldExtractorLens κ L K β ℓ ℓ' 𝓡 ϑ
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) := by
  sorry

-- Round-by-round knowledge soundness for the lifted oracle verifier
theorem sumcheckFoldOracleVerifier_rbrKnowledgeSoundness [Fintype L] :
    OracleVerifier.rbrKnowledgeSoundness
      (oSpec := []ₒ)
      (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) 0)
      (OStmtIn := BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
      (WitIn := RingSwitching.SumcheckWitness L ℓ' 0)
      (StmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ'))
      (OStmtOut := BinaryBasefold.OracleStatement K β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
      (WitOut := BinaryBasefold.Witness K β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') (Fin.last ℓ'))
      (pSpec := BinaryBasefold.pSpecSumcheckFold K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (relIn := RingSwitching.sumcheckRoundRelation κ L K
        (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l (𝓑 := 𝓑)
        (BinaryBasefoldAbstractOStmtIn
          (κ := κ) (L := L) (K := K) (β := β)
          (ℓ' := ℓ') (𝓡 := 𝓡) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) 0)
      (relOut :=
        BinaryBasefold.roundRelation (mp := RingSwitching_SumcheckMultParam κ L K
          (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l) K β (ϑ:=ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑)  (Fin.last ℓ')
      )
      (verifier := sumcheckFoldOracleVerifier (κ := κ) (L := L) (K := K)
        (ℓ := ℓ) (ℓ' := ℓ') (𝓡 := 𝓡) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
        (βfun := fun i => β i)
        (mp := RingSwitching_SumcheckMultParam κ L K
          (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l))
      (init := init)
      (impl := impl)
      (rbrKnowledgeError := BinaryBasefold.CoreInteraction.sumcheckFoldKnowledgeError
        K β (ϑ := ϑ)) := by
  sorry

end Security
end SumcheckFold

section FinalSumcheckStep
/-!
## Final Sumcheck Step
-/

/-! ## Pure Logic Functions (ReductionLogicStep Infrastructure) -/

/-- Pure verifier check for FRI final sumcheck step. -/
@[reducible]
def finalSumcheckVerifierCheck
    (stmtIn : Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ'))
    (c : L) : Prop :=
  let eq_tilde_eval : L := RingSwitching.compute_final_eq_value κ L K
    (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l
    stmtIn.ctx.t_eval_point stmtIn.challenges stmtIn.ctx.r_batching
  stmtIn.sumcheck_target = eq_tilde_eval * c

/-- Pure verifier output for FRI final sumcheck step. -/
@[reducible]
def finalSumcheckVerifierStmtOut
    (stmtIn : Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ'))
    (c : L) : BinaryBasefold.FinalSumcheckStatementOut (L := L) (ℓ := ℓ') := {
      ctx := {
        t_eval_point := getEvaluationPointSuffix κ L ℓ ℓ' h_l stmtIn.ctx.t_eval_point
        original_claim := stmtIn.ctx.original_claim
      }
      sumcheck_target := stmtIn.sumcheck_target
      challenges := stmtIn.challenges
      final_constant := c
    }

/-- Pure prover message computation for FRI final sumcheck step. -/
@[reducible]
def finalSumcheckProverComputeMsg
    (witIn : BinaryBasefold.Witness K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') (Fin.last ℓ')) : L :=
  witIn.f ⟨0, by simp only [zero_mem]⟩

/-- Pure prover output witness for FRI final sumcheck step. -/
@[reducible]
def finalSumcheckProverWitOut : Unit := ()

/-- Executable verifier check using explicit multiplier data. -/
private def finalSumcheckVerifierCheckExec
    (mp : SumcheckMultiplierParam L ℓ' (RingSwitchingBaseContext κ L K ℓ))
    (stmtIn : Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ'))
    (c : L) : Prop :=
  stmtIn.sumcheck_target = ((mp.multpoly stmtIn.ctx).val.eval stmtIn.challenges) * c

/-- Executable prover message computation over explicit basis values. -/
private def finalSumcheckProverComputeMsgExec
    (βfun : Fin (2 ^ κ) → L)
    [Fact (LinearIndependent K βfun)] [Fact (βfun 0 = 1)]
    (witIn : BinaryBasefold.Witness K βfun
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') (Fin.last ℓ')) : L :=
  witIn.f ⟨0, by simp only [zero_mem]⟩

/-! ## ReductionLogicStep Instance -/

/-- The logic instance for the FRI final sumcheck step. -/
def finalSumcheckStepLogic :
    Binius.BinaryBasefold.ReductionLogicStep
      (Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ'))
      (BinaryBasefold.Witness K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') (Fin.last ℓ'))
      (BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
      (BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
      (BinaryBasefold.FinalSumcheckStatementOut (L := L) (ℓ := ℓ'))
      Unit
      (BinaryBasefold.pSpecFinalSumcheckStep (L := L)) :=
  { completeness_relIn := fun ((stmt, oStmt), wit) =>
      ((stmt, oStmt), wit) ∈ BinaryBasefold.strictRoundRelation
        (mp := RingSwitching_SumcheckMultParam κ L K
        (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l) K β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (Fin.last ℓ')
    completeness_relOut := fun ((stmtOut, oStmtOut), witOut) =>
      ((stmtOut, oStmtOut), witOut) ∈ BinaryBasefold.strictFinalSumcheckRelOut K β
        (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    verifierCheck := fun stmtIn transcript =>
      finalSumcheckVerifierCheck κ L K β ℓ ℓ' h_l stmtIn (transcript.messages ⟨0, rfl⟩)
    verifierOut := fun stmtIn transcript =>
      finalSumcheckVerifierStmtOut κ L K ℓ ℓ' h_l stmtIn (transcript.messages ⟨0, rfl⟩)
    embed := ⟨fun j => Sum.inl j, fun a b h => by cases h; rfl⟩
    hEq := fun _ => rfl
    honestProverTranscript := fun _stmtIn witIn _oStmtIn _chal =>
      let c : L := finalSumcheckProverComputeMsg (κ := κ) (L := L) (K := K) (β := β)
        (ℓ' := ℓ') (𝓡 := 𝓡) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) witIn
      FullTranscript.mk1 c
    proverOut := fun stmtIn _witIn oStmtIn transcript =>
      let c : L := transcript.messages ⟨0, rfl⟩
      let stmtOut := finalSumcheckVerifierStmtOut κ L K ℓ ℓ' h_l stmtIn c
      ((stmtOut, oStmtIn), ()) }

private def finalSumcheckStepLogicExec
    (βfun : Fin (2 ^ κ) → L)
    [Fact (LinearIndependent K βfun)] [Fact (βfun 0 = 1)]
    (mp : SumcheckMultiplierParam L ℓ' (RingSwitchingBaseContext κ L K ℓ)) :
    Binius.BinaryBasefold.ReductionLogicStep
      (Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ'))
      (BinaryBasefold.Witness K βfun (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') (Fin.last ℓ'))
      (BinaryBasefold.OracleStatement K βfun (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
      (BinaryBasefold.OracleStatement K βfun (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
      (BinaryBasefold.FinalSumcheckStatementOut (L := L) (ℓ := ℓ'))
      Unit
      (BinaryBasefold.pSpecFinalSumcheckStep (L := L)) where
  completeness_relIn := fun ((stmt, oStmt), wit) =>
    ((stmt, oStmt), wit) ∈ BinaryBasefold.strictRoundRelation (mp := mp) K βfun (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (Fin.last ℓ')
  completeness_relOut := fun ((stmtOut, oStmtOut), witOut) =>
    ((stmtOut, oStmtOut), witOut) ∈ BinaryBasefold.strictFinalSumcheckRelOut K βfun
      (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  verifierCheck := fun stmtIn transcript =>
    finalSumcheckVerifierCheckExec (κ := κ) (L := L) (K := K) (ℓ := ℓ) (ℓ' := ℓ')
      (mp := mp) stmtIn (transcript.messages ⟨0, rfl⟩)
  verifierOut := fun stmtIn transcript =>
    finalSumcheckVerifierStmtOut κ L K ℓ ℓ' h_l stmtIn (transcript.messages ⟨0, rfl⟩)
  embed := ⟨fun j => Sum.inl j, fun a b h => by cases h; rfl⟩
  hEq := fun _ => rfl
  honestProverTranscript := fun _stmtIn witIn _oStmtIn _chal =>
    let c : L := finalSumcheckProverComputeMsgExec (κ := κ) (L := L) (K := K)
      (ℓ' := ℓ') (𝓡 := 𝓡) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) βfun witIn
    FullTranscript.mk1 c
  proverOut := fun stmtIn _witIn oStmtIn transcript =>
    let c : L := transcript.messages ⟨0, rfl⟩
    let stmtOut := finalSumcheckVerifierStmtOut κ L K ℓ ℓ' h_l stmtIn c
    ((stmtOut, oStmtIn), ())

/-- The verifier for the final sumcheck step over explicit basis/multiplier inputs. -/
def finalSumcheckVerifier
    (βfun : Fin (2 ^ κ) → L)
    [Fact (LinearIndependent K βfun)] [Fact (βfun 0 = 1)]
    (mp : SumcheckMultiplierParam L ℓ' (RingSwitchingBaseContext κ L K ℓ)) :
  OracleVerifier
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ'))
    (OStmtIn := BinaryBasefold.OracleStatement K βfun
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (StmtOut := BinaryBasefold.FinalSumcheckStatementOut (L := L) (ℓ := ℓ'))
    (OStmtOut := BinaryBasefold.OracleStatement K βfun
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (pSpec := BinaryBasefold.pSpecFinalSumcheckStep (L := L)) where
  verify := fun stmtIn _ => do
    let s' : L ← query (spec := [(BinaryBasefold.pSpecFinalSumcheckStep
      (L := L)).Message]ₒ) ⟨⟨0, by rfl⟩, (by exact ())⟩
    let c : L := s'
    let t := FullTranscript.mk1 (pSpec := BinaryBasefold.pSpecFinalSumcheckStep (L := L)) s'
    have : Decidable
        (finalSumcheckVerifierCheckExec (κ := κ) (L := L) (K := K) (ℓ := ℓ) (ℓ' := ℓ')
          (mp := mp) stmtIn c) := by
      change Decidable
        (stmtIn.sumcheck_target =
          ((mp.multpoly stmtIn.ctx).val.eval stmtIn.challenges) * c)
      infer_instance
    guard (finalSumcheckVerifierCheckExec (κ := κ) (L := L) (K := K) (ℓ := ℓ) (ℓ' := ℓ')
      (mp := mp) stmtIn c)
    pure (finalSumcheckVerifierStmtOut κ L K ℓ ℓ' h_l stmtIn c)
  embed := (finalSumcheckStepLogicExec (κ := κ) (L := L) (K := K)
    (ℓ := ℓ) (ℓ' := ℓ') (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (h_l := h_l) (𝓑 := 𝓑) βfun mp).embed
  hEq := (finalSumcheckStepLogicExec (κ := κ) (L := L) (K := K)
    (ℓ := ℓ) (ℓ' := ℓ') (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (h_l := h_l) (𝓑 := 𝓑) βfun mp).hEq

/-- Executable prover for the final sumcheck step. -/
private def finalSumcheckProverExec
    (βfun : Fin (2 ^ κ) → L)
    [Fact (LinearIndependent K βfun)] [Fact (βfun 0 = 1)]
    (mp : SumcheckMultiplierParam L ℓ' (RingSwitchingBaseContext κ L K ℓ)) :
  OracleProver
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ'))
    (OStmtIn := BinaryBasefold.OracleStatement K βfun
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (WitIn := BinaryBasefold.Witness K βfun
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') (Fin.last ℓ'))
    (StmtOut := BinaryBasefold.FinalSumcheckStatementOut (L := L) (ℓ := ℓ'))
    (OStmtOut := BinaryBasefold.OracleStatement K βfun
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (WitOut := Unit)
    (pSpec := BinaryBasefold.pSpecFinalSumcheckStep (L := L)) where
  PrvState := fun
    | 0 => Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ')
      × (∀ j, BinaryBasefold.OracleStatement K βfun
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ') j)
      × BinaryBasefold.Witness K βfun
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') (Fin.last ℓ')
    | _ => Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ')
      × (∀ j, BinaryBasefold.OracleStatement K βfun
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ') j)
      × BinaryBasefold.Witness K βfun
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') (Fin.last ℓ')
      × L
  input := fun ⟨⟨stmt, oStmt⟩, wit⟩ => (stmt, oStmt, wit)
  sendMessage
    | ⟨0, _⟩ => fun ⟨stmtIn, oStmtIn, witIn⟩ => do
      let c : L := finalSumcheckProverComputeMsgExec (κ := κ) (L := L) (K := K)
        (ℓ' := ℓ') (𝓡 := 𝓡) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) βfun witIn
      pure ⟨c, (stmtIn, oStmtIn, witIn, c)⟩
  receiveChallenge
    | ⟨0, h⟩ => nomatch h
  output := fun ⟨stmtIn, oStmtIn, witIn, s'⟩ => do
    let logic := finalSumcheckStepLogicExec (κ := κ) (L := L) (K := K)
      (ℓ := ℓ) (ℓ' := ℓ') (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (h_l := h_l) (𝓑 := 𝓑) βfun mp
    let t := FullTranscript.mk1 (pSpec := BinaryBasefold.pSpecFinalSumcheckStep (L := L)) s'
    pure (logic.proverOut stmtIn witIn oStmtIn t)

/-- Executable reduction for the final sumcheck step. -/
private def finalSumcheckOracleReductionExec
    (βfun : Fin (2 ^ κ) → L)
    [Fact (LinearIndependent K βfun)] [Fact (βfun 0 = 1)]
    (mp : SumcheckMultiplierParam L ℓ' (RingSwitchingBaseContext κ L K ℓ)) :
    OracleReduction
        (oSpec := []ₒ)
        (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ)
          (Fin.last ℓ'))
        (OStmtIn := BinaryBasefold.OracleStatement K βfun
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
        (WitIn := BinaryBasefold.Witness K βfun
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') (Fin.last ℓ'))
        (StmtOut := BinaryBasefold.FinalSumcheckStatementOut (L := L) (ℓ := ℓ'))
        (OStmtOut := BinaryBasefold.OracleStatement K βfun
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
        (WitOut := Unit)
        (pSpec := BinaryBasefold.pSpecFinalSumcheckStep (L := L)) where
  prover := finalSumcheckProverExec (κ := κ) (L := L) (K := K) (ℓ := ℓ)
    (ℓ' := ℓ') (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_l := h_l)
    (𝓑 := 𝓑) βfun mp
  verifier := finalSumcheckVerifier (κ := κ) (L := L) (K := K) (ℓ := ℓ)
    (ℓ' := ℓ') (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_l := h_l)
    (𝓑 := 𝓑) βfun mp

/-- The prover for the final sumcheck step -/
def finalSumcheckProver :
  OracleProver
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ'))
    (OStmtIn := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (WitIn := BinaryBasefold.Witness K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') (Fin.last ℓ'))
    (StmtOut := BinaryBasefold.FinalSumcheckStatementOut (L := L) (ℓ := ℓ'))
    (OStmtOut := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (WitOut := Unit)
    (pSpec := BinaryBasefold.pSpecFinalSumcheckStep (L := L)) where
  PrvState := fun
    | 0 => Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ')
      × (∀ j, BinaryBasefold.OracleStatement K β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ') j)
      × BinaryBasefold.Witness K β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') (Fin.last ℓ')
    | _ => Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ')
      × (∀ j, BinaryBasefold.OracleStatement K β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ') j)
      × BinaryBasefold.Witness K β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') (Fin.last ℓ')
      × L
  input := fun ⟨⟨stmt, oStmt⟩, wit⟩ => (stmt, oStmt, wit)
  sendMessage
    | ⟨0, _⟩ => fun ⟨stmtIn, oStmtIn, witIn⟩ => do
      let c : L := finalSumcheckProverComputeMsg (κ := κ) (L := L) (K := K) (β := β)
        (ℓ' := ℓ') (𝓡 := 𝓡) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) witIn
      pure ⟨c, (stmtIn, oStmtIn, witIn, c)⟩
  receiveChallenge
    | ⟨0, h⟩ => nomatch h
  output := fun ⟨stmtIn, oStmtIn, witIn, s'⟩ => do
    let logic := finalSumcheckStepLogic κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l (𝓑 := 𝓑)
    let t := FullTranscript.mk1 (pSpec := BinaryBasefold.pSpecFinalSumcheckStep (L := L)) s'
    pure (logic.proverOut stmtIn witIn oStmtIn t)

/-- The oracle reduction for the final sumcheck step -/
@[reducible]
def finalSumcheckOracleReduction
    (βfun : Fin (2 ^ κ) → L)
    [Fact (LinearIndependent K βfun)] [Fact (βfun 0 = 1)]
    (mp : SumcheckMultiplierParam L ℓ' (RingSwitchingBaseContext κ L K ℓ)) :=
  finalSumcheckOracleReductionExec (κ := κ) (L := L) (K := K) (ℓ := ℓ) (ℓ' := ℓ')
    (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_l := h_l)
    (𝓑 := 𝓑) βfun mp

/-- At `Fin.last ℓ'`, sumcheck consistency simplifies to a single evaluation. -/
lemma sumcheckConsistency_at_last_simplifies
    (target : L) (H : BinaryBasefold.MultiquadraticPoly L (ℓ' - Fin.last ℓ'))
    (h_cons : BinaryBasefold.sumcheckConsistencyProp (𝓑 := 𝓑) target H) :
    target = H.val.eval (fun _ => (0 : L)) := by
  simp only [Fin.val_last] at H h_cons ⊢
  simp only [BinaryBasefold.sumcheckConsistencyProp] at h_cons
  haveI : IsEmpty (Fin 0) := Fin.isEmpty
  rw [Finset.sum_eq_single (a := fun _ => 0)
    (h₀ := fun b _ hb_ne => by
      exfalso
      apply hb_ne
      funext i
      simp only [tsub_self] at i
      exact i.elim0)
    (h₁ := fun h_not_mem => by
      exfalso
      apply h_not_mem
      simp only [Fintype.mem_piFinset]
      intro i
      simp only [tsub_self] at i
      exact i.elim0)] at h_cons
  exact h_cons

/-- The final codeword value at `0` equals `t(challenges)`. -/
lemma finalCodeword_zero_eq_t_eval
    (stmtIn : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ'))
    (witIn : BinaryBasefold.Witness K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') (Fin.last ℓ'))
    (h_wit_struct : BinaryBasefold.witnessStructuralInvariant K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (mp := RingSwitching_SumcheckMultParam κ L K
        (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l)
      (stmt := stmtIn) (wit := witIn)) :
    witIn.f ⟨0, by simp only [zero_mem]⟩ = witIn.t.val.eval stmtIn.challenges := by
  sorry

omit [SampleableType L] [NeZero κ] [NeZero ℓ] in
/-- Strict helper: folding the last oracle block in the final sumcheck step yields
the constant function equal to the prover message `witIn.f(0)`. -/
lemma iterated_fold_to_const_strict
    (stmtIn : Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ'))
    (witIn : BinaryBasefold.Witness K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') (Fin.last ℓ'))
    (oStmtIn : ∀ j, BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ') j)
    (h_strictOracleWitConsistency_In : BinaryBasefold.strictOracleWitnessConsistency K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Context := RingSwitchingBaseContext κ L K ℓ)
      (mp := RingSwitching_SumcheckMultParam κ L K
        (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l)
      (stmtIdx := Fin.last ℓ')
      (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ'))
      (stmt := stmtIn) (wit := witIn) (oStmt := oStmtIn)) :
    let c : L := witIn.f ⟨0, by simp only [zero_mem]⟩
    let lastDomainIdx := getLastOracleDomainIndex ℓ' ϑ (Fin.last ℓ')
    let k := lastDomainIdx.val
    have h_k : k = ℓ' - ϑ := by
      dsimp only [k, lastDomainIdx]
      rw [getLastOraclePositionIndex_last, Nat.sub_mul, Nat.one_mul,
        Nat.div_mul_cancel (hdiv.out)]
    let curDomainIdx : Fin (2 ^ κ) := ⟨k, by
      rw [h_k]
      omega
    ⟩
    have h_destIdx_eq : curDomainIdx.val = lastDomainIdx.val := rfl
    let f_k : OracleFunction K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) curDomainIdx :=
      getLastOracle (h_destIdx := h_destIdx_eq) (oracleFrontierIdx := Fin.last ℓ')
        K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (oStmt := oStmtIn)
    let finalChallenges : Fin ϑ → L := fun cId => stmtIn.challenges ⟨k + cId, by
      rw [h_k]
      have h_le : ϑ ≤ ℓ' := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ') (hdiv.out)
      have h_cId : cId.val < ϑ := cId.isLt
      have h_last : (Fin.last ℓ').val = ℓ' := rfl
      omega
    ⟩
    let destDomainIdx : Fin (2 ^ κ) := ⟨k + ϑ, by
      rw [h_k]
      have h_le : ϑ ≤ ℓ' := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ') (hdiv.out)
      omega
    ⟩
    let folded := iterated_fold K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := curDomainIdx) (steps := ϑ) (destIdx := destDomainIdx) (h_destIdx := by rfl)
      (h_destIdx_le := by
        dsimp only [destDomainIdx, k, lastDomainIdx]
        rw [getLastOraclePositionIndex_last, Nat.sub_mul, Nat.one_mul,
          Nat.div_mul_cancel (hdiv.out)]
        rw [Nat.sub_add_cancel (by
          exact Nat.le_of_dvd (h := by exact Nat.pos_of_neZero ℓ') (hdiv.out))]
      ) (f := f_k)
      (r_challenges := finalChallenges)
    ∀ y, folded y = c := by
  sorry
/-
  have h_ϑ_le_ℓ' : ϑ ≤ ℓ' := by
    apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ') (hdiv.out)
  intro c lastDomainIdx k h_k curDomainIdx h_destIdx_eq f_k finalChallenges destDomainIdx folded
  let P₀ : L[X]_(2 ^ ℓ') := computablePolynomialFromNovelCoeffsF₂ K β ℓ' (by omega)
    (fun ω => witIn.t.val.eval (bitsOfIndex ω))
  let f₀ := polyToOracleFunc K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := 0) (P := P₀)
  have h_wit_struct := h_strictOracleWitConsistency_In.1
  have h_strict_oracle_folding := h_strictOracleWitConsistency_In.2
  dsimp only [Fin.val_last, OracleFrontierIndex.val_mkFromStmtIdx,
    strictOracleFoldingConsistencyProp] at h_strict_oracle_folding
  have h_eq : folded = fun x => c := by
    dsimp only [folded, f_k]
    have h_f_last_consistency := h_strict_oracle_folding
      (j := (getLastOraclePositionIndex ℓ' ϑ (Fin.last ℓ')))
    have h_wit_f_eq : witIn.f = getMidCodewords K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) witIn.t stmtIn.challenges := h_wit_struct.2
    dsimp only [Fin.val_last, getMidCodewords] at h_wit_f_eq
    dsimp only [c]
    conv_rhs =>
      rw [h_wit_f_eq]
      simp only [Fin.val_last]
    have h_curDomainIdx_eq : curDomainIdx = ⟨ℓ' - ϑ, by omega⟩ := by
      dsimp [curDomainIdx, k, lastDomainIdx]
      simp only [Fin.mk.injEq]
      rw [getLastOraclePositionIndex_last, Nat.sub_mul, Nat.div_mul_cancel (hdiv.out)]
      simp only [one_mul]
    let res := iterated_fold_congr_source_index K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := curDomainIdx) (i' := ⟨ℓ' - ϑ, by omega⟩) (h := h_curDomainIdx_eq) (steps := ϑ)
      (destIdx := destDomainIdx)
      (h_destIdx := by rfl) (h_destIdx' := by simp only [destDomainIdx, h_k])
      (h_destIdx_le := by
        dsimp only [destDomainIdx]
        rw [h_k]
        rw [Nat.sub_add_cancel (by
          exact Nat.le_of_dvd (h := by exact Nat.pos_of_neZero ℓ') (hdiv.out))]
      ) (f := (getLastOracle K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_destIdx_eq oStmtIn))
      (r_challenges := finalChallenges)
    rw [res]
    dsimp only [getLastOracle, finalChallenges]
    rw [h_f_last_consistency]
    simp only [Fin.take_eq_self]
    let k_pos_idx := getLastOraclePositionIndex ℓ' ϑ (Fin.last ℓ')
    let k_steps := k_pos_idx.val * ϑ
    have h_k_steps_eq : k_steps = k := by
      dsimp only [k_steps, k_pos_idx, k, lastDomainIdx]
    have h_cast_elim := iterated_fold_congr_dest_index K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := 0) (steps := k_steps) (destIdx := curDomainIdx) (destIdx' := ⟨k_steps, by omega⟩)
      (h_destIdx := by simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]; omega)
      (h_destIdx_le := by
        dsimp only [curDomainIdx]
        simp only [h_k, tsub_le_iff_right, le_add_iff_nonneg_right, zero_le]
      ) (h_destIdx_eq_destIdx' := by rfl)
      (f := f₀)
      (r_challenges := getFoldingChallenges (𝓡 := 𝓡) (r := 2 ^ κ) (Fin.last ℓ')
        stmtIn.challenges 0 (by simp only [zero_add, Fin.val_last]; omega))
    have h_cast_elim2 := iterated_fold_congr_dest_index K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := 0) (steps := k_steps) (destIdx := ⟨ℓ' - ϑ, by omega⟩) (destIdx' := curDomainIdx)
      (h_destIdx := by simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]; omega)
      (h_destIdx_le := by
        dsimp only [curDomainIdx]
        simp only [tsub_le_iff_right, le_add_iff_nonneg_right, zero_le]
      )
      (h_destIdx_eq_destIdx' := by
        dsimp only [curDomainIdx]
        simp only [Fin.mk.injEq]; omega
      )
      (f := f₀)
      (r_challenges := getFoldingChallenges (𝓡 := 𝓡) (r := 2 ^ κ) (Fin.last ℓ')
        stmtIn.challenges 0 (by simp only [zero_add, Fin.val_last]; omega))
    dsimp only [k_steps, k_pos_idx, f₀, P₀] at h_cast_elim
    dsimp only [k_steps, k_pos_idx, f₀, P₀] at h_cast_elim2
    conv_lhs =>
      simp only [←h_cast_elim]
      simp only [←h_cast_elim2]
      simp only [←fun_eta_expansion]
    have h_transitivity := iterated_fold_transitivity K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := 0) (midIdx := ⟨ℓ' - ϑ, by omega⟩) (destIdx := destDomainIdx)
      (steps₁ := k_steps) (steps₂ := ϑ)
      (h_midIdx := by
        simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, h_k_steps_eq, h_k, zero_add]
      )
      (h_destIdx := by
        dsimp only [destDomainIdx, k_steps, k_pos_idx]
        rw [h_k]
        simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add, Nat.add_right_cancel_iff]
        rw [getLastOraclePositionIndex_last]
        simp only
        rw [Nat.sub_mul, Nat.div_mul_cancel (hdiv.out)]
        simp only [one_mul]
      )
      (h_destIdx_le := by
        dsimp only [destDomainIdx]
        rw [h_k]
        rw [Nat.sub_add_cancel (by
          exact Nat.le_of_dvd (h := by exact Nat.pos_of_neZero ℓ') (hdiv.out))]
      )
      (f := f₀)
      (r_challenges₁ := getFoldingChallenges (𝓡 := 𝓡) (r := 2 ^ κ) (Fin.last ℓ')
        stmtIn.challenges 0 (by simp only [zero_add, Fin.val_last]; omega))
      (r_challenges₂ := finalChallenges)
    have h_finalChallenges_eq : finalChallenges = fun cId : Fin ϑ => stmtIn.challenges
      ⟨k + cId.val, by
        rw [h_k]
        have h_le : ϑ ≤ ℓ' := by
          apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ') (hdiv.out)
        have h_cId : cId.val < ϑ := cId.isLt
        have h_last : (Fin.last ℓ').val = ℓ' := rfl
        omega
      ⟩ := by
      rfl
    rw [h_finalChallenges_eq] at h_transitivity
    rw [h_transitivity]
    have h_steps_eq : k_steps + ϑ = ℓ' := by
      dsimp only [k_steps, k_pos_idx, h_k_steps_eq, h_k]
      rw [getLastOraclePositionIndex_last]
      simp only [Nat.sub_mul, Nat.one_mul, Nat.div_mul_cancel (hdiv.out)]
      rw [Nat.sub_add_cancel (by
        exact Nat.le_of_dvd (h := by exact Nat.pos_of_neZero ℓ') (hdiv.out))]
    have h_concat_challenges_eq :
        Fin.append
          (getFoldingChallenges (𝓡 := 𝓡) (r := 2 ^ κ) (ϑ := k_steps)
            (Fin.last ℓ') stmtIn.challenges 0
            (by simp only [zero_add, Fin.val_last]; omega))
          finalChallenges =
        fun (cIdx : Fin (k_steps + ϑ)) => stmtIn.challenges ⟨cIdx, by
          simp only [Fin.val_last]
          omega
        ⟩ := by
      funext cId
      dsimp only [getFoldingChallenges, finalChallenges]
      by_cases h : cId.val < k_steps
      · simp only [Fin.val_last]
        dsimp only [Fin.append, Fin.addCases]
        simp only [h, ↓reduceDIte, getFoldingChallenges, Fin.val_last, Fin.val_castLT, zero_add]
      · simp only [Fin.val_last]
        dsimp only [Fin.append, Fin.addCases]
        simp [h, ↓reduceDIte, Fin.val_subNat, Fin.val_cast, eq_rec_constant]
        congr 1
        simp only [Fin.val_last, Fin.mk.injEq]
        rw [add_comm, ←h_k_steps_eq]
        omega
    dsimp only [finalChallenges] at h_concat_challenges_eq
    simp only [h_concat_challenges_eq]
    funext y
    have h_cast_elim3 := iterated_fold_congr_dest_index K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := 0) (steps := k_steps + ϑ) (destIdx := destDomainIdx)
      (destIdx' := ⟨Fin.last ℓ', by omega⟩)
      (h_destIdx := by simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]; rfl)
      (h_destIdx_le := by dsimp only [destDomainIdx]; omega)
      (h_destIdx_eq_destIdx' := by
        dsimp only [destDomainIdx]
        simp only [Fin.val_last, Fin.mk.injEq]
        omega
      )
      (f := f₀)
      (r_challenges := fun (cIdx : Fin (k_steps + ϑ)) => stmtIn.challenges ⟨cIdx, by
        simp only [Fin.val_last]
        omega
      ⟩)
    rw [h_cast_elim3]
    have h_cast_elim4 := iterated_fold_congr_steps_index K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := 0) (steps := ℓ') (steps' := k_steps + ϑ)
      (destIdx := ⟨Fin.last ℓ', by omega⟩)
      (h_steps_eq_steps' := by simp only [h_steps_eq])
      (h_destIdx := by
        dsimp only [destDomainIdx]
        simp only [Fin.val_last, Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]
      )
      (h_destIdx_le := by simp only [Fin.val_last, le_refl])
      (f := f₀) (r_challenges := stmtIn.challenges)
    rw [←h_cast_elim4]
    set f_last := iterated_fold K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 ℓ'
      (destIdx := ⟨Fin.last ℓ', by omega⟩)
      (h_destIdx := by
        simp only [Fin.val_last, Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]
      )
      (h_destIdx_le := by simp only [Fin.val_last, le_refl]) (f := f₀)
      (r_challenges := stmtIn.challenges)
    have h_eval_eq : ∀ x, f_last x = f_last ⟨0, by simp only [zero_mem]⟩ := by
      intro x
      apply iterated_fold_to_level_ℓ_is_constant K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (t := witIn.t) (destIdx := ⟨Fin.last ℓ', by omega⟩)
        (h_destIdx := by simp only [Fin.val_last]) (challenges := stmtIn.challenges)
        (x := x) (y := 0)
    rw [h_eval_eq]
    rfl
  rw [h_eq]
  intro y
  rfl
-/

/-- Honest prover message in final sumcheck equals `witIn.f(0)`. -/
lemma finalSumcheck_honest_message_eq_f_zero
    (stmtIn : Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ'))
    (witIn : BinaryBasefold.Witness K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') (Fin.last ℓ'))
    (oStmtIn : ∀ j, BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ') j)
    (challenges : (BinaryBasefold.pSpecFinalSumcheckStep (L := L)).Challenges) :
    let step := finalSumcheckStepLogic κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l (𝓑 := 𝓑)
    let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
    transcript.messages ⟨0, rfl⟩ = witIn.f ⟨0, by simp only [zero_mem]⟩ := by
  sorry

/-- Verifier check passes in the FRI final sumcheck logic step. -/
lemma finalSumcheckStep_verifierCheck_passed
    (stmtIn : Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ'))
    (witIn : BinaryBasefold.Witness K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') (Fin.last ℓ'))
    (oStmtIn : ∀ j, BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ') j)
    (challenges : (BinaryBasefold.pSpecFinalSumcheckStep (L := L)).Challenges)
    (h_sumcheck_cons : BinaryBasefold.sumcheckConsistencyProp
      (𝓑 := 𝓑) stmtIn.sumcheck_target witIn.H)
    (h_wit_struct : BinaryBasefold.witnessStructuralInvariant K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (mp := RingSwitching_SumcheckMultParam κ L K
        (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l)
      (stmt := stmtIn) (wit := witIn)) :
    let step := finalSumcheckStepLogic κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l (𝓑 := 𝓑)
    let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
    step.verifierCheck stmtIn transcript := by
  sorry

/-- Strong completeness of the FRI final sumcheck logic step. -/
lemma finalSumcheckStep_is_logic_complete :
    (finalSumcheckStepLogic κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l
      (𝓑 := 𝓑)).IsStronglyComplete := by
  sorry
/-
  intro stmtIn witIn oStmtIn challenges h_relIn
  let step := finalSumcheckStepLogic κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l (𝓑 := 𝓑)
  let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
  let verifierStmtOut := step.verifierOut stmtIn transcript
  let verifierOStmtOut := OracleVerifier.mkVerifierOStmtOut step.embed step.hEq
    oStmtIn transcript
  let proverOutput := step.proverOut stmtIn witIn oStmtIn transcript
  let proverStmtOut := proverOutput.1.1
  let proverOStmtOut := proverOutput.1.2
  let proverWitOut := proverOutput.2
  simp only [finalSumcheckStepLogic, BinaryBasefold.strictRoundRelation,
    BinaryBasefold.strictRoundRelationProp, Set.mem_setOf_eq] at h_relIn
  obtain ⟨h_sumcheck_cons, h_strictOracleWitConsistency⟩ := h_relIn
  have h_wit_struct := h_strictOracleWitConsistency.1
  let h_VCheck_passed : step.verifierCheck stmtIn transcript :=
    finalSumcheckStep_verifierCheck_passed (κ := κ) (L := L) (K := K) (β := β)
      (ℓ := ℓ) (ℓ' := ℓ') (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (h_l := h_l) (𝓑 := 𝓑) stmtIn witIn oStmtIn challenges h_sumcheck_cons h_wit_struct
  have hStmtOut_eq : proverStmtOut = verifierStmtOut := by
    change (step.proverOut stmtIn witIn oStmtIn transcript).1.1 = step.verifierOut stmtIn transcript
    simp only [step, finalSumcheckStepLogic, finalSumcheckVerifierStmtOut]
  have hOStmtOut_eq : proverOStmtOut = verifierOStmtOut := by rfl
  have hRelOut : step.completeness_relOut ((verifierStmtOut, verifierOStmtOut), proverWitOut) := by
    simp only [step, finalSumcheckStepLogic]
    refine ⟨witIn.t, ?_⟩
    unfold BinaryBasefold.strictfinalSumcheckStepFoldingStateProp
    dsimp only [finalSumcheckVerifierStmtOut]
    constructor
    · exact h_strictOracleWitConsistency.2
    · funext y
      have h_const := iterated_fold_to_const_strict (κ := κ) (L := L) (K := K) (β := β)
        (ℓ := ℓ) (ℓ' := ℓ') (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (h_l := h_l) (stmtIn := stmtIn) (witIn := witIn) (oStmtIn := oStmtIn)
        (h_strictOracleWitConsistency_In := h_strictOracleWitConsistency) y
      have h_msg_eq : transcript.messages ⟨0, rfl⟩ = witIn.f ⟨0, by simp only [zero_mem]⟩ :=
        finalSumcheck_honest_message_eq_f_zero (κ := κ) (L := L) (K := K) (β := β) (ℓ := ℓ)
          (ℓ' := ℓ') (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_l := h_l)
          (𝓑 := 𝓑) stmtIn witIn oStmtIn challenges
      dsimp [verifierStmtOut, verifierOStmtOut, transcript, step, finalSumcheckStepLogic,
        finalSumcheckVerifierStmtOut] at h_const ⊢
      dsimp [transcript, step, finalSumcheckStepLogic] at h_msg_eq
      rw [h_msg_eq]
      exact h_const
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h_VCheck_passed
  · exact hRelOut
  · exact hStmtOut_eq
  · exact hOStmtOut_eq
-/

/-- Perfect completeness for the final sumcheck step -/
theorem finalSumcheckOracleReduction_perfectCompleteness {σ : Type}
  (init : ProbComp σ) (hInit : NeverFail init)
  (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
  OracleReduction.perfectCompleteness
    (pSpec := BinaryBasefold.pSpecFinalSumcheckStep (L:=L))
    (relIn := BinaryBasefold.strictRoundRelation (mp := RingSwitching_SumcheckMultParam κ L K
      (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l) K β (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) (Fin.last ℓ'))
    (relOut := BinaryBasefold.strictFinalSumcheckRelOut K β (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (oracleReduction := finalSumcheckOracleReduction (κ := κ) (L := L) (K := K) (ℓ := ℓ)
      (ℓ' := ℓ') (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (h_l := h_l) (𝓑 := 𝓑)
      (βfun := fun i => β i)
      (mp := RingSwitching_SumcheckMultParam κ L K
        (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l))
    (init := init) (impl := impl) := by
  sorry

/-- RBR knowledge error for the final sumcheck step -/
def finalSumcheckKnowledgeError (m : pSpecFinalSumcheckStep (L := L).ChallengeIdx) :
  ℝ≥0 :=
  match m with
  | ⟨0, h0⟩ => nomatch h0

def FinalSumcheckWit := fun (m : Fin (1 + 1)) =>
 match m with
 | ⟨0, _⟩ => BinaryBasefold.Witness K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') (Fin.last ℓ')
 | ⟨1, _⟩ => Unit

/-- The round-by-round extractor for the final sumcheck step -/
noncomputable def finalSumcheckRbrExtractor :
  Extractor.RoundByRound []ₒ
    (StmtIn := (Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ)
      (Fin.last ℓ')) × (∀ j, BinaryBasefold.OracleStatement K β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ  (Fin.last ℓ') j))
    (WitIn := BinaryBasefold.Witness K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') (Fin.last ℓ'))
    (WitOut := Unit)
    (pSpec := BinaryBasefold.pSpecFinalSumcheckStep (L:=L))
    (WitMid := FinalSumcheckWit κ (L := L) K β ℓ' 𝓡 (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) where
  eqIn := rfl
  extractMid := fun m ⟨stmtMid, oStmtMid⟩ trSucc witMidSucc => by
    have hm : m = 0 := by omega
    subst hm
    have _ : witMidSucc = () := by rfl
    -- Decode t from the first oracle f^(0)
    let f0 := getFirstOracle K β oStmtMid
    let polyOpt := extractMLP K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨0, by exact Nat.pos_of_neZero ℓ'⟩) (f := f0)
    let H_constant : BinaryBasefold.MultiquadraticPoly L (ℓ' - ↑(Fin.last ℓ')) :=
      BinaryBasefold.MultiquadraticPoly.C stmtMid.sumcheck_target
    match polyOpt with
    | none =>
      exact {
        t := 0,
        H := H_constant,
        f := fun _ => 0
      }
    | some tpoly =>
      exact {
        t := tpoly,
        H := H_constant,
        f := getMidCodewords K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) tpoly stmtMid.challenges
      }
  extractOut := fun ⟨stmtIn, oStmtIn⟩ tr witOut => ()

def finalSumcheckKStateProp {m : Fin (1 + 1)} (tr : Transcript m (pSpecFinalSumcheckStep (L := L)))
    (stmt : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ'))
    (witMid : FinalSumcheckWit κ (L := L) K β ℓ' 𝓡 (h_ℓ_add_R_rate := h_ℓ_add_R_rate) m)
    (oStmt : ∀ j, BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ') j) : Prop :=
  match m with
  | ⟨0, _⟩ => -- same as relIn
    BinaryBasefold.masterKStateProp K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (mp := RingSwitching_SumcheckMultParam κ L K
        (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l)
      (stmtIdx := Fin.last ℓ') (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ'))
      (stmt := stmt) (wit := witMid) (oStmt := oStmt)
      (localChecks := sumcheckConsistencyProp (𝓑 := 𝓑) stmt.sumcheck_target witMid.H)
  | ⟨1, _⟩ => -- implied by relOut + local checks via extractOut proofs
    let tr_so_far := (pSpecFinalSumcheckStep (L := L)).take 1 (by omega)
    let i_msg0 : tr_so_far.MessageIdx := ⟨⟨0, by omega⟩, rfl⟩
    let s' : L := (ProtocolSpec.Transcript.equivMessagesChallenges (k := 1)
      (pSpec := pSpecFinalSumcheckStep (L := L)) tr).1 i_msg0
    let stmtOut : BinaryBasefold.FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ') := {
      -- **Dummy UNUSED values**
      ctx := {
        t_eval_point := 0,
        original_claim := 0
      },
      sumcheck_target := 0,
      -- **ONLY the last two fields are used in finalSumcheckStepFoldingStateProp**
      challenges := stmt.challenges,
      final_constant := s'
    }
    let sumcheckFinalCheck : Prop := stmt.sumcheck_target = compute_final_eq_value κ L K
      (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l
      stmt.ctx.t_eval_point stmt.challenges stmt.ctx.r_batching * s'
    let finalFoldingProp := finalSumcheckStepFoldingStateProp K β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_le := by
        apply Nat.le_of_dvd;
        · exact Nat.pos_of_neZero ℓ'
        · exact hdiv.out) (input := ⟨stmtOut, oStmt⟩)
    sumcheckFinalCheck ∧ finalFoldingProp -- local checks ∧ (oracleConsitency ∨ badEventExists)

/-- The knowledge state function for the final sumcheck step -/
def finalSumcheckKnowledgeStateFunction {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (finalSumcheckVerifier (κ := κ) (L := L) (K := K) (ℓ := ℓ) (ℓ' := ℓ')
      (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_l := h_l)
      (𝓑 := 𝓑) (βfun := fun i => β i)
      (mp := RingSwitching_SumcheckMultParam κ L K
        (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l)).KnowledgeStateFunction init impl
    (relIn := roundRelation K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑) (mp := RingSwitching_SumcheckMultParam κ L K
        (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l) (Fin.last ℓ'))
    (relOut := BinaryBasefold.finalSumcheckRelOut K β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (extractor := finalSumcheckRbrExtractor κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate)
    where
  toFun := fun m ⟨stmtMid, oStmtMid⟩ tr witMid =>
    finalSumcheckKStateProp (κ := κ) (L := L) (K := K) (β := β)
      (ℓ := ℓ) (ℓ' := ℓ') (𝓡 := 𝓡) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_l := h_l) (𝓑 := 𝓑)
      (m := m) (tr := tr) (stmt := stmtMid) (witMid := witMid) (oStmt := oStmtMid)
  toFun_empty := by
    intro stmtIn witMid
    cases stmtIn
    rfl
  toFun_next := by
    sorry
  toFun_full := by
    sorry

/-- Round-by-round knowledge soundness for the final sumcheck step -/
theorem finalSumcheckOracleVerifier_rbrKnowledgeSoundness [Fintype L] {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (finalSumcheckVerifier (κ := κ) (L := L) (K := K) (ℓ := ℓ) (ℓ' := ℓ')
      (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_l := h_l)
      (𝓑 := 𝓑) (βfun := fun i => β i)
      (mp := RingSwitching_SumcheckMultParam κ L K
        (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l)).rbrKnowledgeSoundness init impl
      (relIn := roundRelation K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) (mp := RingSwitching_SumcheckMultParam κ L K
          (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l) (Fin.last ℓ'))
      (relOut := BinaryBasefold.finalSumcheckRelOut K β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (rbrKnowledgeError := finalSumcheckKnowledgeError L) := by
  sorry

end FinalSumcheckStep

section CoreInteractionPhaseReduction

instance coreInteractionBetaFun_linearIndependent :
    Fact (LinearIndependent K (fun i => β i)) := by
  exact ⟨β.linearIndependent⟩

instance coreInteractionBetaFun_zero_eq_one :
    Fact ((fun i => β i) 0 = 1) := by
  exact h_β₀_eq_1

/-- Executable core-interaction verifier over explicit basis/multiplier inputs. -/
@[reducible]
def coreInteractionOracleVerifier
    (βfun : Fin (2 ^ κ) → L)
    [Fact (LinearIndependent K βfun)] [Fact (βfun 0 = 1)]
    (mp : SumcheckMultiplierParam L ℓ' (RingSwitchingBaseContext κ L K ℓ)) :=
  OracleVerifier.append (oSpec:=[]ₒ)
    (Stmt₁ := Statement (L := L) (ℓ:=ℓ') (RingSwitchingBaseContext κ L K ℓ) 0)
    (Stmt₂ := Statement (L := L) (ℓ:=ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ'))
    (Stmt₃ := BinaryBasefold.FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ'))
    (OStmt₁ := BinaryBasefold.OracleStatement K βfun (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (OStmt₂ := BinaryBasefold.OracleStatement K βfun
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (OStmt₃ := BinaryBasefold.OracleStatement K βfun
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (pSpec₁ := BinaryBasefold.pSpecSumcheckFold K βfun (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (pSpec₂ := pSpecFinalSumcheckStep (L:=L))
    (V₁ := sumcheckFoldOracleVerifierExec (κ := κ) (L := L) (K := K) (ℓ := ℓ)
      (ℓ' := ℓ') (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑) βfun mp)
    (V₂ := finalSumcheckVerifier (κ := κ) (L := L) (K := K) (ℓ := ℓ)
      (ℓ' := ℓ') (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (h_l := h_l) (𝓑 := 𝓑) βfun mp)

/-- Executable core-interaction reduction over explicit basis/multiplier inputs. -/
@[reducible]
def coreInteractionOracleReduction
    (βfun : Fin (2 ^ κ) → L)
    [Fact (LinearIndependent K βfun)] [Fact (βfun 0 = 1)]
    (mp : SumcheckMultiplierParam L ℓ' (RingSwitchingBaseContext κ L K ℓ)) :
    OracleReduction (oSpec := []ₒ)
      (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) 0)
      (OStmtIn := BinaryBasefold.OracleStatement K βfun
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
      (WitIn := RingSwitching.SumcheckWitness L ℓ' 0)
      (StmtOut := BinaryBasefold.FinalSumcheckStatementOut (L := L) (ℓ := ℓ'))
      (OStmtOut := BinaryBasefold.OracleStatement K βfun
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
      (WitOut := Unit)
      (pSpec := BinaryBasefold.pSpecCoreInteraction K βfun (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  OracleReduction.append (oSpec := []ₒ)
    (Stmt₁ := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) 0)
    (Stmt₂ := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ'))
    (Stmt₃ := BinaryBasefold.FinalSumcheckStatementOut (L := L) (ℓ := ℓ'))
    (Wit₁ := RingSwitching.SumcheckWitness L ℓ' 0)
    (Wit₂ := BinaryBasefold.Witness K βfun
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') (Fin.last ℓ'))
    (Wit₃ := Unit)
    (OStmt₁ := BinaryBasefold.OracleStatement K βfun
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (OStmt₂ := BinaryBasefold.OracleStatement K βfun
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (OStmt₃ := BinaryBasefold.OracleStatement K βfun
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (pSpec₁ := BinaryBasefold.pSpecSumcheckFold K βfun (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (pSpec₂ := BinaryBasefold.pSpecFinalSumcheckStep (L := L))
    (R₁ := sumcheckFoldOracleReductionExec (κ := κ) (L := L) (K := K) (ℓ := ℓ)
      (ℓ' := ℓ') (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (h_l := h_l) βfun mp)
    (R₂ := finalSumcheckOracleReductionExec (κ := κ) (L := L) (K := K) (ℓ := ℓ)
      (ℓ' := ℓ') (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_l := h_l)
      (𝓑 := 𝓑) βfun mp)

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

/-- Perfect completeness for the core interaction oracle reduction -/
theorem coreInteractionOracleReduction_perfectCompleteness
    (hInit : NeverFail init) :
    OracleReduction.perfectCompleteness
      (oSpec := []ₒ)
      (pSpec := BinaryBasefold.pSpecCoreInteraction K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (OStmtIn := BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
      (OStmtOut := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
      (relIn := RingSwitching.strictSumcheckRoundRelation κ (L := L) (K := K)
        (β := booleanHypercubeBasis κ L K β)
        (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l) (𝓑 := 𝓑)
        (BinaryBasefoldAbstractOStmtIn
          (κ := κ) (L := L) (K := K) (β := β)
          (ℓ' := ℓ') (𝓡 := 𝓡) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) 0)
      (relOut := BinaryBasefold.strictFinalSumcheckRelOut K β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (oracleReduction := coreInteractionOracleReduction (κ := κ) (L := L) (K := K)
        (ℓ := ℓ) (ℓ' := ℓ') (𝓡 := 𝓡) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_l := h_l) (𝓑 := 𝓑)
        (βfun := fun i => β i)
        (mp := RingSwitching_SumcheckMultParam κ L K
          (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l))
      (init := init)
      (impl := impl) := by
  sorry

noncomputable def coreInteractionOracleRbrKnowledgeError (j : (BinaryBasefold.pSpecCoreInteraction K β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx) : ℝ≥0 :=
    Sum.elim
      (f := fun i => BinaryBasefold.CoreInteraction.sumcheckFoldKnowledgeError
        K β (ϑ := ϑ) i)
      (g := fun i => finalSumcheckKnowledgeError (L := L) i)
      (ChallengeIdx.sumEquiv.symm j)

/-- Round-by-round knowledge soundness for the core interaction oracle verifier -/
theorem coreInteractionOracleVerifier_rbrKnowledgeSoundness :
    (coreInteractionOracleVerifier (κ := κ) (L := L) (K := K) (ℓ := ℓ) (ℓ' := ℓ')
      (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_l := h_l)
      (𝓑 := 𝓑) (βfun := fun i => β i)
      (mp := RingSwitching_SumcheckMultParam κ L K
        (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l)
      ).rbrKnowledgeSoundness init impl
      (OStmtIn := BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
      (OStmtOut := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
      (pSpec := BinaryBasefold.pSpecCoreInteraction K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (relIn := RingSwitching.sumcheckRoundRelation κ L K
        (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l (𝓑 := 𝓑)
        (BinaryBasefoldAbstractOStmtIn
          (κ := κ) (L := L) (K := K) (β := β)
          (ℓ' := ℓ') (𝓡 := 𝓡) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) 0)
      (relOut := BinaryBasefold.finalSumcheckRelOut K β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (rbrKnowledgeError := coreInteractionOracleRbrKnowledgeError κ L K β ℓ' 𝓡 ϑ
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) := by
  sorry

end CoreInteractionPhaseReduction

/-- Sum of the per-round RBR knowledge error over core interaction challenges is **at most**
`2 * ℓ' / |L| + 2^(ℓ' + 𝓡) / |L|` (see `BinaryBasefold.CoreInteraction.sumcheckFoldKnowledgeError_le`). -/
theorem coreInteractionOracleRbrKnowledgeError_le :
    (∑ i : (BinaryBasefold.pSpecCoreInteraction K β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx,
      coreInteractionOracleRbrKnowledgeError κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate i)
    ≤ 2 * (ℓ' : ℝ≥0) / (Fintype.card L : ℝ≥0)
      + (2 ^ (ℓ' + 𝓡) : ℝ≥0) / (Fintype.card L : ℝ≥0) := by
  classical
  unfold coreInteractionOracleRbrKnowledgeError
  rw [Equiv.sum_comp (Equiv.symm ChallengeIdx.sumEquiv)]
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  have hb : (∑ i : (BinaryBasefold.pSpecFinalSumcheckStep (L := L)).ChallengeIdx,
      finalSumcheckKnowledgeError (L := L) i) = 0 := by
    simpa using BinaryBasefold.CoreInteraction.finalSumcheckKnowledgeError_sum_eq_zero (L := L)
  rw [hb, add_zero]
  exact BinaryBasefold.CoreInteraction.sumcheckFoldKnowledgeError_le (𝔽q := K) (L := L) (β := β)
    (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ')

end
end Binius.FRIBinius.CoreInteractionPhase
