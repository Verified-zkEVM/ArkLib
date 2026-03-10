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

Inside this file, `coreInteractionOracleReduction` is exactly the composition of:
1. `LiftContext(sumcheckFoldOracleReduction)` (the lifted Binary
  Basefold sumcheck-fold reduction), then
2. `finalSumcheckOracleReduction`.

`LiftContext` here is only the bridge from batching-output shape to Binary Basefold sumcheck-fold
input shape. Concretely, it maps
`SumcheckWitness (t', H)` to `BinaryBasefold.Witness (t, H, f₀)`, where
`f₀ := getMidCodewords t challenges`, and keeps the output witness unchanged (`toFunB` is
identity on `innerWitOut`).
-/

namespace Binius.FRIBinius.CoreInteractionPhase
noncomputable section

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

/-- Oracle context lens for sumcheck fold lifting -/
def sumcheckFoldCtxLens : OracleContext.Lens
    (OuterStmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) 0)
    (OuterStmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ'))
    (InnerStmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) 0)
    (InnerStmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ'))
    (OuterOStmtIn := BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (OuterOStmtOut := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (InnerOStmtIn := BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (InnerOStmtOut := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (OuterWitIn := RingSwitching.SumcheckWitness L ℓ' 0)
    (OuterWitOut := BinaryBasefold.Witness K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') (Fin.last ℓ'))
    (InnerWitIn := BinaryBasefold.Witness K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') 0)
    (InnerWitOut := BinaryBasefold.Witness K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') (Fin.last ℓ')) where
  wit := {
    toFunA := fun ⟨⟨outerStmtIn, outerOStmtIn⟩, outerWitIn⟩ => by
      let t : L⦃≤ 1⦄[X Fin ℓ'] := outerWitIn.t'
      let H : L⦃≤ 2⦄[X Fin (ℓ' - 0)] := outerWitIn.H
      let f₀ : (sDomain K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
        ⟨0, by omega⟩ → L :=
        BinaryBasefold.getMidCodewords K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := (0 : Fin (ℓ' + 1))) (t := t) (challenges := outerStmtIn.challenges)
      exact { t := t, H := H, f := f₀ }
    toFunB := fun ⟨⟨outerStmtIn, outerOStmtIn⟩, outerWitIn⟩
      ⟨⟨innerStmtOut, innerOStmtOut⟩, innerWitOut⟩ => innerWitOut
  }
  stmt := sumcheckFoldStmtLens κ L K β ℓ ℓ' 𝓡 ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)

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
        t' := innerWitIn.t
        H := innerWitIn.H
      }
      exact outerWitIn
  }

-- The lifted oracle verifier
def sumcheckFoldOracleVerifier :=
  (BinaryBasefold.CoreInteraction.sumcheckFoldOracleVerifier K β (ϑ:=ϑ)
    (mp := RingSwitching_SumcheckMultParam κ L K (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l)
    (𝓑 := 𝓑) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).liftContext
      (lens := sumcheckFoldStmtLens κ L K β ℓ ℓ' 𝓡 ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate))

-- The lifted oracle reduction
def sumcheckFoldOracleReduction :=
  (BinaryBasefold.CoreInteraction.sumcheckFoldOracleReduction K β (ϑ:=ϑ)
    (mp := RingSwitching_SumcheckMultParam κ L K (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)).liftContext
      (lens := sumcheckFoldCtxLens κ L K β ℓ ℓ' 𝓡 ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_l)

-- Security properties for the lifted oracle reduction

section Security

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

-- Completeness instance for the context lens
instance sumcheckFoldCtxLens_complete :
  (sumcheckFoldCtxLens κ L K β ℓ ℓ' 𝓡 ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    h_l).toContext.IsComplete
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
        (sumcheckFoldCtxLens κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l).toContext originalReduction
    ) where
  proj_complete := fun stmtIn oStmtIn hRelIn => by
    rcases stmtIn with ⟨stmtIn, oStmtIn'⟩
    rcases oStmtIn with ⟨t', H⟩
    rcases hRelIn with ⟨h_local, h_struct, h_strict_compat⟩
    refine ⟨?_, ?_⟩
    · simpa [sumcheckFoldStmtLens] using h_local
    · refine ⟨?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · simpa [sumcheckFoldStmtLens, RingSwitching.witnessStructuralInvariant,
            BinaryBasefold.witnessStructuralInvariant] using h_struct
        · rfl
      · change strictOracleFoldingConsistencyProp K β
          (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (t := t') (i := (0 : Fin (ℓ' + 1)))
          (challenges := stmtIn.challenges) (oStmt := oStmtIn')
        have h_strict_compat' :
            strictOracleFoldingConsistencyProp K β
              (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (t := t') (i := (0 : Fin (ℓ' + 1)))
              (challenges := Fin.elim0) (oStmt := oStmtIn') := by
          simpa [BinaryBasefoldAbstractOStmtIn,
            Binius.RingSwitching.BBFSmallFieldIOPCS.bbfAbstractOStmtIn,
            strictOracleFoldingConsistencyProp] using h_strict_compat
        have h_challenges : stmtIn.challenges = (Fin.elim0 : Fin 0 → L) := by
          funext i
          exact Fin.elim0 i
        simpa [h_challenges] using h_strict_compat'
  lift_complete := fun outerStmtIn outerWitIn innerStmtOut innerWitOut compat => by
    intro _ hRelOut
    simpa [sumcheckFoldStmtLens] using hRelOut

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
    (relIn := RingSwitching.strictSumcheckRoundRelation κ L K (booleanHypercubeBasis κ L K β)
      ℓ ℓ' h_l (𝓑 := 𝓑) (aOStmtIn := BinaryBasefoldAbstractOStmtIn (β := β) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) 0)
    (relOut :=
      BinaryBasefold.strictRoundRelation (mp := RingSwitching_SumcheckMultParam κ L K
        (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l) K β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) (Fin.last ℓ')
    )
    (oracleReduction := sumcheckFoldOracleReduction κ L K β ℓ ℓ' 𝓡 ϑ
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_l (𝓑 := 𝓑))
    (init := init)
    (impl := impl) :=
  OracleReduction.liftContext_perfectCompleteness
    (oSpec := []ₒ)
    (OuterStmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) 0)
    (OuterStmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ'))
    (OuterWitIn := RingSwitching.SumcheckWitness L ℓ' 0)
    (OuterWitOut := BinaryBasefold.Witness K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') (Fin.last ℓ'))
    (OuterOStmtIn := BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (OuterOStmtOut := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (InnerStmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) 0)
    (InnerStmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ'))
    (InnerWitIn := BinaryBasefold.Witness K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') 0)
    (InnerWitOut := BinaryBasefold.Witness K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') (Fin.last ℓ'))
    (InnerOStmtIn := BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (InnerOStmtOut := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (pSpec := BinaryBasefold.pSpecSumcheckFold K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (outerRelIn := RingSwitching.strictSumcheckRoundRelation κ L K (booleanHypercubeBasis κ L K β)
      ℓ ℓ' h_l (𝓑 := 𝓑) (aOStmtIn := BinaryBasefoldAbstractOStmtIn
        (κ := κ) (L := L) (K := K) (β := β)
        (ℓ' := ℓ') (𝓡 := 𝓡) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) 0)
    (outerRelOut := BinaryBasefold.strictRoundRelation (mp := RingSwitching_SumcheckMultParam κ L K
      (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l) K β (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) (Fin.last ℓ'))
    (innerRelIn := BinaryBasefold.strictRoundRelation (mp := RingSwitching_SumcheckMultParam κ L K
      (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l) K β (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) 0)
    (innerRelOut := BinaryBasefold.strictRoundRelation (mp := RingSwitching_SumcheckMultParam κ L K
      (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l) K β (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) (Fin.last ℓ'))
    (lens := sumcheckFoldCtxLens κ L K β ℓ ℓ' 𝓡 ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_l)
    (lensComplete := sumcheckFoldCtxLens_complete κ L K β ℓ ℓ' 𝓡 ϑ
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_l)
    (init := init)
    (impl := impl)
    (h := BinaryBasefold.CoreInteraction.sumcheckFoldOracleReduction_perfectCompleteness
      (hInit:=hInit) K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑))

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
      (outerRelIn := RingSwitching.sumcheckRoundRelation κ L K (booleanHypercubeBasis κ L K β)
        ℓ ℓ' h_l (𝓑 := 𝓑) (aOStmtIn := BinaryBasefoldAbstractOStmtIn
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
      (lens := sumcheckFoldExtractorLens κ L K β ℓ ℓ' 𝓡 ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      where
  proj_knowledgeSound := by
    intro outerStmtIn innerStmtOut outerWitOut _ hOuter
    simpa [sumcheckFoldExtractorLens, sumcheckFoldStmtLens] using hOuter
  lift_knowledgeSound := by
    intro outerStmtIn outerWitOut innerWitIn _ hInner
    rcases outerStmtIn with ⟨stmtIn, oStmtIn⟩
    have hInner' :
        BinaryBasefold.roundRelationProp
          (mp := RingSwitching_SumcheckMultParam κ L K
            (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l)
          K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
          (0 : Fin (ℓ' + 1)) ((stmtIn, oStmtIn), innerWitIn) := by
      simpa [BinaryBasefold.roundRelation, Set.mem_setOf_eq] using hInner
    unfold BinaryBasefold.roundRelationProp BinaryBasefold.masterKStateProp at hInner'
    have h_no_bad :
        ¬ incrementalBadEventExistsProp K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (ϑ := ϑ) (stmtIdx := (0 : Fin (ℓ' + 1)))
          (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (0 : Fin (ℓ' + 1)))
          (oStmt := oStmtIn) (challenges := stmtIn.challenges) := by
      intro h_bad
      rcases h_bad with ⟨j, hj⟩
      have hj0 : j = 0 := by
        apply Fin.eq_of_val_eq
        have hjlt : j.val < 1 := by
          simpa [BinaryBasefold.toOutCodewordsCountOf0] using j.isLt
        exact Nat.lt_one_iff.mp hjlt
      subst hj0
      dsimp [BinaryBasefold.oraclePositionToDomainIndex] at hj
      exact absurd hj (by
        apply BinaryBasefold.incrementalFoldingBadEvent_of_k_eq_0_is_false
          (𝔽q := K) (β := β)
          (h_k := by
            simp only [Nat.zero_mod, zero_mul, tsub_self, zero_le, inf_of_le_right])
          (h_midIdx := by simp only [Nat.zero_mod, zero_mul, tsub_self, zero_le,
            inf_of_le_right, add_zero]))
    rcases hInner' with h_bad | h_good
    · exact (h_no_bad h_bad).elim
    · have h_local := h_good.1
      have h_struct := h_good.2.1
      have h_first := h_good.2.2.1
      refine ⟨h_local, ?_, ?_⟩
      · simpa [sumcheckFoldExtractorLens, RingSwitching.witnessStructuralInvariant,
          BinaryBasefold.witnessStructuralInvariant] using h_struct.1
      · simpa [BinaryBasefoldAbstractOStmtIn] using h_first

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
      (relIn := RingSwitching.sumcheckRoundRelation κ L K (booleanHypercubeBasis κ L K β)
        ℓ ℓ' h_l (𝓑 := 𝓑) (aOStmtIn := BinaryBasefoldAbstractOStmtIn
          (κ := κ) (L := L) (K := K) (β := β)
          (ℓ' := ℓ') (𝓡 := 𝓡) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) 0)
      (relOut :=
        BinaryBasefold.roundRelation (mp := RingSwitching_SumcheckMultParam κ L K
          (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l) K β (ϑ:=ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑)  (Fin.last ℓ')
      )
      (verifier := sumcheckFoldOracleVerifier κ L K β ℓ ℓ' (h_l := h_l) (𝓑 := 𝓑) 𝓡 ϑ
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (init := init)
      (impl := impl)
      (rbrKnowledgeError := BinaryBasefold.CoreInteraction.sumcheckFoldKnowledgeError
        K β (ϑ := ϑ)) := by
  letI : Inhabited (Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ')) := ⟨{
      ctx := {
        t_eval_point := 0
        original_claim := 0
        s_hat := 0
        r_batching := 0
      }
      sumcheck_target := 0
      challenges := 0
    }⟩
  letI :
      ∀ i : Fin (toOutCodewordsCount ℓ' ϑ (i := Fin.last ℓ')),
        Inhabited (BinaryBasefold.OracleStatement K β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ') i) := by
    intro i
    exact ⟨fun _ => 0⟩
  letI : Inhabited (BinaryBasefold.Witness K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') 0) := ⟨{
      t := 0
      H := 0
      f := fun _ => 0
    }⟩
  have h_lifted := OracleVerifier.liftContext_rbr_knowledgeSoundness
      (V := BinaryBasefold.CoreInteraction.sumcheckFoldOracleVerifier K β
        (ϑ := ϑ)
        (mp := RingSwitching_SumcheckMultParam κ L K
          (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l)
        (𝓑 := 𝓑)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (stmtLens := sumcheckFoldStmtLens κ L K β ℓ ℓ' 𝓡 ϑ
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (witLens := (sumcheckFoldExtractorLens κ L K β ℓ ℓ' 𝓡 ϑ
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).wit)
      (lensKS := sumcheckFoldExtractorLens_rbr_knowledge_soundness
        (κ := κ) (L := L) (K := K) (β := β) (ℓ := ℓ) (ℓ' := ℓ') (𝓡 := 𝓡) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_l := h_l) (𝓑 := 𝓑)
        (compatStmt := (BinaryBasefold.CoreInteraction.sumcheckFoldOracleVerifier K β
          (ϑ := ϑ)
          (mp := RingSwitching_SumcheckMultParam κ L K (β := booleanHypercubeBasis κ L K β)
            ℓ ℓ' h_l)
          (𝓑 := 𝓑) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).toVerifier.compatStatement
          (sumcheckFoldStmtLens κ L K β ℓ ℓ' 𝓡 ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate))))
      (h := by
        simpa using
          (BinaryBasefold.CoreInteraction.sumcheckFoldOracleVerifier_rbrKnowledgeSoundness
            (L := L) K β
            (ϑ := ϑ)
            (mp := RingSwitching_SumcheckMultParam κ L K
              (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (𝓑 := 𝓑)
            (init := init) (impl := impl)))
  simpa [sumcheckFoldOracleVerifier] using h_lifted

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
      (BinaryBasefold.pSpecFinalSumcheckStep (L := L)) where
  completeness_relIn := fun ((stmt, oStmt), wit) =>
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
    ((stmtOut, oStmtIn), ())

/-- The prover for the final sumcheck step -/
noncomputable def finalSumcheckProver :
  OracleProver
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ'))
    (OStmtIn := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (WitIn := BinaryBasefold.Witness K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') (Fin.last ℓ'))
    (StmtOut := BinaryBasefold.FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ'))
    (OStmtOut := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (WitOut := Unit)
    (pSpec := BinaryBasefold.pSpecFinalSumcheckStep (L:=L)) where
  PrvState := fun
    | 0 => Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ')
      × (∀ j, BinaryBasefold.OracleStatement K β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ') j)
      × BinaryBasefold.Witness K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') (Fin.last ℓ')
    | _ => Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ') ×
      (∀ j, BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ') j)
      × BinaryBasefold.Witness K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') (Fin.last ℓ') × L
  input := fun ⟨⟨stmt, oStmt⟩, wit⟩ => (stmt, oStmt, wit)
  sendMessage
  | ⟨0, _⟩ => fun ⟨stmtIn, oStmtIn, witIn⟩ => do
    let c : L := finalSumcheckProverComputeMsg (κ := κ) (L := L) (K := K) (β := β)
      (ℓ' := ℓ') (𝓡 := 𝓡) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) witIn
    pure ⟨c, (stmtIn, oStmtIn, witIn, c)⟩
  receiveChallenge
  | ⟨0, h⟩ => nomatch h -- No challenges in this step
  output := fun ⟨stmtIn, oStmtIn, witIn, s'⟩ => do
    let logic := finalSumcheckStepLogic κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l (𝓑 := 𝓑)
    let t := FullTranscript.mk1 (pSpec := BinaryBasefold.pSpecFinalSumcheckStep (L := L)) s'
    pure (logic.proverOut stmtIn witIn oStmtIn t)

/-- The verifier for the final sumcheck step -/
noncomputable def finalSumcheckVerifier :
  OracleVerifier
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ'))
    (OStmtIn := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (StmtOut := BinaryBasefold.FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ'))
    (OStmtOut := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (pSpec := BinaryBasefold.pSpecFinalSumcheckStep (L:=L)) where
  verify := fun stmtIn _ => do
    let s' : L ← query (spec := [(BinaryBasefold.pSpecFinalSumcheckStep
      (L:=L)).Message]ₒ) ⟨⟨0, by rfl⟩, (by simpa only using ())⟩
    let t := FullTranscript.mk1 (pSpec := BinaryBasefold.pSpecFinalSumcheckStep (L := L)) s'
    let logic := finalSumcheckStepLogic κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l (𝓑 := 𝓑)
    have : Decidable (logic.verifierCheck stmtIn t) := Classical.propDecidable _
    guard (logic.verifierCheck stmtIn t)
    pure (logic.verifierOut stmtIn t)
  embed := (finalSumcheckStepLogic κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l
    (𝓑 := 𝓑)).embed
  hEq := (finalSumcheckStepLogic κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l
    (𝓑 := 𝓑)).hEq

/-- The oracle reduction for the final sumcheck step -/
noncomputable def finalSumcheckOracleReduction :
  OracleReduction
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ'))
    (OStmtIn := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (WitIn := BinaryBasefold.Witness K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') (Fin.last ℓ'))
    (StmtOut := BinaryBasefold.FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ'))
    (OStmtOut := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (WitOut := Unit)
    (pSpec := BinaryBasefold.pSpecFinalSumcheckStep (L:=L)) where
  prover := finalSumcheckProver κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l (𝓑 := 𝓑)
  verifier := finalSumcheckVerifier κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l (𝓑 := 𝓑)

omit [Fintype L] [DecidableEq L] [CharP L 2] [SampleableType L] [NeZero ℓ'] in
/-- At `Fin.last ℓ'`, sumcheck consistency simplifies to a single evaluation. -/
lemma sumcheckConsistency_at_last_simplifies
    (target : L) (H : L⦃≤ 2⦄[X Fin (ℓ' - Fin.last ℓ')])
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

omit [NeZero κ] [CharP L 2] [SampleableType L] [NeZero ℓ] in
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
  have h_f_eq_getMidCodewords_t :
      witIn.f = BinaryBasefold.getMidCodewords K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := Fin.last ℓ') witIn.t stmtIn.challenges := h_wit_struct.2
  dsimp only [BinaryBasefold.getMidCodewords, Fin.coe_ofNat_eq_mod] at h_f_eq_getMidCodewords_t
  rw [congr_fun h_f_eq_getMidCodewords_t ⟨0, by simp only [zero_mem]⟩]
  let h_eval := BinaryBasefold.iterated_fold_to_level_ℓ_eval K β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (t := witIn.t)
    (destIdx := ⟨Fin.last ℓ', by omega⟩)
    (h_destIdx := by simp only [Fin.val_last]) (challenges := stmtIn.challenges)
  exact congr_fun h_eval ⟨0, by simp only [Fin.val_last, zero_mem]⟩

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
  have h_ϑ_le_ℓ' : ϑ ≤ ℓ' := by
    apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ') (hdiv.out)
  intro c lastDomainIdx k h_k curDomainIdx h_destIdx_eq f_k finalChallenges destDomainIdx folded
  let P₀ : L[X]_(2 ^ ℓ') := polynomialFromNovelCoeffsF₂ K β ℓ' (by omega)
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

omit [NeZero κ] [CharP L 2] [SampleableType L] [DecidableEq K] h_β₀_eq_1 [NeZero ℓ] in
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
  simp only [finalSumcheckStepLogic, finalSumcheckProverComputeMsg]

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
  intro step transcript
  have h_target_eq_H_eval :
      stmtIn.sumcheck_target = witIn.H.val.eval (fun _ => (0 : L)) :=
    sumcheckConsistency_at_last_simplifies (L := L) (ℓ' := ℓ') (𝓑 := 𝓑)
      stmtIn.sumcheck_target witIn.H h_sumcheck_cons
  have h_proj_eval :
      (BinaryBasefold.projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := witIn.t)
        (m := (RingSwitching_SumcheckMultParam κ L K
          (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l).multpoly stmtIn.ctx)
        (i := Fin.last ℓ') (challenges := stmtIn.challenges)).val.eval (fun _ => (0 : L)) =
      ((RingSwitching_SumcheckMultParam κ L K
          (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l).multpoly stmtIn.ctx).val.eval
        stmtIn.challenges * witIn.t.val.eval stmtIn.challenges := by
    apply BinaryBasefold.projectToMidSumcheckPoly_at_last_eval
  have h_mult_eq_eq_value :
      ((RingSwitching_SumcheckMultParam κ L K
          (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l).multpoly stmtIn.ctx).val.eval
        stmtIn.challenges =
      RingSwitching.compute_final_eq_value κ L K
        (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l
        stmtIn.ctx.t_eval_point stmtIn.challenges stmtIn.ctx.r_batching :=
    RingSwitching.compute_A_MLE_eval_eq_final_eq_value κ L K
      (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l
      stmtIn.ctx.t_eval_point stmtIn.challenges stmtIn.ctx.r_batching
  have h_c_eq : witIn.f ⟨0, by simp only [zero_mem]⟩ = witIn.t.val.eval stmtIn.challenges := by
    exact finalCodeword_zero_eq_t_eval (κ := κ) (L := L) (K := K) (β := β)
      (ℓ := ℓ) (ℓ' := ℓ') (𝓡 := 𝓡) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_l := h_l)
      stmtIn witIn h_wit_struct
  let cmsg : L := transcript.messages ⟨0, rfl⟩
  have h_msg_eq : cmsg = witIn.f ⟨0, by simp only [zero_mem]⟩ :=
    finalSumcheck_honest_message_eq_f_zero (κ := κ) (L := L) (K := K) (β := β) (ℓ := ℓ)
      (ℓ' := ℓ') (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_l := h_l)
      (𝓑 := 𝓑) stmtIn witIn oStmtIn challenges
  have h_eq : stmtIn.sumcheck_target = RingSwitching.compute_final_eq_value κ L K
      (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l
      stmtIn.ctx.t_eval_point stmtIn.challenges stmtIn.ctx.r_batching *
      cmsg := by
    calc
      stmtIn.sumcheck_target
          = witIn.H.val.eval (fun _ => (0 : L)) := h_target_eq_H_eval
      _ = (BinaryBasefold.projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := witIn.t)
            (m := (RingSwitching_SumcheckMultParam κ L K
              (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l).multpoly stmtIn.ctx)
            (i := Fin.last ℓ') (challenges := stmtIn.challenges)).val.eval (fun _ => (0 : L)) := by
            rw [h_wit_struct.1]
      _ = ((RingSwitching_SumcheckMultParam κ L K
            (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l).multpoly stmtIn.ctx).val.eval
            stmtIn.challenges * witIn.t.val.eval stmtIn.challenges := h_proj_eval
      _ = RingSwitching.compute_final_eq_value κ L K
            (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l
            stmtIn.ctx.t_eval_point stmtIn.challenges stmtIn.ctx.r_batching *
            witIn.t.val.eval stmtIn.challenges := by
            rw [h_mult_eq_eq_value]
      _ = RingSwitching.compute_final_eq_value κ L K
            (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l
            stmtIn.ctx.t_eval_point stmtIn.challenges stmtIn.ctx.r_batching *
            witIn.f ⟨0, by simp only [zero_mem]⟩ := by
            rw [h_c_eq]
      _ = RingSwitching.compute_final_eq_value κ L K
            (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l
            stmtIn.ctx.t_eval_point stmtIn.challenges stmtIn.ctx.r_batching *
            cmsg := by
            rw [←h_msg_eq]
  simpa [step, finalSumcheckStepLogic, finalSumcheckVerifierCheck, cmsg] using h_eq

/-- Strong completeness of the FRI final sumcheck logic step. -/
lemma finalSumcheckStep_is_logic_complete :
    (finalSumcheckStepLogic κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l
      (𝓑 := 𝓑)).IsStronglyComplete := by
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
      simpa [transcript, step, finalSumcheckStepLogic, finalSumcheckVerifierStmtOut, h_msg_eq]
        using h_const
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h_VCheck_passed
  · exact hRelOut
  · exact hStmtOut_eq
  · exact hOStmtOut_eq

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
    (oracleReduction := finalSumcheckOracleReduction κ L K β ℓ ℓ' 𝓡 ϑ (𝓑 := 𝓑)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_l)
    (init := init) (impl := impl) := by
  rw [OracleReduction.unroll_1_message_reduction_perfectCompleteness_P_to_V (hInit := hInit)
    (hDir0 := by rfl)
    (hImplSupp := by simp only [Set.fmap_eq_image, IsEmpty.forall_iff, implies_true])]
  intro stmtIn oStmtIn witIn h_relIn
  -- Step 2: Convert probability 1 to universal quantification over support
  rw [probEvent_eq_one_iff]
  -- Step 3: Unfold protocol definitions
  dsimp only [finalSumcheckOracleReduction, finalSumcheckProver, finalSumcheckVerifier,
    OracleVerifier.toVerifier, FullTranscript.mk1]
  let step := finalSumcheckStepLogic κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l (𝓑 := 𝓑)
  let strongly_complete : step.IsStronglyComplete := finalSumcheckStep_is_logic_complete
    (κ := κ) (L := L) (K := K) (β := β) (ℓ := ℓ) (ℓ' := ℓ') (𝓡 := 𝓡) (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_l := h_l) (𝓑 := 𝓑)
  -- Step 4: Split into safety and correctness goals
  refine ⟨?_, ?_⟩
  -- GOAL 1: SAFETY - Prove the verifier never crashes ([⊥|...] = 0)
  · -- Peel off monadic layers to reach the core verifier logic
    simp only [probFailure_bind_eq_zero_iff]
    conv_lhs =>
      simp only [liftComp_eq_liftM, liftM_pure, probFailure_eq_zero]
    rw [true_and]
    intro inputState hInputState_mem_support
    simp only [Fin.isValue, Message, Matrix.cons_val_zero, Fin.succ_zero_eq_one, ChallengeIdx,
      Challenge, liftComp_eq_liftM, liftM_pure, support_pure,
      Set.mem_singleton_iff] at hInputState_mem_support
    conv_lhs =>
      simp only [liftM, monadLift, MonadLift.monadLift]
      simp only [ChallengeIdx, Challenge, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero,
        liftComp_eq_liftM, OptionT.probFailure_lift, HasEvalPMF.probFailure_eq_zero]
    rw [true_and]
    -- ⊢ ∀ x ∈ .. support, ... ∧ ... ∧ ...
    intro h_prover_final_output h_prover_final_output_support
    conv =>
      simp only [guard_eq] -- simplify the `guard`
      enter [2];
      simp only [bind_pure_comp, NeverFail.probFailure_eq_zero, implies_true]
    rw [and_true]
    -- Pr[⊥ | (...) : OracleComp ... (Option ...)] = 0
    rw [OptionT.probFailure_liftComp_of_OracleComp_Option] -- split into two summands
    conv_lhs =>
      enter [1]
      simp only [MessageIdx, Fin.isValue, Message, Matrix.cons_val_zero, Fin.succ_zero_eq_one,
        id_eq, bind_pure_comp, OptionT.run_map, HasEvalPMF.probFailure_eq_zero]
    rw [zero_add]
    simp only [probOutput_eq_zero_iff]
    rw [OptionT.support_run_eq]
    simp only [←probOutput_eq_zero_iff]
    simp_all only
    change Pr[= none | OptionT.run (m := (OracleComp []ₒ)) (x := (OptionT.bind _ _)) ] = 0
    rw [OptionT.probOutput_none_bind_eq_zero_iff]
    conv =>
      enter [x]
      rw [OptionT.support_run]
    intro vStmtOut h_vStmtOut_mem_support
    conv at h_vStmtOut_mem_support =>
      erw [simulateQ_bind]
      -- turn the simulated oracle query into OracleInterface.answer form
      rw [OptionT.simulateQ_simOracle2_liftM_query_T2] -- V queries P's message
      change vStmtOut ∈ (Bind.bind (m := (OracleComp []ₒ)) _ _).support
      erw [_root_.bind_pure_simulateQ_comp]
      simp only [Matrix.cons_val_zero, guard_eq]
      -- simp  [bind_pure_comp,
      -- OptionT.simulateQ_map, OptionT.simulateQ_ite, OptionT.simulateQ_pure,
      -- OptionT.support_map_run, OptionT.support_ite_run, support_pure,
      -- OptionT.support_failure_run, Set.mem_image, Set.mem_ite_empty_right,
      -- Set.mem_singleton_iff, and_true, exists_const, Prod.mk.injEq, existsAndEq]
      rw [bind_pure_comp]
      dsimp only [Functor.map]
      rw [OptionT.simulateQ_bind]
      erw [support_bind]
      rw [simulateQ_ite]
      simp only [Fin.isValue, Message, Matrix.cons_val_zero, id_eq, MessageIdx, support_ite,
        toPFunctor_emptySpec, Function.comp_apply, OptionT.simulateQ_pure, Set.mem_iUnion,
        exists_prop]
      simp only [OptionT.simulateQ_failure']
      erw [_root_.simulateQ_pure]
    set V_check := step.verifierCheck stmtIn
      (FullTranscript.mk1 (msg0 := _)) with h_V_check_def
    obtain ⟨h_V_check, h_rel, h_agree⟩ := strongly_complete (stmtIn := stmtIn)
      (witIn := witIn) (h_relIn := h_relIn) (challenges :=
      fun ⟨j, hj⟩ => by
        match j with
        | 0 =>
          have hj_ne : (pSpecFinalSumcheckStep (L := L)).dir 0 ≠ Direction.V_to_P := by
            dsimp only [pSpecFinalSumcheckStep, Fin.isValue, Matrix.cons_val_zero]
            simp only [ne_eq, reduceCtorEq, not_false_eq_true]
          exfalso
          exact hj_ne hj
      )
    have h_V_check_is_true : V_check := h_V_check
    simp only [h_V_check_is_true, ↓reduceIte, support_pure, Set.mem_singleton_iff, Fin.isValue,
      Fin.val_last, exists_eq_left, OptionT.support_OptionT_pure_run] at h_vStmtOut_mem_support
    rw [h_vStmtOut_mem_support]
    simp only [Fin.isValue, Fin.val_last, OptionT.run_pure, probOutput_eq_zero_iff, support_pure,
      Set.mem_singleton_iff, reduceCtorEq, not_false_eq_true]
  · -- GOAL 2: CORRECTNESS - Prove all outputs in support satisfy the relation
    intro x hx_mem_support
    rcases x with ⟨⟨prvStmtOut, prvOStmtOut⟩, ⟨verStmtOut, verOStmtOut⟩, witOut⟩
    simp only
    -- Step 2a: Simplify the support membership to extract the challenge
    simp only [
      support_bind, support_pure,
      Set.mem_iUnion, Set.mem_singleton_iff, exists_prop, Prod.exists
    ] at hx_mem_support
    conv at hx_mem_support =>
      erw [OptionT.support_mk, support_pure]
      simp only [
        Set.mem_singleton_iff, Option.some.injEq, Set.setOf_eq_eq_singleton, Prod.mk.injEq,
        OptionT.mem_support_iff,
        OptionT.run_monadLift, support_map, Set.mem_image, exists_eq_right, Fin.succ_one_eq_two,
        id_eq, guard_eq, bind_pure_comp,
        toPFunctor_add, toPFunctor_emptySpec, OptionT.support_run, ↓existsAndEq, and_true, true_and,
        exists_eq_right_right', liftM_pure, support_pure, exists_eq_left]
      dsimp only [monadLift, MonadLift.monadLift]
    simp only [Fin.isValue, Challenge, ChallengeIdx,
      liftComp_eq_liftM, liftM_pure, liftComp_pure, support_pure, Set.mem_singleton_iff,
      Fin.reduceLast, MessageIdx, Message] at hx_mem_support
    -- Step 2b: Extract the challenge r1 and the trace equations
    rcases hx_mem_support with ⟨prvWitOut, h_prvOut_mem_support, h_verOut_mem_support⟩
    conv at h_prvOut_mem_support =>
      dsimp only [finalSumcheckStepLogic]
      simp only [Fin.val_last, Fin.isValue, Prod.mk.injEq, and_true]
    -- Step 2c: Simplify the verifier computation
    conv at h_verOut_mem_support =>
      erw [simulateQ_bind]
      simp only [Set.mem_singleton_iff]
      change some (verStmtOut, verOStmtOut) ∈ (liftComp _ _).support
      rw [support_liftComp]
      dsimp only [Functor.map]
      erw [support_bind]
      simp only [Fin.isValue, Fin.val_last, OptionT.simulateQ_simOracle2_liftM_query_T2, pure_bind,
        OptionT.simulateQ_bind, toPFunctor_emptySpec, Function.comp_apply, OptionT.simulateQ_pure,
        Set.mem_iUnion, exists_prop]
      rw [simulateQ_ite]; erw [simulateQ_pure]
      simp only [OptionT.simulateQ_failure']
    set V_check := step.verifierCheck stmtIn
      (FullTranscript.mk1
        (msg0 := _))with h_V_check_def
    -- Step 2e: Apply the logic completeness lemma
    obtain ⟨h_V_check, h_rel, h_agree⟩ := strongly_complete (stmtIn := stmtIn)
      (witIn := witIn) (h_relIn := h_relIn) (challenges :=
      fun ⟨j, hj⟩ => by
        match j with
        | 0 =>
          have hj_ne : (pSpecFinalSumcheckStep (L := L)).dir 0 ≠ Direction.V_to_P := by
            dsimp only [pSpecFinalSumcheckStep, Fin.isValue, Matrix.cons_val_zero]
            simp only [ne_eq, reduceCtorEq, not_false_eq_true]
          exfalso
          exact hj_ne hj
      )
    have h_V_check_is_true : V_check := h_V_check
    simp only [h_V_check_is_true, ↓reduceIte, Fin.isValue] at h_verOut_mem_support
    erw [support_bind, support_pure] at h_verOut_mem_support
    simp only [Set.mem_singleton_iff, Fin.isValue, Set.iUnion_iUnion_eq_left,
      OptionT.support_OptionT_pure_run, exists_eq_left, Option.some.injEq,
      Prod.mk.injEq] at h_verOut_mem_support
    rcases h_verOut_mem_support with ⟨verStmtOut_eq, verOStmtOut_eq⟩
    obtain ⟨prvStmtOut_eq, prvOStmtOut_eq⟩ := h_prvOut_mem_support
    constructor
    · rw [verStmtOut_eq, verOStmtOut_eq];
      exact h_rel
    · constructor
      · rw [verStmtOut_eq, prvStmtOut_eq]; rfl
      · rw [verOStmtOut_eq, prvOStmtOut_eq];
        exact h_agree.2

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
    let H_constant : L⦃≤ 2⦄[X Fin (ℓ' - ↑(Fin.last ℓ'))] := ⟨MvPolynomial.C stmtMid.sumcheck_target,
      by
        simp only [Fin.val_last, mem_restrictDegree, MvPolynomial.mem_support_iff,
          MvPolynomial.coeff_C, ne_eq, ite_eq_right_iff, Classical.not_imp, and_imp, forall_eq',
          Finsupp.coe_zero, Pi.zero_apply, zero_le, implies_true]⟩
    match polyOpt with
    | none =>
      exact {
        t := ⟨0, by apply zero_mem⟩,
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
noncomputable def finalSumcheckKnowledgeStateFunction {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (finalSumcheckVerifier κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l
      (𝓑 := 𝓑)).KnowledgeStateFunction init impl
    (relIn := roundRelation K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑) (mp := RingSwitching_SumcheckMultParam κ L K
        (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l) (Fin.last ℓ'))
    (relOut := BinaryBasefold.finalSumcheckRelOut K β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (extractor := finalSumcheckRbrExtractor κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate)
  where
  toFun := fun m ⟨stmt, oStmt⟩ tr witMid =>
    finalSumcheckKStateProp κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l
      (tr := tr) (stmt := stmt) (witMid := witMid) (oStmt := oStmt)
  toFun_empty := fun stmt witMid => by
    rw [cast_eq]
    rfl
  toFun_next := fun m hDir (stmtIn, oStmtIn) tr msg witMid => by
    have h_m_eq_0 : m = 0 := by
      cases m using Fin.cases with
      | zero => rfl
      | succ m' => omega
    subst h_m_eq_0
    simp only [Fin.isValue, Fin.succ_zero_eq_one, Fin.castSucc_zero]
    -- In the single-message final sumcheck step, the new message `msg` *is* the final constant.
    -- We use it directly rather than reconstructing a truncated transcript.
    let s' : L := msg
    let stmtOut : BinaryBasefold.FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ') := {
      ctx := {
        t_eval_point := 0,
        original_claim := 0
      },
      sumcheck_target := 0,
      challenges := stmtIn.challenges,
      final_constant := s'
    }
    intro h_kState_round1
    unfold finalSumcheckKStateProp BinaryBasefold.finalSumcheckStepFoldingStateProp
      BinaryBasefold.masterKStateProp at h_kState_round1 ⊢
    simp only [Fin.isValue] at h_kState_round1
    obtain ⟨h_sumcheckFinalCheck, h_core⟩ := h_kState_round1
    -- Option-B shape at m=0:
    -- incremental bad-event ∨ (local ∧ structural ∧ initial ∧ oracleFoldingConsistency).
    cases h_core with
    | inl hConsistent =>
      have ⟨tpoly, h_extractMLP⟩ :=
        BinaryBasefold.CoreInteraction.extractMLP_some_of_oracleFoldingConsistency K β
          (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut oStmtIn hConsistent
      refine Or.inr ?_
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- local sumcheck consistency at m=0
        unfold finalSumcheckRbrExtractor sumcheckConsistencyProp
        simp only [Fin.val_last, Fin.mk_zero', Fin.coe_ofNat_eq_mod]
        split
        · simp only [MvPolynomial.eval_C, sum_const, Fintype.card_piFinset, card_map, card_univ,
            Fintype.card_fin, prod_const, tsub_self, Fintype.card_eq_zero, pow_zero, one_smul]
        · simp only [MvPolynomial.eval_C, sum_const, Fintype.card_piFinset, card_map, card_univ,
            Fintype.card_fin, prod_const, tsub_self, Fintype.card_eq_zero, pow_zero, one_smul]
      · -- witnessStructuralInvariant for extracted witness
        unfold finalSumcheckRbrExtractor BinaryBasefold.witnessStructuralInvariant
        simp only [Fin.val_last, Fin.mk_zero', h_extractMLP, Fin.coe_ofNat_eq_mod, and_true]
        refine SetLike.coe_eq_coe.mp ?_
        rw [projectToMidSumcheckPoly_at_last_eq]
        have h_s'_eq : s' = tpoly.val.eval stmtIn.challenges := by
          exact BinaryBasefold.CoreInteraction.extracted_t_poly_eval_eq_final_constant K β
            (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (oStmtOut := oStmtIn) (stmtOut := stmtOut)
            (tpoly := tpoly) (h_extractMLP := h_extractMLP)
            (h_finalSumcheckStepOracleConsistency := hConsistent)
        have h_mult_eq : (MvPolynomial.eval stmtIn.challenges
          ((RingSwitching_SumcheckMultParam κ L K
            (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l).multpoly stmtIn.ctx).val) =
          compute_final_eq_value κ L K (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l
            stmtIn.ctx.t_eval_point stmtIn.challenges stmtIn.ctx.r_batching :=
          compute_A_MLE_eval_eq_final_eq_value κ L K (β := booleanHypercubeBasis κ L K β)
            ℓ ℓ' h_l stmtIn.ctx.t_eval_point stmtIn.challenges stmtIn.ctx.r_batching
        have h_sumcheck_target_eq : stmtIn.sumcheck_target =
          (MvPolynomial.eval stmtIn.challenges
            ((RingSwitching_SumcheckMultParam κ L K
              (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l).multpoly stmtIn.ctx).val) *
            (MvPolynomial.eval stmtIn.challenges tpoly.val) := by
          calc
            stmtIn.sumcheck_target
                = compute_final_eq_value κ L K (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l
                    stmtIn.ctx.t_eval_point stmtIn.challenges stmtIn.ctx.r_batching * s' :=
                  h_sumcheckFinalCheck
            _ = compute_final_eq_value κ L K (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l
                  stmtIn.ctx.t_eval_point stmtIn.challenges stmtIn.ctx.r_batching *
                  (MvPolynomial.eval stmtIn.challenges tpoly.val) := by
                    rw [h_s'_eq]
            _ = (MvPolynomial.eval stmtIn.challenges
                  ((RingSwitching_SumcheckMultParam κ L K
                    (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l).multpoly stmtIn.ctx).val) *
                  (MvPolynomial.eval stmtIn.challenges tpoly.val) := by
                    rw [h_mult_eq]
        simp only [h_sumcheck_target_eq, Fin.val_last, Fin.coe_ofNat_eq_mod, MvPolynomial.C_mul]
      · -- initial compatibility via first-oracle consistency
        dsimp only [finalSumcheckRbrExtractor, BinaryBasefold.firstOracleWitnessConsistencyProp]
        simp only [Fin.mk_zero', h_extractMLP, Fin.coe_ofNat_eq_mod, Fin.val_last,
          OracleFrontierIndex.val_mkFromStmtIdx]
        exact (extractMLP_eq_some_iff_pair_UDRClose K β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (f := getFirstOracle K β oStmtIn) (tpoly := tpoly)).mp h_extractMLP
      · exact hConsistent.1
    | inr hBad =>
      -- Convert terminal block bad-event to incremental bad-event.
      exact Or.inl (
        (BinaryBasefold.badEventExistsProp_iff_incrementalBadEventExistsProp_last K β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)
          (oStmt := oStmtIn) (challenges := stmtIn.challenges)).1 hBad
      )
  toFun_full := fun ⟨stmtIn, oStmtIn⟩ tr witOut probEvent_relOut_gt_0 => by
  -- Same pattern as relay: verifier output (stmtOut, oStmtOut) + h_relOut ⇒ commitKStateProp 1
    simp only [StateT.run'_eq, gt_iff_lt, probEvent_pos_iff, Prod.exists] at probEvent_relOut_gt_0
    rcases probEvent_relOut_gt_0 with ⟨stmtOut, oStmtOut, h_output_mem_V_run_support, h_relOut⟩
    have h_output_mem_V_run_support' :
        some (stmtOut, oStmtOut) ∈
          (do
            let s ← init
            Prod.fst <$>
              (simulateQ impl
                (Verifier.run (stmtIn, oStmtIn) tr
                  (finalSumcheckVerifier κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l
                    (𝓑 := 𝓑)).toVerifier)).run s).support := by
      exact (OptionT.mem_support_iff
        (mx := OptionT.mk (do
          let s ← init
          Prod.fst <$>
            (simulateQ impl
              (Verifier.run (stmtIn, oStmtIn) tr
                (finalSumcheckVerifier κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l
                  (𝓑 := 𝓑)).toVerifier)).run s))
        (x := (stmtOut, oStmtOut))).1 h_output_mem_V_run_support
    simp only [support_bind, Set.mem_iUnion, exists_prop] at h_output_mem_V_run_support'
    rcases h_output_mem_V_run_support' with ⟨s, hs_init, h_output_mem_V_run_support⟩
    conv at h_output_mem_V_run_support => -- same as fold step
      simp only [Verifier.run, OracleVerifier.toVerifier]
      -- Now unfold the foldOracleVerifier's `verify()` method
      simp only [finalSumcheckVerifier]
      -- dsimp only [StateT.run]
      -- simp only [simulateQ_bind, simulateQ_query, simulateQ_pure]
      -- oracle query unfolding
      simp only [support_bind, Set.mem_iUnion]
      dsimp only [StateT.run]
      -- enter [1, i_1, 2, 1, x]
      simp only [simulateQ_bind]
      ---------------------------------------
      -- Now simplify the `guard` and `ite` of StateT.map generated from it
      simp only [MessageIdx, Fin.isValue, Matrix.cons_val_zero, simulateQ_pure, Message, guard_eq,
        pure_bind, Function.comp_apply, simulateQ_map, simulateQ_ite,
        OptionT.simulateQ_failure', bind_map_left]
      simp only [MessageIdx, Message, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
        bind_pure_comp, simulateQ_map, simulateQ_ite, simulateQ_pure, OptionT.simulateQ_failure',
        bind_map_left, Function.comp_apply]
      simp only [support_ite]
      simp only [Fin.isValue, Set.mem_ite_empty_right, Set.mem_singleton_iff, Prod.mk.injEq,
        exists_and_left, exists_eq', exists_eq_right, exists_and_right]
      simp only [Fin.isValue, id_eq, FullTranscript.mk1_eq_snoc, support_map, Set.mem_image,
        Prod.exists, exists_and_right, exists_eq_right]
      erw [simulateQ_bind]
      enter [1, x, 1, 1, 1, 2];
      erw [simulateQ_bind]
      erw [OptionT.simulateQ_simOracle2_liftM_query_T2]
      simp only [Fin.isValue, FullTranscript.mk1_eq_snoc, pure_bind, OptionT.simulateQ_map]
    conv at h_output_mem_V_run_support =>
      simp only [Fin.isValue, FullTranscript.mk1_eq_snoc, Function.comp_apply]
    erw [support_bind] at h_output_mem_V_run_support
    let step := (finalSumcheckStepLogic κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l (𝓑 := 𝓑))
    set V_check := step.verifierCheck stmtIn
      (FullTranscript.mk1 (msg0 := _)) with h_V_check_def
    by_cases h_V_check : V_check
    ·
      simp only [Fin.isValue, h_V_check, ↓reduceIte, OptionT.run_pure, simulateQ_pure,
        Set.mem_iUnion, exists_prop, Prod.exists] at h_output_mem_V_run_support
      erw [simulateQ_bind] at h_output_mem_V_run_support
      simp only [simulateQ_pure, Fin.isValue, Function.comp_apply,
        pure_bind] at h_output_mem_V_run_support
      erw [support_pure] at h_output_mem_V_run_support
      simp only [Set.mem_singleton_iff, Prod.mk.injEq, ↓existsAndEq, and_true, exists_eq_left,
        simulateQ_pure] at h_output_mem_V_run_support
      erw [support_pure] at h_output_mem_V_run_support
      simp only [Fin.isValue, Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq,
        exists_eq_right] at h_output_mem_V_run_support
      rcases h_output_mem_V_run_support with ⟨h_stmtOut_eq, h_oStmtOut_eq⟩
      simp only [Fin.reduceLast, Fin.isValue]
      -- h_relOut : ((stmtOut, oStmtOut), witOut) ∈ roundRelation 𝔽q β i.succ
      simp only [finalSumcheckRelOut, finalSumcheckRelOutProp, Set.mem_setOf_eq] at h_relOut
      -- Goal: commitKStateProp 1 stmtIn oStmtIn tr witOut
      unfold finalSumcheckKStateProp
      -- Unfold the sendMessage, receiveChallenge, output logic of prover
      dsimp only
      -- stmtOut = stmtIn; need oStmtOut = snoc_oracle oStmtIn witOut.f so goal matches h_relOut
      simp only [h_stmtOut_eq] at h_relOut ⊢
      have h_oStmtOut_eq_oStmtIn : oStmtOut = oStmtIn := by rw [h_oStmtOut_eq]; rfl
      -- c equals tr.messages ⟨0, rfl⟩
      constructor
      · -- First conjunct: sumcheck_target = eqTilde r challenges * c
        exact h_V_check
      · -- Second conjunct: finalSumcheckStepFoldingStateProp
          -- ({ toStatement := stmtIn, final_constant := c }, oStmtIn)
        rw [h_oStmtOut_eq_oStmtIn] at h_relOut
        exact h_relOut
    ·
      simp only [Fin.isValue, h_V_check, ↓reduceIte, OptionT.run_failure, simulateQ_pure,
        Set.mem_iUnion, exists_prop, Prod.exists] at h_output_mem_V_run_support
      erw [simulateQ_bind] at h_output_mem_V_run_support
      simp only [simulateQ_pure, Fin.isValue, Function.comp_apply,
        pure_bind] at h_output_mem_V_run_support
      erw [support_pure] at h_output_mem_V_run_support
      simp only [Set.mem_singleton_iff, Prod.mk.injEq, ↓existsAndEq, and_true, exists_eq_left,
        simulateQ_pure] at h_output_mem_V_run_support
      erw [support_pure] at h_output_mem_V_run_support
      simp only [Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq, false_and,
        exists_false] at h_output_mem_V_run_support -- False

/-- Round-by-round knowledge soundness for the final sumcheck step -/
theorem finalSumcheckOracleVerifier_rbrKnowledgeSoundness [Fintype L] {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (finalSumcheckVerifier κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l
      (𝓑 := 𝓑)).rbrKnowledgeSoundness init impl
      (relIn := roundRelation K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) (mp := RingSwitching_SumcheckMultParam κ L K
          (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l) (Fin.last ℓ'))
      (relOut := BinaryBasefold.finalSumcheckRelOut K β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (rbrKnowledgeError := finalSumcheckKnowledgeError L) := by
  use FinalSumcheckWit κ (L := L) K β ℓ' 𝓡 (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  use finalSumcheckRbrExtractor κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate
  use finalSumcheckKnowledgeStateFunction κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l init impl
  intro stmtIn witIn prover j
  rcases j with ⟨j, hj⟩
  cases j using Fin.cases with
  | zero =>
    simp only [pSpecFinalSumcheckStep, ne_eq, reduceCtorEq, not_false_eq_true, Fin.isValue,
      Matrix.cons_val_fin_one, Direction.not_P_to_V_eq_V_to_P] at hj
  | succ j' =>
    exact Fin.elim0 j'

end FinalSumcheckStep

section CoreInteractionPhaseReduction

/-- The final oracle verifier that composes sumcheckFold with finalSumcheckStep -/
@[reducible]
def coreInteractionOracleVerifier :=
  OracleVerifier.append (oSpec:=[]ₒ)
    (Stmt₁ := Statement (L := L) (ℓ:=ℓ') (RingSwitchingBaseContext κ L K ℓ) 0)
    (Stmt₂ := Statement (L := L) (ℓ:=ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ'))
    (Stmt₃ := BinaryBasefold.FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ'))
    (OStmt₁ := BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (OStmt₂ := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (OStmt₃ := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (pSpec₁ := BinaryBasefold.pSpecSumcheckFold K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (pSpec₂ := pSpecFinalSumcheckStep (L:=L))
    (V₁ := sumcheckFoldOracleVerifier κ (L := L) (K := K) (β := β) (ℓ := ℓ) (ℓ' := ℓ')
      (h_l := h_l)
      (𝓑 := 𝓑) (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (V₂ := finalSumcheckVerifier κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l (𝓑 := 𝓑))

/-- The final oracle reduction that composes sumcheckFold with finalSumcheckStep -/
@[reducible]
def coreInteractionOracleReduction :=
  OracleReduction.append (oSpec:=[]ₒ)
    (Stmt₁ := Statement (L := L) (ℓ:=ℓ') (RingSwitchingBaseContext κ L K ℓ) 0)
    (Stmt₂ := Statement (L := L) (ℓ:=ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ'))
    (Stmt₃ := BinaryBasefold.FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ'))
    (Wit₁ := RingSwitching.SumcheckWitness L ℓ' 0)
    (Wit₂ := BinaryBasefold.Witness K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') (Fin.last ℓ'))
    (Wit₃ := Unit)
    (OStmt₁ := BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (OStmt₂ := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (OStmt₃ := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (pSpec₁ := BinaryBasefold.pSpecSumcheckFold K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (pSpec₂ := BinaryBasefold.pSpecFinalSumcheckStep (L:=L))
    (R₁ := sumcheckFoldOracleReduction κ L K β ℓ ℓ' 𝓡 ϑ
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_l (𝓑 := 𝓑))
    (R₂ := finalSumcheckOracleReduction κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l (𝓑 := 𝓑))

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

/-- Perfect completeness for the core interaction oracle reduction -/
theorem coreInteractionOracleReduction_perfectCompleteness (hInit : NeverFail init) :
    OracleReduction.perfectCompleteness
      (oSpec := []ₒ)
      (pSpec := BinaryBasefold.pSpecCoreInteraction K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (OStmtIn := BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
      (OStmtOut := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
      (relIn := RingSwitching.strictSumcheckRoundRelation κ (L := L) (K := K)
        (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l (𝓑 := 𝓑)
        (aOStmtIn := BinaryBasefoldAbstractOStmtIn
          (κ := κ) (L := L) (K := K) (β := β)
          (ℓ' := ℓ') (𝓡 := 𝓡) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) 0)
      (relOut := BinaryBasefold.strictFinalSumcheckRelOut K β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (oracleReduction := coreInteractionOracleReduction κ L K β ℓ ℓ' 𝓡 ϑ
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_l (𝓑 := 𝓑))
      (init := init)
      (impl := impl) := by
  unfold coreInteractionOracleReduction Binius.BinaryBasefold.pSpecCoreInteraction
  apply OracleReduction.append_perfectCompleteness
    (rel₂ := (strictRoundRelation K (β := β) (i := Fin.last ℓ')))
    (Wit₁ := (SumcheckWitness L ℓ' 0))
    (Wit₂ := (Witness K (β := β) (i := Fin.last ℓ')))
    (Wit₃ := Unit)
  · -- Perfect completeness of sumcheckFoldOracleReduction
    exact sumcheckFoldOracleReduction_perfectCompleteness κ L K β ℓ ℓ' 𝓡 ϑ
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_l (𝓑 := 𝓑) (init := init) (hInit:=hInit) (impl := impl)
  · -- Perfect completeness of finalSumcheckOracleReduction
    exact finalSumcheckOracleReduction_perfectCompleteness κ L K β ℓ ℓ' 𝓡 ϑ
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_l (𝓑 := 𝓑) init (hInit := hInit) impl

def coreInteractionOracleRbrKnowledgeError (j : (BinaryBasefold.pSpecCoreInteraction K β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx) : ℝ≥0 :=
    Sum.elim
      (f := fun i => BinaryBasefold.CoreInteraction.sumcheckFoldKnowledgeError
        K β (ϑ := ϑ) i)
      (g := fun i => finalSumcheckKnowledgeError (L := L) i)
      (ChallengeIdx.sumEquiv.symm j)

/-- Round-by-round knowledge soundness for the core interaction oracle verifier -/
theorem coreInteractionOracleVerifier_rbrKnowledgeSoundness :
    (coreInteractionOracleVerifier κ (L := L) (K := K) (β := β) (ℓ := ℓ) (ℓ' := ℓ')
      (h_l := h_l) (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑)).rbrKnowledgeSoundness init impl
      (OStmtIn := BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
      (OStmtOut := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
      (pSpec := BinaryBasefold.pSpecCoreInteraction K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (relIn := RingSwitching.sumcheckRoundRelation κ L K (booleanHypercubeBasis κ L K β)
        ℓ ℓ' h_l (𝓑 := 𝓑) (aOStmtIn := BinaryBasefoldAbstractOStmtIn
          (κ := κ) (L := L) (K := K) (β := β)
          (ℓ' := ℓ') (𝓡 := 𝓡) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) 0)
      (relOut := BinaryBasefold.finalSumcheckRelOut K β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (rbrKnowledgeError := coreInteractionOracleRbrKnowledgeError κ L K β ℓ' 𝓡 ϑ
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) := by
  let res := OracleVerifier.append_rbrKnowledgeSoundness
    (oSpec := []ₒ)
    (OStmt₁ := BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (OStmt₂ := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (OStmt₃ := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (init := init) (impl:=impl)
    (Wit₁ := (SumcheckWitness L ℓ' 0))
    (Wit₂ := (Witness K (β := β) (i := Fin.last ℓ')))
    (Wit₃ := Unit)
    (rel₁ := RingSwitching.sumcheckRoundRelation κ L K (booleanHypercubeBasis κ L K β)
        ℓ ℓ' h_l (𝓑 := 𝓑) (aOStmtIn := BinaryBasefoldAbstractOStmtIn
          (κ := κ) (L := L) (K := K) (β := β)
          (ℓ' := ℓ') (𝓡 := 𝓡) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) 0)
    (rel₂ :=  BinaryBasefold.roundRelation (mp := RingSwitching_SumcheckMultParam κ L K
      (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l) K β (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) (Fin.last ℓ'))
    (rel₃ := finalSumcheckRelOut K β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (V₁ := sumcheckFoldOracleVerifier κ (L := L) (K := K) (β := β) (ℓ := ℓ) (ℓ' := ℓ')
      (h_l := h_l)
      (𝓑 := 𝓑) (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (V₂ := finalSumcheckVerifier κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l (𝓑 := 𝓑))
    (Oₛ₃:=by exact fun i ↦ by exact OracleInterface.instDefault)
    (rbrKnowledgeError₁ := BinaryBasefold.CoreInteraction.sumcheckFoldKnowledgeError
        K β (ϑ := ϑ))
    (rbrKnowledgeError₂ := finalSumcheckKnowledgeError (L := L))
    (h₁ := by apply sumcheckFoldOracleVerifier_rbrKnowledgeSoundness)
    (h₂ := by apply finalSumcheckOracleVerifier_rbrKnowledgeSoundness)
  exact res

end CoreInteractionPhaseReduction

end
end Binius.FRIBinius.CoreInteractionPhase
