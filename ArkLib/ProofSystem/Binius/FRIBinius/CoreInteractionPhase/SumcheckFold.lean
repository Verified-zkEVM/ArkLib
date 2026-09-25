/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.OracleReduction.Composition.Sequential.NoAmbient
public import ArkLib.OracleReduction.Composition.Sequential.OracleCompleteness
public import ArkLib.ProofSystem.Binius.BinaryBasefold.CoreInteractionPhase
public import ArkLib.ProofSystem.Binius.BinaryBasefold.ReductionLogic
public import ArkLib.ProofSystem.Binius.FRIBinius.Prelude
public import ArkLib.ProofSystem.RingSwitching.Packing.TensorLemmas

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
-/

@[expose] public section

/- These composed protocol bundles are `def`s whose *inferred* type embeds the inline `Fin` bounds
proofs written in their bodies, so the module system's default elaboration either delays every `by`
until the still-unknown result type is solved, or abstracts the proof into a private auxiliary
theorem a public signature may not mention. `backward.proofsInPublic` restores the classic
elaboration these definitions were written against. See docs/wiki/module-system.md. -/
set_option backward.proofsInPublic true

namespace Binius.FRIBinius.CoreInteractionPhase
noncomputable section

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial
  MvPolynomial TensorProduct Module Binius.BinaryBasefold _root_.RingSwitching
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
variable [hdiv : Fact (ϑ ∣ ℓ')]

/-- The Binius ring-switching profile, built from the boolean-hypercube basis derived from `β`.
Routed through `Binius.FRIBinius.bbfSumcheckProfile` (which is
`tensorProductProfile … (booleanHypercubeBasis …)`) so that the `RingSwitchingBaseContext` keyed by
this profile is syntactically the one the `RingSwitching_BBFSumcheckMultParam` wrapper produces
(with `β := booleanHypercubeBasis κ L K β`), avoiding profile-unification friction. -/
abbrev biniusProfile : RingSwitching.RingSwitchingProfile K L κ :=
  Binius.FRIBinius.bbfSumcheckProfile κ L K (booleanHypercubeBasis κ L K β)

section FixFirstBridge
variable {L' : Type} [CommRing L'] {ℓ'' : ℕ}

/-- The promoted `MvPolynomial.fixFirstVariablesOfMQP` and the legacy
`Binius.BinaryBasefold.fixFirstVariablesOfMQP` compute the same substitution (fix the first `v`
variables to `challenges`); both agree with the `bind₁` normal form.

Local copy of `RingSwitching.SumcheckPhase.mvPoly_fixFirst_eq_bbf_fixFirst` (that module cannot be
imported here without a cycle); used to bridge the ring-switching `WithParam` mid-poly projection to
the identity-combinator `BinaryBasefold.projectToMidSumcheckPoly`. -/
lemma mvPoly_fixFirst_eq_bbf_fixFirst (v : Fin (ℓ'' + 1))
    (poly : MvPolynomial (Fin ℓ'') L') (challenges : Fin v → L') :
    MvPolynomial.fixFirstVariablesOfMQP ℓ'' v poly challenges =
      Binius.BinaryBasefold.fixFirstVariablesOfMQP ℓ'' v poly challenges := by
  rw [Binius.BinaryBasefold.fixFirstVariablesOfMQP_eq_bind₁]
  let subst : Fin ℓ'' → MvPolynomial (Fin (ℓ'' - v)) L' := fun j =>
    if hj : j.val < v.val then MvPolynomial.C (challenges ⟨j.val, hj⟩)
    else MvPolynomial.X (⟨j.val - v, by omega⟩ : Fin (ℓ'' - v))
  have hX : ∀ j : Fin ℓ'',
      MvPolynomial.fixFirstVariablesOfMQP ℓ'' v (MvPolynomial.X j) challenges =
        MvPolynomial.bind₁ subst (MvPolynomial.X j) := by
    intro j
    rw [MvPolynomial.bind₁_X_right]
    unfold subst MvPolynomial.fixFirstVariablesOfMQP
    dsimp only
    rw [MvPolynomial.rename_X]
    by_cases hj : j.val < v.val
    · have hsym : (finSumFinEquiv (m := ↑v) (n := ℓ'' - ↑v)).symm (Fin.cast (by omega) j)
          = Sum.inl (⟨j.val, hj⟩ : Fin ↑v) := by
        rw [Equiv.symm_apply_eq, finSumFinEquiv_apply_left]; apply Fin.ext; simp
      have hmap : (((finCongr (by omega : ℓ'' = ↑v + (ℓ'' - ↑v))).trans
          ((finSumFinEquiv (m := ↑v) (n := ℓ'' - ↑v)).symm.trans (Equiv.sumComm _ _))) j)
          = Sum.inr (⟨j.val, hj⟩ : Fin ↑v) := by
        simp only [Equiv.trans_apply, finCongr_apply, Equiv.sumComm_apply, hsym, Sum.swap_inl]
      rw [hmap]
      simp only [MvPolynomial.sumAlgEquiv_X_inr, MvPolynomial.map_C,
        MvPolynomial.eval_X, hj, ↓reduceDIte]
    · have hsym : (finSumFinEquiv (m := ↑v) (n := ℓ'' - ↑v)).symm (Fin.cast (by omega) j)
          = Sum.inr (⟨j.val - v, by omega⟩ : Fin (ℓ'' - ↑v)) := by
        rw [Equiv.symm_apply_eq, finSumFinEquiv_apply_right]
        apply Fin.ext; simp only [Fin.natAdd_mk, Fin.val_cast]; omega
      have hmap : (((finCongr (by omega : ℓ'' = ↑v + (ℓ'' - ↑v))).trans
          ((finSumFinEquiv (m := ↑v) (n := ℓ'' - ↑v)).symm.trans (Equiv.sumComm _ _))) j)
          = Sum.inl (⟨j.val - v, by omega⟩ : Fin (ℓ'' - ↑v)) := by
        simp only [Equiv.trans_apply, finCongr_apply, Equiv.sumComm_apply, hsym, Sum.swap_inr]
      rw [hmap]
      simp only [MvPolynomial.sumAlgEquiv_X_inl, MvPolynomial.map_X,
        hj, ↓reduceDIte]
  induction poly using MvPolynomial.induction_on with
  | C a =>
    unfold MvPolynomial.fixFirstVariablesOfMQP
    simp only [MvPolynomial.rename_C, MvPolynomial.sumAlgEquiv_C_inl,
      MvPolynomial.map_C, MvPolynomial.eval_C, MvPolynomial.bind₁_C_right]
  | add p q hp hq =>
    have h_add : MvPolynomial.fixFirstVariablesOfMQP ℓ'' v (p + q) challenges =
        MvPolynomial.fixFirstVariablesOfMQP ℓ'' v p challenges +
          MvPolynomial.fixFirstVariablesOfMQP ℓ'' v q challenges := by
      unfold MvPolynomial.fixFirstVariablesOfMQP; simp only [map_add]
    rw [h_add, hp, hq, map_add]
  | mul_X p j hp =>
    have h_mul : MvPolynomial.fixFirstVariablesOfMQP ℓ'' v (p * MvPolynomial.X j) challenges =
        MvPolynomial.fixFirstVariablesOfMQP ℓ'' v p challenges *
          MvPolynomial.fixFirstVariablesOfMQP ℓ'' v (MvPolynomial.X j) challenges := by
      unfold MvPolynomial.fixFirstVariablesOfMQP; simp only [map_mul]
    rw [h_mul, hp, hX, map_mul]

end FixFirstBridge

section SumcheckFold

/-- Query-executable statement lens for the sumcheck-fold lift. It copies the structured
sumcheck fields into Binary Basefold's statement and routes the unchanged oracle queries. -/
def sumcheckFoldExecutableStmtLens : OracleStatement.ExecutableLens
    (OuterStmtIn := Sumcheck.Structured.Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) 0)
    (OuterStmtOut := Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) (Fin.last ℓ'))
    (InnerStmtIn := Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) 0)
    (InnerStmtOut := Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) (Fin.last ℓ'))
    (OuterOStmtIn := BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (OuterOStmtOut := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (InnerOStmtIn := BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (InnerOStmtOut := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ')) where
  projStmt := fun stmt => ⟨stmt.sumcheck_target, stmt.challenges, stmt.ctx⟩
  materializeInput := fun _ outerOStmt => outerOStmt
  simulateInput := fun _ q => liftM <| OracleSpec.query q
  simulateInput_eq := by
    intro outerStmt outerOStmt q
    rcases q with ⟨i, query⟩
    simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      OracleInterface.simOracle0]
    rfl
  liftStmt := fun _ innerStmtOut => innerStmtOut
  materializeOutput := fun _ innerOStmtOut => innerOStmtOut
  simulateOutput := fun q => liftM <| OracleSpec.query
    (show ([BinaryBasefold.OracleStatement K β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0]ₒ +
      [BinaryBasefold.OracleStatement K β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ')]ₒ).Domain from Sum.inr q)
  simulateOutput_eq := by
    intro outerOStmt innerOStmt q
    rcases q with ⟨i, query⟩
    simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query]
    rfl

/-- Extensional view of `sumcheckFoldExecutableStmtLens`, retained for
relation and extractor APIs. -/
def sumcheckFoldStmtLens : OracleStatement.Lens
    (OuterStmtIn := Sumcheck.Structured.Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) 0)
    (OuterStmtOut := Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) (Fin.last ℓ'))
    (InnerStmtIn := Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) 0)
    (InnerStmtOut := Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) (Fin.last ℓ'))
    (OuterOStmtIn := BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (OuterOStmtOut := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (InnerOStmtIn := BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (InnerOStmtOut := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ')) :=
  (sumcheckFoldExecutableStmtLens κ L K β ℓ ℓ' 𝓡 ϑ
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).toLens

/-- Oracle context lens for sumcheck fold lifting -/
def sumcheckFoldCtxLens : OracleContext.Lens
    (OuterStmtIn := Sumcheck.Structured.Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) 0)
    (OuterStmtOut := Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) (Fin.last ℓ'))
    (InnerStmtIn := Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) 0)
    (InnerStmtOut := Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) (Fin.last ℓ'))
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

/-- Executable context lens used by the oracle reduction. -/
def sumcheckFoldExecutableCtxLens : OracleContext.ExecutableLens
    (OuterStmtIn := Sumcheck.Structured.Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) 0)
    (OuterStmtOut := Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) (Fin.last ℓ'))
    (InnerStmtIn := Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) 0)
    (InnerStmtOut := Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) (Fin.last ℓ'))
    (OuterOStmtIn := BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (OuterOStmtOut := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (InnerOStmtIn := BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (InnerOStmtOut := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (OuterWitIn := RingSwitching.SumcheckWitness L ℓ' 0)
    (OuterWitOut := BinaryBasefold.Witness K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') (Fin.last ℓ'))
    (InnerWitIn := BinaryBasefold.Witness K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') 0)
    (InnerWitOut := BinaryBasefold.Witness K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') (Fin.last ℓ')) where
  stmt := sumcheckFoldExecutableStmtLens κ L K β ℓ ℓ' 𝓡 ϑ
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  wit := (sumcheckFoldCtxLens κ L K β ℓ ℓ' 𝓡 ϑ
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_l).wit

/-- The executable lift preserves an inner sumcheck-fold output oracle. -/
def sumcheckFoldLiftContextOutput
    {V : OracleVerifier
      (oSpec := []ₒ)
      (StmtIn := Statement (L := L) (ℓ := ℓ')
        (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) 0)
      (OStmtIn := BinaryBasefold.OracleStatement K β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
      (StmtOut := Statement (L := L) (ℓ := ℓ')
        (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) (Fin.last ℓ'))
      (OStmtOut := BinaryBasefold.OracleStatement K β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
      (pSpec := BinaryBasefold.pSpecSumcheckFold K β
        (ℓ := ℓ') (𝓡 := 𝓡) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate))} :
    OracleVerifier.LiftContextOutput
    (sumcheckFoldExecutableStmtLens κ L K β ℓ ℓ' 𝓡 ϑ
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    V where
  outputOracle := V.outputOracle
  materialize_eq := by
    intro outerStmt challenges outerOStmt messages
    rfl

/-- Extractor lens for sumcheck fold lifting -/
def sumcheckFoldExtractorLens : Extractor.Lens
    (OuterStmtIn := Sumcheck.Structured.Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) 0 ×
      (∀ j, OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0 j))
    (OuterStmtOut := Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) (Fin.last ℓ') ×
      (∀ j, OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ') j))
    (InnerStmtIn := Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) 0 ×
      (∀ j, OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0 j))
    (InnerStmtOut := Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) (Fin.last ℓ')
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
  (BinaryBasefold.CoreInteraction.sumcheckFoldOracleVerifier
    (mp := RingSwitching_BBFSumcheckMultParam κ L K
      (booleanHypercubeBasis κ L K β) ℓ ℓ' h_l)
    K β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := boolEmbedding L)).liftContext
      (sumcheckFoldExecutableStmtLens κ L K β ℓ ℓ' 𝓡 ϑ
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (sumcheckFoldLiftContextOutput κ L K β ℓ ℓ' 𝓡 ϑ
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate))

-- The lifted oracle reduction
def sumcheckFoldOracleReduction :=
  (BinaryBasefold.CoreInteraction.sumcheckFoldOracleReduction
    (mp := RingSwitching_BBFSumcheckMultParam κ L K
      (booleanHypercubeBasis κ L K β) ℓ ℓ' h_l)
    K β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := boolEmbedding L)).liftContext
      (sumcheckFoldExecutableCtxLens κ L K β ℓ ℓ' 𝓡 ϑ
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_l)
      (sumcheckFoldLiftContextOutput κ L K β ℓ ℓ' 𝓡 ϑ
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate))

-- Security properties for the lifted oracle reduction

section Security

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

-- Completeness instance for the context lens
instance sumcheckFoldCtxLens_complete :
  (sumcheckFoldCtxLens κ L K β ℓ ℓ' 𝓡 ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_l).toContext.IsComplete
    (OuterStmtIn := Sumcheck.Structured.Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) 0 ×
      (∀ i, BinaryBasefold.OracleStatement K (⇑β) ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 i))
    (OuterStmtOut := Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) (Fin.last ℓ') ×
      (∀ i, BinaryBasefold.OracleStatement K (⇑β) ϑ
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ') i))
    (InnerStmtIn := Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) 0 ×
      (∀ i, BinaryBasefold.OracleStatement K (⇑β) ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 i))
    (InnerStmtOut := Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) (Fin.last ℓ') ×
      (∀ i, BinaryBasefold.OracleStatement K (⇑β) ϑ
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ') i))
    (OuterWitIn := RingSwitching.SumcheckWitness L ℓ' 0)
    (OuterWitOut := BinaryBasefold.Witness K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') (Fin.last ℓ'))
    (InnerWitIn := Witness K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') 0)
    (InnerWitOut := Witness K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') (Fin.last ℓ'))
    (outerRelIn := RingSwitching.strictSumcheckRoundRelation κ L K
      (biniusProfile κ L K β) ℓ ℓ' h_l
      (aOStmtIn := BinaryBasefoldAbstractOStmtIn
        (κ := κ) (L := L) (K := K) (β := β)
        (ℓ' := ℓ') (𝓡 := 𝓡) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) 0)
    (outerRelOut :=
      BinaryBasefold.strictRoundRelation (mp := RingSwitching_BBFSumcheckMultParam κ L K
        (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l) K β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := boolEmbedding L) (Fin.last ℓ')
    )
    (innerRelIn :=
      BinaryBasefold.strictRoundRelation (mp := RingSwitching_BBFSumcheckMultParam κ L K
        (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l) K β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := boolEmbedding L) 0
    )
    (innerRelOut :=
      BinaryBasefold.strictRoundRelation (mp := RingSwitching_BBFSumcheckMultParam κ L K
        (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l) K β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := boolEmbedding L) (Fin.last ℓ')
    )
    (compat :=
      let originalReduction := (CoreInteraction.sumcheckFoldOracleReduction K β (ϑ:=ϑ)
        (mp := RingSwitching_BBFSumcheckMultParam κ L K
          (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := boolEmbedding L)).toReduction
      Reduction.compatContext (oSpec := []ₒ) (pSpec :=
        pSpecSumcheckFold K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
        (sumcheckFoldCtxLens κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l).toContext originalReduction
    ) where
  proj_complete := fun stmtIn oStmtIn hRelIn => by
    rcases stmtIn with ⟨stmtIn, oStmtIn'⟩
    rcases oStmtIn with ⟨t', H⟩
    -- `strictSumcheckRoundRelation` (main frame) unfolds to
    -- `localChecks (= True) ∧ witnessStructuralInvariant ∧ sumcheckConsistency (boolDomain) ∧
    --  strictInitialCompatibility`.
    obtain ⟨_h_local, h_struct, h_sumcheck_cons, h_strict_compat⟩ := hRelIn
    -- Goal (BBF `strictRoundRelationProp` at 0):
    --   `sumcheckConsistency ∧ (witnessStructuralInvariant ∧ strictOracleFoldingConsistency)`.
    refine ⟨?_, ?_, ?_⟩
    · -- sumcheckConsistency: the `boolDomain L _` form is defeq to the BBF `boolEmbedding L` form.
      dsimp [sumcheckFoldStmtLens] at h_sumcheck_cons ⊢
      exact h_sumcheck_cons
    · -- witnessStructuralInvariant (BBF): `H = projectToMidSumcheckPoly …` (from `h_struct`, defeq
      -- via the shared `multpoly`) and `f = getMidCodewords …` (definitional in the ctx-lens `f₀`).
      refine ⟨?_, ?_⟩
      · -- `H = projectToMidSumcheckPoly …`: bridge the structured `WithParam` projection (in
        -- `h_struct`) to the identity-combinator `projectToMidSumcheckPoly` used by BBF. For the
        -- ring-switching multiplier (combinator `X`) they have the same `.val`, and the two
        -- `multpoly`s are defeq (the `RingSwitching_BBFSumcheckMultParam` wrapper delegates).
        dsimp only [sumcheckFoldCtxLens, sumcheckFoldStmtLens, Statement.Lens.proj,
          OracleContext.Lens.stmt, Witness.Lens.proj]
        apply Subtype.ext
        rw [show (H : L⦃≤ 2⦄[X Fin (ℓ' - (0 : Fin (ℓ' + 1)))]).val = _ from h_struct]
        simp only [Sumcheck.Structured.projectToMidSumcheckPolyWithParam,
          Sumcheck.Structured.computeRoundPoly, BinaryBasefold.projectToMidSumcheckPoly,
          BinaryBasefold.computeInitialSumcheckPoly, RingSwitching_SumcheckMultParam,
          RingSwitching_BBFSumcheckMultParam, bbfSumcheckProfile, biniusProfile,
          Polynomial.aeval_X, mul_comm]
        exact mvPoly_fixFirst_eq_bbf_fixFirst _ _ _
      · rfl
    · -- strictOracleFoldingConsistency: from `strictInitialCompatibility` (= folding consistency at
      -- index 0 with the empty challenge tuple).
      change strictOracleFoldingConsistencyProp K β
        (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (t := t') (i := (0 : Fin (ℓ' + 1)))
        (challenges := stmtIn.challenges) (oStmt := oStmtIn')
      have h_strict_compat' :
          strictOracleFoldingConsistencyProp K β
            (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (t := t') (i := (0 : Fin (ℓ' + 1)))
            (challenges := Fin.elim0) (oStmt := oStmtIn') := by
        dsimp [BinaryBasefoldAbstractOStmtIn,
          Binius.RingSwitching.BBFSmallFieldIOPCS.bbfAbstractOStmtIn,
          strictOracleFoldingConsistencyProp] at h_strict_compat ⊢
        exact h_strict_compat
      have h_challenges : stmtIn.challenges = (Fin.elim0 : Fin 0 → L) := by
        funext i
        exact Fin.elim0 i
      rw [h_challenges]
      exact h_strict_compat'
  lift_complete := fun outerStmtIn outerWitIn innerStmtOut innerWitOut compat => by
    intro _ hRelOut
    dsimp [sumcheckFoldStmtLens] at hRelOut ⊢
    exact hRelOut

-- Perfect completeness for the lifted oracle reduction
omit h_β₀_eq_1 in
theorem sumcheckFoldOracleReduction_perfectCompleteness :
    OracleReduction.perfectCompleteness
    (oSpec := []ₒ)
    (StmtIn := Sumcheck.Structured.Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) 0)
    (OStmtIn := BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (WitIn := RingSwitching.SumcheckWitness L ℓ' 0)
    (StmtOut := Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) (Fin.last ℓ'))
    (OStmtOut := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (WitOut := BinaryBasefold.Witness K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') (Fin.last ℓ'))
    (pSpec := BinaryBasefold.pSpecSumcheckFold K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (relIn := RingSwitching.strictSumcheckRoundRelation κ L K (biniusProfile κ L K β)
      ℓ ℓ' h_l (aOStmtIn := BinaryBasefoldAbstractOStmtIn (β := β) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) 0)
    (relOut :=
      BinaryBasefold.strictRoundRelation (mp := RingSwitching_BBFSumcheckMultParam κ L K
        (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l) K β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := boolEmbedding L) (Fin.last ℓ')
    )
    (oracleReduction := sumcheckFoldOracleReduction κ L K β ℓ ℓ' 𝓡 ϑ
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_l)
    (init := init)
    (impl := impl) :=
  OracleReduction.liftContext_perfectCompleteness
    (oSpec := []ₒ)
    (OuterStmtIn := Sumcheck.Structured.Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) 0)
    (OuterStmtOut := Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) (Fin.last ℓ'))
    (OuterWitIn := RingSwitching.SumcheckWitness L ℓ' 0)
    (OuterWitOut := BinaryBasefold.Witness K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') (Fin.last ℓ'))
    (OuterOStmtIn := BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (OuterOStmtOut := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (InnerStmtIn := Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) 0)
    (InnerStmtOut := Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) (Fin.last ℓ'))
    (InnerWitIn := BinaryBasefold.Witness K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') 0)
    (InnerWitOut := BinaryBasefold.Witness K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') (Fin.last ℓ'))
    (InnerOStmtIn := BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (InnerOStmtOut := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (pSpec := BinaryBasefold.pSpecSumcheckFold K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (outerRelIn := RingSwitching.strictSumcheckRoundRelation κ L K (biniusProfile κ L K β)
      ℓ ℓ' h_l (aOStmtIn := BinaryBasefoldAbstractOStmtIn κ L K β ℓ'
        𝓡 ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) 0)
    (outerRelOut := BinaryBasefold.strictRoundRelation
      (mp := RingSwitching_BBFSumcheckMultParam κ L K
        (booleanHypercubeBasis κ L K β) ℓ ℓ' h_l) K β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := boolEmbedding L) (Fin.last ℓ'))
    (innerRelIn := BinaryBasefold.strictRoundRelation
      (mp := RingSwitching_BBFSumcheckMultParam κ L K
        (booleanHypercubeBasis κ L K β) ℓ ℓ' h_l) K β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := boolEmbedding L) 0)
    (innerRelOut := BinaryBasefold.strictRoundRelation
      (mp := RingSwitching_BBFSumcheckMultParam κ L K
        (booleanHypercubeBasis κ L K β) ℓ ℓ' h_l) K β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := boolEmbedding L) (Fin.last ℓ'))
    (lens := sumcheckFoldExecutableCtxLens κ L K β ℓ ℓ' 𝓡 ϑ
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_l)
    (output := sumcheckFoldLiftContextOutput κ L K β ℓ ℓ' 𝓡 ϑ
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (lensComplete := sumcheckFoldCtxLens_complete κ L K β ℓ ℓ' 𝓡 ϑ
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_l)
    (init := init)
    (impl := impl)
    (h := BinaryBasefold.CoreInteraction.sumcheckFoldOracleReduction_perfectCompleteness
      K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := boolEmbedding L))

/-- Knowledge soundness instance for the extractor lens. This one is compatStmt-agnostic -/
instance sumcheckFoldExtractorLens_rbr_knowledge_soundness
    {compatStmt :
      (Sumcheck.Structured.Statement (L := L) (ℓ := ℓ')
        (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) 0 ×
        (∀ i, BinaryBasefold.OracleStatement K (⇑β) ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 i)) →
      (Statement (L := L) (ℓ := ℓ')
        (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) (Fin.last ℓ') ×
        (∀ i, BinaryBasefold.OracleStatement K (⇑β) ϑ
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ') i)) → Prop} :
    Extractor.Lens.IsKnowledgeSound
      (OuterStmtIn := Sumcheck.Structured.Statement (L := L) (ℓ := ℓ')
        (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) 0 ×
        (∀ i, BinaryBasefold.OracleStatement K (⇑β) ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 i))
      (OuterStmtOut := Statement (L := L) (ℓ := ℓ')
        (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β))
        (Fin.last ℓ') × (∀ i, BinaryBasefold.OracleStatement K (⇑β) ϑ
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ') i))
      (InnerStmtIn := Statement (L := L) (ℓ := ℓ')
        (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) 0 ×
        (∀ i, BinaryBasefold.OracleStatement K (⇑β) ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 i))
      (InnerStmtOut := Statement (L := L) (ℓ := ℓ')
        (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β))
        (Fin.last ℓ') × (∀ i, BinaryBasefold.OracleStatement K (⇑β) ϑ
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ') i))
      (OuterWitIn := RingSwitching.SumcheckWitness L ℓ' 0)
      (OuterWitOut := BinaryBasefold.Witness K β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') (Fin.last ℓ'))
      (InnerWitIn := Witness K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') 0)
      (InnerWitOut := Witness K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') (Fin.last ℓ'))
      (outerRelIn := RingSwitching.sumcheckRoundRelation κ L K (biniusProfile κ L K β)
        ℓ ℓ' h_l (aOStmtIn := BinaryBasefoldAbstractOStmtIn
          (κ := κ) (L := L) (K := K) (β := β)
          (ℓ' := ℓ') (𝓡 := 𝓡) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) 0)
      (outerRelOut :=
        BinaryBasefold.roundRelation (mp := RingSwitching_BBFSumcheckMultParam κ L K
          (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l) K β (ϑ:=ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := boolEmbedding L)  (Fin.last ℓ')
      )
      (innerRelIn :=
        BinaryBasefold.roundRelation (mp := RingSwitching_BBFSumcheckMultParam κ L K
          (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l) K β (ϑ:=ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := boolEmbedding L)  0
      )
      (innerRelOut :=
        BinaryBasefold.roundRelation (mp := RingSwitching_BBFSumcheckMultParam κ L K
          (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l) K β (ϑ:=ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := boolEmbedding L)  (Fin.last ℓ')
      )
      (compatStmt := compatStmt)
      (compatWit := fun _ _ => True)
      (lens := sumcheckFoldExtractorLens κ L K β ℓ ℓ' 𝓡 ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      where
  proj_knowledgeSound := by
    intro outerStmtIn innerStmtOut outerWitOut _ hOuter
    dsimp [sumcheckFoldExtractorLens, sumcheckFoldStmtLens] at hOuter ⊢
    exact hOuter
  lift_knowledgeSound := by
    intro outerStmtIn outerWitOut innerWitIn _ hInner
    rcases outerStmtIn with ⟨stmtIn, oStmtIn⟩
    have hInner' :
        BinaryBasefold.roundRelationProp
          (mp := RingSwitching_BBFSumcheckMultParam κ L K
            (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l)
          K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := boolEmbedding L)
          (0 : Fin (ℓ' + 1))
          ((⟨stmtIn.sumcheck_target, stmtIn.challenges, stmtIn.ctx⟩, oStmtIn), innerWitIn) := by
      dsimp [BinaryBasefold.roundRelation] at hInner ⊢
      dsimp [sumcheckFoldExtractorLens] at hInner ⊢
      exact hInner
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
          have hcount :
              BinaryBasefold.toOutCodewordsCount ℓ' ϑ
                ((OracleFrontierIndex.mkFromStmtIdx (0 : Fin (ℓ' + 1))).val) = 1 := by
            change BinaryBasefold.toOutCodewordsCount ℓ' ϑ 0 = 1
            exact BinaryBasefold.toOutCodewordsCountOf0 (ℓ := ℓ') (ϑ := ϑ)
          exact Nat.lt_of_lt_of_eq j.isLt hcount
        exact Nat.lt_one_iff.mp hjlt
      subst hj0
      dsimp [BinaryBasefold.oraclePositionToDomainIndex] at hj
      exact absurd hj (by
        apply BinaryBasefold.incrementalFoldingBadEvent_of_k_eq_0_is_false
          (𝔽q := K) (β := β)
          (h_k := by
            simp only [zero_mul, tsub_self, zero_le, inf_of_le_right])
          (h_midIdx := by simp only [zero_mul, tsub_self, zero_le,
            inf_of_le_right, add_zero]))
    rcases hInner' with h_bad | h_good
    · exact (h_no_bad h_bad).elim
    · have h_local := h_good.1
      have h_struct := h_good.2.1
      have h_first := h_good.2.2.1
      -- OUTER goal (`sumcheckRoundRelation` = RingSwitching `masterKStateProp`):
      --   `True ∧ witnessStructuralInvariant ∧ sumcheckConsistency (boolDomain) ∧ initialCompat`.
      refine ⟨trivial, ?_, ?_, ?_⟩
      · -- witnessStructuralInvariant (RingSwitching `WithParam` form ← BBF struct first conjunct).
        dsimp only [sumcheckFoldExtractorLens, sumcheckFoldStmtLens,
          RingSwitching.witnessStructuralInvariant]
        rw [congrArg Subtype.val h_struct.1]
        simp only [BinaryBasefold.projectToMidSumcheckPoly,
          Sumcheck.Structured.projectToMidSumcheckPolyWithParam,
          Sumcheck.Structured.computeRoundPoly, BinaryBasefold.computeInitialSumcheckPoly,
          RingSwitching_SumcheckMultParam, RingSwitching_BBFSumcheckMultParam,
          bbfSumcheckProfile, biniusProfile, Polynomial.aeval_X, mul_comm]
        exact (mvPoly_fixFirst_eq_bbf_fixFirst _ _ _).symm
      · -- sumcheckConsistency (boolDomain form is defeq to the BBF `boolEmbedding L` form).
        dsimp [sumcheckFoldExtractorLens, sumcheckFoldStmtLens] at h_local ⊢
        exact h_local
      · -- initialCompatibility = firstOracleWitnessConsistency of `bbfAbstractOStmtIn`.
        dsimp [BinaryBasefoldAbstractOStmtIn] at h_first ⊢
        exact h_first

-- Round-by-round knowledge soundness for the lifted oracle verifier
theorem sumcheckFoldOracleVerifier_rbrKnowledgeSoundness :
    OracleVerifier.rbrKnowledgeSoundness
      (oSpec := []ₒ)
      (StmtIn := Sumcheck.Structured.Statement (L := L) (ℓ := ℓ')
        (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) 0)
      (OStmtIn := BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
      (WitIn := RingSwitching.SumcheckWitness L ℓ' 0)
      (StmtOut := Statement (L := L) (ℓ := ℓ')
        (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) (Fin.last ℓ'))
      (OStmtOut := BinaryBasefold.OracleStatement K β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
      (WitOut := BinaryBasefold.Witness K β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') (Fin.last ℓ'))
      (pSpec := BinaryBasefold.pSpecSumcheckFold K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (relIn := RingSwitching.sumcheckRoundRelation κ L K (biniusProfile κ L K β)
        ℓ ℓ' h_l (aOStmtIn := BinaryBasefoldAbstractOStmtIn
          (κ := κ) (L := L) (K := K) (β := β)
          (ℓ' := ℓ') (𝓡 := 𝓡) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) 0)
      (relOut :=
        BinaryBasefold.roundRelation (mp := RingSwitching_BBFSumcheckMultParam κ L K
          (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l) K β (ϑ:=ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := boolEmbedding L)  (Fin.last ℓ')
      )
      (verifier := sumcheckFoldOracleVerifier κ L K β ℓ ℓ' (h_l := h_l) 𝓡 ϑ
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (init := init)
      (impl := impl)
      (rbrKnowledgeError := BinaryBasefold.CoreInteraction.sumcheckFoldKnowledgeError
        K β (ϑ := ϑ)) := by
  let : Inhabited (Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) (Fin.last ℓ')) := ⟨{
      ctx := {
        t_eval_point := 0
        original_claim := 0
        s_hat := 0
        r_batching := 0
      }
      sumcheck_target := 0
      challenges := 0
    }⟩
  let :
      ∀ i : Fin (toOutCodewordsCount ℓ' ϑ (i := Fin.last ℓ')),
        Inhabited (BinaryBasefold.OracleStatement K β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ') i) := by
    intro i
    exact ⟨fun _ => 0⟩
  let : Inhabited (BinaryBasefold.Witness K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') 0) := ⟨{
      t := 0
      H := 0
      f := fun _ => 0
    }⟩
  have h_lifted := OracleVerifier.liftContext_rbr_knowledgeSoundness
      (V := BinaryBasefold.CoreInteraction.sumcheckFoldOracleVerifier K β
        (ϑ := ϑ)
        (mp := RingSwitching_BBFSumcheckMultParam κ L K
          (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l)
        (𝓑 := boolEmbedding L)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (stmtLens := sumcheckFoldExecutableStmtLens κ L K β ℓ ℓ' 𝓡 ϑ
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (output := sumcheckFoldLiftContextOutput κ L K β ℓ ℓ' 𝓡 ϑ
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (witLens := (sumcheckFoldExtractorLens κ L K β ℓ ℓ' 𝓡 ϑ
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).wit)
      (lensKS := sumcheckFoldExtractorLens_rbr_knowledge_soundness
        (κ := κ) (L := L) (K := K) (β := β) (ℓ := ℓ) (ℓ' := ℓ') (𝓡 := 𝓡) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_l := h_l)
        (compatStmt := (BinaryBasefold.CoreInteraction.sumcheckFoldOracleVerifier K β
          (ϑ := ϑ)
          (mp := RingSwitching_BBFSumcheckMultParam κ L K (β := booleanHypercubeBasis κ L K β)
            ℓ ℓ' h_l)
          (𝓑 := boolEmbedding L) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).toVerifier.compatStatement
          (sumcheckFoldStmtLens κ L K β ℓ ℓ' 𝓡 ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate))))
      (h := by
        exact
          BinaryBasefold.CoreInteraction.sumcheckFoldOracleVerifier_rbrKnowledgeSoundness
            (L := L) K β
            (ϑ := ϑ)
            (mp := RingSwitching_BBFSumcheckMultParam κ L K
              (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (𝓑 := boolEmbedding L)
            (init := init) (impl := impl))
  dsimp [sumcheckFoldOracleVerifier] at h_lifted ⊢
  exact h_lifted

end Security
end SumcheckFold

end
end Binius.FRIBinius.CoreInteractionPhase
