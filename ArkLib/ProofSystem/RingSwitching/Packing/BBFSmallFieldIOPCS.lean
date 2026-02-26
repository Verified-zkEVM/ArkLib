/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.Binius.RingSwitching.General
import ArkLib.ProofSystem.Binius.BinaryBasefold.General
import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness
import ArkLib.OracleReduction.LiftContext.OracleReduction

/-!
# BBF Small-Field IOPCS: Ring-Switching + Binary Basefold Composition

This module instantiates the Ring-Switching protocol with Binary Basefold as the inner
large-field MLIOPCS, producing a **small-field IOPCS** (the standard, non-optimized composition).

## Architecture

The composition follows the protocol layering:
1. **Ring-switching** (outer): Reduces a small-field polynomial commitment to a large-field one
2. **Binary Basefold** (inner): Serves as the `MLIOPCS L ℓ'` for the large-field evaluation

This is the pedagogical/reference implementation that invokes Binary Basefold as a black box,
in contrast to `FRIBinius/CoreInteractionPhase.lean` which fuses the sumcheck-fold steps.

## Main Results

- `bbfMLIOPCS`: Binary Basefold instantiated as an `MLIOPCS L ℓ'`
- `bbf_fullOracleReduction_perfectCompleteness`: Perfect completeness of the composed protocol
- `bbf_fullOracleVerifier_rbrKnowledgeSoundness`: RBR knowledge soundness of the composed protocol

## References

- [DP24] Diamond, Benjamin E., and Jim Posen. "Polylogarithmic Proofs for Multilinears over Binary
  Towers." Cryptology ePrint Archive (2024).
-/

-- **Plan**: fully prove bbfMLIOPCS now. I think we can just use the security theorems of the those protocols, the thing is we have to use some security transfer lemma for case of relIn equality (between Ring-switching output relation & Binary Basefold input relation, I guess they are equivalent since at state i = 0, the input relation of Binary Basefold has no bad events sure it's purely consistency).

namespace Binius.RingSwitching.BBFSmallFieldIOPCS

open Binius.BinaryBasefold Binius.BinaryBasefold.FullBinaryBasefold
open Binius.RingSwitching Binius.RingSwitching.FullRingSwitching
open Polynomial MvPolynomial OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Module
open scoped NNReal

noncomputable section

/-! ## Part 1: Binary Basefold as MLIOPCS

We construct an `MLIOPCS L ℓ'` by wrapping Binary Basefold's full protocol.
The construction is parameterized by Binary Basefold parameters only (no Ring-switching params).
-/

section BinaryBasefoldMLIOPCS

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [SelectableType L]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ' 𝓡 ϑ : ℕ} (γ_repetitions : ℕ) [NeZero ℓ'] [NeZero 𝓡] [NeZero ϑ]
variable {h_ℓ_add_R_rate : ℓ' + 𝓡 < r}
variable {𝓑 : Fin 2 ↪ L}
variable [h_B01 : Fact (𝓑 0 = 0 ∧ 𝓑 1 = 1)]
variable [hdiv : Fact (ϑ ∣ ℓ')]

instance : OracleInterface Unit := OracleInterface.instDefault

/-! ### Type Adapters

| MLIOPCS                | BinaryBasefold                           |
|------------------------|------------------------------------------|
| `MLPEvalStatement L ℓ'`| `Statement (SumcheckBaseContext L ℓ') 0` |
| `WitMLP L ℓ'`          | `Witness 𝔽q β 0`                        |
| `OStmtIn`              | `OracleStatement 𝔽q β ϑ 0`             |

At round 0, `sumcheck_target = original_claim` (since `∑ x, eq(r,x) * t(x) = t(r) = s`). -/

/-- Convert an `MLPEvalStatement L ℓ'` produced at the end of ring-switching protocol
to a `Statement (SumcheckBaseContext L ℓ') 0` that is equal to the initial statement
of the large-field Binary Basefold protocol. -/
def reducedMLPEvalStatement_to_BBF_Statement (stmt : MLPEvalStatement (L := L) (ℓ := ℓ')) :
    Statement (L := L) (SumcheckBaseContext L ℓ') (0 : Fin (ℓ' + 1)) where
  sumcheck_target := stmt.original_claim
  challenges := Fin.elim0
  ctx := ⟨stmt.t_eval_point, stmt.original_claim⟩

/-- Convert `WitMLP L ℓ'` to `Witness 𝔽q β 0`. -/
def MLPEvalWitness_to_BBF_Witness (stmt : MLPEvalStatement (L := L) (ℓ := ℓ'))
    (wit : WitMLP (K := L) (ℓ := ℓ')) :
    Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') (0 : Fin (ℓ' + 1)) where
  t := wit.t
  H := projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := wit.t)
    (m := BBF_SumcheckMultiplierParam.multpoly ⟨stmt.t_eval_point, stmt.original_claim⟩)
    (i := (0 : Fin (ℓ' + 1))) (challenges := Fin.elim0)
  f := getMidCodewords 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) wit.t Fin.elim0

/-! ### Large-Field Invocation Wrapper

Ring-switching ends with a large-field MLP-evaluation statement/witness pair.
This wrapper maps that pair into Binary Basefold's round-0 input context
via `LiftContext`, reusing Binary Basefold's full reduction unchanged. -/

/-- Statement lens for the ring-switching large-field invocation into Binary Basefold. -/
def largeFieldInvocationStmtLens : OracleStatement.Lens
    (OuterStmtIn := MLPEvalStatement (L := L) (ℓ := ℓ'))
    (OuterStmtOut := Bool)
    (InnerStmtIn := Statement (L := L) (SumcheckBaseContext L ℓ') (0 : Fin (ℓ' + 1)))
    (InnerStmtOut := Bool)
    (OuterOStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (ℓ := ℓ') ϑ (0 : Fin (ℓ' + 1)))
    (OuterOStmtOut := fun _ : Empty => Unit)
    (InnerOStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (ℓ := ℓ') ϑ (0 : Fin (ℓ' + 1)))
    (InnerOStmtOut := fun _ : Empty => Unit) where
  toFunA := fun ⟨stmtIn, oStmtIn⟩ =>
    ⟨reducedMLPEvalStatement_to_BBF_Statement stmtIn, oStmtIn⟩
  toFunB := fun _ ⟨stmtOut, oStmtOut⟩ => ⟨stmtOut, oStmtOut⟩

/-- Context lens for the ring-switching large-field invocation into Binary Basefold. -/
def largeFieldInvocationCtxLens : OracleContext.Lens
    (OuterStmtIn := MLPEvalStatement (L := L) (ℓ := ℓ'))
    (OuterStmtOut := Bool)
    (InnerStmtIn := Statement (L := L) (SumcheckBaseContext L ℓ') (0 : Fin (ℓ' + 1)))
    (InnerStmtOut := Bool)
    (OuterOStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (ℓ := ℓ') ϑ (0 : Fin (ℓ' + 1)))
    (OuterOStmtOut := fun _ : Empty => Unit)
    (InnerOStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (ℓ := ℓ') ϑ (0 : Fin (ℓ' + 1)))
    (InnerOStmtOut := fun _ : Empty => Unit)
    (OuterWitIn := WitMLP (K := L) (ℓ := ℓ'))
    (OuterWitOut := Unit)
    (InnerWitIn := Witness (L := L) 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') (0 : Fin (ℓ' + 1)))
    (InnerWitOut := Unit) where
  stmt := largeFieldInvocationStmtLens 𝔽q β
  wit := {
    toFunA := fun ⟨⟨stmtIn, _oStmtIn⟩, witIn⟩ =>
      MLPEvalWitness_to_BBF_Witness 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtIn witIn
    toFunB := fun _ _ => ()
  }

/-- Binary Basefold oracle reduction lifted to the ring-switching large-field invocation context. -/
def largeFieldInvocationOracleReduction :
    OracleReduction (oSpec := []ₒ)
      (StmtIn := MLPEvalStatement (L := L) (ℓ := ℓ'))
      (OStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') ϑ
          (0 : Fin (ℓ' + 1)))
      (StmtOut := Bool)
      (OStmtOut := fun _ : Empty => Unit)
      (WitIn := WitMLP (K := L) (ℓ := ℓ'))
      (WitOut := Unit)
      (pSpec := fullPSpec 𝔽q β γ_repetitions (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  (FullBinaryBasefold.fullOracleReduction 𝔽q β γ_repetitions (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (ℓ := ℓ')).liftContext
    (lens := largeFieldInvocationCtxLens 𝔽q β)

omit [SelectableType L] in
/-- Uniqueness of the polynomial witness from first-oracle UDR-compatibility. -/
lemma firstOracleWitnessConsistency_unique
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') ϑ
      (0 : Fin (ℓ' + 1)) j)
    {t₁ t₂ : MultilinearPoly L ℓ'}
    (h₁ : firstOracleWitnessConsistencyProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ')
      t₁ (getFirstOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmt))
    (h₂ : firstOracleWitnessConsistencyProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ')
      t₂ (getFirstOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmt)) :
    t₁ = t₂ := by
  have h₁_some :
      extractMLP 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') 0
        (getFirstOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmt) = some t₁ :=
    (extractMLP_eq_some_iff_pair_UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (ℓ := ℓ') (f := getFirstOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmt)
      (tpoly := t₁)).2 h₁
  have h₂_some :
      extractMLP 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') 0
        (getFirstOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmt) = some t₂ :=
    (extractMLP_eq_some_iff_pair_UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (ℓ := ℓ') (f := getFirstOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmt)
      (tpoly := t₂)).2 h₂
  rw [h₁_some] at h₂_some
  simpa using h₂_some

lemma map_eval_sumToIter_rename_finSum_zero
    (p : MvPolynomial (Fin ℓ') L) :
    (MvPolynomial.map (MvPolynomial.eval (σ := Fin 0) Fin.elim0)
      ((sumToIter L (Fin ℓ') (Fin 0))
        (MvPolynomial.rename
          (f := ⇑(finSumFinEquiv (m := ℓ') (n := 0)).symm) p))) = p := by
  have h_sumToIter :
      (sumToIter L (Fin ℓ') (Fin 0))
          (MvPolynomial.rename
            (f := ⇑(finSumFinEquiv (m := ℓ') (n := 0)).symm) p) =
        MvPolynomial.map (MvPolynomial.C) p := by
    have h_ren_fun :
        (fun i : Fin ℓ' => (finSumFinEquiv (m := ℓ') (n := 0)).symm i) = Sum.inl := by
      funext i
      simpa using (finSumFinEquiv_symm_apply_castAdd (m := ℓ') (n := 0) i)
    have h_ren :
        MvPolynomial.rename
          (f := ⇑(finSumFinEquiv (m := ℓ') (n := 0)).symm) p =
        MvPolynomial.rename (f := Sum.inl) p := by
      simpa using congrArg (fun f => MvPolynomial.rename (f := f) p) h_ren_fun
    rw [h_ren]
    have h_comp := MvPolynomial.sumAlgEquiv_comp_rename_inl
      (R := L) (S₁ := Fin ℓ') (S₂ := Fin 0)
    have h_eval_comp := congrArg (fun f => f p) h_comp
    simpa using h_eval_comp
  rw [h_sumToIter]
  rw [MvPolynomial.map_map]
  have h_eval_comp_id :
      (MvPolynomial.eval (σ := Fin 0) Fin.elim0).comp MvPolynomial.C = RingHom.id L := by
    ext a
    simp
  rw [h_eval_comp_id]
  exact MvPolynomial.map_id p

lemma fixFirstVariablesOfMQP_zero_eq
    (H : MvPolynomial (Fin ℓ') L) :
    fixFirstVariablesOfMQP (L := L) (ℓ := ℓ') (v := (0 : Fin (ℓ' + 1))) H
      (challenges := Fin.elim0) = H := by
  simpa [fixFirstVariablesOfMQP] using
    (map_eval_sumToIter_rename_finSum_zero (L := L) (p := H))

lemma witnessStructuralInvariant_MLPEvalWitness_to_BBF_Witness
    (stmt : MLPEvalStatement (L := L) (ℓ := ℓ'))
    (wit : WitMLP (K := L) (ℓ := ℓ')) :
    Binius.BinaryBasefold.witnessStructuralInvariant 𝔽q β
      (mp := BBF_SumcheckMultiplierParam) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (reducedMLPEvalStatement_to_BBF_Statement (L := L) (ℓ' := ℓ') stmt)
      (MLPEvalWitness_to_BBF_Witness 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmt wit) := by
  simpa [Binius.BinaryBasefold.witnessStructuralInvariant, reducedMLPEvalStatement_to_BBF_Statement, MLPEvalWitness_to_BBF_Witness]

lemma sumcheckConsistency_MLPEvalWitness_to_BBF_Witness_of_eval
    (stmt : MLPEvalStatement (L := L) (ℓ := ℓ'))
    (wit : WitMLP (K := L) (ℓ := ℓ'))
    (h_eval : wit.t.val.eval stmt.t_eval_point = stmt.original_claim) :
    sumcheckConsistencyProp (𝓑 := 𝓑)
      (reducedMLPEvalStatement_to_BBF_Statement (L := L) (ℓ' := ℓ') stmt).sumcheck_target
      (MLPEvalWitness_to_BBF_Witness 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmt wit).H := by
  rw [sumcheckConsistencyProp]
  dsimp [reducedMLPEvalStatement_to_BBF_Statement, MLPEvalWitness_to_BBF_Witness, computeInitialSumcheckPoly,
    BBF_SumcheckMultiplierParam, BBF_eq_multiplier]
  rw [← h_eval]
  let castEmb : Fin 2 ↪ L := ⟨fun b => (b : L), by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp at h <;> simp [h]⟩
  have h_Beq : 𝓑 = castEmb := by
    ext b
    fin_cases b <;> simp [castEmb, h_B01.out.1, h_B01.out.2]
  subst h_Beq
  have h_H0 :
      projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := wit.t)
        (m := BBF_SumcheckMultiplierParam.multpoly ⟨stmt.t_eval_point, stmt.original_claim⟩)
        (i := (0 : Fin (ℓ' + 1))) (challenges := Fin.elim0) =
      computeInitialSumcheckPoly (ℓ := ℓ') wit.t
        (BBF_SumcheckMultiplierParam.multpoly ⟨stmt.t_eval_point, stmt.original_claim⟩) := by
    have h_fix0 :
        fixFirstVariablesOfMQP (L := L) (ℓ := ℓ')
          (v := (0 : Fin (ℓ' + 1)))
          (H := (computeInitialSumcheckPoly (ℓ := ℓ') wit.t
            (BBF_SumcheckMultiplierParam.multpoly
              ⟨stmt.t_eval_point, stmt.original_claim⟩)).val)
          (challenges := Fin.elim0) =
        (computeInitialSumcheckPoly (ℓ := ℓ') wit.t
          (BBF_SumcheckMultiplierParam.multpoly
            ⟨stmt.t_eval_point, stmt.original_claim⟩)).val :=
      fixFirstVariablesOfMQP_zero_eq (L := L)
        (H := (computeInitialSumcheckPoly (ℓ := ℓ') wit.t
          (BBF_SumcheckMultiplierParam.multpoly
            ⟨stmt.t_eval_point, stmt.original_claim⟩)).val)
    apply Subtype.ext
    simpa [projectToMidSumcheckPoly] using h_fix0

  -- ⊢ (MvPolynomial.eval stmt.t_eval_point) ↑wit.t =
  --   ∑ x ∈ Fintype.piFinset fun i ↦ Finset.map castEmb univ,
  --     (MvPolynomial.eval x) ↑(projectToMidSumcheckPoly ℓ' wit.t ⟨eqPolynomial stmt.t_eval_point, ⋯⟩ 0 Fin.elim0)

  sorry

/-! ### AbstractOStmtIn

Following the pattern from `FRIBinius/Prelude.lean` (`BinaryBasefoldAbstractOStmtIn`). -/

/-- The `AbstractOStmtIn` for Binary Basefold.

The oracle statement type is `OracleStatement 𝔽q β ϑ 0`, representing initial committed
codewords. The compatibility relations tie the polynomial `t'` to the oracle commitments
via first-oracle witness consistency + oracle folding consistency (relaxed),
and exact equality (strict). -/
def bbfAbstractOStmtIn : AbstractOStmtIn L ℓ' where
  ιₛᵢ := Fin (toOutCodewordsCount ℓ' ϑ (0 : Fin (ℓ' + 1)))
  OStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') ϑ
      (0 : Fin (ℓ' + 1))
  Oₛᵢ := instOracleStatementBinaryBasefold 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ) (i := (0 : Fin (ℓ' + 1)))
  -- Relaxed input compatibility at round 0 (RBR-KS style).
  initialCompatibility := fun ⟨t', oStmt⟩ =>
    firstOracleWitnessConsistencyProp 𝔽q β (ℓ := ℓ')
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t'
      (getFirstOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmt)
  -- Strict compatibility: exact oracle folding consistency (implies UDR-closeness).
  strictInitialCompatibility := fun ⟨t', oStmt⟩ =>
    strictOracleFoldingConsistencyProp 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (t := t') (i := (0 : Fin (ℓ' + 1)))
      (challenges := Fin.elim0) (oStmt := oStmt)
  -- Strict (exact equality) implies relaxed (UDR-closeness).
  strictInitialCompatibility_implies_initialCompatibility := by
    intro oStmt t h_compat_strict
    -- strictOracleFoldingConsistencyProp implies f₀ = getFirstOracle
    have h_eq := Binius.BinaryBasefold.QueryPhase.polyToOracleFunc_eq_getFirstOracle
      𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (t := t) (i := (0 : Fin (ℓ' + 1)))
      (challenges := Fin.elim0) (oStmt := oStmt) h_compat_strict
    -- Exact equality implies UDR-closeness (hamming distance 0)
    dsimp only [firstOracleWitnessConsistencyProp]
    rw [← h_eq]
    dsimp only [pair_UDRClose]
    have h_dist_pos :
        0 < BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := (0 : Fin r)) := by
      rw [BBF_CodeDistance_eq 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := (0 : Fin r)) (h_i := by simp)]
      omega
    simp only [hammingDist_self, mul_zero, h_dist_pos]
  -- Unique polynomial determination from oracle (via UDR-closeness)
  initialCompatibility_unique := fun oStmt t₁ t₂ h₁ h₂ => by
    exact firstOracleWitnessConsistency_unique 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ) oStmt h₁ h₂

instance largeFieldInvocationCtxLens_complete :
  (largeFieldInvocationCtxLens 𝔽q β).toContext.IsComplete
    (outerRelIn := (bbfAbstractOStmtIn 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)).toStrictRelInput)
    (innerRelIn := strictRoundRelation (mp := BBF_SumcheckMultiplierParam) 𝔽q β
      (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (0 : Fin (ℓ' + 1)))
    (outerRelOut := acceptRejectOracleRel)
    (innerRelOut := acceptRejectOracleRel)
    (compat := Reduction.compatContext (oSpec := []ₒ)
      (pSpec := fullPSpec 𝔽q β γ_repetitions (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (largeFieldInvocationCtxLens 𝔽q β).toContext
      ((FullBinaryBasefold.fullOracleReduction 𝔽q β γ_repetitions (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (ℓ := ℓ')).toReduction)) where
  proj_complete := fun stmtIn witIn hRelIn => by
    rcases stmtIn with ⟨stmtIn, oStmtIn⟩
    rcases hRelIn with ⟨h_eval, h_compat⟩
    refine ⟨?_, ?_⟩
    · exact sumcheckConsistency_MLPEvalWitness_to_BBF_Witness_of_eval 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) stmtIn witIn h_eval
    · refine ⟨?_, ?_⟩
      · exact witnessStructuralInvariant_MLPEvalWitness_to_BBF_Witness 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtIn witIn
      · simpa [reducedMLPEvalStatement_to_BBF_Statement, strictOracleFoldingConsistencyProp] using
          h_compat
  lift_complete := fun outerStmtIn outerWitIn innerStmtOut innerWitOut hCompat hRelIn hRelOut => by
    cases innerWitOut
    simpa [largeFieldInvocationCtxLens, largeFieldInvocationStmtLens] using hRelOut

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

theorem largeFieldInvocationOracleReduction_perfectCompleteness (hInit : init.neverFails) :
  OracleReduction.perfectCompleteness
    (oracleReduction := largeFieldInvocationOracleReduction 𝔽q β γ_repetitions (𝓑 := 𝓑))
    (relIn := (bbfAbstractOStmtIn 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)).toStrictRelInput)
    (relOut := acceptRejectOracleRel)
    (init := init)
    (impl := impl) := by
  let innerReduction := FullBinaryBasefold.fullOracleReduction 𝔽q β γ_repetitions
    (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (ℓ := ℓ')
  letI : (largeFieldInvocationCtxLens 𝔽q β).toContext.IsComplete
      (outerRelIn := (bbfAbstractOStmtIn 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)).toStrictRelInput)
      (innerRelIn := strictRoundRelation (mp := BBF_SumcheckMultiplierParam) 𝔽q β
        (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (0 : Fin (ℓ' + 1)))
      (outerRelOut := acceptRejectOracleRel)
      (innerRelOut := acceptRejectOracleRel)
      (compat := Reduction.compatContext (oSpec := []ₒ)
        (pSpec := fullPSpec 𝔽q β γ_repetitions (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
        (largeFieldInvocationCtxLens 𝔽q β).toContext
        innerReduction.toReduction) := by
    infer_instance
  have h_inner := FullBinaryBasefold.fullOracleReduction_perfectCompleteness
    𝔽q β γ_repetitions (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
    (init := init) (impl := impl) hInit
  simpa [largeFieldInvocationOracleReduction, innerReduction] using
    (OracleReduction.liftContext_perfectCompleteness
      (R := innerReduction)
      (lens := largeFieldInvocationCtxLens 𝔽q β)
      (outerRelIn := (bbfAbstractOStmtIn 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)).toStrictRelInput)
      (innerRelIn := strictRoundRelation (mp := BBF_SumcheckMultiplierParam) 𝔽q β
        (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (0 : Fin (ℓ' + 1)))
      (outerRelOut := acceptRejectOracleRel)
      (innerRelOut := acceptRejectOracleRel)
      (init := init)
      (impl := impl)
      h_inner)

lemma MLPEvalRelation_of_round0_local_and_structural
    (stmt : MLPEvalStatement (L := L) (ℓ := ℓ'))
    (wit : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ')
      (0 : Fin (ℓ' + 1)))
    (h_local : sumcheckConsistencyProp (𝓑 := 𝓑)
      (reducedMLPEvalStatement_to_BBF_Statement (L := L) (ℓ' := ℓ') stmt).sumcheck_target wit.H)
    (h_struct : Binius.BinaryBasefold.witnessStructuralInvariant 𝔽q β
      (mp := BBF_SumcheckMultiplierParam) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (reducedMLPEvalStatement_to_BBF_Statement (L := L) (ℓ' := ℓ') stmt) wit) :
    wit.t.val.eval stmt.t_eval_point = stmt.original_claim := by
  let stmt_eval : MLPEvalStatement (L := L) (ℓ := ℓ') := {
    t_eval_point := stmt.t_eval_point
    original_claim := wit.t.val.eval stmt.t_eval_point
  }
  let wit_eval : WitMLP (K := L) (ℓ := ℓ') := { t := wit.t }
  have h_eval_stmt_eval : wit_eval.t.val.eval stmt_eval.t_eval_point = stmt_eval.original_claim := by
    rfl
  have h_local_eval :
      sumcheckConsistencyProp (𝓑 := 𝓑)
        (reducedMLPEvalStatement_to_BBF_Statement (L := L) (ℓ' := ℓ') stmt_eval).sumcheck_target
        (MLPEvalWitness_to_BBF_Witness 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmt_eval wit_eval).H :=
    sumcheckConsistency_MLPEvalWitness_to_BBF_Witness_of_eval 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) stmt_eval wit_eval h_eval_stmt_eval
  have h_H_eq :
      wit.H = (MLPEvalWitness_to_BBF_Witness 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmt_eval wit_eval).H := by
    calc
      wit.H = projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := wit.t)
          (m := BBF_SumcheckMultiplierParam.multpoly ⟨stmt.t_eval_point, stmt.original_claim⟩)
          (i := (0 : Fin (ℓ' + 1))) (challenges := Fin.elim0) := by
            simpa [Binius.BinaryBasefold.witnessStructuralInvariant,
              reducedMLPEvalStatement_to_BBF_Statement] using h_struct.1
      _ = projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := wit.t)
          (m := BBF_SumcheckMultiplierParam.multpoly ⟨stmt_eval.t_eval_point,
            stmt_eval.original_claim⟩)
          (i := (0 : Fin (ℓ' + 1))) (challenges := Fin.elim0) := by
            simp [stmt_eval, BBF_SumcheckMultiplierParam, BBF_eq_multiplier]
      _ = (MLPEvalWitness_to_BBF_Witness 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmt_eval wit_eval).H := by
            simp [MLPEvalWitness_to_BBF_Witness, wit_eval]
  have h_sum_eq_claim :
      stmt.original_claim = ∑ x ∈ (univ.map 𝓑) ^ᶠ (ℓ'),
        wit.H.val.eval x := by
    simpa [sumcheckConsistencyProp, reducedMLPEvalStatement_to_BBF_Statement] using h_local
  have h_sum_eq_eval :
      wit.t.val.eval stmt.t_eval_point = ∑ x ∈ (univ.map 𝓑) ^ᶠ (ℓ'),
        wit.H.val.eval x := by
    have h_sum_eq_eval' :
        wit.t.val.eval stmt.t_eval_point = ∑ x ∈ (univ.map 𝓑) ^ᶠ (ℓ'),
          (MLPEvalWitness_to_BBF_Witness 𝔽q β
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmt_eval wit_eval).H.val.eval x := by
      simpa [sumcheckConsistencyProp, reducedMLPEvalStatement_to_BBF_Statement, stmt_eval] using
        h_local_eval
    simpa [h_H_eq] using h_sum_eq_eval'
  calc
    wit.t.val.eval stmt.t_eval_point = ∑ x ∈ (univ.map 𝓑) ^ᶠ (ℓ'), wit.H.val.eval x := h_sum_eq_eval
    _ = stmt.original_claim := h_sum_eq_claim.symm

/-- Extractor lens for lifting Binary Basefold RBR-KS to the large-field invocation wrapper. -/
def largeFieldInvocationExtractorLens : Extractor.Lens
    (OuterStmtIn := MLPEvalStatement (L := L) (ℓ := ℓ') ×
      (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') ϑ
        (0 : Fin (ℓ' + 1)) j))
    (OuterStmtOut := Bool × (∀ j : Empty, Unit))
    (InnerStmtIn := Statement (L := L) (SumcheckBaseContext L ℓ') (0 : Fin (ℓ' + 1)) ×
      (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') ϑ
        (0 : Fin (ℓ' + 1)) j))
    (InnerStmtOut := Bool × (∀ j : Empty, Unit))
    (OuterWitIn := WitMLP (K := L) (ℓ := ℓ'))
    (OuterWitOut := Unit)
    (InnerWitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ')
      (0 : Fin (ℓ' + 1)))
    (InnerWitOut := Unit) where
  stmt := largeFieldInvocationStmtLens 𝔽q β
  wit := {
    toFunA := fun _ => ()
    toFunB := fun ⟨⟨_stmtIn, _oStmtIn⟩, _outerWitOut⟩ innerWitIn => ⟨innerWitIn.t⟩
  }

instance largeFieldInvocationExtractorLens_rbr_knowledge_soundness
    {compatStmt :
      (MLPEvalStatement (L := L) (ℓ := ℓ') ×
        (∀ i, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') ϑ
          (0 : Fin (ℓ' + 1)) i)) →
      (Bool × (∀ i : Empty, Unit)) → Prop} :
    Extractor.Lens.IsKnowledgeSound
      (OuterStmtIn := MLPEvalStatement (L := L) (ℓ := ℓ') ×
        (∀ i, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') ϑ
          (0 : Fin (ℓ' + 1)) i))
      (OuterStmtOut := Bool × (∀ i : Empty, Unit))
      (InnerStmtIn := Statement (L := L) (SumcheckBaseContext L ℓ') (0 : Fin (ℓ' + 1)) ×
        (∀ i, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') ϑ
          (0 : Fin (ℓ' + 1)) i))
      (InnerStmtOut := Bool × (∀ i : Empty, Unit))
      (OuterWitIn := WitMLP (K := L) (ℓ := ℓ'))
      (OuterWitOut := Unit)
      (InnerWitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (ℓ := ℓ') (0 : Fin (ℓ' + 1)))
      (InnerWitOut := Unit)
      (outerRelIn := (bbfAbstractOStmtIn 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)).toRelInput)
      (innerRelIn := roundRelation (mp := BBF_SumcheckMultiplierParam) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (0 : Fin (ℓ' + 1)))
      (outerRelOut := acceptRejectOracleRel)
      (innerRelOut := acceptRejectOracleRel)
      (compatStmt := compatStmt)
      (compatWit := fun _ _ => True)
      (lens := largeFieldInvocationExtractorLens 𝔽q β) where
  proj_knowledgeSound := by
    intro outerStmtIn innerStmtOut outerWitOut _ hOuter
    simpa [largeFieldInvocationExtractorLens, largeFieldInvocationStmtLens] using hOuter
  lift_knowledgeSound := by
    intro outerStmtIn outerWitOut innerWitIn _ hInner
    rcases outerStmtIn with ⟨stmtIn, oStmtIn⟩
    have hInner' :
        roundRelationProp (mp := BBF_SumcheckMultiplierParam) 𝔽q β
          (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
          (0 : Fin (ℓ' + 1))
          ((reducedMLPEvalStatement_to_BBF_Statement (L := L) (ℓ' := ℓ') stmtIn,
            oStmtIn), innerWitIn) := by
      simpa [roundRelation, Set.mem_setOf_eq] using hInner
    unfold roundRelationProp Binius.BinaryBasefold.masterKStateProp at hInner'
    have h_no_bad :
        ¬ incrementalBadEventExistsProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (ϑ := ϑ) (stmtIdx := (0 : Fin (ℓ' + 1)))
          (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (0 : Fin (ℓ' + 1)))
          (oStmt := oStmtIn)
          (challenges := (reducedMLPEvalStatement_to_BBF_Statement (L := L) (ℓ' := ℓ') stmtIn).challenges) := by
      intro h_bad
      rcases h_bad with ⟨j, hj⟩
      have hj0 : j = 0 := by
        apply Fin.eq_of_val_eq
        have hjlt : j.val < 1 := by
          simpa [toOutCodewordsCountOf0] using j.isLt
        exact Nat.lt_one_iff.mp hjlt
      subst hj0
      dsimp [oraclePositionToDomainIndex] at hj
      simp only [incrementalFoldingBadEvent, Nat.zero_mod, zero_mul, tsub_self, zero_le,
        inf_of_le_right, ↓reduceDIte] at hj
    rcases hInner' with h_bad | h_good
    · exact (h_no_bad h_bad).elim
    · have h_local := h_good.1
      have h_struct := h_good.2.1
      have h_first := h_good.2.2.1
      refine ⟨?_, ?_⟩
      · exact MLPEvalRelation_of_round0_local_and_structural 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
          stmtIn innerWitIn h_local h_struct
      · simpa [bbfAbstractOStmtIn] using h_first

/-! ### MLIOPCS Instance -/

/-- Binary Basefold as an `MLIOPCS L ℓ'`.

This wraps the full Binary Basefold protocol (core interaction + query phase)
as a multilinear polynomial commitment scheme over the large field `L`. -/
def bbfMLIOPCS : MLIOPCS L ℓ' where
  toAbstractOStmtIn := bbfAbstractOStmtIn 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)
  numRounds := _  -- inferred from fullPSpec
  pSpec := fullPSpec 𝔽q β γ_repetitions (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  Oₘ := inferInstance
  O_challenges := inferInstance
  oracleReduction := largeFieldInvocationOracleReduction 𝔽q β γ_repetitions (𝓑 := 𝓑)
  perfectCompleteness := by
    intro σ init impl hInit
    exact largeFieldInvocationOracleReduction_perfectCompleteness 𝔽q β γ_repetitions (𝓑 := 𝓑)
      (init := init) (impl := impl) hInit
  strictPerfectCompleteness := by
    intro σ init impl hInit
    exact largeFieldInvocationOracleReduction_perfectCompleteness 𝔽q β γ_repetitions (𝓑 := 𝓑)
      (init := init) (impl := impl) hInit
  rbrKnowledgeError :=
    fullRbrKnowledgeError 𝔽q β γ_repetitions (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  rbrKnowledgeSoundness := by
    intro σ init impl
    have h_bbf := FullBinaryBasefold.fullOracleVerifier_rbrKnowledgeSoundness
      𝔽q β γ_repetitions (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (init := init) (impl := impl)
    letI :
        Inhabited (Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ')
          (0 : Fin (ℓ' + 1))) := ⟨{
        t := 0
        H := 0
        f := fun _ => 0
      }⟩
    letI : ∀ i : Empty, Inhabited ((fun _ : Empty => Unit) i) := by
      intro i
      exact (i.elim)
    have h_lifted := OracleVerifier.liftContext_rbr_knowledgeSoundness
        (V := FullBinaryBasefold.fullOracleVerifier 𝔽q β γ_repetitions (ϑ := ϑ)
          (𝓑 := 𝓑) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
        (stmtLens := largeFieldInvocationStmtLens 𝔽q β)
        (witLens := (largeFieldInvocationExtractorLens 𝔽q β).wit)
        (lensKS := largeFieldInvocationExtractorLens_rbr_knowledge_soundness
          (𝔽q := 𝔽q) (β := β)
          (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
          (compatStmt := (FullBinaryBasefold.fullOracleVerifier 𝔽q β γ_repetitions (ϑ := ϑ)
            (𝓑 := 𝓑) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).toVerifier.compatStatement
            (largeFieldInvocationStmtLens 𝔽q β)))
        (h := by simpa using h_bbf)
    simpa [largeFieldInvocationOracleReduction] using h_lifted

end BinaryBasefoldMLIOPCS

/-! ## Part 2: End-to-End Composition

Compose Ring-switching with the Binary Basefold MLIOPCS using the existing
infrastructure in `RingSwitching/General.lean`.
-/

section Composition

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [SelectableType L]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ' 𝓡 ϑ : ℕ} (γ_repetitions : ℕ) [NeZero ℓ'] [NeZero 𝓡] [NeZero ϑ]
variable {h_ℓ_add_R_rate : ℓ' + 𝓡 < r}
variable {𝓑 : Fin 2 ↪ L}
variable [h_B01 : Fact (𝓑 0 = 0 ∧ 𝓑 1 = 1)]
variable [hdiv : Fact (ϑ ∣ ℓ')]

-- Ring-switching variables
variable (κ : ℕ) [NeZero κ]
variable (K : Type) [Field K] [Fintype K] [DecidableEq K]
variable [Algebra K L]
variable (β_rs : Basis (Fin κ → Fin 2) K L)
variable (ℓ : ℕ) [NeZero ℓ]
variable (h_l : ℓ = ℓ' + κ)

variable {σ : Type} (init : ProbComp σ) {impl : QueryImpl []ₒ (StateT σ ProbComp)}

/-- Perfect completeness of the composed protocol:
Ring-switching + Binary Basefold as MLIOPCS.

This is a direct instantiation of `fullOracleReduction_perfectCompleteness` from
`RingSwitching/General.lean` with the Binary Basefold MLIOPCS. -/
theorem bbf_fullOracleReduction_perfectCompleteness (hInit : init.neverFails) :
    OracleReduction.perfectCompleteness
      (oracleReduction := FullRingSwitching.fullOracleReduction κ L K β_rs ℓ ℓ' h_l
        (𝓑 := 𝓑)
        (bbfMLIOPCS 𝔽q β γ_repetitions
          (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)))
      (relIn := BatchingPhase.strictBatchingInputRelation
        κ L K β_rs ℓ ℓ' h_l
        (bbfMLIOPCS 𝔽q β γ_repetitions
          (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)).toAbstractOStmtIn)
      (relOut := acceptRejectOracleRel)
      (init := init) (impl := impl) :=
  FullRingSwitching.fullOracleReduction_perfectCompleteness κ L K β_rs ℓ ℓ' h_l
    (𝓑 := 𝓑)
    (bbfMLIOPCS 𝔽q β γ_repetitions
      (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑))
    init hInit

/-- RBR knowledge soundness of the composed protocol:
Ring-switching + Binary Basefold as MLIOPCS.

This is a direct instantiation of `fullOracleVerifier_rbrKnowledgeSoundness` from
`RingSwitching/General.lean` with the Binary Basefold MLIOPCS. -/
theorem bbf_fullOracleVerifier_rbrKnowledgeSoundness :
    OracleVerifier.rbrKnowledgeSoundness
      (verifier := FullRingSwitching.fullOracleVerifier κ L K β_rs ℓ ℓ' (𝓑 := 𝓑) h_l
        (bbfMLIOPCS 𝔽q β γ_repetitions
          (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)))
      (init := init) (impl := impl)
      (relIn := BatchingPhase.batchingInputRelation
        κ L K β_rs ℓ ℓ' h_l
        (bbfMLIOPCS 𝔽q β γ_repetitions
          (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)).toAbstractOStmtIn)
      (relOut := acceptRejectOracleRel)
      (rbrKnowledgeError := fun i => FullRingSwitching.fullRbrKnowledgeError κ L K ℓ'
        (bbfMLIOPCS 𝔽q β γ_repetitions
          (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)) i) :=
  FullRingSwitching.fullOracleVerifier_rbrKnowledgeSoundness κ L K β_rs ℓ ℓ' h_l
    (𝓑 := 𝓑)
    (bbfMLIOPCS 𝔽q β γ_repetitions
      (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑))
    init

end Composition

end
end Binius.RingSwitching.BBFSmallFieldIOPCS
