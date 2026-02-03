/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.Binius.RingSwitching.General
import ArkLib.ProofSystem.Binius.BinaryBasefold.General
import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness

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

/-! ### Type Adapters

| MLIOPCS                | BinaryBasefold                           |
|------------------------|------------------------------------------|
| `InitialStatement L ℓ'`| `Statement (SumcheckBaseContext L ℓ') 0` |
| `WitMLP L ℓ'`          | `Witness 𝔽q β 0`                        |
| `OStmtIn`              | `OracleStatement 𝔽q β ϑ 0`             |

At round 0, `sumcheck_target = original_claim` (since `∑ x, eq(r,x) * t(x) = t(r) = s`). -/

/-- Convert an `InitialStatement L ℓ'` to a `Statement (SumcheckBaseContext L ℓ') 0`. -/
def initialToStatement0 (stmt : InitialStatement (L := L) (ℓ := ℓ')) :
    Statement (L := L) (SumcheckBaseContext L ℓ') (0 : Fin (ℓ' + 1)) where
  sumcheck_target := stmt.original_claim
  challenges := Fin.elim0
  ctx := ⟨stmt.t_eval_point, stmt.original_claim⟩

/-- Convert `WitMLP L ℓ'` to `Witness 𝔽q β 0`. -/
def witMLPToWitness0 (stmt : InitialStatement (L := L) (ℓ := ℓ'))
    (wit : WitMLP (K := L) (ℓ := ℓ')) :
    Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') (0 : Fin (ℓ' + 1)) where
  t := wit.t
  H := projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := wit.t)
    (m := BBF_SumcheckMultiplierParam.multpoly ⟨stmt.t_eval_point, stmt.original_claim⟩)
    (i := (0 : Fin (ℓ' + 1))) (challenges := Fin.elim0)
  f := getMidCodewords 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) wit.t Fin.elim0

/-! ### Adapted OracleReduction

Reuse BinaryBasefold's prover states, `sendMessage`, `receiveChallenge` — only the `input`
function and verifier's `verify` convert types. -/

/-- The adapted `OracleProver` for the MLIOPCS. -/
def bbfOracleProver :
    OracleProver (oSpec := []ₒ)
      (StmtIn := InitialStatement (L := L) (ℓ := ℓ'))
      (OStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') ϑ
          (0 : Fin (ℓ' + 1)))
      (WitIn := WitMLP (K := L) (ℓ := ℓ'))
      (StmtOut := Bool)
      (OStmtOut := fun _ : Empty => Unit)
      (WitOut := Unit)
      (pSpec := fullPSpec 𝔽q β γ_repetitions (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  let bbfP := (fullOracleReduction 𝔽q β γ_repetitions (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (ℓ := ℓ')).prover
  { PrvState := bbfP.PrvState
    input := fun ⟨⟨stmt, oStmt⟩, wit⟩ =>
      bbfP.input ⟨⟨initialToStatement0 stmt, oStmt⟩,
        witMLPToWitness0 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmt wit⟩
    sendMessage := bbfP.sendMessage
    receiveChallenge := bbfP.receiveChallenge
    output := bbfP.output }

/-- The adapted `OracleVerifier` for the MLIOPCS. -/
def bbfOracleVerifier :
    OracleVerifier (oSpec := []ₒ)
      (StmtIn := InitialStatement (L := L) (ℓ := ℓ'))
      (OStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') ϑ
          (0 : Fin (ℓ' + 1)))
      (StmtOut := Bool)
      (OStmtOut := fun _ : Empty => Unit)
      (pSpec := fullPSpec 𝔽q β γ_repetitions (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  let bbfV := (fullOracleReduction 𝔽q β γ_repetitions (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (ℓ := ℓ')).verifier
  { verify := fun stmt challenges =>
      bbfV.verify (initialToStatement0 stmt) challenges
    embed := bbfV.embed
    hEq := bbfV.hEq }

/-- The full Binary Basefold protocol, adapted as an `OracleReduction` with MLIOPCS-compatible
types. -/
def bbfAdaptedOracleReduction :
    OracleReduction (oSpec := []ₒ)
      (StmtIn := InitialStatement (L := L) (ℓ := ℓ'))
      (OStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') ϑ
          (0 : Fin (ℓ' + 1)))
      (StmtOut := Bool)
      (OStmtOut := fun _ : Empty => Unit)
      (WitIn := WitMLP (K := L) (ℓ := ℓ'))
      (WitOut := Unit)
      (pSpec := fullPSpec 𝔽q β γ_repetitions (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) where
  prover := bbfOracleProver 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
  verifier := bbfOracleVerifier 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)

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

lemma witnessStructuralInvariant_witMLPToWitness0
    (stmt : InitialStatement (L := L) (ℓ := ℓ'))
    (wit : WitMLP (K := L) (ℓ := ℓ')) :
    Binius.BinaryBasefold.witnessStructuralInvariant 𝔽q β
      (mp := BBF_SumcheckMultiplierParam) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (initialToStatement0 (L := L) (ℓ' := ℓ') stmt)
      (witMLPToWitness0 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmt wit) := by
  simpa [Binius.BinaryBasefold.witnessStructuralInvariant, initialToStatement0, witMLPToWitness0]

lemma sumcheckConsistency_witMLPToWitness0_of_eval
    (stmt : InitialStatement (L := L) (ℓ := ℓ'))
    (wit : WitMLP (K := L) (ℓ := ℓ'))
    (h_eval : wit.t.val.eval stmt.t_eval_point = stmt.original_claim) :
    sumcheckConsistencyProp (𝓑 := 𝓑)
      (initialToStatement0 (L := L) (ℓ' := ℓ') stmt).sumcheck_target
      (witMLPToWitness0 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmt wit).H := by
  rw [sumcheckConsistencyProp]
  dsimp [initialToStatement0, witMLPToWitness0, computeInitialSumcheckPoly,
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
  sorry
  -- simpa [computeInitialSumcheckPoly, BBF_SumcheckMultiplierParam, BBF_eq_multiplier,
  --   multilinearWeight, castEmb, h_H0] using
  --     (multilinear_eval_eq_sum_bool_hypercube (L := L) (ℓ := ℓ')
  --       (challenges := stmt.t_eval_point) (t := wit.t))

/-! ### AbstractOStmtIn

Following the pattern from `FRIBinius/Prelude.lean` (`BinaryBasefoldAbstractOStmtIn`). -/

/-- The `AbstractOStmtIn` for Binary Basefold.

The oracle statement type is `OracleStatement 𝔽q β ϑ 0`, representing initial committed
codewords. The compatibility relations tie the polynomial `t'` to the oracle commitments
via UDR-closeness (relaxed) and exact equality (strict). -/
def bbfAbstractOStmtIn : AbstractOStmtIn L ℓ' where
  ιₛᵢ := Fin (toOutCodewordsCount ℓ' ϑ (0 : Fin (ℓ' + 1)))
  OStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') ϑ
      (0 : Fin (ℓ' + 1))
  Oₛᵢ := instOracleStatementBinaryBasefold 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ) (i := (0 : Fin (ℓ' + 1)))
  -- Input compatibility at round 0: exact oracle folding consistency.
  initialCompatibility := fun ⟨t', oStmt⟩ =>
    strictOracleFoldingConsistencyProp 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (t := t') (i := (0 : Fin (ℓ' + 1)))
      (challenges := Fin.elim0) (oStmt := oStmt)
  -- Strict compatibility is identical in this instantiation.
  strictInitialCompatibility := fun ⟨t', oStmt⟩ =>
    strictOracleFoldingConsistencyProp 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (t := t') (i := (0 : Fin (ℓ' + 1)))
      (challenges := Fin.elim0) (oStmt := oStmt)
  -- Strict implies relaxed by reflexivity.
  strictInitialCompatibility_implies_initialCompatibility := by
    intro oStmt t h_compat_strict
    exact h_compat_strict
  -- Unique polynomial determination from oracle
  initialCompatibility_unique := fun oStmt t₁ t₂ h₁ h₂ => by
    have h₁_eq := Binius.BinaryBasefold.QueryPhase.polyToOracleFunc_eq_getFirstOracle 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (t := t₁) (i := (0 : Fin (ℓ' + 1)))
      (challenges := Fin.elim0) (oStmt := oStmt) h₁
    have h₂_eq := Binius.BinaryBasefold.QueryPhase.polyToOracleFunc_eq_getFirstOracle 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (t := t₂) (i := (0 : Fin (ℓ' + 1)))
      (challenges := Fin.elim0) (oStmt := oStmt) h₂
    have h_dist_pos :
        0 < BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := (0 : Fin r)) := by
      rw [BBF_CodeDistance_eq 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := (0 : Fin r)) (h_i := by simp)]
      omega
    have h₁_close :
        firstOracleWitnessConsistencyProp 𝔽q β (ℓ := ℓ')
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t₁
          (getFirstOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmt) := by
      dsimp only [firstOracleWitnessConsistencyProp]
      rw [← h₁_eq]
      dsimp only [pair_UDRClose]
      simp only [hammingDist_self, mul_zero, h_dist_pos]
    have h₂_close :
        firstOracleWitnessConsistencyProp 𝔽q β (ℓ := ℓ')
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t₂
          (getFirstOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmt) := by
      dsimp only [firstOracleWitnessConsistencyProp]
      rw [← h₂_eq]
      dsimp only [pair_UDRClose]
      simp only [hammingDist_self, mul_zero, h_dist_pos]
    exact firstOracleWitnessConsistency_unique 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ) oStmt h₁_close h₂_close

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
  oracleReduction := bbfAdaptedOracleReduction 𝔽q β γ_repetitions
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
  perfectCompleteness := by
    intro σ init impl hInit
    -- The adapted reduction wraps BinaryBasefold's fullOracleReduction with type adapters.
    -- We unfold to `Reduction.completeness` and show each input mapping preserves the relation.
    have h_bbf := FullBinaryBasefold.fullOracleReduction_perfectCompleteness
      𝔽q β γ_repetitions (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (init := init) (impl := impl) hInit
    -- Unfold both sides to Reduction.completeness level
    simp only [OracleReduction.perfectCompleteness, Reduction.perfectCompleteness] at h_bbf ⊢
    intro stmtIn witIn h_relIn
    -- Convert the adapted computation to BinaryBasefold's computation
    -- The adapted reduction's toReduction.run is definitionally equal to
    -- BinaryBasefold's toReduction.run with type-adapted inputs
    apply h_bbf (initialToStatement0 stmtIn.1, stmtIn.2)
      (witMLPToWitness0 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtIn.1 witIn)
    -- Now show the converted input is in strictRoundRelation 0
    rcases h_relIn with ⟨h_eval, h_compat⟩
    refine ⟨?_, ?_⟩
    · exact sumcheckConsistency_witMLPToWitness0_of_eval 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) stmtIn.1 witIn h_eval
    · refine ⟨?_, ?_⟩
      · exact witnessStructuralInvariant_witMLPToWitness0 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtIn.1 witIn
      · simpa [initialToStatement0, strictOracleFoldingConsistencyProp] using h_compat
  strictPerfectCompleteness := by
    intro σ init impl hInit
    have h_bbf := FullBinaryBasefold.fullOracleReduction_perfectCompleteness
      𝔽q β γ_repetitions (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (init := init) (impl := impl) hInit
    simp only [OracleReduction.perfectCompleteness, Reduction.perfectCompleteness] at h_bbf ⊢
    intro stmtIn witIn h_relIn
    apply h_bbf (initialToStatement0 stmtIn.1, stmtIn.2)
      (witMLPToWitness0 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtIn.1 witIn)
    rcases h_relIn with ⟨h_eval, h_compat⟩
    refine ⟨?_, ?_⟩
    · exact sumcheckConsistency_witMLPToWitness0_of_eval 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) stmtIn.1 witIn h_eval
    · refine ⟨?_, ?_⟩
      · exact witnessStructuralInvariant_witMLPToWitness0 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtIn.1 witIn
      · simpa [initialToStatement0, strictOracleFoldingConsistencyProp] using h_compat
  rbrKnowledgeError :=
    fullRbrKnowledgeError 𝔽q β γ_repetitions (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  rbrKnowledgeSoundness := by
    intro σ init impl
    have h_bbf := FullBinaryBasefold.fullOracleVerifier_rbrKnowledgeSoundness
      𝔽q β γ_repetitions (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (init := init) (impl := impl)
    -- simpa only [OracleVerifier.rbrKnowledgeSoundness, bbfAdaptedOracleReduction, bbfOracleVerifier,
    --   roundRelation, roundRelationProp, masterKStateProp, oracleWitnessConsistency,
    --   witnessStructuralInvariant, initialToStatement0, witMLPToWitness0,
    --   AbstractOStmtIn.toRelInput, MLPEvalRelation, Set.mem_setOf_eq]
    --   using h_bbf
    sorry

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
        (bbfMLIOPCS 𝔽q β γ_repetitions (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)))
      (relIn := BatchingPhase.strictBatchingInputRelation
        κ L K β_rs ℓ ℓ' h_l
        (bbfMLIOPCS 𝔽q β γ_repetitions
          (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (𝓑 := 𝓑)).toAbstractOStmtIn)
      (relOut := acceptRejectOracleRel)
      (init := init) (impl := impl) :=
  FullRingSwitching.fullOracleReduction_perfectCompleteness κ L K β_rs ℓ ℓ' h_l
    (𝓑 := 𝓑)
    (bbfMLIOPCS 𝔽q β γ_repetitions (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑))
    init hInit

/-- RBR knowledge soundness of the composed protocol:
Ring-switching + Binary Basefold as MLIOPCS.

This is a direct instantiation of `fullOracleVerifier_rbrKnowledgeSoundness` from
`RingSwitching/General.lean` with the Binary Basefold MLIOPCS. -/
theorem bbf_fullOracleVerifier_rbrKnowledgeSoundness :
    OracleVerifier.rbrKnowledgeSoundness
      (verifier := FullRingSwitching.fullOracleVerifier κ L K β_rs ℓ ℓ' (𝓑 := 𝓑) h_l
        (bbfMLIOPCS 𝔽q β γ_repetitions (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)))
      (init := init) (impl := impl)
      (relIn := BatchingPhase.batchingInputRelation
        κ L K β_rs ℓ ℓ' h_l
        (bbfMLIOPCS 𝔽q β γ_repetitions
          (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (𝓑 := 𝓑)).toAbstractOStmtIn)
      (relOut := acceptRejectOracleRel)
      (rbrKnowledgeError := fun i => FullRingSwitching.fullRbrKnowledgeError κ L K ℓ'
        (bbfMLIOPCS 𝔽q β γ_repetitions (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)) i) :=
  FullRingSwitching.fullOracleVerifier_rbrKnowledgeSoundness κ L K β_rs ℓ ℓ' h_l
    (𝓑 := 𝓑)
    (bbfMLIOPCS 𝔽q β γ_repetitions (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑))
    init

end Composition

end
end Binius.RingSwitching.BBFSmallFieldIOPCS
