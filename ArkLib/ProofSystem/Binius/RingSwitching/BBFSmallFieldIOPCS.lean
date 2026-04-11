/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
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
- `bbfSmallFieldConcreteKnowledgeError`: closed-form scalar error (ring-switching front + BBF (43)-style tail)
- `bbf_fullOracleVerifier_knowledgeSoundness`: Scalar KS for the composed verifier via
  `FullRingSwitching.fullOracleVerifier_knowledgeSoundness` and
  `FullBinaryBasefold.fullRbrKnowledgeError_sum_le_concrete` (PCS RBR-error sum).

## References

- [DP24] Diamond, Benjamin E., and Jim Posen. "Polylogarithmic Proofs for Multilinears over Binary
  Towers." Cryptology ePrint Archive (2024).
  Statement numbering follows the archived revision of [DP24].
-/


namespace Binius.RingSwitching.BBFSmallFieldIOPCS

open Binius.BinaryBasefold Binius.BinaryBasefold.FullBinaryBasefold
open Binius.RingSwitching Binius.RingSwitching.FullRingSwitching
open Polynomial MvPolynomial OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Module
open scoped NNReal

section

/-! ## Part 1: Binary Basefold as MLIOPCS

We construct an `MLIOPCS L ℓ'` by wrapping Binary Basefold's full protocol.
The construction is parameterized by Binary Basefold parameters only (no Ring-switching params).
-/

section BinaryBasefoldMLIOPCS

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [SampleableType L]
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
noncomputable def MLPEvalWitness_to_BBF_Witness (wit : WitMLP L ℓ') :
    Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') (0 : Fin (ℓ' + 1)) :=
  {
    t := MultilinearPoly.ofCMvPoly wit.t
    H := 0
    f := fun _ => 0
  }

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

/-- Context lens for the ring-switching large-field invocation into computable BBF. -/
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
    (OuterWitIn := WitMLP L ℓ')
    (OuterWitOut := Unit)
    (InnerWitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') (0 : Fin (ℓ' + 1)))
    (InnerWitOut := Unit) where
  stmt := largeFieldInvocationStmtLens 𝔽q β
  wit := {
    toFunA := fun ⟨⟨stmtIn, _oStmtIn⟩, witIn⟩ =>
      {
        t := MultilinearPoly.ofCMvPoly witIn.t
        H := 0
        f := fun _ => 0
      }
    toFunB := fun _ _ => ()
  }

/-- Computable BBF oracle reduction lifted to the ring-switching large-field invocation context. -/
def largeFieldInvocationOracleReduction :
    OracleReduction (oSpec := []ₒ)
      (StmtIn := MLPEvalStatement (L := L) (ℓ := ℓ'))
      (OStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') ϑ
          (0 : Fin (ℓ' + 1)))
      (StmtOut := Bool)
      (OStmtOut := fun _ : Empty => Unit)
      (WitIn := WitMLP L ℓ')
      (WitOut := Unit)
      (pSpec := fullPSpec 𝔽q β γ_repetitions (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  OracleReduction.liftContext
    (lens := largeFieldInvocationCtxLens 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ) (𝓡 := 𝓡))
    (R := FullBinaryBasefold.fullOracleReduction 𝔽q β γ_repetitions (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑))

omit [SampleableType L] in
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
  sorry

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
      exact finSumFinEquiv_symm_apply_castAdd (m := ℓ') (n := 0) i
    have h_ren :
        MvPolynomial.rename
          (f := ⇑(finSumFinEquiv (m := ℓ') (n := 0)).symm) p =
        MvPolynomial.rename (f := Sum.inl) p := by
      exact congrArg (fun f => MvPolynomial.rename (f := f) p) h_ren_fun
    rw [h_ren]
    have h_comp := MvPolynomial.sumAlgEquiv_comp_rename_inl
      (R := L) (S₁ := Fin ℓ') (S₂ := Fin 0)
    have h_eval_comp := congrArg (fun f => f p) h_comp
    exact h_eval_comp
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
  rw [fixFirstVariablesOfMQP_eq_bind₁ (L := L) (ℓ := ℓ') (v := (0 : Fin (ℓ' + 1)))
    (poly := H) (challenges := Fin.elim0)]
  change MvPolynomial.bind₁ (fun j : Fin ℓ' => MvPolynomial.X j) H = H
  rw [MvPolynomial.bind₁_X_left]
  rfl

lemma witnessStructuralInvariant_MLPEvalWitness_to_BBF_Witness
    (stmt : MLPEvalStatement (L := L) (ℓ := ℓ'))
    (wit : WitMLP L ℓ') :
    Binius.BinaryBasefold.witnessStructuralInvariant 𝔽q β
      (mp := BBF_SumcheckMultiplierParam) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (reducedMLPEvalStatement_to_BBF_Statement (L := L) (ℓ' := ℓ') stmt)
      (MLPEvalWitness_to_BBF_Witness 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) wit) := by
  sorry

/-- If `t(r) = s` for the outer MLP statement, then the mapped round-0 BBF witness
satisfies the BBF round-0 sumcheck consistency identity. -/
lemma sumcheckConsistency_MLPEvalWitness_to_BBF_Witness_of_eval
    (stmt : MLPEvalStatement (L := L) (ℓ := ℓ'))
    (wit : WitMLP L ℓ')
    (h_eval : CPoly.CMvPolynomial.eval stmt.t_eval_point wit.t = stmt.original_claim) :
    Binius.BinaryBasefold.sumcheckConsistencyProp (𝓑 := 𝓑)
      (sumcheckTarget := (reducedMLPEvalStatement_to_BBF_Statement (L := L) (ℓ' := ℓ') stmt).sumcheck_target)
      (H := (MLPEvalWitness_to_BBF_Witness 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) wit).H) := by
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
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (MultilinearPoly.ofCMvPoly t')
      (getFirstOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmt)
  -- Strict compatibility: exact oracle folding consistency (implies UDR-closeness).
  strictInitialCompatibility := fun ⟨t', oStmt⟩ =>
    strictOracleFoldingConsistencyProp 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (t := MultilinearPoly.ofCMvPoly t')
      (i := (0 : Fin (ℓ' + 1)))
      (challenges := Fin.elim0) (oStmt := oStmt)
  -- Strict (exact equality) implies relaxed (UDR-closeness).
  strictInitialCompatibility_implies_initialCompatibility := by
    intro oStmt t h_compat_strict
    sorry
  -- Unique polynomial determination from oracle (via UDR-closeness)
  initialCompatibility_unique := fun oStmt t₁ t₂ h₁ h₂ => by
    sorry

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

lemma MLPEvalRelation_of_round0_local_and_structural
    (stmt : MLPEvalStatement (L := L) (ℓ := ℓ'))
    (wit : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ')
      (0 : Fin (ℓ' + 1)))
    (h_local : Binius.BinaryBasefold.sumcheckConsistencyProp (𝓑 := 𝓑)
      (sumcheckTarget := (reducedMLPEvalStatement_to_BBF_Statement (L := L) (ℓ' := ℓ') stmt).sumcheck_target)
      (H := wit.H))
    (h_struct : Binius.BinaryBasefold.witnessStructuralInvariant 𝔽q β
      (mp := BBF_SumcheckMultiplierParam) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (reducedMLPEvalStatement_to_BBF_Statement (L := L) (ℓ' := ℓ') stmt) wit) :
    wit.t.val.eval stmt.t_eval_point = stmt.original_claim := by
  sorry

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
    (OuterWitIn := WitMLP L ℓ')
    (OuterWitOut := Unit)
    (InnerWitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ')
      (0 : Fin (ℓ' + 1)))
    (InnerWitOut := Unit) where
  stmt := largeFieldInvocationStmtLens 𝔽q β
  wit := {
    toFunA := fun _ => ()
    toFunB := fun ⟨⟨_stmtIn, _oStmtIn⟩, _outerWitOut⟩ innerWitIn =>
      ⟨MultilinearPoly.toCMvPoly innerWitIn.t⟩
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
      (OuterWitIn := WitMLP L ℓ')
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
    dsimp [largeFieldInvocationExtractorLens, largeFieldInvocationStmtLens] at hOuter ⊢
    exact hOuter
  lift_knowledgeSound := by
    sorry

/-! ### MLIOPCS Instance -/

/-- Binary Basefold as an `MLIOPCS L ℓ'`.

This wraps the full Binary Basefold protocol (core interaction + query phase)
as a multilinear polynomial commitment scheme over the large field `L`. -/
noncomputable def bbfMLIOPCS : MLIOPCS L ℓ' :=
  let _ := 𝔽q
  let _ := β
  let _ := γ_repetitions
  let _ := 𝓑
  let _ := (ϑ : ℕ)
  let _ := h_ℓ_add_R_rate
  {
    toAbstractOStmtIn := bbfAbstractOStmtIn 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)
    numRounds := _
    pSpec := fullPSpec 𝔽q β γ_repetitions (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    Oₘ := by
      intro i
      infer_instance
    O_challenges := by
      intro i
      infer_instance
    oracleReduction := largeFieldInvocationOracleReduction 𝔽q β γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ) (𝓡 := 𝓡) (𝓑 := 𝓑)
    perfectCompleteness := by
      intro σ init impl hInit
      sorry
    strictPerfectCompleteness := by
      intro σ init impl hInit
      sorry
    rbrKnowledgeError := fun _ => 0
    rbrKnowledgeSoundness := by
      intro σ init impl
      sorry
  }

end BinaryBasefoldMLIOPCS

/-! ## Part 2: End-to-End Composition

Compose Ring-switching with the Binary Basefold MLIOPCS using the existing
infrastructure in `RingSwitching/General.lean`.
-/

section Composition

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [SampleableType L]
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
theorem bbf_fullOracleReduction_perfectCompleteness (hInit : NeverFail init) :
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

/-- Closed-form scalar knowledge-soundness error: **Protocol 3.1** front
`(2ℓ' + κ)/|L|` plus `concreteBinaryBasefoldKnowledgeError` for the
large-field Binary Basefold MLIOPCS tail (same decomposition as `fullRingSwitchingConcreteKnowledgeError`). -/
noncomputable def bbfSmallFieldConcreteKnowledgeError (κ : ℕ) (L : Type) [Fintype L]
    (ℓ' 𝓡 γ_rep : ℕ) : ℝ≥0 :=
  FullRingSwitching.fullRingSwitchingConcreteKnowledgeError κ L ℓ'
    (concreteBinaryBasefoldKnowledgeError L ℓ' 𝓡 γ_rep)

/-- Scalar knowledge soundness for ring-switching composed with Binary Basefold as `MLIOPCS`.

Proof: `FullRingSwitching.fullOracleVerifier_knowledgeSoundness` with
`ε_pcs := concreteBinaryBasefoldKnowledgeError …` and `h_pcs` from
`FullBinaryBasefold.fullRbrKnowledgeError_sum_le_concrete` (PCS sum at most that tail). -/
theorem bbf_fullOracleVerifier_knowledgeSoundness :
    (FullRingSwitching.fullOracleVerifier κ L K β_rs ℓ ℓ' (𝓑 := 𝓑) h_l
        (bbfMLIOPCS 𝔽q β γ_repetitions
          (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑))).toVerifier.knowledgeSoundness
      (init := init) (impl := impl)
      (relIn := BatchingPhase.batchingInputRelation
        κ L K β_rs ℓ ℓ' h_l
        (bbfMLIOPCS 𝔽q β γ_repetitions
          (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)).toAbstractOStmtIn)
      (relOut := acceptRejectOracleRel)
      (knowledgeError := bbfSmallFieldConcreteKnowledgeError κ L ℓ' 𝓡 γ_repetitions) := by
  sorry

end Composition

end
end Binius.RingSwitching.BBFSmallFieldIOPCS
