/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.Data.MvPolynomial.Multilinear
import ArkLib.OracleReduction.Basic
import ArkLib.OracleReduction.Security.RoundByRound
import CompPoly.Fields.Binary.Tower.TensorAlgebra
import ArkLib.ProofSystem.Binius.BinaryBasefold.Relations
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Matrix.Basic

/-!
# Ring-Switching IOP Prelude

This module contains the core definitions and infrastructure for the ring-switching IOP,
including tensor algebra operations, field extension handling, and basic protocol types.

## Main Components

1. **Tensor Algebra operations**: Operations for handling tensor products
between small field K and large field L, including embeddings `φ₀ : L → L ⊗[K] L`,
`φ₁ : L → L ⊗[K] L`, and row/column decompositions with respect to a `K`-basis `β`.
2. **Protocol Types**: Statement and witness types for each phase
3. **Security Definitions**: Relations & Kstate for security analysis
-/

noncomputable section

namespace Binius.RingSwitching
open Binius.BinaryBasefold

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial TensorProduct
open scoped NNReal

/- This section defines generic preliminaries for the ring-switching protocol. -/
section Preliminaries

variable (κ : ℕ) [NeZero κ]
variable (L : Type) [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
variable (K : Type) [Field K] [Fintype K] [DecidableEq K]
variable [Algebra K L]
variable (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
variable (h_l : ℓ = ℓ' + κ)

section TensorAlgebraOps
/-!
## Enhanced Tensor Algebra Operations

Additional tensor algebra operations for the enhanced protocol specification.
Based on the tensor algebra theory from Section 2.1.
-/

/-- Tensor Algebra A = L ⊗_K L. Based on the spec,
it's viewed as (2^κ)x(2^κ) arrays of K-elements.
The imported TensorAlgebra file provides the leftAlgebra instances. -/
abbrev TensorAlgebra (K L : Type*) [Field K] [Field L] [Algebra K L] := L ⊗[K] L

/--
Column embedding φ₀: L → A as a ring homomorphism.
φ₀(α) = α ⊗ 1, operates on columns.
-/
def φ₀ (L K : Type*) [Field K] [Field L] [Algebra K L] : L →+* TensorAlgebra K L where
  toFun α := α ⊗ₜ[K] (1 : L)
  map_one' := rfl
  map_mul' α β := by simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  map_zero' := by simp only [zero_tmul]
  map_add' α β := by simp only [add_tmul]

/--
Row embedding φ₁: L → A as a ring homomorphism.
φ₁(α) = 1 ⊗ α, operates on rows.
-/
def φ₁ (L K : Type*) [Field K] [Field L] [Algebra K L] : L →+* TensorAlgebra K L where
  toFun α := (1 : L) ⊗ₜ[K] α
  map_one' := by rfl
  map_mul' α β := by
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  map_zero' := by simp only [tmul_zero]
  map_add' α β := by simp only [tmul_add]

open Module
/-- Decompose `ŝ` into row components `(ŝ =: Σ_{u ∈ {0,1}^κ} β_u ⊗ ŝ_u)`.
This views `L ⊗ L` as a module over `L` (right action)
and finds the coordinates of `ŝ` with respect to the basis lifted from `β`. -/
def decompose_tensor_algebra_rows {σ : Type*} (β : Basis σ K L)
  (s_hat : TensorAlgebra K L) : σ → L :=
  fun u => by
    let b := Basis.baseChangeRight (b:=β) (Right:=L)
    letI rightAlgebra : Algebra L (L ⊗[K] L) := by
      exact Algebra.TensorProduct.rightAlgebra
    letI rightModule : Module L (L ⊗[K] L) := rightAlgebra.toModule
    exact b.repr s_hat u

/-- Decompose `ŝ` into column components `(ŝ =: Σ_{v ∈ {0,1}^κ} ŝ_v ⊗ β_v)`.
This views `L ⊗ L` as a module over `L` (left action)
and finds the coordinates of `ŝ` with respect to the basis lifted from `β`. -/
def decompose_tensor_algebra_columns {σ : Type*} (β : Basis σ K L) (s_hat : L ⊗[K] L) : σ → L :=
  fun v =>
    (β.baseChange L).repr s_hat v
/--
**Definition 2.1 (MLE packing)**.
Packs a small-field multilinear `t` into a large-field multilinear `t'` by
reinterpreting chunks of `2^κ` coefficients as single `L`-elements.
For each `w ∈ {0,1}^ℓ'`, the evaluation `t'(w)` is defined as:
`t'(w) := ∑_{v ∈ {0,1}^κ} t(v₀, ..., v_{κ-1}, w₀, ..., w_{ℓ'-1}) ⋅ β_v`
-/
def packMLE (β : Basis (Fin κ → Fin 2) K L) (t : MultilinearPoly K ℓ) :
    MultilinearPoly L ℓ' :=
  -- 1. Define the function that gives the evaluations of t' on the boolean hypercube.
  let packing_func (w : Fin ℓ' → Fin 2) : L :=
    -- a. Define a function that computes the K-coefficients for a given `w`.
    let coeffs_for_w (v : Fin κ → Fin 2) : K :=
      -- Construct the full evaluation point `(v, w)` of length `ℓ`.
      let concatenated_point (i : Fin ℓ) : Fin 2 :=
        if h : i.val < κ then
          v ⟨i.val, h⟩
        else
          w ⟨i.val - κ, by omega⟩
      -- Evaluate the small-field polynomial `t` at this point.
      MvPolynomial.eval (fun i => ↑(concatenated_point i)) t.val
    -- b. Use `equivFun.symm` = ∑ v, (coeffs_for_w v) • (β v).
    β.equivFun.symm coeffs_for_w
  -- 2. The packed polynomial `t'` is the multilinear extension of this function.
  ⟨MvPolynomial.MLE packing_func, MLE_mem_restrictDegree packing_func⟩

/--
**Unpacking a Packed Multilinear Polynomial**.
Reverses the packing defined in `packMLE`. It reconstructs the small-field
multilinear `t` from the large-field multilinear `t'`.

The evaluation of `t` at a point `(v, w)` is recovered by taking the evaluation
of `t'` at `w`, which is an element of `L`, and finding its `v`-th coordinate
with respect to the basis `β`.
-/
def unpackMLE (β : Basis (Fin κ → Fin 2) K L) (t' : MultilinearPoly L ℓ') :
    MultilinearPoly K ℓ :=
  -- 1. Define the function that gives the evaluations of the original small-field polynomial `t`.
  let unpacked_evals (p : Fin ℓ → Fin 2) : K :=
    -- a. Deconstruct the evaluation point `p` into `v` (first κ bits) and `w` (last ℓ' bits).
    let v (i : Fin κ) : Fin 2 := p ⟨i.val, by omega⟩
    let w (i : Fin ℓ') : Fin 2 := p ⟨i.val + κ, by { rw [h_l]; omega }⟩
    -- b. Evaluate the large-field polynomial `t'` at the point `w`.
    let t'_eval_at_w : L := MvPolynomial.eval (fun i => ↑(w i)) t'.val
    -- c. Get the K-coefficients of this L-element with respect to the basis `β`.
    -- `β.repr/β.equivFun` maps an element of L to its coordinate function `(Fin κ → Fin 2) → K`.
    let coeffs : (Fin κ → Fin 2) → K := β.repr t'_eval_at_w
    -- d. The desired evaluation t(p) = t(v,w)
      -- is the coefficient corresponding to the basis vector `β_v`.
    coeffs v
  -- 2. The unpacked polynomial `t` is the multilinear extension of this evaluation function.
  ⟨MvPolynomial.MLE unpacked_evals, MLE_mem_restrictDegree unpacked_evals⟩

/--
**Component-wise `φ₁` embedding**.
Takes a polynomial `t'` with coefficients in `L` and embeds it into a polynomial
with coefficients in the tensor algebra `A` by applying `φ₁` to each coefficient.
This is achieved by using `MvPolynomial.map`.
-/
def componentWise_φ₁_embed_MLE (t' : MultilinearPoly L ℓ') :
    MultilinearPoly (TensorAlgebra K L) ℓ' :=
  ⟨MvPolynomial.map (R:=L) (S₁ := TensorAlgebra K L) (f:=φ₁ L K) (t'.val), by
    rw [MvPolynomial.mem_restrictDegree_iff_degreeOf_le]
    intro i -- for any specific variable Xᵢ,
      -- we prove its max individual degree is at most 1 in ANY monomial terms
    calc
      MvPolynomial.degreeOf i (MvPolynomial.map (φ₁ L K) t'.val)
      _ ≤ MvPolynomial.degreeOf i t'.val := by
        refine degreeOf_le_iff.mpr ?_
        intro m hm_support_mapped_t' -- consider any specific monomial term
        have hm_in_support_t' : m ∈ t'.val.support := by
          apply MvPolynomial.support_map_subset (f:=φ₁ L K)
          exact hm_support_mapped_t'
        exact monomial_le_degreeOf i hm_in_support_t'
      _ ≤ 1 := by
        have h_og_t' := t'.property
        simp only [MvPolynomial.mem_restrictDegree_iff_degreeOf_le] at h_og_t'
        exact h_og_t' i
  ⟩

end TensorAlgebraOps

section ProtocolTypes
/-!
## Enhanced Protocol Type Definitions (Interfaces between phases)

We define the Statement and Witness types at the boundaries of each phase
following the enhanced specification.
-/

structure WitMLP where
  t : MultilinearPoly K ℓ

structure BatchingWitIn where
  t : MultilinearPoly K ℓ
  t' : MultilinearPoly L ℓ'

structure BatchingStmtIn where
  t_eval_point : Fin ℓ → L         -- r = (r_0, ..., r_{ℓ-1}) => shared input
  original_claim : L               -- s = t(r) => the original claim to verify

structure RingSwitchingBaseContext extends (SumcheckBaseContext L ℓ) where
  -- context from batching phase
  s_hat : TensorAlgebra K L  -- ŝ
  r_batching : Fin κ → L     -- r''

structure SumcheckWitness (i : Fin (ℓ' + 1)) where
  t' : MultilinearPoly L ℓ' -- the packed polynomial
  -- `h(X_0, ..., X_{ℓ'-1}) := A(X_0, ..., X_{ℓ'-1}) ⋅ t'(X_0, ..., X_{ℓ'-1})`
  H : L⦃≤ 2⦄[X Fin (ℓ' - i)]

section MLIOPCS
-- Define the specific Stmt/Wit types Π' expects.
structure MLIOPCSStmt where
  point : Fin ℓ' → L
  evaluation : L

/-- Standard input relation for MLIOPCS: polynomial evaluation at point equals claimed evaluation -/
def MLPEvalRelation (ιₛᵢ : Type) (OStmtIn : ιₛᵢ → Type)
    (input : ((MLPEvalStatement L ℓ') × (∀ j, OStmtIn j)) × (WitMLP L ℓ')) : Prop :=
  let ⟨⟨stmt, _⟩, wit⟩ := input
  wit.t.val.eval stmt.t_eval_point = stmt.original_claim

structure AbstractOStmtIn where
  ιₛᵢ : Type
  OStmtIn : ιₛᵢ → Type
  Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)
  -- The abstract initial compatibility relation, which along with
  -- MLPEvalRelation, forms the initial input relation for the MLIOPCS.
  initialCompatibility : (MultilinearPoly L ℓ') × (∀ j, OStmtIn j) → Prop
  -- Strict compatibility relation used by perfect-completeness statements.
  strictInitialCompatibility : (MultilinearPoly L ℓ') × (∀ j, OStmtIn j) → Prop
  -- Strict compatibility is stronger and should imply the relaxed one.
  strictInitialCompatibility_implies_initialCompatibility :
    ∀ (oStmt : ∀ j, OStmtIn j) (t : MultilinearPoly L ℓ'),
      strictInitialCompatibility ⟨t, oStmt⟩ → initialCompatibility ⟨t, oStmt⟩
  -- The ideal oracle **(Functionality 2.4, 2.5, 2.6)** stores the exact vector, so the
  -- oracle commitment uniquely determines the polynomial t'.
  -- **NOTE**: This captures `|Λ| = 1` (i.e. set of compatible witnesses
    -- compatible with oracles) in the WARP paper's terminology.
  initialCompatibility_unique : ∀ (oStmt : ∀ j, OStmtIn j) (t₁ t₂ : MultilinearPoly L ℓ'),
    initialCompatibility ⟨t₁, oStmt⟩ → initialCompatibility ⟨t₂, oStmt⟩ → t₁ = t₂

/-- Relaxed relation used for RBR knowledge-soundness statements. -/
def AbstractOStmtIn.toRelInput (aOStmtIn : AbstractOStmtIn L ℓ') :
  Set (((MLPEvalStatement L ℓ') × (∀ j, aOStmtIn.OStmtIn j)) × (WitMLP L ℓ')) :=
  {input |
    MLPEvalRelation L ℓ' aOStmtIn.ιₛᵢ aOStmtIn.OStmtIn input
    ∧ aOStmtIn.initialCompatibility ⟨input.2.t, input.1.2⟩}

/-- Strict relation used for perfect-completeness statements. -/
def AbstractOStmtIn.toStrictRelInput (aOStmtIn : AbstractOStmtIn L ℓ') :
  Set (((MLPEvalStatement L ℓ') × (∀ j, aOStmtIn.OStmtIn j)) × (WitMLP L ℓ')) :=
  {input |
    MLPEvalRelation L ℓ' aOStmtIn.ιₛᵢ aOStmtIn.OStmtIn input
    ∧ aOStmtIn.strictInitialCompatibility ⟨input.2.t, input.1.2⟩}

omit [Fintype L] [DecidableEq L] [CharP L 2] [NeZero ℓ'] in
lemma AbstractOStmtIn.toStrictRelInput_subset_toRelInput (aOStmtIn : AbstractOStmtIn L ℓ') :
    aOStmtIn.toStrictRelInput ⊆ aOStmtIn.toRelInput := by
  intro input h_input
  rcases input with ⟨⟨stmt, oStmt⟩, wit⟩
  rcases h_input with ⟨h_eval, h_compat_strict⟩
  exact ⟨h_eval,
    aOStmtIn.strictInitialCompatibility_implies_initialCompatibility oStmt wit.t
      h_compat_strict⟩

structure MLIOPCS extends (AbstractOStmtIn L ℓ') where
  /-- Protocol specification -/
  numRounds : ℕ
  pSpec : ProtocolSpec numRounds
  Oₘ: ∀ j, OracleInterface (pSpec.Message j)
  O_challenges: ∀ (i : pSpec.ChallengeIdx), SampleableType (pSpec.Challenge i)
  -- /-- The evaluation protocol Π' as an OracleReduction -/
  oracleReduction : OracleReduction (oSpec:=[]ₒ)
    (StmtIn := MLPEvalStatement L ℓ') (OStmtIn:= OStmtIn)
    (StmtOut := Bool) (OStmtOut := fun _: Empty => Unit)
    (WitIn := WitMLP L ℓ') (WitOut := Unit)
    (pSpec := pSpec)
  -- Security properties
  perfectCompleteness : ∀ {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)},
    NeverFail init →
    OracleReduction.perfectCompleteness (oSpec:=[]ₒ)
      (StmtIn:=MLPEvalStatement L ℓ') (OStmtIn:=OStmtIn)
      (StmtOut:=Bool) (OStmtOut:=fun _: Empty => Unit)
      (WitIn:=WitMLP L ℓ') (WitOut:=Unit) (pSpec:=pSpec) (init:=init) (impl:=impl)
      (relIn := toAbstractOStmtIn.toStrictRelInput)
      (relOut := acceptRejectOracleRel)
      (oracleReduction := oracleReduction)
  strictPerfectCompleteness : ∀ {σ : Type} {init : ProbComp σ}
      {impl : QueryImpl []ₒ (StateT σ ProbComp)},
    NeverFail init →
    OracleReduction.perfectCompleteness (oSpec:=[]ₒ)
      (StmtIn:=MLPEvalStatement L ℓ') (OStmtIn:=OStmtIn)
      (StmtOut:=Bool) (OStmtOut:=fun _: Empty => Unit)
      (WitIn:=WitMLP L ℓ') (WitOut:=Unit) (pSpec:=pSpec) (init:=init) (impl:=impl)
      (relIn := toAbstractOStmtIn.toStrictRelInput)
      (relOut := acceptRejectOracleRel)
      (oracleReduction := oracleReduction)
  -- RBR knowledge error function for the MLIOPCS
  rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0
  -- RBR knowledge soundness property
  rbrKnowledgeSoundness : ∀ {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)
  },
    OracleVerifier.rbrKnowledgeSoundness
      (verifier := oracleReduction.verifier)
      (init := init)
      (impl := impl)
      (relIn := toAbstractOStmtIn.toRelInput)
      (relOut := acceptRejectOracleRel)
      (rbrKnowledgeError := rbrKnowledgeError)

end MLIOPCS

section OStmt
variable (aOStmtIn : AbstractOStmtIn L ℓ')

instance instOstmtMLIOPCS : ∀ (i : aOStmtIn.ιₛᵢ), OracleInterface (aOStmtIn.OStmtIn i) :=
  fun i => aOStmtIn.Oₛᵢ i

end OStmt

end ProtocolTypes
end Preliminaries

/- This section defines the specific relations for the ring-switching protocol, whereas
the basis of L over K has rank `2^κ` instead of `κ` as in the Preliminaries section.
-/
section Relations
open Module Binius.BinaryBasefold

variable (κ : ℕ) [NeZero κ]
variable (L : Type) [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [SampleableType L]
variable (K : Type) [Field K] [Fintype K] [DecidableEq K]
variable [Algebra K L]
variable (β : Basis (Fin κ → Fin 2) K L)
variable (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
variable (h_l : ℓ = ℓ' + κ)
variable {𝓑 : Fin 2 ↪ L}

/-- Compute the tensor value ŝ := φ₁(t')(φ₀(r_κ), ..., φ₀(r_{ℓ-1})) -/
def embedded_MLP_eval (t' : MultilinearPoly L ℓ') (r : Fin ℓ → L) :
  TensorAlgebra K L :=
  -- This implements the identity:
  -- ŝ = Σ_{w ∈ {0,1}^ℓ'} eq̃(r_suffix, w) ⊗ t'(w)
  let r_suffix : Fin ℓ' → L :=
    fun i => r ⟨i.val + κ, by { rw [h_l]; omega }⟩
  let φ₁_mapped_t': MultilinearPoly (TensorAlgebra K L) ℓ' := componentWise_φ₁_embed_MLE L K ℓ' t'
  let φ₀_mapped_r: Fin ℓ' → (TensorAlgebra K L) := fun i => φ₀ L K (r_suffix i)
  φ₁_mapped_t'.val.eval φ₀_mapped_r

/-- Step 2 (V): Check 1: s ?= Σ_{v ∈ {0,1}^κ} eqTilde(v, r_{0..κ-1}) ⋅ ŝ_v. -/
def performCheckOriginalEvaluation (s : L) (r : Fin ℓ → L) (s_hat : TensorAlgebra K L) : Bool :=
  let r_prefix : Fin κ → L := fun i => r ⟨i.val, by omega⟩
  let check_sum := Finset.sum Finset.univ fun (v : Fin κ → Fin 2) =>
    let v_as_L : Fin κ → L := fun i => if (v i == 1) then 1 else 0
    (eqTilde v_as_L r_prefix) * (decompose_tensor_algebra_columns (L:=L)
      (K:=K) (β:=β) s_hat v)
  decide (s = check_sum)

/-- **Correctness of the Batching Check**

This lemma proves that when the prover honestly computes the message `s_hat` using
`packMLE` and `embedded_MLP_eval`, the verifier's check passes.
-/
private lemma unpack_pack_id (t : MultilinearPoly K ℓ) :
    unpackMLE κ L K ℓ ℓ' h_l β (packMLE κ L K ℓ ℓ' h_l β t) = t := by
  apply Subtype.ext
  apply (MvPolynomial.is_multilinear_eq_iff_eq_evals_zeroOne
    (p := (unpackMLE κ L K ℓ ℓ' h_l β (packMLE κ L K ℓ ℓ' h_l β t)).val)
    (q := t.val)
    (hp := (unpackMLE κ L K ℓ ℓ' h_l β (packMLE κ L K ℓ ℓ' h_l β t)).property)
    (hq := t.property)).2
  funext p
  unfold unpackMLE packMLE
  simp only [MvPolynomial.toEvalsZeroOne, MvPolynomial.MLE_eval_zeroOne,
    Basis.equivFun_symm_apply]
  rw [Basis.repr_sum_self]
  apply congrArg (fun x => MvPolynomial.eval x t.val)
  funext i
  by_cases h : i.val < κ
  · simp [h]
  · simp [h]
    have hk : κ ≤ i.val := Nat.le_of_not_lt h
    have h_idx : (⟨i.val - κ + κ, by omega⟩ : Fin ℓ) = i := by
      apply Fin.ext
      exact Nat.sub_add_cancel hk
    rw [h_idx]

private lemma zeroOneTensor_eq_phi1 (w : Fin ℓ' → Fin 2) :
    (fun i => ((w i : Fin 2) : TensorAlgebra K L)) =
      fun i => φ₁ L K (((w i : Fin 2) : L)) := by
  funext i
  have hi : w i = 0 ∨ w i = 1 := by omega
  rcases hi with hi | hi
  · simp [hi, φ₁]
  · simp [hi, φ₁, Algebra.TensorProduct.one_def]

private lemma zeroOneTensor_eq_phi0 (w : Fin ℓ' → Fin 2) :
    (fun i => ((w i : Fin 2) : TensorAlgebra K L)) =
      fun i => φ₀ L K (((w i : Fin 2) : L)) := by
  funext i
  have hi : w i = 0 ∨ w i = 1 := by omega
  rcases hi with hi | hi
  · simp [hi, φ₀]
  · simp [hi, φ₀, Algebra.TensorProduct.one_def]

private lemma map_eqPolynomial_phi0_pre (r : Fin ℓ' → L) :
    MvPolynomial.map (φ₀ L K) (MvPolynomial.eqPolynomial r : MvPolynomial (Fin ℓ') L) =
      (MvPolynomial.eqPolynomial (fun i => φ₀ L K (r i)) :
        MvPolynomial (Fin ℓ') (TensorAlgebra K L)) := by
  rw [MvPolynomial.eqPolynomial_expanded, MvPolynomial.eqPolynomial_expanded]
  simp

private lemma map_phi1_eq_MLE (t' : MultilinearPoly L ℓ') :
    MvPolynomial.map (φ₁ L K) t'.val =
      MvPolynomial.MLE (fun w : Fin ℓ' → Fin 2 => φ₁ L K
        (MvPolynomial.eval (w : Fin ℓ' → L) t'.val)) := by
  have h_mle : t'.val =
      MvPolynomial.MLE (fun w : Fin ℓ' → Fin 2 => MvPolynomial.eval (w : Fin ℓ' → L) t'.val) := by
    symm
    exact (MvPolynomial.is_multilinear_iff_eq_evals_zeroOne (p := t'.val)).mp t'.property
  conv_lhs => rw [h_mle]
  rw [MvPolynomial.MLE, MvPolynomial.MLE]
  simp_rw [map_sum, map_mul, MvPolynomial.map_C]
  apply Finset.sum_congr rfl
  intro w hw
  rw [MvPolynomial.eqPolynomial_zeroOne (R := L) (r := w)]
  rw [MvPolynomial.eqPolynomial_zeroOne (R := TensorAlgebra K L) (r := w)]
  rw [map_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hwi : w i = 0
  · simp [hwi, φ₁]
  · have hwi1 : w i = 1 := by omega
    simp [hwi, hwi1, φ₁]

private lemma embedded_MLP_eval_eq_sum (t' : MultilinearPoly L ℓ') (r : Fin ℓ → L) :
    embedded_MLP_eval κ L K ℓ ℓ' h_l t' r =
      ∑ w : Fin ℓ' → Fin 2,
        φ₀ L K (eqTilde (fun i => r ⟨i.val + κ, by { rw [h_l]; omega }⟩) (w : Fin ℓ' → L)) *
          φ₁ L K (MvPolynomial.eval (w : Fin ℓ' → L) t'.val) := by
  let r_suffix : Fin ℓ' → L := fun i => r ⟨i.val + κ, by { rw [h_l]; omega }⟩
  unfold embedded_MLP_eval
  change MvPolynomial.eval (fun i => φ₀ L K (r_suffix i)) (MvPolynomial.map (φ₁ L K) t'.val) = _
  rw [map_phi1_eq_MLE (L := L) (K := K) (t' := t')]
  unfold MvPolynomial.MLE
  simp only [MvPolynomial.eval_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C]
  apply Finset.sum_congr rfl
  intro w hw
  have h_eval :
      MvPolynomial.eval (fun i => ((w i : Fin 2) : TensorAlgebra K L))
        (MvPolynomial.eqPolynomial (fun i => φ₀ L K (r_suffix i))) =
      φ₀ L K (eqTilde r_suffix (w : Fin ℓ' → L)) := by
        rw [show (MvPolynomial.eqPolynomial (fun i => φ₀ L K (r_suffix i)) :
            MvPolynomial (Fin ℓ') (TensorAlgebra K L)) =
            MvPolynomial.map (φ₀ L K) (MvPolynomial.eqPolynomial r_suffix) by
          symm
          exact map_eqPolynomial_phi0_pre (L := L) (K := K) (r := r_suffix)]
        rw [zeroOneTensor_eq_phi0 (L := L) (K := K) (w := w)]
        rw [MvPolynomial.eval_map, Binius.BinaryBasefold.eqTilde]
        exact (MvPolynomial.eval₂_comp (f := φ₀ L K) (g := (w : Fin ℓ' → L))
          (p := MvPolynomial.eqPolynomial r_suffix)).symm
  rw [MvPolynomial.eqPolynomial_symm]
  rw [h_eval]

private lemma decompose_embedded_MLP_eval_columns
    (t' : MultilinearPoly L ℓ') (r : Fin ℓ → L) (v : Fin κ → Fin 2) :
    decompose_tensor_algebra_columns (L := L) (K := K) (β := β)
      (embedded_MLP_eval κ L K ℓ ℓ' h_l t' r) v =
      ∑ w : Fin ℓ' → Fin 2,
        (β.repr (MvPolynomial.eval (w : Fin ℓ' → L) t'.val)) v •
          eqTilde (fun i => r ⟨i.val + κ, by { rw [h_l]; omega }⟩) (w : Fin ℓ' → L) := by
  rw [embedded_MLP_eval_eq_sum (κ := κ) (L := L) (K := K) (ℓ := ℓ) (ℓ' := ℓ')
    (h_l := h_l) (t' := t') (r := r)]
  change ((β.baseChange L).repr (∑ w : Fin ℓ' → Fin 2,
    φ₀ L K (eqTilde (fun i => r ⟨i.val + κ, by { rw [h_l]; omega }⟩) (w : Fin ℓ' → L)) *
      φ₁ L K (MvPolynomial.eval (w : Fin ℓ' → L) t'.val))) v = _
  rw [map_sum, Finset.sum_apply']
  apply Finset.sum_congr rfl
  intro w hw
  rw [φ₀, φ₁]
  change ((β.baseChange L).repr
    (((eqTilde (fun i => r ⟨i.val + κ, by { rw [h_l]; omega }⟩) (w : Fin ℓ' → L)) ⊗ₜ[K] (1 : L)) *
      ((1 : L) ⊗ₜ[K] MvPolynomial.eval (w : Fin ℓ' → L) t'.val))) v = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [Basis.baseChange_repr_tmul]

private lemma decompose_embedded_MLP_eval_rows
    (t' : MultilinearPoly L ℓ') (r : Fin ℓ → L) (u : Fin κ → Fin 2) :
    decompose_tensor_algebra_rows (L := L) (K := K) (β := β)
      (embedded_MLP_eval κ L K ℓ ℓ' h_l t' r) u =
      ∑ w : Fin ℓ' → Fin 2,
        (β.repr (eqTilde (fun i => r ⟨i.val + κ, by
          rw [h_l]
          omega⟩) (w : Fin ℓ' → L)) u) • MvPolynomial.eval (w : Fin ℓ' → L) t'.val := by
  letI rightAlgebra : Algebra L (TensorAlgebra K L) := by
    exact Algebra.TensorProduct.rightAlgebra
  letI rightModule : Module L (TensorAlgebra K L) := rightAlgebra.toModule
  rw [embedded_MLP_eval_eq_sum (κ := κ) (L := L) (K := K) (ℓ := ℓ) (ℓ' := ℓ')
    (h_l := h_l) (t' := t') (r := r)]
  change ((Basis.baseChangeRight (b := β) (Right := L)).repr (∑ w : Fin ℓ' → Fin 2,
    φ₀ L K (eqTilde (fun i => r ⟨i.val + κ, by
      rw [h_l]
      omega⟩) (w : Fin ℓ' → L)) *
      φ₁ L K (MvPolynomial.eval (w : Fin ℓ' → L) t'.val))) u = _
  rw [map_sum, Finset.sum_apply']
  apply Finset.sum_congr rfl
  intro w hw
  rw [φ₀, φ₁]
  change ((Basis.baseChangeRight (b := β) (Right := L)).repr
      (((eqTilde (fun i => r ⟨i.val + κ, by
        rw [h_l]
        omega⟩) (w : Fin ℓ' → L)) ⊗ₜ[K] (1 : L)) *
        ((1 : L) ⊗ₜ[K] MvPolynomial.eval (w : Fin ℓ' → L) t'.val))) u = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [Basis.baseChangeRight_repr_tmul]

private lemma repr_packMLE_eval
    (t : MultilinearPoly K ℓ)
    (w : Fin ℓ' → Fin 2)
    (v : Fin κ → Fin 2) :
    β.repr (MvPolynomial.eval (w : Fin ℓ' → L) (packMLE κ L K ℓ ℓ' h_l β t).val) v =
      MvPolynomial.eval
        (fun i : Fin ℓ =>
          if h : i.val < κ then
            ((v ⟨i.val, h⟩ : Fin 2) : K)
          else
            ((w ⟨i.val - κ, by omega⟩ : Fin 2) : K))
        t.val := by
  unfold packMLE
  simp only [MvPolynomial.MLE_eval_zeroOne, Basis.equivFun_symm_apply, Basis.repr_sum_self]
  apply congrArg (fun x => MvPolynomial.eval x t.val)
  funext i
  by_cases h : i.val < κ
  · simp [h]
  · simp [h]

private def splitBoolPointEquiv :
    ((Fin κ → Fin 2) × (Fin ℓ' → Fin 2)) ≃ (Fin ℓ → Fin 2) where
  toFun vw := fun i =>
    if h : i.val < κ then
      vw.1 ⟨i.val, h⟩
    else
      vw.2 ⟨i.val - κ, by omega⟩
  invFun p :=
    (fun i => p ⟨i.val, by omega⟩,
      fun i => p ⟨i.val + κ, by
        rw [h_l]
        omega⟩)
  left_inv := by
    intro vw
    rcases vw with ⟨v, w⟩
    apply Prod.ext
    · funext i
      simp
    · funext i
      have hi : ¬ i.val + κ < κ := by
        omega
      simp [hi]
  right_inv := by
    intro p
    funext i
    by_cases hi : i.val < κ
    · simp [hi]
    · have hge : κ ≤ i.val := Nat.le_of_not_lt hi
      have hidx : (⟨i.val - κ + κ, by omega⟩ : Fin ℓ) = i := by
        apply Fin.ext
        exact Nat.sub_add_cancel hge
      simp [hi, hidx]

private lemma splitBoolPointEquiv_apply
    (v : Fin κ → Fin 2) (w : Fin ℓ' → Fin 2) (i : Fin ℓ) :
    splitBoolPointEquiv (κ := κ) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l) (v, w) i =
      if h : i.val < κ then
        v ⟨i.val, h⟩
      else
        w ⟨i.val - κ, by omega⟩ := rfl

private lemma splitBoolPointEquiv_prefix
    (v : Fin κ → Fin 2) (w : Fin ℓ' → Fin 2) (i : Fin κ) :
    splitBoolPointEquiv (κ := κ) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l) (v, w)
      ⟨i.val, by omega⟩ = v i := by
  rw [splitBoolPointEquiv_apply (κ := κ) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l) (v := v) (w := w)]
  simp

private lemma splitBoolPointEquiv_suffix
    (v : Fin κ → Fin 2) (w : Fin ℓ' → Fin 2) (i : Fin ℓ') :
    splitBoolPointEquiv (κ := κ) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l) (v, w)
      ⟨i.val + κ, by
        rw [h_l]
        omega⟩ = w i := by
  rw [splitBoolPointEquiv_apply (κ := κ) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l) (v := v) (w := w)]
  have hi : ¬ i.val + κ < κ := by
    omega
  simp [hi]

set_option maxHeartbeats 200000 in
private lemma eval₂_eqPolynomial_concat
    (eval_point : Fin ℓ → L)
    (v : Fin κ → Fin 2)
    (w : Fin ℓ' → Fin 2) :
    MvPolynomial.eval₂ (algebraMap K L) eval_point
      (MvPolynomial.eqPolynomial
        (fun i : Fin ℓ =>
          if h : i.val < κ then
            ((v ⟨i.val, h⟩ : Fin 2) : K)
          else
            ((w ⟨i.val - κ, by omega⟩ : Fin 2) : K))) =
      eqTilde (v : Fin κ → L) (fun i => eval_point ⟨i.val, by omega⟩) *
        eqTilde (fun i => eval_point ⟨i.val + κ, by
          rw [h_l]
          omega⟩) (w : Fin ℓ' → L) := by
  have h_eq : ℓ = κ + ℓ' := by
    omega
  let eval_point' : Fin (κ + ℓ') → L := eval_point ∘ Fin.cast h_eq.symm
  have hmain :
      MvPolynomial.eval₂ (algebraMap K L) eval_point'
        (MvPolynomial.eqPolynomial
          (fun i : Fin (κ + ℓ') =>
            if h : i.val < κ then
              ((v ⟨i.val, h⟩ : Fin 2) : K)
            else
              ((w ⟨i.val - κ, by omega⟩ : Fin 2) : K))) =
        eqTilde (v : Fin κ → L) (fun i => eval_point' (Fin.castAdd ℓ' i)) *
          eqTilde (fun i => eval_point' (Fin.natAdd κ i)) (w : Fin ℓ' → L) := by
    unfold Binius.BinaryBasefold.eqTilde eval_point'
    simp_rw [MvPolynomial.eqPolynomial_expanded]
    rw [MvPolynomial.eval₂_prod, Fin.prod_univ_add, MvPolynomial.eval_prod, MvPolynomial.eval_prod]
    congr 1
    · apply Finset.prod_congr rfl
      intro i hi
      simp
    · apply Finset.prod_congr rfl
      intro i hi
      simp
      ring_nf
  have hcast_poly :
      MvPolynomial.eval₂ (algebraMap K L) eval_point
        (MvPolynomial.eqPolynomial
          (fun i : Fin ℓ =>
            if h : i.val < κ then
              ((v ⟨i.val, h⟩ : Fin 2) : K)
            else
              ((w ⟨i.val - κ, by omega⟩ : Fin 2) : K))) =
      MvPolynomial.eval₂ (algebraMap K L) eval_point'
        (MvPolynomial.eqPolynomial
          (fun i : Fin (κ + ℓ') =>
            if h : i.val < κ then
              ((v ⟨i.val, h⟩ : Fin 2) : K)
            else
              ((w ⟨i.val - κ, by omega⟩ : Fin 2) : K))) := by
    subst h_eq
    rfl
  rw [hcast_poly, hmain]
  unfold Binius.BinaryBasefold.eqTilde eval_point'
  congr 1
  apply congrArg (fun x => MvPolynomial.eval (w : Fin ℓ' → L) (MvPolynomial.eqPolynomial x))
  funext i
  have hidx : Fin.cast h_eq.symm (Fin.natAdd κ i) = ⟨i.val + κ, by
      rw [h_l]
      omega⟩ := by
    apply Fin.ext
    simp [h_eq, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
  change eval_point (Fin.cast h_eq.symm (Fin.natAdd κ i)) = eval_point ⟨i.val + κ, by
      rw [h_l]
      omega⟩
  rw [hidx]

private def batchingCheckSummand
    (t : MultilinearPoly K ℓ)
    (eval_point : Fin ℓ → L)
    (p : Fin ℓ → Fin 2) : L :=
  MvPolynomial.eval₂ (algebraMap K L) eval_point
      (MvPolynomial.eqPolynomial (fun i => ((p i : Fin 2) : K))) *
    (algebraMap K L)
      ((β.repr
        (MvPolynomial.eval
          (fun i => ((p ⟨i.val + κ, by
            rw [h_l]
            omega⟩ : Fin 2) : L))
          (packMLE κ L K ℓ ℓ' h_l β t).val))
        (fun i => p ⟨i.val, by omega⟩))

set_option maxHeartbeats 200000 in
private lemma batchingCheckSummand_split
    (t : MultilinearPoly K ℓ)
    (eval_point : Fin ℓ → L)
    (v : Fin κ → Fin 2)
    (w : Fin ℓ' → Fin 2) :
    batchingCheckSummand κ L K β ℓ ℓ' h_l t eval_point
      (splitBoolPointEquiv (κ := κ) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l) (v, w)) =
      (eqTilde (fun i => if (v i == 1) then 1 else 0) fun i => eval_point ⟨i.val, by omega⟩) *
        (β.repr (MvPolynomial.eval (w : Fin ℓ' → L) (packMLE κ L K ℓ ℓ' h_l β t).val)) v •
          eqTilde (fun i => eval_point ⟨i.val + κ, by
            rw [h_l]
            omega⟩) (w : Fin ℓ' → L) := by
  unfold batchingCheckSummand
  simp only [splitBoolPointEquiv_apply, splitBoolPointEquiv_prefix, splitBoolPointEquiv_suffix]
  have hpoly :
      (fun i : Fin ℓ =>
        (((if h : i.val < κ then v ⟨i.val, h⟩ else w ⟨i.val - κ, by omega⟩) : Fin 2) : K)) =
      (fun i : Fin ℓ =>
        if h : i.val < κ then
          ((v ⟨i.val, h⟩ : Fin 2) : K)
        else
          ((w ⟨i.val - κ, by omega⟩ : Fin 2) : K)) := by
    funext i
    by_cases h : i.val < κ
    · simp [h]
    · simp [h]
  have hsuffix :
      (fun i : Fin ℓ' =>
        (((if h : i.val + κ < κ then v ⟨i.val + κ, h⟩ else w ⟨i.val + κ - κ, by omega⟩) :
          Fin 2) : L)) = (w : Fin ℓ' → L) := by
    funext i
    have hi : ¬ i.val + κ < κ := by
      omega
    simp [hi]
  have hprefix :
      (fun i : Fin κ =>
        if h : i.val < κ then
          v ⟨i.val, h⟩
        else
          w ⟨i.val - κ, by omega⟩) = v := by
    funext i
    simp
  rw [show MvPolynomial.eqPolynomial
      (fun i : Fin ℓ =>
        (((if h : i.val < κ then v ⟨i.val, h⟩ else w ⟨i.val - κ, by omega⟩) : Fin 2) : K)) =
      MvPolynomial.eqPolynomial
        (fun i : Fin ℓ =>
          if h : i.val < κ then
            ((v ⟨i.val, h⟩ : Fin 2) : K)
          else
            ((w ⟨i.val - κ, by omega⟩ : Fin 2) : K)) by
    rw [hpoly]]
  rw [show (fun i : Fin ℓ' =>
      (((if h : i.val + κ < κ then v ⟨i.val + κ, h⟩ else w ⟨i.val + κ - κ, by omega⟩) :
        Fin 2) : L)) = (w : Fin ℓ' → L) by
    exact hsuffix]
  rw [show (fun i : Fin κ =>
      if h : i.val < κ then
        v ⟨i.val, h⟩
      else
        w ⟨i.val - κ, by omega⟩) = v by
    exact hprefix]
  rw [eval₂_eqPolynomial_concat (κ := κ) (L := L) (K := K) (ℓ := ℓ) (ℓ' := ℓ')
    (h_l := h_l) (eval_point := eval_point) (v := v) (w := w)]
  rw [repr_packMLE_eval (κ := κ) (L := L) (K := K) (β := β) (ℓ := ℓ) (ℓ' := ℓ')
    (h_l := h_l) (t := t) (w := w) (v := v)]
  have hvL : (fun i => if (v i == 1) then (1 : L) else 0) = (v : Fin κ → L) := by
    funext i
    have hi : v i = 0 ∨ v i = 1 := by
      omega
    rcases hi with hi | hi
    · simp [hi]
    · simp [hi]
  rw [show (fun i => if (v i == 1) then (1 : L) else 0) = (v : Fin κ → L) by
    exact hvL]
  rw [Algebra.smul_def]
  let A : L := eqTilde (v : Fin κ → L) (fun i => eval_point ⟨i.val, by omega⟩)
  let B : L := eqTilde (fun i : Fin ℓ' => eval_point ⟨i.val + κ, by
    rw [h_l]
    omega⟩) (w : Fin ℓ' → L)
  let C : L := algebraMap K L (MvPolynomial.eval
    (fun i : Fin ℓ =>
      if h : i.val < κ then
        ((v ⟨i.val, h⟩ : Fin 2) : K)
      else
        ((w ⟨i.val - κ, by omega⟩ : Fin 2) : K))
    t.val)
  change (A * B) * C = A * (C * B)
  rw [mul_assoc]
  congr 1
  rw [mul_comm]

set_option maxHeartbeats 200000 in
lemma batching_check_correctness
    (t : MultilinearPoly K ℓ)
    (eval_point : Fin ℓ → L) :
  performCheckOriginalEvaluation κ L K β ℓ ℓ' h_l
    (t.val.aeval eval_point)
    (r := eval_point) (s_hat := embedded_MLP_eval κ (L := L) (K := K) ℓ ℓ' h_l
      (packMLE κ (L := L) (K := K) ℓ ℓ' h_l β t) eval_point) = true := by
  unfold performCheckOriginalEvaluation
  simp only [decide_eq_true_eq]
  simp_rw [decompose_embedded_MLP_eval_columns (κ := κ) (L := L) (K := K) (β := β) (ℓ := ℓ)
    (ℓ' := ℓ') (h_l := h_l) (t' := packMLE κ L K ℓ ℓ' h_l β t) (r := eval_point)]
  conv_lhs =>
    rw [← unpack_pack_id (κ := κ) (L := L) (K := K) (β := β) (ℓ := ℓ) (ℓ' := ℓ')
      (h_l := h_l) (t := t)]
  unfold unpackMLE
  rw [MvPolynomial.aeval_def]
  change MvPolynomial.eval₂ (algebraMap K L) eval_point
      (MvPolynomial.MLE
        (fun p : Fin ℓ → Fin 2 =>
          let v : Fin κ → Fin 2 := fun i => p ⟨i.val, by omega⟩
          let w : Fin ℓ' → Fin 2 := fun i => p ⟨i.val + κ, by
            rw [h_l]
            omega⟩
          (β.repr (MvPolynomial.eval (w : Fin ℓ' → L) (packMLE κ L K ℓ ℓ' h_l β t).val)) v)) = _
  rw [MvPolynomial.MLE]
  simp only [MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C]
  change ∑ p : Fin ℓ → Fin 2, batchingCheckSummand κ L K β ℓ ℓ' h_l t eval_point p = _
  have hsplit :
      ∑ p : Fin ℓ → Fin 2, batchingCheckSummand κ L K β ℓ ℓ' h_l t eval_point p =
        ∑ vw : (Fin κ → Fin 2) × (Fin ℓ' → Fin 2),
          batchingCheckSummand κ L K β ℓ ℓ' h_l t eval_point
            ((splitBoolPointEquiv (κ := κ) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l)) vw) := by
    symm
    exact Fintype.sum_equiv (splitBoolPointEquiv (κ := κ) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l))
      _ _ (fun vw => rfl)
  rw [hsplit]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro v hv
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  rw [batchingCheckSummand_split (κ := κ) (L := L) (K := K) (β := β) (ℓ := ℓ) (ℓ' := ℓ')
    (h_l := h_l) (t := t) (eval_point := eval_point) (v := v) (w := w)]

/-- Step 4a: For each `w ∈ {0,1}^{ℓ'}`, P decompose `eq̃(r_κ, ..., r_{ℓ-1}, w_0, ..., w_{ℓ'-1})`
`=: Σ_{u ∈ {0,1}^κ} A_{w, u} ⋅ β_u`.
P define the function
`A: w ↦ Σ_{u ∈ {0,1}^κ} eq̃(u_0, ..., u_{κ-1}, r''_0, ..., r''_{κ-1}) ⋅ A_{w, u}`
on `{0,1}^{ℓ'}`.
-/
def compute_A_func (original_r_eval_suffix : Fin ℓ' → L)
    (r''_batching : Fin κ → L) : ((Fin (ℓ') → (Fin 2)) → L) :=
  fun w =>
    -- Decompose eq̃(r_suffix, w) into K-basis coefficients A_{w,u}
    let w_as_L : Fin ℓ' → L := fun i => if w i == 1 then 1 else 0
    -- `eq̃(r_κ, ..., r_{ℓ-1}, w_0, ..., w_{ℓ'-1})`
    let eq_w: L := eqTilde original_r_eval_suffix w_as_L
    let coords_A_w_u: (Fin κ → Fin 2) →₀ K := β.repr eq_w
    -- Compute A(w) = Σ_{u ∈ {0,1}^κ} eq̃(u, r'') ⋅ A_{w,u}
    Finset.sum Finset.univ fun (u : Fin κ → Fin 2) =>
      let A_w_u : K := coords_A_w_u u
      let u_as_L : Fin κ → L := fun i => if u i == 1 then 1 else 0
      -- `eq̃(u_0, ..., u_{κ-1}, r''_0, ..., r''_{κ-1}) ⋅ A_{w, u}`
      let eq_u_r_batching : L := eqTilde u_as_L r''_batching
      A_w_u • eq_u_r_batching

/-- Step 4b: P writes `A(X_0, ..., X_{ℓ'-1})` for its multilinear extension of `A_func`. -/
def compute_A_MLE
  (original_r_eval_suffix : Fin ℓ' → L) (r''_batching : Fin κ → L) :
  MultilinearPoly L ℓ' :=
  let A_func := compute_A_func κ L K β ℓ' original_r_eval_suffix r''_batching
  let A_MLE: MultilinearPoly L ℓ' := ⟨MvPolynomial.MLE A_func, MLE_mem_restrictDegree A_func⟩
  A_MLE

def getEvaluationPointSuffix (r : Fin ℓ → L) : Fin ℓ' → L :=
  fun i => r ⟨i.val + κ, by { rw [h_l]; omega }⟩

/-- Ring-Switching multiplier parameter for sumcheck, using `A_MLE` as the multiplier. -/
def RingSwitching_SumcheckMultParam :
  SumcheckMultiplierParam L ℓ' (RingSwitchingBaseContext κ L K ℓ) :=
{ multpoly := fun ctx => -- This is supposed to be (r_κ, …, r_{ℓ-1})
    compute_A_MLE κ L K β ℓ' (original_r_eval_suffix :=
      getEvaluationPointSuffix κ L ℓ ℓ' h_l (r := ctx.t_eval_point))
      (r''_batching := ctx.r_batching)
}

/-- Step 5 (V): Compute `s₀ := Σ_{u ∈ {0,1}^κ} eqTilde(u, r'') ⋅ ŝ_u`,
where ŝ_u is the row components of ŝ. -/
def compute_s0 (s_hat : TensorAlgebra K L) (r''_batching : Fin κ → L) : L :=
  Finset.sum Finset.univ fun (u : Fin κ → Fin 2) =>
    let u_as_L : Fin κ → L := fun i => if (u i == 1) then 1 else 0
    (eqTilde u_as_L r''_batching)
      * (decompose_tensor_algebra_rows (L:=L) (K:=K) (β:=β) s_hat u)

/-- Compute the tensor `e := eq̃(φ₀(r_κ), ..., φ₀(r_{ℓ-1}), φ₁(r'_0), ..., φ₁(r'_{ℓ'-1}))` -/
def compute_final_eq_tensor (r : Fin ℓ → L) (r' : Fin ℓ' → L) : TensorAlgebra K L :=
  let φ₀_mapped_r_suffix : Fin ℓ' → TensorAlgebra K L := fun i =>
    φ₀ L K (r ⟨i.val + κ, by { rw [h_l]; omega }⟩)
  let φ₁_mapped_r': Fin ℓ' → (TensorAlgebra K L) := fun i => φ₁ L K (r' i)
  eqTilde φ₀_mapped_r_suffix φ₁_mapped_r'

/-- Decompose the final eq tensor `e := Σ_{u ∈ {0,1}^κ} eq̃(u, r'') ⨂ e_u`,
where e_u is the row components of e.
Then compute `Σ_{u ∈ {0,1}^κ} eq̃(u_0, ..., u_{κ-1}, r''_0, ..., r''_{κ-1}) ⋅ e_u`.
-/
def compute_final_eq_value (r_eval : Fin ℓ → L)
    (r'_challenges : Fin ℓ' → L) (r''_batching : Fin κ → L) : L :=
  let e_tensor := compute_final_eq_tensor κ L K ℓ ℓ' h_l r_eval r'_challenges
  let e_u : (Fin κ → Fin 2) → L := decompose_tensor_algebra_rows (L:=L) (K:=K) (β:=β) e_tensor
  Finset.sum Finset.univ fun (u : Fin κ → Fin 2) =>
    let u_as_L : Fin κ → L := fun i => if u i == 1 then 1 else 0
    let eq_u_r_batching : L := -- `eq̃(u_0, ..., u_{κ-1}, r''_0, ..., r''_{κ-1})`
      eqTilde u_as_L r''_batching
    eq_u_r_batching * (e_u u)

private lemma eqPolynomial_eq_MLE (r : Fin ℓ' → L) :
    MvPolynomial.MLE (fun w : Fin ℓ' → Fin 2 => eqTilde r (w : Fin ℓ' → L)) =
      (MvPolynomial.eqPolynomial r : MvPolynomial (Fin ℓ') L) := by
  change MvPolynomial.MLE ((MvPolynomial.eqPolynomial r).toEvalsZeroOne) =
    (MvPolynomial.eqPolynomial r : MvPolynomial (Fin ℓ') L)
  exact
    (MvPolynomial.is_multilinear_iff_eq_evals_zeroOne
      (p := (MvPolynomial.eqPolynomial r : MvPolynomial (Fin ℓ') L))).mp
      (MvPolynomial.eqPolynomial_mem_restrictDegree r)

private lemma map_eqPolynomial_φ₀ (r : Fin ℓ' → L) :
    MvPolynomial.map (φ₀ L K) (MvPolynomial.eqPolynomial r : MvPolynomial (Fin ℓ') L) =
      (MvPolynomial.eqPolynomial (fun i => φ₀ L K (r i)) :
        MvPolynomial (Fin ℓ') (TensorAlgebra K L)) := by
  rw [MvPolynomial.eqPolynomial_expanded, MvPolynomial.eqPolynomial_expanded]
  simp

private lemma eval₂_eqPolynomial_zeroOne_φ₁
    (r' : Fin ℓ' → L) (w : Fin ℓ' → Fin 2) :
    MvPolynomial.eval₂ (φ₀ L K) (fun i => φ₁ L K (r' i))
      (MvPolynomial.eqPolynomial (w : Fin ℓ' → L)) =
    φ₁ L K (eqTilde (w : Fin ℓ' → L) r') := by
  unfold Binius.BinaryBasefold.eqTilde
  calc
    MvPolynomial.eval₂ (φ₀ L K) (fun i => φ₁ L K (r' i))
        (MvPolynomial.eqPolynomial (w : Fin ℓ' → L)) =
      MvPolynomial.eval (fun i => φ₁ L K (r' i))
        (MvPolynomial.map (φ₀ L K) (MvPolynomial.eqPolynomial (w : Fin ℓ' → L))) := by
          rw [MvPolynomial.eval_map]
    _ = MvPolynomial.eval (fun i => φ₁ L K (r' i))
        (MvPolynomial.map (φ₁ L K) (MvPolynomial.eqPolynomial (w : Fin ℓ' → L))) := by
          apply congrArg (MvPolynomial.eval (fun i => φ₁ L K (r' i)))
          rw [MvPolynomial.eqPolynomial_zeroOne (r := w)]
          simp_rw [map_prod]
          apply Finset.prod_congr rfl
          intro i hi
          by_cases h : w i = 0
          · simp [h, φ₀, φ₁]
          · have h1 : w i = 1 := by omega
            simp [h, h1, φ₀, φ₁]
    _ = MvPolynomial.eval₂ (φ₁ L K) (fun i => φ₁ L K (r' i))
        (MvPolynomial.eqPolynomial (w : Fin ℓ' → L)) := by
          rw [MvPolynomial.eval_map]
    _ = φ₁ L K (MvPolynomial.eval r' (MvPolynomial.eqPolynomial (w : Fin ℓ' → L))) := by
          symm
          exact MvPolynomial.eval₂_comp (f := φ₁ L K) (g := r')
            (p := MvPolynomial.eqPolynomial (w : Fin ℓ' → L))

private lemma compute_final_eq_tensor_eq_sum
    (r_eval : Fin ℓ → L)
    (r'_challenges : Fin ℓ' → L) :
    compute_final_eq_tensor κ L K ℓ ℓ' h_l r_eval r'_challenges =
      ∑ w : Fin ℓ' → Fin 2,
        φ₀ L K (eqTilde (getEvaluationPointSuffix κ L ℓ ℓ' h_l r_eval) (w : Fin ℓ' → L)) *
          φ₁ L K (eqTilde (w : Fin ℓ' → L) r'_challenges) := by
  let r_suffix := getEvaluationPointSuffix κ L ℓ ℓ' h_l r_eval
  unfold compute_final_eq_tensor Binius.BinaryBasefold.eqTilde
  change MvPolynomial.eval (fun i => φ₁ L K (r'_challenges i))
      (MvPolynomial.eqPolynomial (fun i => φ₀ L K (r_suffix i))) = _
  rw [show (MvPolynomial.eqPolynomial (fun i => φ₀ L K (r_suffix i)) :
      MvPolynomial (Fin ℓ') (TensorAlgebra K L)) =
      MvPolynomial.map (φ₀ L K) (MvPolynomial.eqPolynomial r_suffix) by
    symm
    exact map_eqPolynomial_φ₀ (L := L) (K := K) (r := r_suffix)]
  rw [MvPolynomial.eval_map]
  calc
    MvPolynomial.eval₂ (φ₀ L K) (fun i => φ₁ L K (r'_challenges i))
        (MvPolynomial.eqPolynomial r_suffix)
      =
        MvPolynomial.eval₂ (φ₀ L K) (fun i => φ₁ L K (r'_challenges i))
          (MvPolynomial.MLE (fun w : Fin ℓ' → Fin 2 => eqTilde r_suffix (w : Fin ℓ' → L))) := by
            rw [eqPolynomial_eq_MLE (L := L) (ℓ' := ℓ') (r := r_suffix)]
    _ = ∑ w : Fin ℓ' → Fin 2,
          φ₀ L K (eqTilde r_suffix (w : Fin ℓ' → L)) *
            φ₁ L K (eqTilde (w : Fin ℓ' → L) r'_challenges) := by
            unfold MvPolynomial.MLE
            simp only [MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C]
            apply Finset.sum_congr rfl
            intro w hw
            rw [eval₂_eqPolynomial_zeroOne_φ₁ (L := L) (K := K) (ℓ' := ℓ')
              (r' := r'_challenges) (w := w)]
            rw [mul_comm]

private lemma decompose_compute_final_eq_tensor_rows
    (r_eval : Fin ℓ → L)
    (r'_challenges : Fin ℓ' → L)
    (u : Fin κ → Fin 2) :
    decompose_tensor_algebra_rows (L := L) (K := K) (β := β)
      (compute_final_eq_tensor κ L K ℓ ℓ' h_l r_eval r'_challenges) u =
      ∑ w : Fin ℓ' → Fin 2,
        (β.repr (eqTilde (getEvaluationPointSuffix κ L ℓ ℓ' h_l r_eval)
          (w : Fin ℓ' → L)) u) • eqTilde (w : Fin ℓ' → L) r'_challenges := by
  letI rightAlgebra : Algebra L (TensorAlgebra K L) := by
    exact Algebra.TensorProduct.rightAlgebra
  letI rightModule : Module L (TensorAlgebra K L) := rightAlgebra.toModule
  rw [compute_final_eq_tensor_eq_sum (κ := κ) (L := L) (K := K) (ℓ := ℓ) (ℓ' := ℓ')
    (h_l := h_l) (r_eval := r_eval) (r'_challenges := r'_challenges)]
  change ((Basis.baseChangeRight (b := β) (Right := L)).repr (∑ w : Fin ℓ' → Fin 2,
    φ₀ L K
        (eqTilde (getEvaluationPointSuffix κ L ℓ ℓ' h_l r_eval) (w : Fin ℓ' → L)) *
      φ₁ L K (eqTilde (w : Fin ℓ' → L) r'_challenges))) u = _
  rw [map_sum, Finset.sum_apply']
  apply Finset.sum_congr rfl
  intro w hw
  rw [φ₀, φ₁]
  change ((Basis.baseChangeRight (b := β) (Right := L)).repr
      (((eqTilde (getEvaluationPointSuffix κ L ℓ ℓ' h_l r_eval) (w : Fin ℓ' → L)) ⊗ₜ[K] (1 : L)) *
        ((1 : L) ⊗ₜ[K] eqTilde (w : Fin ℓ' → L) r'_challenges))) u = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [Basis.baseChangeRight_repr_tmul]

private lemma zeroOnePoint_eq_coe {n : ℕ} (x : Fin n → Fin 2) :
    (fun i => if x i == 1 then (1 : L) else 0) = (x : Fin n → L) := by
  funext i
  have hi : x i = 0 ∨ x i = 1 := by omega
  rcases hi with hi | hi
  · simp [hi]
  · simp [hi]

private lemma compute_A_MLE_eval_term_eq
    (r_eval : Fin ℓ → L)
    (r'_challenges : Fin ℓ' → L)
    (r''_batching : Fin κ → L)
    (w : Fin ℓ' → Fin 2) :
    MvPolynomial.eval r'_challenges (MvPolynomial.eqPolynomial (w : Fin ℓ' → L)) *
      ∑ u : Fin κ → Fin 2,
        (β.repr
            (eqTilde
              (getEvaluationPointSuffix κ L ℓ ℓ' h_l r_eval)
              (fun i => if w i == 1 then 1 else 0))
            u) •
          eqTilde (fun i => if u i == 1 then 1 else 0) r''_batching
      =
    eqTilde (w : Fin ℓ' → L) r'_challenges *
      ∑ u : Fin κ → Fin 2,
        (β.repr
            (eqTilde
              (getEvaluationPointSuffix κ L ℓ ℓ' h_l r_eval)
              (w : Fin ℓ' → L))
            u) •
          eqTilde (u : Fin κ → L) r''_batching := by
  change eqTilde (w : Fin ℓ' → L) r'_challenges *
      ∑ u : Fin κ → Fin 2,
        (β.repr
            (eqTilde
              (getEvaluationPointSuffix κ L ℓ ℓ' h_l r_eval)
              (fun i => if w i == 1 then 1 else 0))
            u) •
          eqTilde (fun i => if u i == 1 then 1 else 0) r''_batching = _
  rw [zeroOnePoint_eq_coe (L := L) (x := w)]
  have hsum :
      ∑ u : Fin κ → Fin 2,
        (β.repr
            (eqTilde
              (getEvaluationPointSuffix κ L ℓ ℓ' h_l r_eval)
              (w : Fin ℓ' → L))
            u) •
          eqTilde (fun i => if u i == 1 then 1 else 0) r''_batching
      =
      ∑ u : Fin κ → Fin 2,
        (β.repr
            (eqTilde
              (getEvaluationPointSuffix κ L ℓ ℓ' h_l r_eval)
              (w : Fin ℓ' → L))
            u) •
          eqTilde (u : Fin κ → L) r''_batching := by
        apply Finset.sum_congr rfl
        intro u hu
        rw [zeroOnePoint_eq_coe (L := L) (x := u)]
  rw [hsum]

/-- **Key Identity**: Evaluating `compute_A_MLE` at any point `r'_challenges` equals
`compute_final_eq_value` at that point.

This lemma connects the MLE-based definition of the multiplier polynomial with the
direct tensor-based computation used in the final sumcheck verification.
`MLE(f).eval(x) = f(x)` when `x` is a boolean hypercube point.
-/
lemma compute_A_MLE_eval_eq_final_eq_value
    (r_eval : Fin ℓ → L)
    (r'_challenges : Fin ℓ' → L)
    (r''_batching : Fin κ → L) :
    (compute_A_MLE κ L K β ℓ' (getEvaluationPointSuffix κ L ℓ ℓ' h_l r_eval)
      r''_batching).val.eval r'_challenges =
    compute_final_eq_value κ L K β ℓ ℓ' h_l r_eval r'_challenges r''_batching := by
  simp only [compute_A_MLE, compute_final_eq_value, compute_A_func, MvPolynomial.MLE,
    MvPolynomial.eval_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C]
  calc
    ∑ w : Fin ℓ' → Fin 2,
        MvPolynomial.eval r'_challenges (MvPolynomial.eqPolynomial (w : Fin ℓ' → L)) *
          ∑ u : Fin κ → Fin 2,
            (β.repr
                (eqTilde
                  (getEvaluationPointSuffix κ L ℓ ℓ' h_l r_eval)
                  (fun i => if w i == 1 then 1 else 0))
                u) •
              eqTilde (fun i => if u i == 1 then 1 else 0) r''_batching
      = ∑ w : Fin ℓ' → Fin 2,
          eqTilde (w : Fin ℓ' → L) r'_challenges *
            ∑ u : Fin κ → Fin 2,
              (β.repr
                  (eqTilde
                    (getEvaluationPointSuffix κ L ℓ ℓ' h_l r_eval)
                    (w : Fin ℓ' → L))
                  u) •
                eqTilde (u : Fin κ → L) r''_batching := by
          apply Finset.sum_congr rfl
          intro w hw
          exact compute_A_MLE_eval_term_eq (κ := κ) (L := L) (K := K) (β := β) (ℓ := ℓ)
            (ℓ' := ℓ') (h_l := h_l) (r_eval := r_eval) (r'_challenges := r'_challenges)
            (r''_batching := r''_batching) (w := w)
    _ = ∑ u : Fin κ → Fin 2,
          eqTilde (u : Fin κ → L) r''_batching *
            ∑ w : Fin ℓ' → Fin 2,
              (β.repr
                  (eqTilde
                    (getEvaluationPointSuffix κ L ℓ ℓ' h_l r_eval)
                    (w : Fin ℓ' → L))
                  u) •
                eqTilde (w : Fin ℓ' → L) r'_challenges := by
          calc
            _ = ∑ w : Fin ℓ' → Fin 2,
                ∑ u : Fin κ → Fin 2,
                  eqTilde (w : Fin ℓ' → L) r'_challenges *
                    ((β.repr
                        (eqTilde
                          (getEvaluationPointSuffix κ L ℓ ℓ' h_l r_eval)
                          (w : Fin ℓ' → L))
                        u) •
                      eqTilde (u : Fin κ → L) r''_batching) := by
                  apply Finset.sum_congr rfl
                  intro w hw
                  rw [Finset.mul_sum]
            _ = ∑ u : Fin κ → Fin 2,
                ∑ w : Fin ℓ' → Fin 2,
                  eqTilde (u : Fin κ → L) r''_batching *
                    ((β.repr
                        (eqTilde
                          (getEvaluationPointSuffix κ L ℓ ℓ' h_l r_eval)
                          (w : Fin ℓ' → L))
                        u) •
                      eqTilde (w : Fin ℓ' → L) r'_challenges) := by
                  rw [Finset.sum_comm]
                  apply Finset.sum_congr rfl
                  intro u hu
                  apply Finset.sum_congr rfl
                  intro w hw
                  rw [Algebra.smul_def, Algebra.smul_def]
                  ring_nf
            _ = _ := by
                  apply Finset.sum_congr rfl
                  intro u hu
                  rw [Finset.mul_sum]
    _ = ∑ u : Fin κ → Fin 2,
          eqTilde (u : Fin κ → L) r''_batching *
            decompose_tensor_algebra_rows (L := L) (K := K) (β := β)
              (compute_final_eq_tensor κ L K ℓ ℓ' h_l r_eval r'_challenges) u := by
          apply Finset.sum_congr rfl
          intro u hu
          rw [decompose_compute_final_eq_tensor_rows (κ := κ) (L := L) (K := K) (β := β)
            (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l) (r_eval := r_eval)
            (r'_challenges := r'_challenges) (u := u)]
    _ = ∑ u : Fin κ → Fin 2,
          eqTilde (fun i => if u i == 1 then 1 else 0) r''_batching *
            decompose_tensor_algebra_rows (L := L) (K := K) (β := β)
              (compute_final_eq_tensor κ L K ℓ ℓ' h_l r_eval r'_challenges) u := by
          apply Finset.sum_congr rfl
          intro u hu
          rw [zeroOnePoint_eq_coe (L := L) (x := u)]

/-- This condition ensures that the witness polynomial `H` has the
correct structure `A(...) * t'(...)` -/
def witnessStructuralInvariant {i : Fin (ℓ' + 1)}
    (stmt : Statement (L := L) (RingSwitchingBaseContext κ L K ℓ) i)
    (wit : SumcheckWitness L ℓ' i) : Prop :=
  wit.H = projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := wit.t') (m :=
    (RingSwitching_SumcheckMultParam κ L K β ℓ ℓ' h_l).multpoly stmt.ctx)
    (i := i) (challenges := stmt.challenges)

def masterKStateProp (aOStmtIn : AbstractOStmtIn L ℓ') (stmtIdx : Fin (ℓ' + 1))
    (stmt : Statement (L := L) (RingSwitchingBaseContext κ L K ℓ) stmtIdx)
    (oStmt : ∀ j, aOStmtIn.OStmtIn j)
    (wit : SumcheckWitness L ℓ' stmtIdx)
    (localChecks : Prop) : Prop :=
  localChecks
  -- Should witnessStructuralInvariant be part of localChecks?
  ∧ witnessStructuralInvariant κ L K β ℓ ℓ' h_l stmt wit
  ∧ aOStmtIn.initialCompatibility ⟨wit.t', oStmt⟩

def masterStrictKStateProp (aOStmtIn : AbstractOStmtIn L ℓ') (stmtIdx : Fin (ℓ' + 1))
    (stmt : Statement (L := L) (RingSwitchingBaseContext κ L K ℓ) stmtIdx)
    (oStmt : ∀ j, aOStmtIn.OStmtIn j)
    (wit : SumcheckWitness L ℓ' stmtIdx)
    (localChecks : Prop) : Prop :=
  localChecks
  ∧ witnessStructuralInvariant κ L K β ℓ ℓ' h_l stmt wit
  ∧ aOStmtIn.strictInitialCompatibility ⟨wit.t', oStmt⟩

def sumcheckRoundRelationProp (aOStmtIn : AbstractOStmtIn L ℓ') (i : Fin (ℓ' + 1))
    (stmt : Statement (L := L) (RingSwitchingBaseContext κ L K ℓ) i)
    (oStmt : ∀ j, aOStmtIn.OStmtIn j)
    (wit : SumcheckWitness L ℓ' i) : Prop :=
  masterKStateProp κ L K β ℓ ℓ' h_l aOStmtIn i stmt oStmt wit
    (localChecks := sumcheckConsistencyProp (𝓑:=𝓑) stmt.sumcheck_target wit.H)

/-- Input relation for single round: proper sumcheck statement -/
def sumcheckRoundRelation (aOStmtIn : AbstractOStmtIn L ℓ') (i : Fin (ℓ' + 1)) :
  Set (((Statement (L := L) (RingSwitchingBaseContext κ L K ℓ) i) ×
    (∀ j, aOStmtIn.OStmtIn j)) × SumcheckWitness L ℓ' i) :=
  { ((stmt, oStmt), wit) | sumcheckRoundRelationProp κ L K β ℓ ℓ' h_l (𝓑:=𝓑)
    aOStmtIn i stmt oStmt wit }

def strictSumcheckRoundRelationProp (aOStmtIn : AbstractOStmtIn L ℓ') (i : Fin (ℓ' + 1))
    (stmt : Statement (L := L) (RingSwitchingBaseContext κ L K ℓ) i)
    (oStmt : ∀ j, aOStmtIn.OStmtIn j)
    (wit : SumcheckWitness L ℓ' i) : Prop :=
  masterStrictKStateProp κ L K β ℓ ℓ' h_l aOStmtIn i stmt oStmt wit
    (localChecks := sumcheckConsistencyProp (𝓑:=𝓑) stmt.sumcheck_target wit.H)

/-- Strict round relation for completeness proofs. -/
def strictSumcheckRoundRelation (aOStmtIn : AbstractOStmtIn L ℓ') (i : Fin (ℓ' + 1)) :
  Set (((Statement (L := L) (RingSwitchingBaseContext κ L K ℓ) i) ×
    (∀ j, aOStmtIn.OStmtIn j)) × SumcheckWitness L ℓ' i) :=
  { ((stmt, oStmt), wit) | strictSumcheckRoundRelationProp κ L K β ℓ ℓ' h_l (𝓑:=𝓑)
    aOStmtIn i stmt oStmt wit }

omit [Fintype L] [DecidableEq L] [CharP L 2] [SampleableType L] [Fintype K] [DecidableEq K]
  [NeZero ℓ] [NeZero ℓ'] in
lemma strictSumcheckRoundRelation_subset_sumcheckRoundRelation (aOStmtIn : AbstractOStmtIn L ℓ')
    (i : Fin (ℓ' + 1)) :
    strictSumcheckRoundRelation κ L K β ℓ ℓ' h_l (𝓑:=𝓑) aOStmtIn i ⊆
      sumcheckRoundRelation κ L K β ℓ ℓ' h_l (𝓑:=𝓑) aOStmtIn i := by
  intro input h_input
  rcases input with ⟨⟨stmt, oStmt⟩, wit⟩
  rcases h_input with ⟨h_local, h_struct, h_strict_compat⟩
  exact ⟨h_local, h_struct,
    aOStmtIn.strictInitialCompatibility_implies_initialCompatibility oStmt wit.t'
      h_strict_compat⟩

private def castEmb : Fin 2 ↪ L := ⟨fun b => (b : L), by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp at h <;> simp [h]⟩

private lemma castEmb_eq_of_B01 [h_B01 : Fact (𝓑 0 = 0 ∧ 𝓑 1 = 1)] :
    𝓑 = castEmb (L := L) := by
  ext b
  fin_cases b <;> simp [castEmb, h_B01.out.1, h_B01.out.2]

private lemma piFinset_castEmb_eq_image :
    Fintype.piFinset (fun _ : Fin ℓ' =>
      Finset.map (castEmb (L := L)) (Finset.univ : Finset (Fin 2))) =
      (Finset.univ : Finset (Fin ℓ' → Fin 2)).image
        (fun b : Fin ℓ' → Fin 2 => fun i => castEmb (L := L) (b i)) := by
  have h_arg :
      (fun _ : Fin ℓ' => Finset.map (castEmb (L := L)) (Finset.univ : Finset (Fin 2))) =
        (fun _ : Fin ℓ' => (Finset.univ : Finset (Fin 2)).image (castEmb (L := L))) := by
    funext i
    rw [Finset.map_eq_image]
  have h_pi' :=
    Fintype.piFinset_image
      (f := fun _ : Fin ℓ' => castEmb (L := L))
      (s := fun _ : Fin ℓ' => (Finset.univ : Finset (Fin 2)))
  rw [h_arg]
  rw [Fintype.piFinset_univ] at h_pi'
  exact h_pi'

private lemma fixFirstVariablesOfMQP_zero_eq
    (H : MvPolynomial (Fin ℓ') L) :
    fixFirstVariablesOfMQP (L := L) (ℓ := ℓ') (v := (0 : Fin (ℓ' + 1))) H
      (challenges := Fin.elim0) = H := by
  simpa [MvPolynomial.bind₁_X_left] using
    (fixFirstVariablesOfMQP_eq_bind₁ (L := L) (ℓ := ℓ') (v := (0 : Fin (ℓ' + 1)))
      (poly := H) (challenges := Fin.elim0))

private lemma projectToMidSumcheckPoly_zero_eq_computeInitial
    (t' : MultilinearPoly L ℓ')
    (m : MultilinearPoly L ℓ') :
    projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := t')
      (m := m) (i := (0 : Fin (ℓ' + 1))) (challenges := Fin.elim0) =
    computeInitialSumcheckPoly (L := L) (ℓ := ℓ') t' m := by
  have h_fix0 :
      fixFirstVariablesOfMQP (L := L) (ℓ := ℓ')
        (v := (0 : Fin (ℓ' + 1)))
        (H := (computeInitialSumcheckPoly (L := L) (ℓ := ℓ') t' m).val)
        (challenges := Fin.elim0) =
      (computeInitialSumcheckPoly (L := L) (ℓ := ℓ') t' m).val :=
    fixFirstVariablesOfMQP_zero_eq (L := L)
      (H := (computeInitialSumcheckPoly (L := L) (ℓ := ℓ') t' m).val)
  apply Subtype.ext
  unfold projectToMidSumcheckPoly
  dsimp
  exact h_fix0

set_option maxHeartbeats 200000 in
-- Expand the honest tensor row decomposition and identify the batching multiplier at zero-one points.
private lemma compute_s0_embedded_MLP_eval_eq_sum
    (t' : MultilinearPoly L ℓ')
    (r_eval : Fin ℓ → L)
    (r''_batching : Fin κ → L) :
    compute_s0 κ L K β
      (embedded_MLP_eval κ L K ℓ ℓ' h_l t' r_eval) r''_batching =
    ∑ w : Fin ℓ' → Fin 2,
      MvPolynomial.eval (w : Fin ℓ' → L)
          (compute_A_MLE κ L K β ℓ'
            (getEvaluationPointSuffix κ L ℓ ℓ' h_l r_eval) r''_batching).val *
        MvPolynomial.eval (w : Fin ℓ' → L) t'.val := by
  rw [compute_s0]
  simp_rw [decompose_embedded_MLP_eval_rows (κ := κ) (L := L) (K := K) (β := β)
    (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l) (t' := t') (r := r_eval)]
  calc
    ∑ u : Fin κ → Fin 2,
        eqTilde (fun i => if u i == 1 then 1 else 0) r''_batching *
          ∑ w : Fin ℓ' → Fin 2,
            (β.repr
                (eqTilde (getEvaluationPointSuffix κ L ℓ ℓ' h_l r_eval)
                  (w : Fin ℓ' → L)) u) •
              MvPolynomial.eval (w : Fin ℓ' → L) t'.val
      = ∑ w : Fin ℓ' → Fin 2,
          ∑ u : Fin κ → Fin 2,
            eqTilde (fun i => if u i == 1 then 1 else 0) r''_batching *
              ((β.repr
                  (eqTilde (getEvaluationPointSuffix κ L ℓ ℓ' h_l r_eval)
                    (w : Fin ℓ' → L)) u) •
                MvPolynomial.eval (w : Fin ℓ' → L) t'.val) := by
            calc
              _ = ∑ u : Fin κ → Fin 2,
                  ∑ w : Fin ℓ' → Fin 2,
                    eqTilde (fun i => if u i == 1 then 1 else 0) r''_batching *
                      ((β.repr
                          (eqTilde (getEvaluationPointSuffix κ L ℓ ℓ' h_l r_eval)
                            (w : Fin ℓ' → L)) u) •
                        MvPolynomial.eval (w : Fin ℓ' → L) t'.val) := by
                    apply Finset.sum_congr rfl
                    intro u hu
                    rw [Finset.mul_sum]
              _ = _ := by
                    rw [Finset.sum_comm]
    _ = ∑ w : Fin ℓ' → Fin 2,
          (∑ u : Fin κ → Fin 2,
            (β.repr
                (eqTilde (getEvaluationPointSuffix κ L ℓ ℓ' h_l r_eval)
                  (w : Fin ℓ' → L)) u) •
              eqTilde (u : Fin κ → L) r''_batching) *
            MvPolynomial.eval (w : Fin ℓ' → L) t'.val := by
            apply Finset.sum_congr rfl
            intro w hw
            calc
              ∑ u : Fin κ → Fin 2,
                  eqTilde (fun i => if u i == 1 then 1 else 0) r''_batching *
                    ((β.repr
                        (eqTilde (getEvaluationPointSuffix κ L ℓ ℓ' h_l r_eval)
                          (w : Fin ℓ' → L)) u) •
                      MvPolynomial.eval (w : Fin ℓ' → L) t'.val)
                = ∑ u : Fin κ → Fin 2,
                    ((β.repr
                        (eqTilde (getEvaluationPointSuffix κ L ℓ ℓ' h_l r_eval)
                          (w : Fin ℓ' → L)) u) •
                      eqTilde (u : Fin κ → L) r''_batching) *
                        MvPolynomial.eval (w : Fin ℓ' → L) t'.val := by
                      apply Finset.sum_congr rfl
                      intro u hu
                      rw [zeroOnePoint_eq_coe (L := L) (x := u)]
                      rw [Algebra.smul_def, Algebra.smul_def]
                      ring_nf
              _ = _ := by
                    rw [← Finset.sum_mul]
    _ = ∑ w : Fin ℓ' → Fin 2,
          MvPolynomial.eval (w : Fin ℓ' → L)
              (compute_A_MLE κ L K β ℓ'
                (getEvaluationPointSuffix κ L ℓ ℓ' h_l r_eval) r''_batching).val *
            MvPolynomial.eval (w : Fin ℓ' → L) t'.val := by
            apply Finset.sum_congr rfl
            intro w hw
            have h_mEq_w :
                MvPolynomial.eval (w : Fin ℓ' → L)
                    (compute_A_MLE κ L K β ℓ'
                      (getEvaluationPointSuffix κ L ℓ ℓ' h_l r_eval) r''_batching).val =
                  ∑ u : Fin κ → Fin 2,
                    (β.repr
                        (eqTilde (getEvaluationPointSuffix κ L ℓ ℓ' h_l r_eval)
                          (w : Fin ℓ' → L)) u) •
                      eqTilde (u : Fin κ → L) r''_batching := by
                  simp only [compute_A_MLE, MvPolynomial.MLE_eval_zeroOne]
                  unfold compute_A_func
                  dsimp
                  rw [zeroOnePoint_eq_coe (L := L) (x := w)]
                  apply Finset.sum_congr rfl
                  intro u hu
                  rw [zeroOnePoint_eq_coe (L := L) (x := u)]
            rw [h_mEq_w]

/-- **Consistency of the Batching Target**

This lemma proves that the batched target value `s₀` computed by the verifier
matches the sum over the hypercube of the honestly computed batched polynomial `H`.
-/
lemma batching_target_consistency
    [h_B01 : Fact (𝓑 0 = 0 ∧ 𝓑 1 = 1)]
    (t' : MultilinearPoly L ℓ')
    (msg0 : TensorAlgebra K L)
    (ctx : RingSwitchingBaseContext κ L K ℓ)
    (h_msg0 : msg0 = embedded_MLP_eval κ L K ℓ ℓ' h_l t' ctx.t_eval_point) :
  let s₀ := compute_s0 κ L K β msg0 ctx.r_batching
  let H := projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := t')
    (m := (RingSwitching_SumcheckMultParam κ L K β ℓ ℓ' h_l).multpoly ctx) (i := 0)
    (challenges := Fin.elim0)
  sumcheckConsistencyProp (𝓑:=𝓑) s₀ H := by
  classical
  rw [h_msg0]
  have h_Beq : 𝓑 = castEmb (L := L) := castEmb_eq_of_B01 (L := L) (𝓑 := 𝓑)
  subst h_Beq
  have h_H0 :
      projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := t')
        (m := (RingSwitching_SumcheckMultParam κ L K β ℓ ℓ' h_l).multpoly ctx)
        (i := (0 : Fin (ℓ' + 1))) (challenges := Fin.elim0) =
      computeInitialSumcheckPoly (L := L) (ℓ := ℓ') t'
        ((RingSwitching_SumcheckMultParam κ L K β ℓ ℓ' h_l).multpoly ctx) :=
    projectToMidSumcheckPoly_zero_eq_computeInitial (L := L)
      (t' := t') (m := (RingSwitching_SumcheckMultParam κ L K β ℓ ℓ' h_l).multpoly ctx)
  change compute_s0 κ L K β
      (embedded_MLP_eval κ L K ℓ ℓ' h_l t' ctx.t_eval_point) ctx.r_batching =
    ∑ x ∈ Fintype.piFinset (fun _ : Fin ℓ' =>
      Finset.map (castEmb (L := L)) (Finset.univ : Finset (Fin 2))),
      MvPolynomial.eval x
        (projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := t')
          (m := (RingSwitching_SumcheckMultParam κ L K β ℓ ℓ' h_l).multpoly ctx)
          (i := (0 : Fin (ℓ' + 1))) (challenges := Fin.elim0)).val
  rw [h_H0]
  change compute_s0 κ L K β
      (embedded_MLP_eval κ L K ℓ ℓ' h_l t' ctx.t_eval_point) ctx.r_batching =
    ∑ x ∈ Fintype.piFinset (fun _ : Fin ℓ' =>
      Finset.map (castEmb (L := L)) (Finset.univ : Finset (Fin 2))),
      MvPolynomial.eval x
        (((RingSwitching_SumcheckMultParam κ L K β ℓ ℓ' h_l).multpoly ctx).val * t'.val)
  rw [piFinset_castEmb_eq_image (L := L) (ℓ' := ℓ'), Finset.sum_image]
  · simp only [MvPolynomial.eval_mul]
    simpa [castEmb] using
      (compute_s0_embedded_MLP_eval_eq_sum (κ := κ) (L := L) (K := K) (β := β)
        (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l) (t' := t') (r_eval := ctx.t_eval_point)
        (r''_batching := ctx.r_batching))
  · intro x hx y hy hxy
    funext i
    apply (castEmb (L := L)).injective
    exact congrFun hxy i

end Relations

end Binius.RingSwitching
