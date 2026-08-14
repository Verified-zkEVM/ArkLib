/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.Data.MvPolynomial.Multilinear
import ArkLib.OracleReduction.Basic
import ArkLib.OracleReduction.Security.RoundByRound
import CompPoly.Fields.Binary.Tower.TensorAlgebra
import ArkLib.ProofSystem.RingSwitching.Packing.Profile
import ArkLib.ProofSystem.Sumcheck.Structured
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

namespace RingSwitching

open OracleSpec OracleComp ProtocolSpec Finset Polynomial MvPolynomial TensorProduct
open scoped NNReal
open Sumcheck.Structured

/- This section defines generic preliminaries for the ring-switching protocol. -/
section Preliminaries

variable (κ : ℕ) [NeZero κ]
variable (L : Type) [CommRing L] [Fintype L] [DecidableEq L]
variable (K : Type) [CommRing K] [Fintype K] [DecidableEq K]
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
abbrev TensorAlgebra (K L : Type*) [CommRing K] [CommRing L] [Algebra K L] := L ⊗[K] L

/--
Column embedding φ₀: L → A as a ring homomorphism.
φ₀(α) = α ⊗ 1, operates on columns.
-/
def φ₀ (L K : Type*) [CommRing K] [CommRing L] [Algebra K L] : L →+* TensorAlgebra K L where
  toFun α := α ⊗ₜ[K] (1 : L)
  map_one' := rfl
  map_mul' α β := by simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  map_zero' := by simp only [zero_tmul]
  map_add' α β := by simp only [add_tmul]

/--
Row embedding φ₁: L → A as a ring homomorphism.
φ₁(α) = 1 ⊗ α, operates on rows.
-/
def φ₁ (L K : Type*) [CommRing K] [CommRing L] [Algebra K L] : L →+* TensorAlgebra K L where
  toFun α := (1 : L) ⊗ₜ[K] α
  map_one' := by rfl
  map_mul' α β := by
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  map_zero' := by simp only [tmul_zero]
  map_add' α β := by simp only [tmul_add]

open Module
/-- Decompose `ŝ` into row components `(ŝ =: Σ_{u ∈ {0,1}^κ} β_u ⊗ ŝ_u)`.
This views `L ⊗ L` as a module over `L` (left action)
and finds the coordinates of `ŝ` with respect to the basis lifted from `β`. -/
def decompose_tensor_algebra_rows {σ : Type*} (β : Basis σ K L)
  (s_hat : TensorAlgebra K L) : σ → L :=
  fun u =>
    (β.baseChange L).repr s_hat u

/-- Decompose `ŝ` into column components `(ŝ =: Σ_{v ∈ {0,1}^κ} ŝ_v ⊗ β_v)`.
This views `L ⊗ L` as a module over `L` (right action)
and finds the coordinates of `ŝ` with respect to the basis lifted from `β`. -/
def decompose_tensor_algebra_columns {σ : Type*} (β : Basis σ K L) (s_hat : L ⊗[K] L) : σ → L :=
  fun v => by
    let b := Basis.baseChangeRight (b:=β) (Right:=L)
    letI rightAlgebra : Algebra L (L ⊗[K] L) := by
      exact Algebra.TensorProduct.rightAlgebra
    letI rightModule : Module L (L ⊗[K] L) := rightAlgebra.toModule
    exact b.repr s_hat v
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

/-- `unpackMLE ∘ packMLE = id`: unpacking a packed polynomial recovers the original.
Basis-generic (our HEAD ground-truth, ported into Alex's frame with `β` explicit). -/
private lemma unpack_pack_id [IsDomain K] (β : Basis (Fin κ → Fin 2) K L)
    (t : MultilinearPoly K ℓ) :
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

/-- Bijection `{0,1}^κ × {0,1}^{ℓ'} ≃ {0,1}^ℓ` (combinatorial; ported verbatim from HEAD). -/
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

/--
**Component-wise `φ₁` embedding**.
Takes a polynomial `t'` with coefficients in `L` and embeds it into a polynomial
with coefficients in the tensor algebra `A` by applying `φ₁` to each coefficient.
This is achieved by using `MvPolynomial.map`.
-/
def componentWise_embed_MLE {A' : Type} [CommRing A'] (φ : L →+* A')
    (t' : MultilinearPoly L ℓ') : MultilinearPoly A' ℓ' :=
  ⟨MvPolynomial.map (R:=L) (S₁ := A') (f:=φ) (t'.val), by
    rw [MvPolynomial.mem_restrictDegree_iff_degreeOf_le]
    intro i -- for any specific variable Xᵢ,
      -- we prove its max individual degree is at most 1 in ANY monomial terms
    calc
      MvPolynomial.degreeOf i (MvPolynomial.map φ t'.val)
      _ ≤ MvPolynomial.degreeOf i t'.val := by
        refine degreeOf_le_iff.mpr ?_
        intro m hm_support_mapped_t' -- consider any specific monomial term
        have hm_in_support_t' : m ∈ t'.val.support := by
          apply MvPolynomial.support_map_subset (f:=φ)
          exact hm_support_mapped_t'
        exact monomial_le_degreeOf i hm_in_support_t'
      _ ≤ 1 := by
        have h_og_t' := t'.property
        simp only [MvPolynomial.mem_restrictDegree_iff_degreeOf_le] at h_og_t'
        exact h_og_t' i
  ⟩

/-- Binius-named alias: component-wise `φ₁` embedding into the tensor algebra `L ⊗[K] L`. -/
def componentWise_φ₁_embed_MLE (t' : MultilinearPoly L ℓ') :
    MultilinearPoly (TensorAlgebra K L) ℓ' :=
  componentWise_embed_MLE L ℓ' (A' := TensorAlgebra K L) (φ₁ L K) t'

end TensorAlgebraOps

section ProtocolTypes
/-!
## Enhanced Protocol Type Definitions (Interfaces between phases)

We define the Statement and Witness types at the boundaries of each phase
following the enhanced specification.
-/

/-- Initial input (input to the Batching Phase): a polynomial-evaluation claim `s = t(r)`. -/
structure MLPEvalStatement where
  /-- The evaluation point `r = (r₀, …, r_{ℓ-1})` — shared input. -/
  t_eval_point : Fin ℓ → L
  /-- The claimed evaluation `s = t(r)`. -/
  original_claim : L

structure WitMLP where
  t : MultilinearPoly K ℓ

structure BatchingWitIn where
  t : MultilinearPoly K ℓ
  t' : MultilinearPoly L ℓ'

structure BatchingStmtIn where
  t_eval_point : Fin ℓ → L -- r = (r_0, ..., r_{ℓ-1}) => shared input
  original_claim : L -- s = t(r) => the original claim to verify

structure RingSwitchingBaseContext (P : RingSwitchingProfile K L κ)
    extends (SumcheckBaseContext L ℓ) where
  -- context from batching phase
  s_hat : P.A -- ŝ
  r_batching : Fin κ → L -- r''

-- `SumcheckWitness` was lifted to `ArkLib.ProofSystem.Sumcheck.Structured` (the data shape is
-- generic and degree-neutral; only the per-round prover/verifier in `SumcheckPhase.lean` consume
-- it). Binius ring-switching is the degree-2 case `H = m · t'`, so this Binius-local abbrev pins
-- `d := 2`. Other instantiations (e.g. Hachi at `d := 2b+1`) pin their own degree — no
-- instantiation is privileged by a default on the generic type. The packed polynomial `t'` and
-- round polynomial `H` (after fixing previous challenges) live in the same structure.
abbrev SumcheckWitness (L : Type) [CommSemiring L] (ℓ : ℕ) (i : Fin (ℓ + 1)) :=
  Sumcheck.Structured.SumcheckWitness L ℓ i 2

section MLIOPCS
-- Define the specific Stmt/Wit types Π' expects.
structure MLIOPCSStmt where
  point : Fin ℓ' → L
  evaluation : L

/-- Standard input relation for MLIOPCS: polynomial evaluation at point equals claimed evaluation -/
def MLPEvalRelation (ιₛᵢ : Type) (OStmtIn : ιₛᵢ → Type)
    (input : ((MLPEvalStatement L ℓ') × (∀ j, OStmtIn j)) × (WitMLP L ℓ')) : Prop :=
  let ⟨⟨stmt, _⟩, wit⟩ := input
  stmt.original_claim = wit.t.val.eval stmt.t_eval_point

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

omit [Fintype L] [DecidableEq L] [NeZero ℓ'] in
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
open Module

variable (κ : ℕ) [NeZero κ]
variable (L : Type) [CommRing L] [Nontrivial L] [Fintype L] [DecidableEq L]
  [SampleableType L]
variable (K : Type) [CommRing K] [Fintype K] [DecidableEq K]
variable [Algebra K L]
variable (P : RingSwitchingProfile K L κ)
variable (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
variable (h_l : ℓ = ℓ' + κ)

/-- Compute the tensor value ŝ := φ₁(t')(φ₀(r_κ), ..., φ₀(r_{ℓ-1})) -/
def embedded_MLP_eval (t' : MultilinearPoly L ℓ') (r : Fin ℓ → L) :
  P.A :=
  -- This implements the identity:
  -- ŝ = Σ_{w ∈ {0,1}^ℓ'} eq̃(r_suffix, w) ⊗ t'(w)
  let r_suffix : Fin ℓ' → L :=
    fun i => r ⟨i.val + κ, by { rw [h_l]; omega }⟩
  let φ₁_mapped_t': MultilinearPoly P.A ℓ' := componentWise_embed_MLE L ℓ' P.φ₁ t'
  let φ₀_mapped_r: Fin ℓ' → P.A := fun i => P.φ₀ (r_suffix i)
  φ₁_mapped_t'.val.eval φ₀_mapped_r

/-! ### Generic ring-hom helpers for `embedded_MLP_eval_eq_sum` (ported from HEAD, φ₀/φ₁ → any
`φ : L →+* A'`; ring homs preserve 0/1 so all steps generalize). -/
section EmbeddedSum
variable {A' : Type*} [CommRing A'] (φ : L →+* A')

-- NOTE: `[IsDomain L]` is only needed for the MLE-uniqueness step
-- (`is_multilinear_iff_eq_evals_zeroOne`, which is stated over `[IsDomain R]` in
-- `ArkLib.Data.MvPolynomial.Multilinear` — see its TODO). The MLE bijection actually holds over any
-- `CommRing`; a `CommRing` version there would let this (and the whole ring-switching completeness)
-- apply to Hachi (`L = R_q`, not a domain) too. Binius (`L` a field) satisfies `[IsDomain L]`.
private lemma map_ringHom_eq_MLE [IsDomain L] (t' : MultilinearPoly L ℓ') :
    MvPolynomial.map φ t'.val =
      MvPolynomial.MLE (fun w : Fin ℓ' → Fin 2 => φ (MvPolynomial.eval (w : Fin ℓ' → L) t'.val)) := by
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
  rw [MvPolynomial.eqPolynomial_zeroOne (R := A') (r := w)]
  rw [map_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hwi : w i = 0
  · simp [hwi, map_sub, map_one]
  · have hwi1 : w i = 1 := by omega
    simp [hwi, hwi1, map_sub, map_one]

private lemma zeroOneCoe_eq_ringHom (w : Fin ℓ' → Fin 2) :
    (fun i => ((w i : Fin 2) : A')) = fun i => φ (((w i : Fin 2) : L)) := by
  funext i
  have hi : w i = 0 ∨ w i = 1 := by omega
  rcases hi with hi | hi
  · simp [hi]
  · simp [hi]

private lemma map_eqPolynomial_ringHom (r : Fin ℓ' → L) :
    MvPolynomial.map φ (MvPolynomial.eqPolynomial r : MvPolynomial (Fin ℓ') L) =
      (MvPolynomial.eqPolynomial (fun i => φ (r i)) : MvPolynomial (Fin ℓ') A') := by
  rw [MvPolynomial.eqPolynomial_expanded, MvPolynomial.eqPolynomial_expanded]
  simp

/-- `map φ` of the (multilinear) `eqPolynomial r` is its own MLE, indexed by the zero-one
evaluations `φ(eqTilde(r, w))`. Specialization of `map_ringHom_eq_MLE` to `eqPolynomial`. -/
private lemma map_ringHom_eq_MLE_eqPolynomial [IsDomain L] (r : Fin ℓ' → L) :
    MvPolynomial.map φ (MvPolynomial.eqPolynomial r : MvPolynomial (Fin ℓ') L) =
      MvPolynomial.MLE (fun w : Fin ℓ' → Fin 2 =>
        φ (eqTilde r (w : Fin ℓ' → L))) := by
  have h := map_ringHom_eq_MLE (L := L) (ℓ' := ℓ') (φ := φ)
    (t' := ⟨MvPolynomial.eqPolynomial r, MvPolynomial.eqPolynomial_mem_restrictDegree r⟩)
  simpa only [MvPolynomial.eqTilde] using h

end EmbeddedSum

/-- `embedded_MLP_eval` expands as `∑_w φ₀(eqTilde(r_suffix, w)) · φ₁(t'(w))`. Ported from HEAD,
Profile-parameterized. -/
private lemma embedded_MLP_eval_eq_sum [IsDomain L] (t' : MultilinearPoly L ℓ') (r : Fin ℓ → L) :
    embedded_MLP_eval κ L K P ℓ ℓ' h_l t' r =
      ∑ w : Fin ℓ' → Fin 2,
        P.φ₀ (eqTilde (fun i => r ⟨i.val + κ, by { rw [h_l]; omega }⟩) (w : Fin ℓ' → L)) *
          P.φ₁ (MvPolynomial.eval (w : Fin ℓ' → L) t'.val) := by
  let r_suffix : Fin ℓ' → L := fun i => r ⟨i.val + κ, by { rw [h_l]; omega }⟩
  unfold embedded_MLP_eval componentWise_embed_MLE
  change MvPolynomial.eval (fun i => P.φ₀ (r_suffix i)) (MvPolynomial.map P.φ₁ t'.val) = _
  rw [map_ringHom_eq_MLE (L := L) (ℓ' := ℓ') (φ := P.φ₁) (t' := t')]
  unfold MvPolynomial.MLE
  simp only [MvPolynomial.eval_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C]
  apply Finset.sum_congr rfl
  intro w hw
  have h_eval :
      MvPolynomial.eval (fun i => ((w i : Fin 2) : P.A))
        (MvPolynomial.eqPolynomial (fun i => P.φ₀ (r_suffix i))) =
      P.φ₀ (eqTilde r_suffix (w : Fin ℓ' → L)) := by
    rw [show (MvPolynomial.eqPolynomial (fun i => P.φ₀ (r_suffix i)) :
        MvPolynomial (Fin ℓ') P.A) = MvPolynomial.map P.φ₀ (MvPolynomial.eqPolynomial r_suffix) from
      (map_eqPolynomial_ringHom (L := L) (ℓ' := ℓ') (φ := P.φ₀) (r := r_suffix)).symm]
    rw [zeroOneCoe_eq_ringHom (L := L) (ℓ' := ℓ') (φ := P.φ₀) (w := w)]
    rw [MvPolynomial.eval_map, MvPolynomial.eqTilde]
    exact (MvPolynomial.eval₂_comp (f := P.φ₀) (g := (w : Fin ℓ' → L))
      (p := MvPolynomial.eqPolynomial r_suffix)).symm
  rw [MvPolynomial.eqPolynomial_symm]
  rw [h_eval]

/-- **KEY GENERIC LEMMA** (was the tensor-concrete blocker): the `v`-column coordinate of
`embedded_MLP_eval` distributes over the `∑_w φ₀(eqTilde_w)·φ₁(t'(w))` structure via the new
Profile laws `decomposeColumns_add` + `decomposeColumns_tmul`. Proven abstractly for ANY profile
`P` — no `L ⊗ L`-specific facts. -/
private lemma decompose_embedded_MLP_eval_columns [IsDomain L]
    (t' : MultilinearPoly L ℓ') (r : Fin ℓ → L) (v : Fin κ → Fin 2) :
    P.decomposeColumns (embedded_MLP_eval κ L K P ℓ ℓ' h_l t' r) v =
      ∑ w : Fin ℓ' → Fin 2,
        (P.basis.repr
          (eqTilde (fun i => r ⟨i.val + κ, by { rw [h_l]; omega }⟩) (w : Fin ℓ' → L)) v)
          • MvPolynomial.eval (w : Fin ℓ' → L) t'.val := by
  rw [embedded_MLP_eval_eq_sum (κ := κ) (L := L) (K := K) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l)
    (P := P) (t' := t') (r := r)]
  have hzero : P.decomposeColumns 0 v = 0 := by
    have h := P.decomposeColumns_add 0 0 v; simpa using h
  have hsum : ∀ (s : Finset (Fin ℓ' → Fin 2)) (f : (Fin ℓ' → Fin 2) → P.A),
      P.decomposeColumns (∑ w ∈ s, f w) v = ∑ w ∈ s, P.decomposeColumns (f w) v := by
    intro s f
    induction s using Finset.cons_induction with
    | empty => simp only [Finset.sum_empty, hzero]
    | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, P.decomposeColumns_add, ih]
  rw [hsum]
  apply Finset.sum_congr rfl
  intro w hw
  rw [P.decomposeColumns_tmul]

/-- Row dual of `decompose_embedded_MLP_eval_columns` (via `decomposeRows_add`/`decomposeRows_tmul`;
the `φ₀`/`φ₁` extraction roles swap). Generic for any profile `P`. -/
private lemma decompose_embedded_MLP_eval_rows [IsDomain L]
    (t' : MultilinearPoly L ℓ') (r : Fin ℓ → L) (u : Fin κ → Fin 2) :
    P.decomposeRows (embedded_MLP_eval κ L K P ℓ ℓ' h_l t' r) u =
      ∑ w : Fin ℓ' → Fin 2,
        (P.basis.repr (MvPolynomial.eval (w : Fin ℓ' → L) t'.val) u)
          • eqTilde (fun i => r ⟨i.val + κ, by { rw [h_l]; omega }⟩) (w : Fin ℓ' → L) := by
  rw [embedded_MLP_eval_eq_sum (κ := κ) (L := L) (K := K) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l)
    (P := P) (t' := t') (r := r)]
  have hzero : P.decomposeRows 0 u = 0 := by
    have h := P.decomposeRows_add 0 0 u; simpa using h
  have hsum : ∀ (s : Finset (Fin ℓ' → Fin 2)) (f : (Fin ℓ' → Fin 2) → P.A),
      P.decomposeRows (∑ w ∈ s, f w) u = ∑ w ∈ s, P.decomposeRows (f w) u := by
    intro s f
    induction s using Finset.cons_induction with
    | empty => simp only [Finset.sum_empty, hzero]
    | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, P.decomposeRows_add, ih]
  rw [hsum]
  apply Finset.sum_congr rfl
  intro w hw
  rw [P.decomposeRows_tmul]

/-- Step 2 (V): Check 1: s ?= Σ_{v ∈ {0,1}^κ} eqTilde(v, r_{0..κ-1}) ⋅ ŝ_v. -/
def performCheckOriginalEvaluation (s : L) (r : Fin ℓ → L) (s_hat : P.A) : Bool :=
  let r_prefix : Fin κ → L := fun i => r ⟨i.val, by omega⟩
  let check_sum := Finset.sum Finset.univ fun (v : Fin κ → Fin 2) =>
    let v_as_L : Fin κ → L := fun i => if (v i == 1) then 1 else 0
    -- Uses `decomposeRows` (= baseChange-LEFT, our HEAD ground-truth convention). Alex's frame
    -- swapped the Columns/Rows (baseChange left↔right) def bodies vs HEAD; on the honest
    -- `ŝ = Σ_w eqTilde_w ⊗ eval(t',w)`, `decomposeRows ŝ v = Σ_w (β.repr eval_w v)·eqTilde_w`, which
    -- is exactly Check 1 and reconstructs `t(eval_point)`. `decomposeColumns` (baseChangeRight)
    -- would extract the wrong factor. (compute_s0 likewise uses decomposeRows.)
    (eqTilde v_as_L r_prefix) * (P.decomposeRows s_hat v)
  decide (s = check_sum)

/-! ### Batching-check correctness (basis-generic chain, ported from HEAD with `β` explicit).
These use `packMLE`/`P.basis.repr`/`MvPolynomial.eval₂`/`eqTilde` only (no tensor structure), so they
stay generic over an explicit basis `β`. `batching_check_correctness` glues them with the (already
green) `decompose_embedded_MLP_eval_columns` + `unpack_pack_id`. -/

private lemma repr_packMLE_eval (β : Basis (Fin κ → Fin 2) K L)
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
    unfold MvPolynomial.eqTilde eval_point'
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
  unfold MvPolynomial.eqTilde eval_point'
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

private def batchingCheckSummand (β : Basis (Fin κ → Fin 2) K L)
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
private lemma batchingCheckSummand_split (β : Basis (Fin κ → Fin 2) K L)
    (t : MultilinearPoly K ℓ)
    (eval_point : Fin ℓ → L)
    (v : Fin κ → Fin 2)
    (w : Fin ℓ' → Fin 2) :
    batchingCheckSummand κ L K ℓ ℓ' h_l β t eval_point
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

set_option maxHeartbeats 400000 in
/-- **Batching check correctness**: on the honest prover message `ŝ = embedded_MLP_eval (packMLE t)`,
the verifier's Check 1 passes. Ported from HEAD with `β → P` / `P.basis`; uses the (green)
`decompose_embedded_MLP_eval_columns` + `unpack_pack_id`. -/
lemma batching_check_correctness [IsDomain K] [IsDomain L]
    (t : MultilinearPoly K ℓ)
    (eval_point : Fin ℓ → L) :
  performCheckOriginalEvaluation κ L K P ℓ ℓ' h_l
    (t.val.aeval eval_point)
    (r := eval_point) (s_hat := embedded_MLP_eval κ L K P ℓ ℓ' h_l
      (packMLE κ L K ℓ ℓ' h_l P.basis t) eval_point) = true := by
  unfold performCheckOriginalEvaluation
  simp only [decide_eq_true_eq]
  simp_rw [decompose_embedded_MLP_eval_rows (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ)
    (ℓ' := ℓ') (h_l := h_l) (t' := packMLE κ L K ℓ ℓ' h_l P.basis t) (r := eval_point)]
  conv_lhs =>
    rw [← unpack_pack_id (κ := κ) (L := L) (K := K) (β := P.basis) (ℓ := ℓ) (ℓ' := ℓ')
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
          (P.basis.repr (MvPolynomial.eval (w : Fin ℓ' → L)
            (packMLE κ L K ℓ ℓ' h_l P.basis t).val)) v)) = _
  rw [MvPolynomial.MLE]
  simp only [MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C]
  change ∑ p : Fin ℓ → Fin 2, batchingCheckSummand κ L K ℓ ℓ' h_l P.basis t eval_point p = _
  have hsplit :
      ∑ p : Fin ℓ → Fin 2, batchingCheckSummand κ L K ℓ ℓ' h_l P.basis t eval_point p =
        ∑ vw : (Fin κ → Fin 2) × (Fin ℓ' → Fin 2),
          batchingCheckSummand κ L K ℓ ℓ' h_l P.basis t eval_point
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
  rw [batchingCheckSummand_split (κ := κ) (L := L) (K := K) (β := P.basis) (ℓ := ℓ) (ℓ' := ℓ')
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
    let coords_A_w_u: (Fin κ → Fin 2) →₀ K := P.basis.repr eq_w
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
  let A_func := compute_A_func κ L K P ℓ' original_r_eval_suffix r''_batching
  let A_MLE: MultilinearPoly L ℓ' := ⟨MvPolynomial.MLE A_func, MLE_mem_restrictDegree A_func⟩
  A_MLE

def getEvaluationPointSuffix (r : Fin ℓ → L) : Fin ℓ' → L :=
  fun i => r ⟨i.val + κ, by { rw [h_l]; omega }⟩

/-- Ring-Switching multiplier parameter for sumcheck, using `A_MLE` as the multiplier. -/
def RingSwitching_SumcheckMultParam :
  SumcheckMultiplierParam L ℓ' (RingSwitchingBaseContext κ L K ℓ P) :=
{ multpoly := fun ctx => -- This is supposed to be (r_κ, …, r_{ℓ-1})
    compute_A_MLE κ L K P ℓ' (original_r_eval_suffix :=
      getEvaluationPointSuffix κ L ℓ ℓ' h_l (r := ctx.t_eval_point))
      (r''_batching := ctx.r_batching)
  -- Ring-switching is the plain degree-2 case `H = P · t'`: combinator `Q := X`, degree 1.
  combinator := fun _ => Polynomial.X
  degCombinator := 1
  combinator_natDegree_le := by intro _; exact Polynomial.natDegree_X_le
}

/-- Step 5 (V): Compute `s₀ := Σ_{u ∈ {0,1}^κ} eqTilde(u, r'') ⋅ ŝ_u`,
where ŝ_u is the column components of ŝ. Uses `decomposeColumns` (= `baseChangeRight` in Alex's
frame, = HEAD's `decompose_tensor_algebra_rows`): on the honest `ŝ = Σ_w φ₀(eqTilde_w)·φ₁(eval_w)`,
`decomposeColumns ŝ u = Σ_w (β.repr eqTilde_w u)·eval_w`, so `s₀ = Σ_w A(w)·eval(w,t')` matches
the honest round-0 polynomial `H = A·t'` (sumcheck-consistency). (HEAD used `rows` because HEAD's
`rows`=`baseChangeRight`; Alex swapped the two def bodies, so the correct choice here is `columns`.)
-/
def compute_s0 (s_hat : P.A) (r''_batching : Fin κ → L) : L :=
  Finset.sum Finset.univ fun (u : Fin κ → Fin 2) =>
    let u_as_L : Fin κ → L := fun i => if (u i == 1) then 1 else 0
    (eqTilde u_as_L r''_batching)
      * (P.decomposeColumns s_hat u)

/-- Compute the tensor `e := eq̃(φ₀(r_κ), ..., φ₀(r_{ℓ-1}), φ₁(r'_0), ..., φ₁(r'_{ℓ'-1}))` -/
def compute_final_eq_tensor (r : Fin ℓ → L) (r' : Fin ℓ' → L) : P.A :=
  let φ₀_mapped_r_suffix : Fin ℓ' → P.A := fun i =>
    P.φ₀ (r ⟨i.val + κ, by { rw [h_l]; omega }⟩)
  let φ₁_mapped_r': Fin ℓ' → P.A := fun i => P.φ₁ (r' i)
  eqTilde φ₀_mapped_r_suffix φ₁_mapped_r'

/-- Decompose the final eq tensor `e := Σ_{u ∈ {0,1}^κ} eq̃(u, r'') ⨂ e_u`,
where e_u is the column components of e.
Then compute `Σ_{u ∈ {0,1}^κ} eq̃(u_0, ..., u_{κ-1}, r''_0, ..., r''_{κ-1}) ⋅ e_u`.
Uses `decomposeColumns` (= baseChange-LEFT in Alex's swapped frame — the same convention as
`compute_s0`): on `e = Σ_w φ₀(eqTilde_suffix_w)·φ₁(eqTilde_w_r')`,
`decomposeColumns e u = Σ_w (basis.repr eqTilde_suffix_w u)·eqTilde_w_r'`, so this value equals
`A_MLE.eval(r')` (`compute_A_MLE_eval_eq_final_eq_value`). (`decomposeRows`, HEAD's naming, would
extract the wrong factor — the same rows/columns swap fixed in `compute_s0`.) -/
def compute_final_eq_value (r_eval : Fin ℓ → L)
    (r'_challenges : Fin ℓ' → L) (r''_batching : Fin κ → L) : L :=
  let e_tensor := compute_final_eq_tensor κ L K P ℓ ℓ' h_l r_eval r'_challenges
  let e_u : (Fin κ → Fin 2) → L := P.decomposeColumns e_tensor
  Finset.sum Finset.univ fun (u : Fin κ → Fin 2) =>
    let u_as_L : Fin κ → L := fun i => if u i == 1 then 1 else 0
    let eq_u_r_batching : L := -- `eq̃(u_0, ..., u_{κ-1}, r''_0, ..., r''_{κ-1})`
      eqTilde u_as_L r''_batching
    eq_u_r_batching * (e_u u)

private lemma zeroOnePoint_eq_coe {n : ℕ} (x : Fin n → Fin 2) :
    (fun i => if x i == 1 then (1 : L) else 0) = (x : Fin n → L) := by
  funext i
  have hi : x i = 0 ∨ x i = 1 := by omega
  rcases hi with hi | hi
  · simp [hi]
  · simp [hi]

/-! ### Final-step algebra bridges (ported from HEAD, `β/tensor → P`).
The final sumcheck verifier check needs `A_MLE.eval(challenges) = compute_final_eq_value`. Ported
from HEAD `compute_A_MLE_eval_eq_final_eq_value`; the `TensorAlgebra`-concrete steps are replaced by
the generic Profile laws `decomposeRows_add`/`decomposeRows_tmul` (mirroring
`decompose_embedded_MLP_eval_rows`). -/

/-- `compute_final_eq_tensor` expands as `∑_w P.φ₀(eqTilde(r_suffix, w)) · P.φ₁(eqTilde(w, r'))`.
Profile analog of `embedded_MLP_eval_eq_sum`; here the MLE is that of the multilinear
`eqPolynomial r_suffix`, evaluated pointwise. -/
private lemma compute_final_eq_tensor_eq_sum [IsDomain L]
    (r_eval : Fin ℓ → L) (r'_challenges : Fin ℓ' → L) :
    compute_final_eq_tensor κ L K P ℓ ℓ' h_l r_eval r'_challenges =
      ∑ w : Fin ℓ' → Fin 2,
        P.φ₀ (eqTilde (getEvaluationPointSuffix κ L ℓ ℓ' h_l r_eval) (w : Fin ℓ' → L)) *
          P.φ₁ (eqTilde (w : Fin ℓ' → L) r'_challenges) := by
  let r_suffix : Fin ℓ' → L := getEvaluationPointSuffix κ L ℓ ℓ' h_l r_eval
  unfold compute_final_eq_tensor MvPolynomial.eqTilde
  change MvPolynomial.eval (fun i => P.φ₁ (r'_challenges i))
      (MvPolynomial.eqPolynomial (fun i => P.φ₀ (r_suffix i))) = _
  rw [show (MvPolynomial.eqPolynomial (fun i => P.φ₀ (r_suffix i)) :
      MvPolynomial (Fin ℓ') P.A) = MvPolynomial.map P.φ₀ (MvPolynomial.eqPolynomial r_suffix) from
    (map_eqPolynomial_ringHom (L := L) (ℓ' := ℓ') (φ := P.φ₀) (r := r_suffix)).symm]
  -- `eqPolynomial r_suffix` is multilinear, so `map φ₀` of it is its own MLE.
  rw [map_ringHom_eq_MLE_eqPolynomial (L := L) (ℓ' := ℓ') (φ := P.φ₀) (r := r_suffix)]
  unfold MvPolynomial.MLE
  simp only [MvPolynomial.eval_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C]
  apply Finset.sum_congr rfl
  intro w hw
  have h_eval :
      MvPolynomial.eval (fun i => P.φ₁ (r'_challenges i))
        (MvPolynomial.eqPolynomial (fun i => ((w i : Fin 2) : P.A))) =
      P.φ₁ (eqTilde (w : Fin ℓ' → L) r'_challenges) := by
    rw [zeroOneCoe_eq_ringHom (L := L) (ℓ' := ℓ') (φ := P.φ₁) (w := w)]
    rw [show (MvPolynomial.eqPolynomial (fun i => P.φ₁ (((w i : Fin 2) : L))) :
        MvPolynomial (Fin ℓ') P.A) =
        MvPolynomial.map P.φ₁ (MvPolynomial.eqPolynomial (w : Fin ℓ' → L)) from
      (map_eqPolynomial_ringHom (L := L) (ℓ' := ℓ') (φ := P.φ₁) (r := (w : Fin ℓ' → L))).symm]
    rw [MvPolynomial.eval_map, MvPolynomial.eqTilde]
    exact (MvPolynomial.eval₂_comp (f := P.φ₁) (g := r'_challenges)
      (p := MvPolynomial.eqPolynomial (w : Fin ℓ' → L))).symm
  rw [h_eval]
  simp only [MvPolynomial.eqTilde]; ring

/-- The `u`-column coordinate of `compute_final_eq_tensor`, via
`decomposeColumns_add`/`decomposeColumns_tmul` (same convention as `compute_s0`; see
`compute_final_eq_value`). Profile analog of HEAD `decompose_compute_final_eq_tensor_rows`
under the frame's rows/columns swap. -/
private lemma decompose_compute_final_eq_tensor_columns [IsDomain L]
    (r_eval : Fin ℓ → L) (r'_challenges : Fin ℓ' → L) (u : Fin κ → Fin 2) :
    P.decomposeColumns (compute_final_eq_tensor κ L K P ℓ ℓ' h_l r_eval r'_challenges) u =
      ∑ w : Fin ℓ' → Fin 2,
        (P.basis.repr
            (eqTilde (getEvaluationPointSuffix κ L ℓ ℓ' h_l r_eval) (w : Fin ℓ' → L)) u) •
          eqTilde (w : Fin ℓ' → L) r'_challenges := by
  rw [compute_final_eq_tensor_eq_sum (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ')
    (h_l := h_l) (r_eval := r_eval) (r'_challenges := r'_challenges)]
  have hzero : P.decomposeColumns 0 u = 0 := by
    have h := P.decomposeColumns_add 0 0 u; simpa using h
  have hsum : ∀ (s : Finset (Fin ℓ' → Fin 2)) (f : (Fin ℓ' → Fin 2) → P.A),
      P.decomposeColumns (∑ w ∈ s, f w) u = ∑ w ∈ s, P.decomposeColumns (f w) u := by
    intro s f
    induction s using Finset.cons_induction with
    | empty => simp only [Finset.sum_empty, hzero]
    | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, P.decomposeColumns_add, ih]
  rw [hsum]
  apply Finset.sum_congr rfl
  intro w hw
  rw [P.decomposeColumns_tmul]

/-- **Key Identity**: `A_MLE.eval(challenges) = compute_final_eq_value`. Connects the MLE-based
multiplier polynomial with the tensor/row-decomposition-based final verifier value. Ported from
HEAD, Profile-parameterized. -/
lemma compute_A_MLE_eval_eq_final_eq_value [IsDomain L]
    (r_eval : Fin ℓ → L) (r'_challenges : Fin ℓ' → L) (r''_batching : Fin κ → L) :
    (compute_A_MLE κ L K P ℓ' (getEvaluationPointSuffix κ L ℓ ℓ' h_l r_eval)
      r''_batching).val.eval r'_challenges =
    compute_final_eq_value κ L K P ℓ ℓ' h_l r_eval r'_challenges r''_batching := by
  simp only [compute_A_MLE, compute_final_eq_value, compute_A_func, MvPolynomial.MLE,
    MvPolynomial.eval_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C]
  calc
    ∑ w : Fin ℓ' → Fin 2,
        MvPolynomial.eval r'_challenges (MvPolynomial.eqPolynomial (w : Fin ℓ' → L)) *
          ∑ u : Fin κ → Fin 2,
            (P.basis.repr
                (eqTilde (getEvaluationPointSuffix κ L ℓ ℓ' h_l r_eval)
                  (fun i => if w i == 1 then 1 else 0)) u) •
              eqTilde (fun i => if u i == 1 then 1 else 0) r''_batching
      = ∑ w : Fin ℓ' → Fin 2,
          eqTilde (w : Fin ℓ' → L) r'_challenges *
            ∑ u : Fin κ → Fin 2,
              (P.basis.repr
                  (eqTilde (getEvaluationPointSuffix κ L ℓ ℓ' h_l r_eval)
                    (w : Fin ℓ' → L)) u) •
                eqTilde (u : Fin κ → L) r''_batching := by
          apply Finset.sum_congr rfl
          intro w hw
          rw [show (fun i => if w i == 1 then (1 : L) else 0) = (w : Fin ℓ' → L) from
            zeroOnePoint_eq_coe (L := L) (x := w)]
          rw [show MvPolynomial.eval r'_challenges (MvPolynomial.eqPolynomial (w : Fin ℓ' → L))
              = eqTilde (w : Fin ℓ' → L) r'_challenges from rfl]
          apply congrArg (eqTilde (w : Fin ℓ' → L) r'_challenges * ·)
          apply Finset.sum_congr rfl
          intro u hu
          rw [show (fun i => if u i == 1 then (1 : L) else 0) = (u : Fin κ → L) from
            zeroOnePoint_eq_coe (L := L) (x := u)]
    _ = ∑ u : Fin κ → Fin 2,
          eqTilde (u : Fin κ → L) r''_batching *
            ∑ w : Fin ℓ' → Fin 2,
              (P.basis.repr
                  (eqTilde (getEvaluationPointSuffix κ L ℓ ℓ' h_l r_eval)
                    (w : Fin ℓ' → L)) u) •
                eqTilde (w : Fin ℓ' → L) r'_challenges := by
          calc
            _ = ∑ w : Fin ℓ' → Fin 2,
                ∑ u : Fin κ → Fin 2,
                  eqTilde (w : Fin ℓ' → L) r'_challenges *
                    ((P.basis.repr
                        (eqTilde (getEvaluationPointSuffix κ L ℓ ℓ' h_l r_eval)
                          (w : Fin ℓ' → L)) u) •
                      eqTilde (u : Fin κ → L) r''_batching) := by
                  apply Finset.sum_congr rfl
                  intro w hw
                  rw [Finset.mul_sum]
            _ = ∑ u : Fin κ → Fin 2,
                ∑ w : Fin ℓ' → Fin 2,
                  eqTilde (u : Fin κ → L) r''_batching *
                    ((P.basis.repr
                        (eqTilde (getEvaluationPointSuffix κ L ℓ ℓ' h_l r_eval)
                          (w : Fin ℓ' → L)) u) •
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
            P.decomposeColumns
              (compute_final_eq_tensor κ L K P ℓ ℓ' h_l r_eval r'_challenges) u := by
          apply Finset.sum_congr rfl
          intro u hu
          rw [decompose_compute_final_eq_tensor_columns (κ := κ) (L := L) (K := K) (P := P)
            (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l) (r_eval := r_eval)
            (r'_challenges := r'_challenges) (u := u)]
    _ = ∑ u : Fin κ → Fin 2,
          eqTilde (fun i => if u i == 1 then 1 else 0) r''_batching *
            P.decomposeColumns
              (compute_final_eq_tensor κ L K P ℓ ℓ' h_l r_eval r'_challenges) u := by
          apply Finset.sum_congr rfl
          intro u hu
          rw [show (fun i => if u i == 1 then (1 : L) else 0) = (u : Fin κ → L) from
            zeroOnePoint_eq_coe (L := L) (x := u)]

/-- This condition ensures that the witness polynomial `H` has the
correct structure `A(...) * t'(...)` -/
def witnessStructuralInvariant {i : Fin (ℓ' + 1)}
    (stmt : Statement (L := L) (RingSwitchingBaseContext κ L K ℓ P) i)
    (wit : SumcheckWitness L ℓ' i) : Prop :=
  wit.H.val = (projectToMidSumcheckPolyWithParam (L := L) (ℓ := ℓ')
    (param := RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l)
    (ctx := stmt.ctx) (t := wit.t')
    (i := i) (challenges := stmt.challenges)
  ).val

def masterKStateProp (aOStmtIn : AbstractOStmtIn L ℓ') (stmtIdx : Fin (ℓ' + 1))
    (stmt : Statement (L := L) (RingSwitchingBaseContext κ L K ℓ P) stmtIdx)
    (oStmt : ∀ j, aOStmtIn.OStmtIn j)
    (wit : SumcheckWitness L ℓ' stmtIdx)
    (localChecks : Prop := True) : Prop :=
  localChecks
  ∧ witnessStructuralInvariant κ L K P ℓ ℓ' h_l stmt wit
  ∧ sumcheckConsistencyProp (boolDomain L _) stmt.sumcheck_target wit.H
  ∧ aOStmtIn.initialCompatibility ⟨wit.t', oStmt⟩

def sumcheckRoundRelationProp (aOStmtIn : AbstractOStmtIn L ℓ') (i : Fin (ℓ' + 1))
    (stmt : Statement (L := L) (RingSwitchingBaseContext κ L K ℓ P) i)
    (oStmt : ∀ j, aOStmtIn.OStmtIn j)
    (wit : SumcheckWitness L ℓ' i) : Prop :=
  masterKStateProp κ L K P ℓ ℓ' h_l aOStmtIn i stmt oStmt wit

/-- Input relation for single round: proper sumcheck statement -/
def sumcheckRoundRelation (aOStmtIn : AbstractOStmtIn L ℓ') (i : Fin (ℓ' + 1)) :
  Set (((Statement (L := L) (RingSwitchingBaseContext κ L K ℓ P) i) ×
    (∀ j, aOStmtIn.OStmtIn j)) × SumcheckWitness L ℓ' i) :=
  { ((stmt, oStmt), wit) | sumcheckRoundRelationProp κ L K P ℓ ℓ' h_l
    aOStmtIn i stmt oStmt wit }

/-- Strict master-state predicate: identical to `masterKStateProp` but carries the strict
(exact-oracle) compatibility `strictInitialCompatibility`. Used by perfect-completeness statements
(our ground-truth Binius uses strict relations for completeness; relaxed stays for soundness). -/
def masterStrictKStateProp (aOStmtIn : AbstractOStmtIn L ℓ') (stmtIdx : Fin (ℓ' + 1))
    (stmt : Statement (L := L) (RingSwitchingBaseContext κ L K ℓ P) stmtIdx)
    (oStmt : ∀ j, aOStmtIn.OStmtIn j)
    (wit : SumcheckWitness L ℓ' stmtIdx)
    (localChecks : Prop := True) : Prop :=
  localChecks
  ∧ witnessStructuralInvariant κ L K P ℓ ℓ' h_l stmt wit
  ∧ sumcheckConsistencyProp (boolDomain L _) stmt.sumcheck_target wit.H
  ∧ aOStmtIn.strictInitialCompatibility ⟨wit.t', oStmt⟩

def strictSumcheckRoundRelationProp (aOStmtIn : AbstractOStmtIn L ℓ') (i : Fin (ℓ' + 1))
    (stmt : Statement (L := L) (RingSwitchingBaseContext κ L K ℓ P) i)
    (oStmt : ∀ j, aOStmtIn.OStmtIn j)
    (wit : SumcheckWitness L ℓ' i) : Prop :=
  masterStrictKStateProp κ L K P ℓ ℓ' h_l aOStmtIn i stmt oStmt wit

/-- Strict round relation for completeness proofs. -/
def strictSumcheckRoundRelation (aOStmtIn : AbstractOStmtIn L ℓ') (i : Fin (ℓ' + 1)) :
  Set (((Statement (L := L) (RingSwitchingBaseContext κ L K ℓ P) i) ×
    (∀ j, aOStmtIn.OStmtIn j)) × SumcheckWitness L ℓ' i) :=
  { ((stmt, oStmt), wit) | strictSumcheckRoundRelationProp κ L K P ℓ ℓ' h_l
    aOStmtIn i stmt oStmt wit }

omit [Fintype L] [DecidableEq L] [NeZero ℓ] [NeZero ℓ'] in
lemma strictSumcheckRoundRelation_subset_sumcheckRoundRelation (aOStmtIn : AbstractOStmtIn L ℓ')
    (i : Fin (ℓ' + 1)) :
    strictSumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i ⊆
      sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i := by
  intro input h_input
  obtain ⟨⟨stmt, oStmt⟩, wit⟩ := input
  obtain ⟨hLocal, hStruct, hSum, hCompat⟩ := h_input
  exact ⟨hLocal, hStruct, hSum,
    aOStmtIn.strictInitialCompatibility_implies_initialCompatibility oStmt wit.t' hCompat⟩

/-! ### Batching-target consistency (completeness core, ported from HEAD, `β/𝓑 → P`).
The verifier's `s₀` matches the sum over the boolean hypercube of the honest round-0 polynomial
`H = A · t'`. Ported from HEAD `RingSwitching/Prelude.lean`; the `TensorAlgebra`-concrete steps are
replaced by the (already-green) generic `decompose_embedded_MLP_eval_rows` + `P.decomposeRows_*`
laws, and `castEmb` (`0↦0, 1↦1`) becomes the library `boolEmbedding L`. -/


set_option maxHeartbeats 400000 in
-- Expand the honest tensor row decomposition and identify the batching multiplier at zero-one points.
private lemma compute_s0_embedded_MLP_eval_eq_sum [IsDomain L]
    (t' : MultilinearPoly L ℓ')
    (r_eval : Fin ℓ → L)
    (r''_batching : Fin κ → L) :
    compute_s0 κ L K P
      (embedded_MLP_eval κ L K P ℓ ℓ' h_l t' r_eval) r''_batching =
    ∑ w : Fin ℓ' → Fin 2,
      MvPolynomial.eval (w : Fin ℓ' → L)
          (compute_A_MLE κ L K P ℓ'
            (getEvaluationPointSuffix κ L ℓ ℓ' h_l r_eval) r''_batching).val *
        MvPolynomial.eval (w : Fin ℓ' → L) t'.val := by
  rw [compute_s0]
  simp_rw [decompose_embedded_MLP_eval_columns (κ := κ) (L := L) (K := K) (P := P)
    (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l) (t' := t') (r := r_eval)]
  calc
    ∑ u : Fin κ → Fin 2,
        eqTilde (fun i => if u i == 1 then 1 else 0) r''_batching *
          ∑ w : Fin ℓ' → Fin 2,
            (P.basis.repr
                (eqTilde (getEvaluationPointSuffix κ L ℓ ℓ' h_l r_eval)
                  (w : Fin ℓ' → L)) u) •
              MvPolynomial.eval (w : Fin ℓ' → L) t'.val
      = ∑ w : Fin ℓ' → Fin 2,
          ∑ u : Fin κ → Fin 2,
            eqTilde (fun i => if u i == 1 then 1 else 0) r''_batching *
              ((P.basis.repr
                  (eqTilde (getEvaluationPointSuffix κ L ℓ ℓ' h_l r_eval)
                    (w : Fin ℓ' → L)) u) •
                MvPolynomial.eval (w : Fin ℓ' → L) t'.val) := by
            calc
              _ = ∑ u : Fin κ → Fin 2,
                  ∑ w : Fin ℓ' → Fin 2,
                    eqTilde (fun i => if u i == 1 then 1 else 0) r''_batching *
                      ((P.basis.repr
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
            (P.basis.repr
                (eqTilde (getEvaluationPointSuffix κ L ℓ ℓ' h_l r_eval)
                  (w : Fin ℓ' → L)) u) •
              eqTilde (u : Fin κ → L) r''_batching) *
            MvPolynomial.eval (w : Fin ℓ' → L) t'.val := by
            apply Finset.sum_congr rfl
            intro w hw
            calc
              ∑ u : Fin κ → Fin 2,
                  eqTilde (fun i => if u i == 1 then 1 else 0) r''_batching *
                    ((P.basis.repr
                        (eqTilde (getEvaluationPointSuffix κ L ℓ ℓ' h_l r_eval)
                          (w : Fin ℓ' → L)) u) •
                      MvPolynomial.eval (w : Fin ℓ' → L) t'.val)
                = ∑ u : Fin κ → Fin 2,
                    ((P.basis.repr
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
              (compute_A_MLE κ L K P ℓ'
                (getEvaluationPointSuffix κ L ℓ ℓ' h_l r_eval) r''_batching).val *
            MvPolynomial.eval (w : Fin ℓ' → L) t'.val := by
            apply Finset.sum_congr rfl
            intro w hw
            have h_mEq_w :
                MvPolynomial.eval (w : Fin ℓ' → L)
                    (compute_A_MLE κ L K P ℓ'
                      (getEvaluationPointSuffix κ L ℓ ℓ' h_l r_eval) r''_batching).val =
                  ∑ u : Fin κ → Fin 2,
                    (P.basis.repr
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

/-- **Consistency of the Batching Target**: the verifier's `s₀` equals the sum over the boolean
hypercube of the honest round-0 sumcheck polynomial `H = A · t'`. Ported from HEAD. -/
lemma batching_target_consistency [IsDomain L]
    (t' : MultilinearPoly L ℓ')
    (msg0 : P.A)
    (ctx : RingSwitchingBaseContext κ L K ℓ P)
    (h_msg0 : msg0 = embedded_MLP_eval κ L K P ℓ ℓ' h_l t' ctx.t_eval_point) :
  let s₀ := compute_s0 κ L K P msg0 ctx.r_batching
  let H := projectToMidSumcheckPolyWithParam (L := L) (ℓ := ℓ')
    (param := RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l) (ctx := ctx) (t := t') (i := 0)
    (challenges := Fin.elim0)
  sumcheckConsistencyProp (boolDomain L _) s₀ H := by
  classical
  subst h_msg0
  intro s₀ H
  rw [sumcheckConsistencyProp]
  show s₀ = ∑ x ∈ (boolDomain L ℓ').cube, H.val.eval x
  -- `H.val = fixFirstVariablesOfMQP 0 (computeRoundPoly) = computeRoundPoly.val = A.val * t'.val`
  have h_Hval :
      H.val = (compute_A_MLE κ L K P ℓ'
          (getEvaluationPointSuffix κ L ℓ ℓ' h_l ctx.t_eval_point) ctx.r_batching).val *
        t'.val := by
    have hH1 : H.val = MvPolynomial.fixFirstVariablesOfMQP ℓ'
        (0 : Fin (ℓ' + 1))
        (computeRoundPoly (L := L) (ℓ := ℓ')
          (RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l) ctx t').val
        Fin.elim0 := rfl
    rw [hH1, MvPolynomial.fixFirstVariablesOfMQP_zero_eq (ℓ := ℓ')
      (H := (computeRoundPoly (L := L) (ℓ := ℓ')
        (RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l) ctx t').val)]
    unfold computeRoundPoly RingSwitching_SumcheckMultParam
    simp only [Polynomial.aeval_X]
  rw [h_Hval]
  have h_cube_eq : (boolDomain L ℓ').cube =
      (Finset.univ : Finset (Fin ℓ' → Fin 2)).image
        (fun b : Fin ℓ' → Fin 2 => fun i => boolEmbedding L (b i)) := by
    rw [show (boolDomain L ℓ').cube =
        Fintype.piFinset (fun _ : Fin ℓ' => Finset.univ.map (boolEmbedding L)) from rfl]
    have h_pi' := Fintype.piFinset_image
      (f := fun _ : Fin ℓ' => boolEmbedding L)
      (s := fun _ : Fin ℓ' => (Finset.univ : Finset (Fin 2)))
    rw [Fintype.piFinset_univ] at h_pi'
    simp only [Finset.map_eq_image]
    exact h_pi'
  rw [h_cube_eq, Finset.sum_image
    (fun x hx y hy hxy => by funext i; exact (boolEmbedding L).injective (congrFun hxy i))]
  simp only [MvPolynomial.eval_mul]
  have hcoe : ∀ w : Fin ℓ' → Fin 2, (fun i => boolEmbedding L (w i)) = (w : Fin ℓ' → L) := by
    intro w; funext i
    have hi : w i = 0 ∨ w i = 1 := by omega
    rcases hi with hi | hi <;> simp [hi]
  simp_rw [hcoe]
  exact compute_s0_embedded_MLP_eval_eq_sum (κ := κ) (L := L) (K := K) (P := P)
    (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l) (t' := t') (r_eval := ctx.t_eval_point)
    (r''_batching := ctx.r_batching)

end Relations

open Module in
/-- The Binius (binary-tower) instantiation of `RingSwitchingProfile`, built from the tensor-algebra
definitions above: `A := L ⊗[K] L`, embeddings `φ₀ = · ⊗ 1` / `φ₁ = 1 ⊗ ·`, and the decompositions
are the `K`-basis coordinates via the left/right `L`-module structures.

Marked `@[reducible]` so that, once the protocol code is rewired through the profile, references to
`(binaryTowerProfile …).A` (etc.) unfold to `L ⊗[K] L` at reducible transparency — preserving the
existing `rfl`/instance-driven Binius proofs (and the byte-identical `#print axioms`). -/
@[reducible] def binaryTowerProfile (κ : ℕ) [NeZero κ] (K L : Type)
    [Field K] [Field L] [Algebra K L] (β : Module.Basis (Fin κ → Fin 2) K L) :
    RingSwitchingProfile K L κ where
  basis := β
  A := TensorAlgebra K L
  commRingA := inferInstanceAs (CommRing (L ⊗[K] L))
  algLA := Algebra.TensorProduct.leftAlgebra
  φ₀ := φ₀ L K
  φ₁ := φ₁ L K
  decomposeRows := fun s => decompose_tensor_algebra_rows (L := L) (K := K) (β := β) s
  decomposeColumns := fun s => decompose_tensor_algebra_columns (L := L) (K := K) (β := β) s
  decomposeRows_spec := fun z => by
    conv_lhs => rw [← (β.baseChange L).sum_repr z]
    refine Finset.sum_congr rfl fun u _ => ?_
    unfold decompose_tensor_algebra_rows
    rw [Basis.baseChange_apply, smul_tmul']
    show _ = (φ₀ L K) _ * (φ₁ L K) _
    unfold φ₀ φ₁
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  decomposeColumns_spec := fun z => by
    letI rightAlgebra : Algebra L (L ⊗[K] L) := Algebra.TensorProduct.rightAlgebra
    letI rightModule : Module L (L ⊗[K] L) := rightAlgebra.toModule
    conv_lhs => rw [← (Basis.baseChangeRight (b := β) (Right := L)).sum_repr z]
    refine Finset.sum_congr rfl fun v _ => ?_
    unfold decompose_tensor_algebra_columns
    rw [Basis.baseChangeRight_apply, Algebra.smul_def]
    show algebraMap L (L ⊗[K] L) _ * _ = (φ₁ L K) _ * (φ₀ L K) _
    rw [show (algebraMap L (L ⊗[K] L)) =
      (Algebra.TensorProduct.includeRight).toRingHom.comp (algebraMap L L) by rfl]
    unfold φ₀ φ₁
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  decomposeColumns_add := fun z z' v => by
    letI rightAlgebra : Algebra L (L ⊗[K] L) := Algebra.TensorProduct.rightAlgebra
    letI rightModule : Module L (L ⊗[K] L) := rightAlgebra.toModule
    unfold decompose_tensor_algebra_columns
    simp only [map_add, Finsupp.add_apply]
  decomposeColumns_tmul := fun x y v => by
    letI rightAlgebra : Algebra L (L ⊗[K] L) := Algebra.TensorProduct.rightAlgebra
    letI rightModule : Module L (L ⊗[K] L) := rightAlgebra.toModule
    unfold decompose_tensor_algebra_columns φ₀ φ₁
    simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    exact Basis.baseChangeRight_repr_tmul (b := β) (Right := L) x y v
  decomposeRows_add := fun z z' u => by
    unfold decompose_tensor_algebra_rows
    simp only [map_add, Finsupp.add_apply]
  decomposeRows_tmul := fun x y u => by
    unfold decompose_tensor_algebra_rows φ₀ φ₁
    simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    exact Basis.baseChange_repr_tmul (b := β) (S := L) x y u
  decomposeColumns_injective := by
    letI rightAlgebra : Algebra L (L ⊗[K] L) := Algebra.TensorProduct.rightAlgebra
    letI rightModule : Module L (L ⊗[K] L) := rightAlgebra.toModule
    intro z z' h
    -- `decompose_tensor_algebra_columns β · = (baseChangeRight β).repr ·`, a `LinearEquiv`,
    -- so pointwise equality of column coords forces equality of the `A`-elements.
    apply (Basis.baseChangeRight (b := β) (Right := L)).repr.injective
    apply Finsupp.ext
    intro v
    exact congrFun h v

end RingSwitching
