/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.Prelims
public import ArkLib.Data.Fin.BigOperators
public import ArkLib.Data.CodingTheory.BerlekampWelch.BerlekampWelch
public import ArkLib.Data.CodingTheory.ReedSolomon
public import CompPoly.Fields.Binary.AdditiveNTT.AdditiveNTT
public import ArkLib.Data.MvPolynomial.Multilinear
public import ArkLib.Data.MvPolynomial.RestrictDegree
public import CompPoly.Data.Vector.Basic
public import ArkLib.ProofSystem.Sumcheck.Spec.SingleRound
public import ArkLib.ProofSystem.Sumcheck.Structured.SingleRound
public import ArkLib.ToMathlib.InformationTheory.Hamming
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.RingTheory.Polynomial.DegreeLT
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Binary Basefold Prelude

Core folding definitions and evaluation lemmas for Binary Basefold.

## References

* [Diamond, B.E. and Posen, J., *Polylogarithmic proofs for multilinears over binary towers*][DP24]
  Lemma numbering in this file follows the archived revision of [DP24].
-/

@[expose] public section

namespace Binius.BinaryBasefold

open OracleSpec ProtocolSpec Polynomial MvPolynomial Binius.BinaryBasefold
open scoped NNReal Polynomial
open Finset AdditiveNTT Nat Matrix

/-
## Main definitions
- `qMap_total_fiber_repr_coeff` : the coefficients of the `k`-th `ϑ`-step fiber point of a
  point `y` in the `(i+ϑ)`-th domain.
- `qMap_total_fiber_basis_sum_repr` : sum reprensetation of the `k`-th `ϑ`-step fiber point of a
  point `y` in the `(i+ϑ)`-th domain, relies on `qMap_total_fiber_repr_coeff` for proof.
-/
section Preliminaries

/-- Hamming distance is non-increasing under inner composition with an injective function.
NOTE : we can prove strict equality given `g` being an equivalence instead of injection.
-/
theorem hammingDist_le_of_outer_comp_injective {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    {β : ι₂ → Type*} [∀ i, DecidableEq (β i)]
    (x y : ∀ i, β i) (g : ι₁ → ι₂) (hg : Function.Injective g) :
    hammingDist (fun i => x (g i)) (fun i => y (g i)) ≤ hammingDist x y := by
  classical
  -- Let D₂ be the set of disagreeing indices for x and y.
  let D₂ := Finset.filter (fun i₂ => x i₂ ≠ y i₂) Finset.univ
  -- The Hamming distance of the composed functions is the card of the preimage of D₂.
  suffices (Finset.filter (fun i₁ => x (g i₁) ≠ y (g i₁)) Finset.univ).card ≤ D₂.card by
    unfold hammingDist; simp only [this, D₂]
  -- The cardinality of a preimage is at most the cardinalit
    --  of the original set for an injective function.
  -- ⊢ #{i₁ | x (g i₁) ≠ y (g i₁)} ≤ #D₂
   -- First, we state that the set on the left is the `preimage` of D₂ under g.
  have h_preimage : Finset.filter (fun i₁ => x (g i₁) ≠ y (g i₁)) Finset.univ
    = D₂.preimage g (by exact hg.injOn) := by
    -- Use `ext` to prove equality by showing the membership conditions are the same.
    ext i₁
    -- Now `simp` can easily unfold `mem_filter` and `mem_preimage` and see they are equivalent.
    simp only [ne_eq, mem_filter, mem_univ, true_and, mem_preimage, D₂]
  -- Now, rewrite the goal using `preimage`.
  rw [h_preimage]
  rw [Finset.card_preimage]
  exact Finset.card_filter_le _ _

variable {L : Type*}

/-- Tensor product of challenge vectors : for a local fold length `n`,
`CTensor(n, r_0, ..., r_{n-1}) = ⨂_{j=0}^{n-1}(1-r_j, r_j)` -/
def challengeTensorExpansion [CommRing L] (n : ℕ) (r : Fin n → L) :
    Fin (2 ^ n) → L := multilinearWeight (F := L) (ϑ := n) (r := r)

lemma challengeTensorExpansion_one [CommRing L] (r : L) :
    challengeTensorExpansion 1 (r := fun _ => r) = ![1 - r, r] := by
  unfold challengeTensorExpansion multilinearWeight
  simp only [reducePow, univ_unique, Fin.default_eq_zero, Fin.isValue, Fin.val_eq_zero,
    testBit_zero, decide_eq_true_eq, prod_ite_irrel, prod_const, card_singleton, pow_one,
    succ_eq_add_one, reduceAdd]
  funext i
  by_cases hi_eq_0 : i = 0
  · simp only [hi_eq_0, Fin.isValue, Fin.coe_ofNat_eq_mod, zero_mod, zero_ne_one, ↓reduceIte,
    cons_val_zero]
  · have hi_eq_1 : i = 1 := by omega
    simp only [hi_eq_1, Fin.isValue, Fin.coe_ofNat_eq_mod, mod_succ, ↓reduceIte, cons_val_one,
      cons_val_fin_one]

/-- **Challenge Tensor Expansion Matrix**
Constructs the block-diagonal matrix containing the challenge tensor expansion of
size `n`: `MatrixCTensor(n, r) = [ CTensor(n, r)   0    ]`
                                `[   0     CTensor(n, r) ]` ,
which is used for decomposing `CTensor(n+1, r)` into a vector-matrix multiplication form. -/
def challengeTensorExpansionMatrix [CommRing L] (n : ℕ) (r : Fin n → L) :
    Matrix (Fin 2) (Fin (2 ^ (n + 1))) L :=
  let C_n_finmap := challengeTensorExpansion n r
  let C_n : Matrix (Fin (1)) (Fin (2 ^ n)) L := Matrix.of (fun _rowIdx colIdx => C_n_finmap colIdx)
  -- Create the block diagonal matrix using 1-row matrices
  let emptyBlock : Matrix (Fin 1) (Fin (2 ^ n)) L := 0
  let block := Matrix.from4Blocks (C_n)      emptyBlock
                                 emptyBlock (C_n)
  Matrix.reindex (eₘ := finCongr (by omega)) (eₙ := finCongr (by omega)) block

/-- Challenge Tensor Expansion Matrix multiplication on top half returns M_top * v_top
Proof similar to blockDiagMatrix_mulVec_F₂_eq_Fin_merge_PO2.
-/
lemma challengeTensorExpansionMatrix_mulVec_F₂_eq_Fin_merge_PO2 [CommRing L] (n : ℕ)
    (r : Fin n → L) (v_top : Fin (2 ^ n) → L) (v_bot : Fin (2 ^ n) → L) :
    let C_n_finmap := challengeTensorExpansion (n := n) (r := r)
    let C_n : Matrix (Fin (1)) (Fin (2 ^ n)) L :=
      Matrix.of (fun _rowIdx colIdx => C_n_finmap colIdx)
    (mergeFinMap_PO2_left_right (L := L) (n := 0) ((C_n *ᵥ v_top) : (Fin 1) → L)
      ((C_n *ᵥ v_bot) : (Fin 1) → L) : (Fin 2) → L)
    = (challengeTensorExpansionMatrix (n := n) (r := r)) *ᵥ
      mergeFinMap_PO2_left_right (n := n) v_top v_bot := by
  dsimp only [challengeTensorExpansionMatrix]
  conv_rhs =>
    -- Move reindexing from Matrix to Vector
    rw [Matrix.reindex_mulVec]
  funext k
  unfold mergeFinMap_PO2_left_right
  unfold Matrix.from4Blocks Fin.reindex Matrix.mulVec dotProduct
  -- Now unfold everything
  simp only [Matrix.zero_apply, finCongr_symm, Function.comp_apply, finCongr_apply,
    dite_mul, zero_mul,
    sum_dite_irrel, Fin.val_cast]
  simp_rw [Fin.sum_univ_add]
  simp_rw [←Finset.sum_add_distrib]
  simp only [reduceAdd, reducePow, pow_zero, lt_one_iff, Fin.val_eq_zero_iff, Fin.isValue,
    Nat.pow_zero, of_apply, dite_eq_ite, Fin.val_castAdd, Fin.is_lt, ↓reduceDIte, Fin.eta,
    Fin.natAdd_eq_addNat, Fin.val_addNat, add_lt_iff_neg_right, _root_.not_lt_zero, add_zero,
    add_tsub_cancel_right, zero_add]

/-- **Challenge Tensor Expansion Decomposition Lemma (Vector-Matrix multiplication form)**
Prove that `CTensor(n+1, r_0, ..., r_n) = [1-r_n, r_n] * MatrixCTensor(n, r_0, ..., r_{n-1})` -/
lemma challengeTensorExpansion_decompose_succ [CommRing L] (n : ℕ) (r : Fin (n + 1) → L) :
    challengeTensorExpansion (n + 1) (r := r) = ![1 - r (Fin.last n), r (Fin.last n)]
      ᵥ* (challengeTensorExpansionMatrix n (r := Fin.init r)) := by
  funext colIdx
  unfold challengeTensorExpansionMatrix challengeTensorExpansion
  simp only [succ_eq_add_one, reduceAdd, reindex_apply]
  simp only [vecMul_eq_sum, Finset.sum_apply, Pi.smul_apply, submatrix_apply, smul_eq_mul,
    Fin.sum_univ_two, Fin.isValue, cons_val_zero, cons_val_one, cons_val_fin_one]
  dsimp only [finCongr_symm, finCongr_apply, Fin.cast_eq_self, Fin.isValue]
  unfold Matrix.from4Blocks
  by_cases h_colIdx_lt_2_pow_n : colIdx.val < 2 ^ n
  · simp only [reduceAdd, Fin.isValue, Fin.coe_ofNat_eq_mod, zero_mod, zero_lt_one, ↓reduceDIte,
    finCongr_apply_coe, h_colIdx_lt_2_pow_n, Fin.zero_eta, of_apply, mod_succ, lt_self_iff_false,
    Matrix.zero_apply, mul_zero, add_zero]
    rw [multilinearWeight_succ_lower_half (r := r) (i := colIdx)
      (h_lt := h_colIdx_lt_2_pow_n), mul_comm]
  · have h_ne_lt_2_pow_n : ¬(colIdx.val < 2 ^ n) := by exact h_colIdx_lt_2_pow_n
    simp only [reduceAdd, Fin.isValue, Fin.coe_ofNat_eq_mod, zero_mod, zero_lt_one, ↓reduceDIte,
      finCongr_apply_coe, h_ne_lt_2_pow_n, Matrix.zero_apply, mul_zero, mod_succ,
      lt_self_iff_false, tsub_self,
      Fin.zero_eta, of_apply, zero_add]
    let u : Fin (2 ^ n) := ⟨colIdx.val - (2 ^ n), by omega⟩
    have h_eq: colIdx.val = u.val + (2 ^ n) := by dsimp only [u]; omega
    rw [multilinearWeight_succ_upper_half (r := r) (i := colIdx) (j := u)
      (h_eq := h_eq), mul_comm]

variable {L : Type} [CommRing L] (ℓ : ℕ) [NeZero ℓ]
variable (𝓑 : Fin 2 ↪ L)

noncomputable abbrev MultilinearPoly (L : Type) [CommSemiring L] (ℓ : ℕ) := L⦃≤ 1⦄[X Fin ℓ]
noncomputable abbrev MultiquadraticPoly (L : Type) [CommSemiring L] (ℓ : ℕ) := L⦃≤ 2⦄[X Fin ℓ]

/-- Fixes the first `v` variables of a `ℓ`-variate multivariate polynomial.
`t` -> `H_i` derivation
-/
def splitFirstVariables (v : Fin (ℓ + 1)) : Fin ℓ → Fin (ℓ - v) ⊕ Fin v :=
  fun j =>
    if hj : j.val < v.val then
      Sum.inr ⟨j.val, hj⟩
    else
      Sum.inl ⟨j.val - v, by omega⟩

def mergeFirstVariables (v : Fin (ℓ + 1)) : Fin (ℓ - v) ⊕ Fin v → Fin ℓ
  | Sum.inl j => ⟨j.val + v, by omega⟩
  | Sum.inr j => ⟨j.val, by omega⟩

def splitFirstVariablesEquiv (v : Fin (ℓ + 1)) : Fin ℓ ≃ Fin (ℓ - v) ⊕ Fin v where
  toFun := splitFirstVariables (ℓ := ℓ) v
  invFun := mergeFirstVariables (ℓ := ℓ) v
  left_inv := by
    intro j
    dsimp [splitFirstVariables, mergeFirstVariables]
    by_cases hj : j.val < v.val
    · simp [hj]
    · simp only [hj, ↓reduceDIte]
      apply Fin.ext
      exact Nat.sub_add_cancel (Nat.le_of_not_lt hj)
  right_inv := by
    intro j
    cases j with
    | inl j =>
        dsimp [splitFirstVariables, mergeFirstVariables]
        have hj : ¬ j.val + v < v := by omega
        simp [hj]
    | inr j =>
        dsimp [splitFirstVariables, mergeFirstVariables]
        have hj : j.val < v := j.isLt
        simp [hj]

noncomputable def fixFirstVariablesOfMQP (v : Fin (ℓ + 1))
  (H : MvPolynomial (Fin ℓ) L) (challenges : Fin v → L) : MvPolynomial (Fin (ℓ - v)) L :=
  -- Step 1 : Rename L[X Fin ℓ] to L[X (Fin (ℓ - v) ⊕ Fin v)], sending
  -- the first `v` variables to `Sum.inr` so they can be evaluated away.
  let H_sum : L[X (Fin (ℓ - v) ⊕ Fin v)] := by
    apply MvPolynomial.rename (f := splitFirstVariablesEquiv (ℓ := ℓ) v) H
  -- Step 2 : Convert to (L[X Fin v])[X Fin (ℓ - v)] via sumAlgEquiv
  let H_forward : L[X Fin v][X Fin (ℓ - v)] := (sumAlgEquiv L (Fin (ℓ - v)) (Fin v)) H_sum
  -- Step 3 : Evaluate the poly at the point challenges to get a final L[X Fin (ℓ - v)]
  let eval_map : L[X Fin ↑v] →+* L := (eval challenges : MvPolynomial (Fin v) L →+* L)
  MvPolynomial.map (f := eval_map) (σ := Fin (ℓ - v)) H_forward

private lemma sumAlgEquiv_mem_restrictDegree {R : Type*} [CommSemiring R]
    {S₁ S₂ : Type*}
    (p : MvPolynomial (S₁ ⊕ S₂) R) (n : ℕ)
    (hp : p ∈ MvPolynomial.restrictDegree (S₁ ⊕ S₂) R n) :
    (MvPolynomial.sumAlgEquiv R S₁ S₂) p ∈
      MvPolynomial.restrictDegree S₁ (MvPolynomial S₂ R) n := by
  change (MvPolynomial.sumAlgEquiv R S₁ S₂) p ∈
    MvPolynomial.restrictDegreeVar S₁ (MvPolynomial S₂ R)
      ((fun _ : S₁ ⊕ S₂ => n) ∘ (Sum.inl : S₁ → S₁ ⊕ S₂))
  change p ∈ MvPolynomial.restrictDegreeVar (S₁ ⊕ S₂) R (fun _ => n) at hp
  exact MvPolynomial.sumAlgEquiv_mem_restrictDegreeVar (p := p) (b := fun _ => n) hp

private lemma rename_equiv_mem_restrictDegree {R : Type*} [CommSemiring R]
    {σ τ : Type*}
    (e : σ ≃ τ) (p : MvPolynomial σ R) (n : ℕ)
    (hp : p ∈ MvPolynomial.restrictDegree σ R n) :
    (MvPolynomial.rename e p) ∈ MvPolynomial.restrictDegree τ R n := by
  change (MvPolynomial.rename e p) ∈ MvPolynomial.restrictDegreeVar τ R
    ((fun _ : σ => n) ∘ e.symm)
  change p ∈ MvPolynomial.restrictDegreeVar σ R (fun _ => n) at hp
  exact MvPolynomial.rename_equiv_mem_restrictDegreeVar e p (b := fun _ => n) hp

private lemma eval_map_sumAlgEquiv {R : Type*} [CommSemiring R]
    {S₁ S₂ : Type*} (x : S₁ → R) (y : S₂ → R) :
    ((MvPolynomial.eval x).comp
      ((MvPolynomial.map (MvPolynomial.eval y)).comp
        ((MvPolynomial.sumAlgEquiv R S₁ S₂).toRingHom))) =
      (MvPolynomial.eval (Sum.elim x y) : MvPolynomial (S₁ ⊕ S₂) R →+* R) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, MvPolynomial.eval_C]
    rw [show ((MvPolynomial.sumAlgEquiv R S₁ S₂).toRingEquiv.toRingHom) (MvPolynomial.C r) =
      MvPolynomial.C (MvPolynomial.C r) by
        exact MvPolynomial.sumAlgEquiv_C_inl R S₁ S₂ r]
    simp
  · intro i
    cases i with
    | inl i =>
        simp only [RingHom.comp_apply, MvPolynomial.eval_X, Sum.elim_inl]
        rw [show ((MvPolynomial.sumAlgEquiv R S₁ S₂).toRingEquiv.toRingHom)
          (MvPolynomial.X (.inl i)) = MvPolynomial.X i by
            exact MvPolynomial.sumAlgEquiv_X_inl R S₁ S₂ i]
        simp
    | inr i =>
        simp only [RingHom.comp_apply, MvPolynomial.eval_X, Sum.elim_inr]
        rw [show ((MvPolynomial.sumAlgEquiv R S₁ S₂).toRingEquiv.toRingHom)
          (MvPolynomial.X (.inr i)) = MvPolynomial.C (MvPolynomial.X i) by
            exact MvPolynomial.sumAlgEquiv_X_inr R S₁ S₂ i]
        simp

omit [NeZero ℓ] in
lemma fixFirstVariablesOfMQP_eval_eq (v : Fin (ℓ + 1)) {challenges : Fin v → L}
    {poly : L[X Fin ℓ]} (x : Fin (ℓ - v) → L) :
    (fixFirstVariablesOfMQP ℓ v poly challenges).eval x =
      poly.eval (fun j =>
        if hj : j.val < v.val then
          challenges ⟨j.val, hj⟩
        else
          x ⟨j.val - v, by omega⟩) := by
  have h_fun :
      (Sum.elim x challenges) ∘ splitFirstVariablesEquiv (ℓ := ℓ) v =
        (fun j =>
          if hj : j.val < v.val then
            challenges ⟨j.val, hj⟩
          else
            x ⟨j.val - v, by omega⟩) := by
    funext j
    dsimp [splitFirstVariablesEquiv, splitFirstVariables]
    by_cases hj : j.val < v.val
    · simp [hj]
    · simp [hj]
  have h_eval :=
    DFunLike.congr_fun
      (eval_map_sumAlgEquiv (R := L) (S₁ := Fin (ℓ - v)) (S₂ := Fin v) x challenges)
      (MvPolynomial.rename (splitFirstVariablesEquiv (ℓ := ℓ) v) poly)
  unfold fixFirstVariablesOfMQP
  dsimp
  exact h_eval.trans (by
    rw [MvPolynomial.eval_rename, h_fun])

omit [NeZero ℓ] in
/-- Auxiliary lemma for proving that the polynomial sent by the honest prover is of degree at most
`deg` -/
theorem fixFirstVariablesOfMQP_degreeLE {deg : ℕ} (v : Fin (ℓ + 1)) {challenges : Fin v → L}
    {poly : L[X Fin ℓ]} (hp : poly ∈ L⦃≤ deg⦄[X Fin ℓ]) :
    fixFirstVariablesOfMQP ℓ v poly challenges ∈ L⦃≤ deg⦄[X Fin (ℓ - v)] := by
  -- The goal is to prove the totalDegree of the result is ≤ deg.
  rw [MvPolynomial.mem_restrictDegree]
  unfold fixFirstVariablesOfMQP
  dsimp only
  intro term h_term_in_support i
  -- ⊢ term i ≤ deg
  set splitEquiv := splitFirstVariablesEquiv (ℓ := ℓ) v
  set H_sum := MvPolynomial.rename (f := splitEquiv) poly
  set H_grouped : L[X Fin ↑v][X Fin (ℓ - ↑v)] := (sumAlgEquiv L (Fin (ℓ - v)) (Fin v)) H_sum
  set eval_map : L[X Fin ↑v] →+* L := (eval challenges : MvPolynomial (Fin v) L →+* L)
  have h_Hgrouped_degreeLE : H_grouped ∈ (L[X Fin ↑v])⦃≤ deg⦄[X Fin (ℓ - ↑v)] := by
    exact Binius.BinaryBasefold.sumAlgEquiv_mem_restrictDegree H_sum deg
      (Binius.BinaryBasefold.rename_equiv_mem_restrictDegree
        splitEquiv poly deg hp)
  have h_mem_support_max_deg_LE := MvPolynomial.mem_restrictDegree (R := L[X Fin ↑v]) (n := deg)
    (σ := Fin (ℓ - ↑v)) (p := H_grouped).mp (h_Hgrouped_degreeLE)
  have h_term_in_Hgrouped_support : term ∈ H_grouped.support := by
    have h_support_map_subset : ((MvPolynomial.map eval_map) H_grouped).support
      ⊆ H_grouped.support := by apply MvPolynomial.support_map_subset
    exact (h_support_map_subset) h_term_in_support
  -- h_Hgrouped_degreeLE
  let res : term i ≤ deg := h_mem_support_max_deg_LE term h_term_in_Hgrouped_support i
  exact res

/- `H_i(X_i, ..., X_{ℓ-1})` -> `g_i(X)` derivation -/
noncomputable def getSumcheckRoundPoly (i : Fin ℓ) (h : ↥L⦃≤ 2⦄[X Fin (ℓ - ↑i.castSucc)]) :
    L⦃≤ 2⦄[X] := by
  have h_i_lt_ℓ : ℓ - ↑i.castSucc > 0 := by
    have hi := i.2
    exact Nat.zero_lt_sub_of_lt hi
  have h_count_eq : ℓ - ↑i.castSucc - 1 + 1 = ℓ - ↑i.castSucc := by
    omega
  let challenges : Fin 0 → L := fun (j : Fin 0) => j.elim0
  let curH_cast : L[X Fin ((ℓ - ↑i.castSucc - 1) + 1)] := by
    convert h.val
  let g := ∑ x ∈ (univ.map 𝓑) ^ᶠ (ℓ - ↑i.castSucc - 1), curH_cast ⸨X ⦃0⦄, challenges, x⸩' (by omega)
  exact ⟨g, by
    have h_deg_le_2 : g ∈ L⦃≤ 2⦄[X] := by
      simp only [g]
      let hDegIn := Sumcheck.Spec.SingleRound.sumcheck_roundPoly_degreeLE
        (R := L) (D := 𝓑) (n := ℓ - ↑i.castSucc - 1) (deg := 2) (i := ⟨0, by omega⟩)
        (challenges := fun j => j.elim0) (poly := curH_cast)
      have h_in_degLE : curH_cast ∈ L⦃≤ 2⦄[X Fin (ℓ - ↑i.castSucc - 1 + 1)] := by
        rw! (castMode := .all) [h_count_eq]
        dsimp only [Fin.val_castSucc, eq_mpr_eq_cast, curH_cast]
        rw [eqRec_eq_cast, cast_cast, cast_eq]
        exact h.property
      let res := hDegIn h_in_degLE
      exact res
    rw [mem_degreeLE] at h_deg_le_2 ⊢
    exact h_deg_le_2
  ⟩

private lemma cube_eval_sum_cons (n : ℕ) (p : L[X Fin (n + 1)]) :
    ∑ y ∈ (univ.map 𝓑) ^ᶠ (n + 1), MvPolynomial.eval y p =
      ∑ a ∈ univ.map 𝓑, ∑ x ∈ (univ.map 𝓑) ^ᶠ n, MvPolynomial.eval (Fin.cons a x) p := by
  have h_pi := Finset.filter_piFinset_eq_map_consEquiv
    (S := fun _ : Fin (n + 1) => univ.map 𝓑) (P := fun _ => True)
  simp only [Finset.filter_true] at h_pi
  rw [h_pi, Finset.sum_map, Finset.sum_product]
  congr 1

omit [NeZero ℓ] in
lemma getSumcheckRoundPoly_eval_eq (i : Fin ℓ) (h_poly : ↥L⦃≤ 2⦄[X Fin (ℓ - ↑i.castSucc)])
    (r : L) :
    (getSumcheckRoundPoly ℓ 𝓑 i h_poly).val.eval r =
    ∑ x ∈ (univ.map 𝓑) ^ᶠ (ℓ - ↑i.castSucc - 1),
      MvPolynomial.eval (Fin.cons r x ∘ Fin.cast (by
        exact (Nat.sub_add_cancel (Nat.one_le_of_lt (Nat.sub_pos_of_lt i.isLt))).symm
      )) h_poly.val := by
  have h_pos : 0 < (ℓ - ↑i.castSucc) := Nat.sub_pos_of_lt i.isLt
  have h_eq_nat : (ℓ - ↑i.castSucc) = ((ℓ - ↑i.castSucc) - 1) + 1 :=
    (Nat.sub_add_cancel (Nat.one_le_of_lt h_pos)).symm
  have h_cast_rename {n m : ℕ} (h : n = m) (p : L[X Fin n]) :
      cast (congrArg (fun k => L[X Fin k]) h) p = MvPolynomial.rename (Fin.cast h) p := by
    cases h
    simp
  unfold getSumcheckRoundPoly
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_map]
  apply Finset.sum_congr rfl
  intro x hx
  let ψ : Fin (ℓ - ↑i.castSucc) ≃ Fin (((ℓ - ↑i.castSucc) - 1) + 1) :=
    { toFun := Fin.cast h_eq_nat
      invFun := Fin.cast h_eq_nat.symm
      left_inv := fun _ => Fin.ext (by simp)
      right_inv := fun _ => Fin.ext (by simp) }
  let h_val' := MvPolynomial.rename ψ h_poly.val
  have h_eval_eq : MvPolynomial.eval (Fin.cons r x ∘ Fin.cast h_eq_nat) h_poly.val =
                   MvPolynomial.eval (Fin.cons r x) h_val' := by
    rw [MvPolynomial.eval_rename]
    rfl
  have h_cast_op : Fin.cast (by
    exact (Nat.sub_add_cancel (Nat.one_le_of_lt (Nat.sub_pos_of_lt i.isLt))).symm)
      = Fin.cast h_eq_nat := rfl
  rw [h_cast_op]
  trans MvPolynomial.eval (Fin.insertNth 0 r x) h_val'
  swap
  · conv_lhs => rw [Fin.insertNth_zero]
    exact h_eval_eq.symm
  · rw [MvPolynomial.eval_eq_eval_mv_eval_finSuccEquivNth (p := 0)]
    have h_eval_append :
        MvPolynomial.eval (Fin.append (fun j : Fin 0 => j.elim0) x ∘
          Fin.cast (Nat.zero_add _).symm) = MvPolynomial.eval x := by
      ext j
      · simp only [RingHom.comp_apply, Fin.elim0_append, MvPolynomial.eval_C]
      · simp only [Fin.elim0_append, MvPolynomial.eval_X,
          Function.comp_apply, Fin.cast_cast]
        rfl
    rw [h_eval_append]
    simp only [Polynomial.eval_map]
    have h_cast_eq : cast (congrArg (fun k => L[X Fin k]) h_eq_nat) h_poly.val = h_val' := by
      change cast (congrArg (fun k => L[X Fin k]) h_eq_nat) h_poly.val =
        MvPolynomial.rename (Fin.cast h_eq_nat) h_poly.val
      exact h_cast_rename h_eq_nat h_poly.val
    exact congrArg
      (fun p => Polynomial.eval₂ (MvPolynomial.eval x) r ((MvPolynomial.finSuccEquivNth L 0) p))
      h_cast_eq

omit [NeZero ℓ] in
lemma getSumcheckRoundPoly_sum_eq (i : Fin ℓ) (h : ↥L⦃≤ 2⦄[X Fin (ℓ - ↑i.castSucc)]) :
    (getSumcheckRoundPoly ℓ 𝓑 i h).val.eval (𝓑 0) + (getSumcheckRoundPoly ℓ 𝓑 i h).val.eval (𝓑 1) =
    ∑ x ∈ (univ.map 𝓑) ^ᶠ (ℓ - ↑i.castSucc), MvPolynomial.eval x h.val := by
  rw [getSumcheckRoundPoly_eval_eq, getSumcheckRoundPoly_eval_eq, ← Finset.sum_add_distrib]
  have h_pos : 0 < (ℓ - ↑i.castSucc) := Nat.sub_pos_of_lt i.isLt
  have hm : (ℓ - ↑i.castSucc) = ((ℓ - ↑i.castSucc) - 1) + 1 :=
    (Nat.sub_add_cancel (Nat.one_le_of_lt h_pos)).symm
  let ψ : Fin (ℓ - ↑i.castSucc) ≃ Fin (((ℓ - ↑i.castSucc) - 1) + 1) :=
    { toFun := Fin.cast hm
      invFun := Fin.cast hm.symm
      left_inv := fun _ => Fin.ext (by simp)
      right_inv := fun _ => Fin.ext (by simp) }
  let h_val' := MvPolynomial.rename ψ h.val
  have h_eval_cons (a : L) (x : Fin (ℓ - ↑i.castSucc - 1) → L) :
      MvPolynomial.eval (Fin.cons a x ∘ Fin.cast hm) h.val =
        MvPolynomial.eval (Fin.cons a x) h_val' := by
    rw [MvPolynomial.eval_rename]
    rfl
  have h_sum :
      ∑ x ∈ (univ.map 𝓑) ^ᶠ (ℓ - ↑i.castSucc), MvPolynomial.eval x h.val =
        ∑ y ∈ (univ.map 𝓑) ^ᶠ (((ℓ - ↑i.castSucc) - 1) + 1), MvPolynomial.eval y h_val' := by
    let e_pi : (Fin (ℓ - ↑i.castSucc) → L) ≃ (Fin (((ℓ - ↑i.castSucc) - 1) + 1) → L) :=
      { toFun := fun x => x ∘ ψ.symm
        invFun := fun y => y ∘ ψ
        left_inv := by intro x; ext a; rfl
        right_inv := by intro y; ext a; rfl }
    apply Finset.sum_equiv e_pi
    · intro x
      simp only [Fintype.mem_piFinset, e_pi]
      constructor
      · intro hx a
        exact hx (ψ.symm a)
      · intro hx a
        exact hx (ψ a)
    · intro x hx
      rw [MvPolynomial.eval_rename]
      rfl
  erw [h_sum]
  rw [cube_eval_sum_cons, Finset.sum_map, Fin.sum_univ_two, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  rw [h_eval_cons (𝓑 0), h_eval_cons (𝓑 1)]

/-- Helper to convert an index `k` into a vector of bits (as field elements). -/
def bitsOfIndex {n : ℕ} (k : Fin (2 ^ n)) : Fin n → L :=
  fun i => if Nat.testBit k i then 1 else 0

/-- The double coercion `Fin (2^n) → (Fin n → Fin 2) → (Fin n → L)` equals `bitsOfIndex`.
This connects the implicit coercion used in `polynomialFromNovelCoeffsF₂` with the explicit
bit extraction, which is essential for proving multilinear polynomial evaluation formulas. -/
lemma coe_fin_pow_two_eq_bitsOfIndex {n : ℕ} (k : Fin (2 ^ n)) :
    ((finFunctionFinEquiv.invFun k : Fin n → Fin 2) : Fin n → L) = bitsOfIndex k := by
  ext i
  simp only [bitsOfIndex]
  simp only [Equiv.invFun_as_coe, finFunctionFinEquiv_symm_apply_val]
  conv_lhs =>
    rw [←Nat.shiftRight_eq_div_pow, ←Nat.and_one_is_mod]
    change Nat.getBit (k := i) (n := k)
  rw [Nat.getBit_eq_testBit]
  split
  · simp only [cast_one]
  · simp only [cast_zero]

omit [NeZero ℓ] in
/-- **Multilinear extension over the Boolean hypercube**:
as the sum of its values on all Boolean vertices `bitsOfIndex x`, weighted by
`multilinearWeight challenges x`, the standard multilinear “eq” polynomial.
i.e., `t(challenges) = ∑ x ∈ {0, 1}, eq(challenges, x) * t(x)`.
-/
lemma eval_eqPolynomial_bitsOfIndex [IsDomain L]
    (challenges : Fin ℓ → L) (k : Fin (2 ^ ℓ)) :
    MvPolynomial.eval challenges (MvPolynomial.eqPolynomial (bitsOfIndex (L := L) k)) =
      multilinearWeight (r := challenges) (i := k) := by
  unfold MvPolynomial.eqPolynomial multilinearWeight bitsOfIndex
  rw [MvPolynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro j hj
  by_cases hbit : k.val.testBit j.val
  · simp [hbit]
  · simp [hbit]

omit [NeZero ℓ] in
theorem multilinear_eval_eq_sum_bool_hypercube [IsDomain L]
    (challenges : Fin ℓ → L) (t : ↥L⦃≤ 1⦄[X Fin ℓ]) :
    t.val.eval challenges = ∑ (x : Fin (2^ℓ)),
      (multilinearWeight (r := challenges) (i := x)) * (t.val.eval (bitsOfIndex x) : L) := by
  have h_multilinear : MvPolynomial.MLE
      (fun x : Fin ℓ → Fin 2 => MvPolynomial.eval (x : Fin ℓ → L) t.val) = t.val := by
    exact (MvPolynomial.is_multilinear_iff_eq_evals_zeroOne (p := t.val)).mp t.property
  calc
    t.val.eval challenges = MvPolynomial.eval challenges
        (MvPolynomial.MLE (fun x : Fin ℓ → Fin 2 => MvPolynomial.eval (x : Fin ℓ → L) t.val)) := by
      exact congrArg (MvPolynomial.eval challenges) h_multilinear.symm
    _ = ∑ x : Fin ℓ → Fin 2,
          MvPolynomial.eval challenges (MvPolynomial.eqPolynomial (x : Fin ℓ → L)) *
            MvPolynomial.eval (x : Fin ℓ → L) t.val := by
      unfold MvPolynomial.MLE
      simp only [MvPolynomial.eval_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C]
    _ = ∑ x : Fin (2 ^ ℓ),
          multilinearWeight (r := challenges) (i := x) *
            MvPolynomial.eval (bitsOfIndex x) t.val := by
      apply Fintype.sum_equiv finFunctionFinEquiv
      intro x
      have hx_bits : (x : Fin ℓ → L) = bitsOfIndex (L := L) (finFunctionFinEquiv x) := by
        rw [← coe_fin_pow_two_eq_bitsOfIndex (L := L) (k := finFunctionFinEquiv x)]
        simp
      calc
        MvPolynomial.eval challenges (MvPolynomial.eqPolynomial (x : Fin ℓ → L)) *
            MvPolynomial.eval (x : Fin ℓ → L) t.val
          = MvPolynomial.eval challenges
              (MvPolynomial.eqPolynomial (bitsOfIndex (L := L) (finFunctionFinEquiv x))) *
              MvPolynomial.eval (bitsOfIndex (L := L) (finFunctionFinEquiv x)) t.val := by
              rw [hx_bits]
        _ = multilinearWeight (r := challenges) (i := finFunctionFinEquiv x) *
              MvPolynomial.eval (bitsOfIndex (L := L) (finFunctionFinEquiv x)) t.val := by
              rw [eval_eqPolynomial_bitsOfIndex (L := L) (ℓ := ℓ)]

end Preliminaries

noncomputable section       -- expands with 𝔽q in front
variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} (γ_repetitions : ℕ) [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ] -- Should we allow ℓ = 0?
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r} -- ℓ ∈ {1, ..., r-1}
variable {𝓑 : Fin 2 ↪ L}

section Essentials
-- In this section, we ue notation `ϑ` for the folding steps, along with `(hdiv : ϑ ∣ ℓ)`

/-- Oracle function type for round i.
f^(i) : S⁽ⁱ⁾ → L, where |S⁽ⁱ⁾| = 2^{ℓ + R - i} -/
abbrev OracleFunction (domainIdx : Fin r) := sDomain 𝔽q β h_ℓ_add_R_rate domainIdx → L
-- abbrev OracleFunction (i : Fin (ℓ + 1)) : Type _ := sDomain 𝔽q β h_ℓ_add_R_rate ⟨i, by
--   exact Nat.lt_of_le_of_lt (n := i) (k := r) (m := ℓ) (h₁ := by exact Fin.is_le i)
--     (by exact lt_of_add_right_lt h_ℓ_add_R_rate)⟩ → L

omit [NeZero ℓ] in
lemma fin_ℓ_lt_ℓ_add_one (i : Fin ℓ) : i < ℓ + 1 :=
  Nat.lt_of_lt_of_le i.isLt (Nat.le_succ ℓ)

omit [NeZero ℓ] [NeZero r] [NeZero 𝓡] in
lemma fin_ℓ_lt_ℓ_add_R (i : Fin ℓ) : i.val < ℓ + 𝓡 := by omega

omit [NeZero ℓ] [NeZero r] [NeZero 𝓡] in
lemma fin_ℓ_lt_r {h_ℓ_add_R_rate : ℓ + 𝓡 < r} (i : Fin ℓ) : i.val < r := by omega

omit [NeZero ℓ] [NeZero r] [NeZero 𝓡] in
lemma fin_ℓ_add_one_lt_r {h_ℓ_add_R_rate : ℓ + 𝓡 < r} (i : Fin (ℓ + 1)) : i.val < r := by omega

omit [NeZero ℓ] in
lemma fin_ℓ_steps_lt_ℓ_add_one (i : Fin ℓ) (steps : ℕ)
    (h : i.val + steps ≤ ℓ) : i.val + steps < ℓ + 1 :=
  Nat.lt_of_le_of_lt h (Nat.lt_succ_self ℓ)

omit [NeZero ℓ] in
lemma fin_ℓ_steps_lt_ℓ_add_R (i : Fin ℓ) (steps : ℕ) (h : i.val + steps ≤ ℓ) :
    i.val + steps < ℓ + 𝓡 := by
  apply Nat.lt_add_of_pos_right_of_le; omega

omit [NeZero ℓ] [NeZero r] [NeZero 𝓡] in
lemma fin_ℓ_steps_lt_r {h_ℓ_add_R_rate : ℓ + 𝓡 < r} (i : Fin ℓ) (steps : ℕ)
    (h : i.val + steps ≤ ℓ) : i.val + steps < r := by
  apply Nat.lt_of_le_of_lt (n := i + steps) (k := r) (m := ℓ) (h₁ := h)
    (by exact lt_of_add_right_lt h_ℓ_add_R_rate)

omit [NeZero ℓ] [NeZero r] [NeZero 𝓡] in
lemma ℓ_lt_r {h_ℓ_add_R_rate : ℓ + 𝓡 < r} : ℓ < r := by omega

omit [NeZero ℓ] [NeZero r] [NeZero 𝓡] in
lemma fin_r_succ_bound {h_ℓ_add_R_rate : ℓ + 𝓡 < r} (i : Fin r)
    (h_i : i + 1 < ℓ + 𝓡) : i + 1 < r := by omega

/-- Helper: Bound proof for the indices -/
lemma index_bound_check {ℓ i steps : ℕ} (j m : ℕ)
    (hj : j < 2 ^ (ℓ - (i + steps))) (hm : m < 2 ^ steps) (h_le : i + steps ≤ ℓ) :
    j * 2 ^ steps + m < 2 ^ (ℓ - i) := by
  -- Arithmetic proof: j * 2^s + m < (j+1) * 2^s <= 2^(L-i-s) * 2^s = 2^(L-i)
  calc
    j * 2 ^ steps + m
    _ < j * 2 ^ steps + 2 ^ steps := by apply Nat.add_lt_add_left hm
    _ = (j + 1) * 2 ^ steps := by ring
    _ ≤ (2 ^ (ℓ - (i + steps))) * 2 ^ steps := by
      apply Nat.mul_le_mul_right
      exact hj
    _ = 2 ^ (ℓ - i - steps + steps) := by
      rw [←Nat.pow_add]; simp only [ofNat_pos, ne_eq, OfNat.ofNat_ne_one, not_false_eq_true,
        pow_right_inj₀, Nat.add_right_cancel_iff]; omega
    _ = 2 ^ (ℓ - i) := by
      congr 1
      rw [Nat.sub_add_cancel]
      -- Proof that steps ≤ ℓ - i
      apply Nat.le_sub_of_add_le
      omega

omit [NeZero r] [NeZero ℓ] in
lemma Sdomain_bound {x : ℕ} (h_x : x ≤ ℓ) :
    x < ℓ + 𝓡 := by
  apply Nat.lt_add_of_pos_right_of_le; omega
section FiberMath
/-!
### The Fiber of the Quotient Map `qMap`

Utilities for constructing fibers and defining the fold operations used by Binary Basefold.
-/

def Fin2ToF2 (𝔽q : Type*) [Ring 𝔽q] (k : Fin 2) : 𝔽q :=
  if k = 0 then 0 else 1

/-- Helper for the fiber coefficients used in `qMap_total_fiber`.
It computes the coefficient of the `j`-th basis vector for a point (indexed by `elementIdx`)
in the fiber list of `y ∈ S^{i+steps-1}`.
- If `j < steps`, the coefficient comes from the binary expansion of `elementIdx`.
- If `j ≥ steps`, the coefficient comes from `y_coeffs` (coefficients of the target point `y`). -/
noncomputable def fiber_coeff
    (i : Fin r) (steps : ℕ)
    {destIdx : Fin r} (h_destIdx : destIdx.val = i.val + steps)
    -- Input j is just an index in the source dimension
    (basisIdx : Fin (ℓ + 𝓡 - i))
    (elementIdx : Fin (2 ^ steps))
    -- y_coeffs now uses the clean 'destIdx'
    (y_coeffs : Fin (ℓ + 𝓡 - destIdx) →₀ 𝔽q) : 𝔽q :=
  if hj : basisIdx.val < steps then
    if Nat.getBit (k := basisIdx) (n := elementIdx) = 0 then 0 else 1
  else
    -- We need to access y_coeffs at (basisIdx - steps).
    -- We must prove (j - steps) < (ℓ + 𝓡 - destIdx).
    y_coeffs ⟨basisIdx.val - steps, by
      -- Clean proof using the equality h_dest
      rw [h_destIdx]
      rw [←Nat.sub_sub]
      apply Nat.sub_lt_sub_right
      · exact Nat.le_of_not_lt hj
      · exact basisIdx.isLt⟩

/-- Get the full fiber list `(x₀, ..., x_{2 ^ steps-1})` which represents the
joined fiber `(q⁽ⁱ⁺steps⁻¹⁾ ∘ ⋯ ∘ q⁽ⁱ⁾)⁻¹({y}) ⊂ S⁽ⁱ⁾` over `y ∈ S^(i+steps)`,
in which the LSB repsents the FIRST qMap `q⁽ⁱ⁾`, and the MSB represents the LAST `q⁽ⁱ⁺steps⁻¹⁾`
-/
noncomputable def qMap_total_fiber
    -- S^i is source domain, S^{i + steps} is the target domain
    (i : Fin r) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps)
    (h_destIdx_le: destIdx ≤ ℓ)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := destIdx)) :
    Fin (2 ^ steps) → sDomain 𝔽q β h_ℓ_add_R_rate i :=
  if h_steps : steps = 0 then by
    -- Base case : 0 steps, the fiber is just the point y itself.
    subst h_steps
    have h_i_eq_j : i = destIdx := by omega
    subst h_i_eq_j
    -- simp only [add_zero, Fin.eta] at y
    exact fun _ => y
  else by
    -- fun (k : 𝔽q) =>
    let basis_y := sDomain_basis 𝔽q β h_ℓ_add_R_rate (i := destIdx)
      (h_i := Sdomain_bound (by omega))
    let y_coeffs : Fin (ℓ + 𝓡 - destIdx) →₀ 𝔽q := basis_y.repr y
    let basis_x := sDomain_basis 𝔽q β h_ℓ_add_R_rate i (h_i := by omega)
    exact fun elementIdx => by
      let x_coeffs : Fin (ℓ + 𝓡 - i) → 𝔽q := fun j =>
        if hj_lt_steps : j.val < steps then
          if Nat.getBit (k := j) (n := elementIdx) = 0 then (0 : 𝔽q)
          else (1 : 𝔽q)
        else
          y_coeffs ⟨j.val - steps, by omega⟩  -- Shift indices to match y's basis
      exact basis_x.repr.symm ((Finsupp.equivFunOnFinite).symm x_coeffs)

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
lemma qMap_total_fiber_congr_steps
    {i : Fin r} (steps steps' : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx = i.val + steps)
    (h_destIdx_le : destIdx ≤ ℓ)
    (h_steps_eq : steps = steps')
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := destIdx)) :
    qMap_total_fiber 𝔽q β (i := i) (steps := steps) (h_destIdx := h_destIdx)
      (h_destIdx_le := h_destIdx_le) (y := y) =
    fun (x : Fin (2 ^ steps)) ↦
      qMap_total_fiber 𝔽q β (i := i) (steps := steps') (h_destIdx := by omega)
        (h_destIdx_le := h_destIdx_le) (y := y)
        ⟨x.val, by subst h_steps_eq; exact x.is_lt⟩ := by
  subst h_steps_eq; rfl

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
lemma qMap_total_fiber_congr_source
    {sourceIdx₁ sourceIdx₂ : Fin r} (steps : ℕ) {destIdx : Fin r}
    (h_sourceIdx_eq : sourceIdx₁ = sourceIdx₂)
    (h_destIdx : destIdx = sourceIdx₁.val + steps)
    (h_destIdx_le : destIdx ≤ ℓ)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := destIdx)) :
    qMap_total_fiber 𝔽q β (i := sourceIdx₁) (steps := steps) (h_destIdx := h_destIdx)
      (h_destIdx_le := h_destIdx_le) (y := y) =
    cast (by subst h_sourceIdx_eq; rfl) (qMap_total_fiber 𝔽q β (i := sourceIdx₂)
      (steps := steps) (h_destIdx := by omega) (h_destIdx_le := h_destIdx_le) (y := y)) := by
  subst h_sourceIdx_eq; rfl

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
lemma qMap_total_fiber_congr_source_apply
    {sourceIdx₁ sourceIdx₂ : Fin r} (steps : ℕ) {destIdx : Fin r}
    (h_sourceIdx_eq : sourceIdx₁ = sourceIdx₂)
    (h_destIdx : destIdx = sourceIdx₁.val + steps)
    (h_destIdx_le : destIdx ≤ ℓ)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := destIdx)) (x : Fin (2 ^ steps)) :
    qMap_total_fiber 𝔽q β (i := sourceIdx₁) (steps := steps) (h_destIdx := h_destIdx)
      (h_destIdx_le := h_destIdx_le) (y := y) x =
    cast (by subst h_sourceIdx_eq; rfl) (qMap_total_fiber 𝔽q β (i := sourceIdx₂)
      (steps := steps) (h_destIdx := by omega) (h_destIdx_le := h_destIdx_le) (y := y) x) := by
  subst h_sourceIdx_eq; rfl

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
lemma qMap_total_fiber_congr_dest
    {sourceIdx : Fin r} (steps : ℕ) {destIdx₁ destIdx₂ : Fin r}
    (h_destIdx_congr : destIdx₁ = destIdx₂)
    (h_destIdx : destIdx₁ = sourceIdx.val + steps)
    (h_destIdx_le : destIdx₁ ≤ ℓ)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := destIdx₁)) :
    qMap_total_fiber 𝔽q β (i := sourceIdx) (steps := steps) (destIdx := destIdx₁)
      (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (y := y) =
    qMap_total_fiber 𝔽q β (i := sourceIdx)
      (steps := steps) (destIdx := destIdx₂) (h_destIdx := by omega) (h_destIdx_le := by omega)
      (y := cast (by subst h_destIdx_congr; rfl) y) := by
  subst h_destIdx_congr; rfl

/- TODO : state that the fiber of y is the set of all 2 ^ steps points in the
larger domain S⁽ⁱ⁾ that get mapped to y by the series of quotient maps q⁽ⁱ⁾, ..., q⁽ⁱ⁺steps⁻¹⁾. -/

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
/-- **qMap_fiber coefficient extraction**.
The coefficients of `x = qMap_total_fiber(y, k)` with respect to `basis_x` are exactly
the function that puts binary coeffs corresponding to bits of `k` in
the first `steps` positions, and shifts `y`'s coefficients.
This is the multi-step counterpart of `qMap_fiber_repr_coeff`.
-/
lemma qMap_total_fiber_repr_coeff (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx.val = i.val + steps)
  (h_destIdx_le : destIdx ≤ ℓ)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := destIdx))
    (k : Fin (2 ^ steps)) :
    let x := qMap_total_fiber 𝔽q β (i := i) (steps := steps) (h_destIdx := h_destIdx)
      (h_destIdx_le := h_destIdx_le) (y := y) k
    let basis_y := sDomain_basis 𝔽q β h_ℓ_add_R_rate (i := destIdx)
      (h_i := Sdomain_bound (by omega))
    let y_coeffs := basis_y.repr y
    ∀ j, -- j refers to bit index of the fiber point x
      ((sDomain_basis 𝔽q β h_ℓ_add_R_rate (i := i) (h_i := Sdomain_bound (by omega))).repr x) j
      = fiber_coeff (i := i) (steps := steps) (destIdx := destIdx) (h_destIdx := h_destIdx)
        (basisIdx := j) (elementIdx := k) (y_coeffs := y_coeffs) := by
  unfold fiber_coeff
  simp only
  intro j
  -- have h_steps_ne_0 : steps ≠ 0 := by exact?
  by_cases h_steps_eq_0 : steps = 0
  · subst h_steps_eq_0
    have h_i_eq_destIdx : i = destIdx := by omega
    subst h_i_eq_destIdx
    rfl
  · simp only [qMap_total_fiber, h_steps_eq_0, ↓reduceDIte, Module.Basis.repr_symm_apply,
    Module.Basis.repr_linearCombination, Finsupp.equivFunOnFinite_symm_apply_apply]

def pointToIterateQuotientIndex (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (x : sDomain 𝔽q β h_ℓ_add_R_rate (i := i)) : Fin (2 ^ steps) := by
  let basis_x := sDomain_basis 𝔽q β h_ℓ_add_R_rate (i := i)
    (h_i := Sdomain_bound (by omega))
  let x_coeffs := basis_x.repr x
  let k_bits : Fin steps → Nat := fun j =>
    if x_coeffs ⟨j, by omega⟩ = 0 then 0 else 1
  let k := Nat.binaryFinMapToNat (n := steps) (m := k_bits) (h_binary := by
    intro j; simp only [k_bits]; split_ifs
    · norm_num
    · norm_num
  )
  exact k

omit [CharP L 2] [NeZero ℓ] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 in
/-- When ϑ = 1, qMap_total_fiber maps k = 0 to an element with first coefficient 0
and k = 1 to an element with first coefficient 1. -/
lemma qMap_total_fiber_one_level_eq (i : Fin r) {destIdx : Fin r}
    (h_destIdx : destIdx = i.val + 1) (h_destIdx_le : destIdx ≤ ℓ)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := destIdx)) (k : Fin 2) :
    let basis_x := sDomain_basis 𝔽q β h_ℓ_add_R_rate i (h_i := by omega)
    let x : sDomain 𝔽q β h_ℓ_add_R_rate i := qMap_total_fiber 𝔽q β (i := i)
      (steps := 1) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (y := y) k
    let y_lifted : sDomain 𝔽q β h_ℓ_add_R_rate i := sDomain.lift 𝔽q β h_ℓ_add_R_rate
      (i := i) (j := destIdx)
      (h_j := by apply Nat.lt_add_of_pos_right_of_le; omega) (h_le := by omega) y
    let free_coeff_term : sDomain 𝔽q β h_ℓ_add_R_rate i :=
      (Fin2ToF2 𝔽q k) • (basis_x ⟨0, by omega⟩)
    x = free_coeff_term + y_lifted := by
  let basis_x := sDomain_basis 𝔽q β h_ℓ_add_R_rate i (h_i := by omega)
  apply basis_x.repr.injective
  simp only [map_add, map_smul]
  simp only [Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one, basis_x]
  ext j
  have h_repr_x := qMap_total_fiber_repr_coeff 𝔽q β i (steps := 1) (by omega)
    (y := y) (k := k) (j := j)
  simp only [h_repr_x, Finsupp.coe_add, Pi.add_apply]
  simp only [fiber_coeff, lt_one_iff, reducePow, Fin2ToF2, Fin.isValue]
  have h_i_lt_destIdx : i < destIdx := by omega
  by_cases hj : j = ⟨0, by omega⟩
  · simp only [hj, ↓reduceDIte, Fin.isValue, Finsupp.single_eq_same]
    by_cases hk : k = 0
    · simp only [getBit, hk, Fin.isValue, Fin.coe_ofNat_eq_mod, zero_mod, shiftRight_zero,
      and_one_is_mod, ↓reduceIte, zero_add]
      -- => Now use basis_repr_of_sDomain_lift
      rw [basis_repr_of_sDomain_lift]
      simp only [tsub_pos_iff_lt, Fin.val_fin_lt, h_i_lt_destIdx, ↓reduceDIte]
    · have h_k_eq_1 : k = 1 := by omega
      simp only [getBit, h_k_eq_1, Fin.isValue, Fin.coe_ofNat_eq_mod, mod_succ, shiftRight_zero,
        Nat.and_self, one_ne_zero, ↓reduceIte, left_eq_add]
      have h : 0 < destIdx.val - i.val := by omega
      simp only [basis_repr_of_sDomain_lift, h, ↓reduceDIte]
  · have hj_ne_zero : j ≠ ⟨0, by omega⟩ := by omega
    have hj_val_ne_zero : j.val ≠ 0 := by
      change j.val ≠ ((⟨0, by omega⟩ :  Fin (ℓ + 𝓡 - ↑i)).val)
      apply Fin.val_ne_of_ne
      exact hj_ne_zero
    simp only [hj_val_ne_zero, ↓reduceDIte, Finsupp.single, Fin.isValue, ite_eq_left_iff,
      one_ne_zero, imp_false, Decidable.not_not, Pi.single, Finsupp.coe_mk, Function.update,
      hj_ne_zero, Pi.zero_apply, zero_add]
    have h_not_lt : ¬(j.val < destIdx.val - i.val) := by omega
    simp only [basis_repr_of_sDomain_lift, h_not_lt, ↓reduceDIte]
    congr 1
    simp only [Fin.mk.injEq]; rw [h_destIdx]; norm_num

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ [NeZero ℓ] in
/-- `x` is in the fiber of `y` under `qMap_total_fiber` iff `y` is the iterated
quotient of `x`. That is, for binary field, the fiber of `y` is exactly the set of
all `x` that map to `y` under the iterated quotient map. -/
theorem generates_quotient_point_if_is_fiber_of_y
    (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (x : sDomain 𝔽q β h_ℓ_add_R_rate (i := i))
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := destIdx))
    (hx_is_fiber : ∃ (k : Fin (2 ^ steps)), x = qMap_total_fiber 𝔽q β (i := i)
      (steps := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (y := y) k) :
    y = iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate i (k := steps)
      (h_destIdx) (h_destIdx_le)  (x := x) := by
 -- Get the fiber index `k` and the equality from the hypothesis.
  rcases hx_is_fiber with ⟨k, hx_eq⟩
  let basis_y := sDomain_basis 𝔽q β h_ℓ_add_R_rate
    (i := destIdx) (h_i := Sdomain_bound (by omega))
  apply basis_y.repr.injective
  ext j
  conv_rhs =>
    rw [getSDomainBasisCoeff_of_iteratedQuotientMap]
  have h_repr_x := qMap_total_fiber_repr_coeff 𝔽q β i (steps := steps)
    h_destIdx h_destIdx_le (y := y) (k := k) (j := ⟨j + steps, by omega⟩)
  rw [←hx_eq] at h_repr_x
  simp only [fiber_coeff, add_lt_iff_neg_right, _root_.not_lt_zero, ↓reduceDIte,
    add_tsub_cancel_right, Fin.eta] at h_repr_x
  exact h_repr_x.symm

omit [CharP L 2] [NeZero ℓ] in
/-- State the corrrespondence between the forward qMap and the backward qMap_total_fiber -/
theorem is_fiber_iff_generates_quotient_point (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (x : sDomain 𝔽q β h_ℓ_add_R_rate (i := i))
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := destIdx)) :
    let qMapFiber := qMap_total_fiber 𝔽q β (i := i) (steps := steps) h_destIdx h_destIdx_le (y := y)
    let k := pointToIterateQuotientIndex 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i) (steps := steps) h_destIdx h_destIdx_le (x := x)
    y = iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate i (k := steps) h_destIdx h_destIdx_le x ↔
    qMapFiber k = x := by
  let basis_x := sDomain_basis 𝔽q β h_ℓ_add_R_rate i
    (h_i := Sdomain_bound (by omega))
  let basis_y := sDomain_basis 𝔽q β h_ℓ_add_R_rate destIdx
    (h_i := Sdomain_bound (by omega))
  simp only
  set k := pointToIterateQuotientIndex 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := i) (steps := steps) h_destIdx h_destIdx_le (x := x)
  constructor
  · intro h_x_generates_y
    -- ⊢ qMap_total_fiber ...` ⟨↑i, ⋯⟩ steps ⋯ y k = x
    -- We prove that `qMap_total_fiber` with this `k` reconstructs `x` via basis repr
    apply basis_x.repr.injective
    ext j
    let reConstructedX := basis_x.repr (qMap_total_fiber 𝔽q β (i := i)
      (steps := steps) h_destIdx h_destIdx_le (y := y) k)
    have h_repr_of_reConstructedX := qMap_total_fiber_repr_coeff 𝔽q β i (steps := steps)
      h_destIdx h_destIdx_le (y := y) (k := k) (j := j)
    -- ⊢ repr of reConstructedX at j = repr of x at j
    rw [h_repr_of_reConstructedX]; dsimp [k, pointToIterateQuotientIndex, fiber_coeff];
    rw [getBit_of_binaryFinMapToNat]; simp only [Fin.eta, dite_eq_right_iff, ite_eq_left_iff,
      one_ne_zero, imp_false, Decidable.not_not]
    -- Now we only need to do case analysis
    by_cases h_j : j.val < steps
    · -- Case 1 : The first `steps` coefficients, determined by `k`.
      simp only [h_j, ↓reduceDIte, forall_const]
      by_cases h_coeff_j_of_x : basis_x.repr x j = 0
      · simp only [basis_x, h_coeff_j_of_x, ↓reduceIte];
      · simp only [basis_x, h_coeff_j_of_x, ↓reduceIte];
        have h_coeff := 𝔽q_element_eq_zero_or_eq_one 𝔽q (c := basis_x.repr x j)
        simp only [h_coeff_j_of_x, false_or] at h_coeff
        exact id (Eq.symm h_coeff)
    · -- Case 2 : The remaining coefficients, determined by `y`.
      simp only [h_j, ↓reduceDIte]
      simp only [basis_x]
      -- ⊢ Here we compare coeffs, not the basis elements
      simp only [h_x_generates_y]
      have h_res := getSDomainBasisCoeff_of_iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate i (k := steps)
        h_destIdx h_destIdx_le x (j := ⟨j - steps, by omega⟩) -- ⊢ ↑j - steps < ℓ + 𝓡 - (↑i + steps)
      have h_j_sub_add_steps : j - steps + steps = j := by omega
      simp only at h_res
      simp only [h_j_sub_add_steps, Fin.eta] at h_res
      exact h_res
  · intro h_x_is_fiber_of_y
    -- y is the quotient point of x over steps steps
    exact generates_quotient_point_if_is_fiber_of_y 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i) (steps := steps) h_destIdx h_destIdx_le (x := x) (y := y)
      (hx_is_fiber := by use k; exact h_x_is_fiber_of_y.symm)

omit [CharP L 2] hF₂ h_β₀_eq_1 [NeZero ℓ] in
/-- the pointToIterateQuotientIndex of qMap_total_fiber -/
lemma pointToIterateQuotientIndex_qMap_total_fiber_eq_self (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (y : (sDomain 𝔽q β h_ℓ_add_R_rate) (i := destIdx)) (k : Fin (2 ^ steps)) :
    pointToIterateQuotientIndex 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
      (steps := steps) h_destIdx h_destIdx_le (x := (qMap_total_fiber 𝔽q β (i := i)
        (steps := steps) h_destIdx h_destIdx_le (y := y) k)) = k := by
  apply Fin.eq_mk_iff_val_eq.mpr
  apply eq_iff_eq_all_getBits.mpr
  intro j -- bit index j
  simp only [pointToIterateQuotientIndex, qMap_total_fiber]
  rw [Nat.getBit_of_binaryFinMapToNat]
  simp only [Nat.add_zero, Nat.pow_zero, Module.Basis.repr_symm_apply]
  by_cases h_j : j < steps
  · simp only [h_j, ↓reduceDIte];
    by_cases hsteps : steps = 0
    · simp only [hsteps, ↓reduceDIte]; omega
    · simp only [hsteps, ↓reduceDIte, Module.Basis.repr_linearCombination,
      Finsupp.equivFunOnFinite_symm_apply_apply, h_j, ite_eq_left_iff, one_ne_zero,
      imp_false, Decidable.not_not]
      -- ⊢ (if j.getBit ↑k = 0 then 0 else 1) = j.getBit ↑k
      have h := Nat.getBit_eq_zero_or_one (k := j) (n := k)
      by_cases h_j_getBit_k_eq_0 : j.getBit ↑k = 0
      · simp only [h_j_getBit_k_eq_0, ↓reduceIte]
      · simp only [h_j_getBit_k_eq_0, false_or, ↓reduceIte] at h ⊢
        exact id (Eq.symm h)
  · rw [Nat.getBit_of_lt_two_pow];
    simp only [h_j, ↓reduceDIte, ↓reduceIte];

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
/-- **qMap_fiber coefficient extraction** -/
lemma qMap_total_fiber_basis_sum_repr (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (y : (sDomain 𝔽q β h_ℓ_add_R_rate) (i := destIdx))
    (k : Fin (2 ^ steps)) :
    let x : sDomain 𝔽q β h_ℓ_add_R_rate (i := i) := qMap_total_fiber 𝔽q β
      (i := i) (steps := steps) h_destIdx h_destIdx_le (y := y) (k)
    let basis_x := sDomain_basis 𝔽q β h_ℓ_add_R_rate i (h_i := Sdomain_bound (by omega))
    let basis_y := sDomain_basis 𝔽q β h_ℓ_add_R_rate destIdx (h_i := Sdomain_bound (by omega))
    let y_coeffs := basis_y.repr y
    x = ∑ j : Fin (ℓ + 𝓡 - i), (
      fiber_coeff 𝔽q (i := i) (steps := steps) h_destIdx (basisIdx := j)
        (elementIdx := k) (y_coeffs := y_coeffs)
    ) • (basis_x j) := by
    set basis_x := sDomain_basis 𝔽q β h_ℓ_add_R_rate i (Sdomain_bound (by omega))
    set basis_y := sDomain_basis 𝔽q β h_ℓ_add_R_rate destIdx
      (h_i := Sdomain_bound (by omega))
    set y_coeffs := basis_y.repr y
    -- Let `x` be the element from the fiber for brevity.
    set x := qMap_total_fiber 𝔽q β (i := i) (steps := steps)
      h_destIdx h_destIdx_le (y := y) (k)
    simp only;
    -- Express `(x:L)` using its basis representation, which is built from `x_coeffs_fn`.
    set x_coeffs_fn := fun j : Fin (ℓ + 𝓡 - i) =>
      fiber_coeff 𝔽q (i := i) (steps := steps) h_destIdx (basisIdx := j)
        (elementIdx := k) (y_coeffs := y_coeffs)
    have hx_val_sum : (x : L) = ∑ j, (x_coeffs_fn j) • (basis_x j) := by
      rw [←basis_x.sum_repr x]
      rw [Submodule.coe_sum, Submodule.coe_sum]
      congr; funext j;
      simp_rw [Submodule.coe_smul]
      congr; unfold x_coeffs_fn
      have h := qMap_total_fiber_repr_coeff 𝔽q β (i := i) (steps := steps)
        h_destIdx h_destIdx_le (y := y) (k := k) (j := j)
      rw [h]
    apply Subtype.ext -- convert to equality in Subtype embedding
    rw [hx_val_sum]

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
theorem qMap_total_fiber_injective (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := destIdx)) :
    Function.Injective (qMap_total_fiber 𝔽q β (i := i) (steps := steps)
      h_destIdx h_destIdx_le (y := y)) := by
  intro k₁ k₂ h_eq
  let basis_x := sDomain_basis 𝔽q β h_ℓ_add_R_rate i (Sdomain_bound (by omega))
  set fiberMap := qMap_total_fiber 𝔽q β (i := i) (steps := steps)
    h_destIdx h_destIdx_le (y := y)
  have h_coeffs_eq : basis_x.repr (fiberMap k₁) = basis_x.repr (fiberMap k₂) := by
    rw [h_eq]
  have h_bits_eq : ∀ j : Fin steps,
      Nat.getBit (k := j) (n := k₁.val) = Nat.getBit (k := j) (n := k₂.val) := by
    intro j
    have h_coeff_j_eq : basis_x.repr (fiberMap k₁) ⟨j, by omega⟩
      = basis_x.repr (fiberMap k₂) ⟨j, by omega⟩ := by rw [h_coeffs_eq]
    rw [qMap_total_fiber_repr_coeff 𝔽q β (i := i) (steps := steps)
      h_destIdx h_destIdx_le (y := y) (j := ⟨j, by omega⟩)]
      at h_coeff_j_eq
    rw [qMap_total_fiber_repr_coeff 𝔽q β (i := i) (steps := steps)
      h_destIdx h_destIdx_le (y := y) (k := k₂) (j := ⟨j, by omega⟩)]
      at h_coeff_j_eq
    simp only [fiber_coeff, Fin.is_lt, ↓reduceDIte] at h_coeff_j_eq
    by_cases hbitj_k₁ : Nat.getBit (k := j) (n := k₁.val) = 0
    · simp only [hbitj_k₁, ↓reduceIte, left_eq_ite_iff, zero_ne_one, imp_false,
      Decidable.not_not] at ⊢ h_coeff_j_eq
      simp only [h_coeff_j_eq]
    · simp only [hbitj_k₁, ↓reduceIte, right_eq_ite_iff, one_ne_zero,
      imp_false] at ⊢ h_coeff_j_eq
      have b1 : Nat.getBit (k := j) (n := k₁.val) = 1 := by
        have h := Nat.getBit_eq_zero_or_one (k := j) (n := k₁.val)
        simp only [hbitj_k₁, false_or] at h
        exact h
      have b2 : Nat.getBit (k := j) (n := k₂.val) = 1 := by
        have h := Nat.getBit_eq_zero_or_one (k := j) (n := k₂.val)
        simp only [h_coeff_j_eq, false_or] at h
        exact h
      simp only [b1, b2]
  apply Fin.eq_of_val_eq
  apply eq_iff_eq_all_getBits.mpr
  intro k
  by_cases h_k : k < steps
  · simp only [h_bits_eq ⟨k, by omega⟩]
  · conv_lhs => rw [Nat.getBit_of_lt_two_pow]
    conv_rhs => rw [Nat.getBit_of_lt_two_pow]
    simp only [h_k, ↓reduceIte]

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
theorem card_qMap_total_fiber (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := destIdx)) :
    Fintype.card (Set.image (qMap_total_fiber 𝔽q β (i := i) (steps := steps)
      h_destIdx h_destIdx_le
      (y := y)) Set.univ) = 2 ^ steps := by
  rw [Set.card_image_of_injective Set.univ]
  · simp only [Fintype.card_setUniv, Fintype.card_fin]
  · exact qMap_total_fiber_injective 𝔽q β i steps h_destIdx h_destIdx_le y

omit [CharP L 2] [DecidableEq 𝔽q] [NeZero ℓ] in
/-- The images of `qMap_total_fiber` over distinct quotient points `y₁ ≠ y₂` are
disjoint -/
theorem qMap_total_fiber_disjoint
    (i : Fin r) {destIdx : Fin r} (steps : ℕ)
  (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
  {y₁ y₂ : sDomain 𝔽q β h_ℓ_add_R_rate destIdx}
  (hy_ne : y₁ ≠ y₂) :
  Disjoint
    ((qMap_total_fiber 𝔽q β (i := i) (steps := steps)
      h_destIdx h_destIdx_le y₁ '' Set.univ).toFinset)
    ((qMap_total_fiber 𝔽q β (i := i) (steps := steps)
      h_destIdx h_destIdx_le y₂ '' Set.univ).toFinset) := by
  classical
 -- Proof by contradiction. Assume the intersection is non-empty.
  rw [Finset.disjoint_iff_inter_eq_empty]
  by_contra h_nonempty
  -- Let `x` be an element in the intersection of the two fiber sets.
  obtain ⟨x, h_x_mem_inter⟩ := Finset.nonempty_of_ne_empty h_nonempty
  have hx₁ := Finset.mem_of_mem_inter_left h_x_mem_inter
  have hx₂ := Finset.mem_of_mem_inter_right h_x_mem_inter
  -- A helper lemma : applying the forward map to a point in a generated fiber returns
  -- the original quotient point.
  have iteratedQuotientMap_of_qMap_total_fiber_eq_self
    (y : sDomain 𝔽q β h_ℓ_add_R_rate destIdx)
    (k : Fin (2 ^ steps)) :
    iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := i) (k := steps)
      h_destIdx h_destIdx_le
      (qMap_total_fiber 𝔽q β (i := i) (steps := steps)
        h_destIdx h_destIdx_le (y := y) k) = y := by
      have h := generates_quotient_point_if_is_fiber_of_y 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps) h_destIdx h_destIdx_le (x:=
        ((qMap_total_fiber 𝔽q β (i := i) (steps := steps)
          h_destIdx h_destIdx_le (y := y) k) :
          sDomain 𝔽q β h_ℓ_add_R_rate (i := i))
      ) (y := y) (hx_is_fiber := by use k)
      exact h.symm
  have h_exists_k₁ : ∃ k, x = qMap_total_fiber 𝔽q β (i := i) (steps := steps)
      h_destIdx h_destIdx_le y₁ k := by
    -- convert (x ∈ Finset of the image of the fiber) to statement
    -- about membership in the Set.
    rw [Set.mem_toFinset] at hx₁
    rw [Set.mem_image] at hx₁ -- Set.mem_image gives us t an index that maps to x
    -- ⊢ `∃ (k : Fin (2 ^ steps)), k ∈ Set.univ ∧ qMap_total_fiber ... y₁ k = x`.
    rcases hx₁ with ⟨k, _, h_eq⟩
    use k; exact h_eq.symm
  have h_exists_k₂ : ∃ k, x = qMap_total_fiber 𝔽q β (i := i) (steps := steps)
      h_destIdx h_destIdx_le y₂ k := by
    rw [Set.mem_toFinset] at hx₂
    rw [Set.mem_image] at hx₂ -- Set.mem_image gives us t an index that maps to x
    rcases hx₂ with ⟨k, _, h_eq⟩
    use k; exact h_eq.symm
  have h_y₁_eq_quotient_x : y₁ =
      iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := i) (k := steps) h_destIdx h_destIdx_le x := by
    apply generates_quotient_point_if_is_fiber_of_y (hx_is_fiber := by exact h_exists_k₁)
  have h_y₂_eq_quotient_x : y₂ =
      iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := i) (k := steps) h_destIdx h_destIdx_le x := by
    apply generates_quotient_point_if_is_fiber_of_y (hx_is_fiber := by exact h_exists_k₂)
  let kQuotientIndex := pointToIterateQuotientIndex 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
    (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (x := x)
  -- Since `x` is in the fiber of `y₁`, applying the forward map to `x` yields `y₁`.
  have h_map_x_eq_y₁ : iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := i)
      (k := steps) h_destIdx h_destIdx_le x = y₁ := by
    have h := iteratedQuotientMap_of_qMap_total_fiber_eq_self (y := y₁) (k := kQuotientIndex)
    have hx₁ : x = qMap_total_fiber 𝔽q β (i := i) (steps := steps)
        h_destIdx h_destIdx_le y₁ kQuotientIndex := by
      have h_res := is_fiber_iff_generates_quotient_point 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := i) (steps := steps) h_destIdx h_destIdx_le (x := x) (y := y₁).mp (h_y₁_eq_quotient_x)
      exact h_res.symm
    rw [hx₁]
    exact iteratedQuotientMap_of_qMap_total_fiber_eq_self y₁ kQuotientIndex
  -- Similarly, since `x` is in the fiber of `y₂`, applying the forward map yields `y₂`.
  have h_map_x_eq_y₂ : iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := i)
      (k := steps) h_destIdx h_destIdx_le x = y₂ := by
    -- have h := iteratedQuotientMap_of_qMap_total_fiber_eq_self (y := y₂) (k := kQuotientIndex)
    have hx₂ : x = qMap_total_fiber 𝔽q β (i := i) (steps := steps)
        h_destIdx h_destIdx_le y₂ kQuotientIndex := by
      have h_res := is_fiber_iff_generates_quotient_point 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := i) (steps := steps) h_destIdx h_destIdx_le (x := x) (y := y₂).mp (h_y₂_eq_quotient_x)
      exact h_res.symm
    rw [hx₂]
    exact iteratedQuotientMap_of_qMap_total_fiber_eq_self y₂ kQuotientIndex
  exact hy_ne (h_map_x_eq_y₁.symm.trans h_map_x_eq_y₂)

/-- Evaluation vector `[f^(i)(x_0) ... f^(i)(x_{2 ^ steps-1})]^T`. This is the rhs
vector in the identity in **Lemma 4.9** -/
def fiberEvaluations (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx = i + steps)
  (h_destIdx_le : destIdx ≤ ℓ)
  (f : (sDomain 𝔽q β h_ℓ_add_R_rate) i → L)
  (y : (sDomain 𝔽q β h_ℓ_add_R_rate) destIdx) : Fin (2 ^ steps) → L :=
  -- Get the fiber points
  let fiberMap := qMap_total_fiber 𝔽q β (i := i) (steps := steps) (h_destIdx := h_destIdx)
    (h_destIdx_le := h_destIdx_le) (y := y)
  -- Evaluate f at each fiber point
  fun idx => f (fiberMap idx)

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
lemma fiberEvaluations_eq_merge_fiberEvaluations_of_one_step_fiber
    (i : Fin r) {midIdx destIdx : Fin r} (steps : ℕ) (h_midIdx : midIdx = i + steps)
    (h_destIdx : destIdx = i + steps + 1)
    (h_destIdx_le : destIdx ≤ ℓ)
    (f : (sDomain 𝔽q β h_ℓ_add_R_rate) i → L)
    (y : (sDomain 𝔽q β h_ℓ_add_R_rate) destIdx) :
    let fiberMap := qMap_total_fiber 𝔽q β (i := midIdx) (steps := 1)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_destIdx := by omega) h_destIdx_le (y := y)
    let z₀ := fiberMap 0
    let z₁ := fiberMap 1
    let fiber_eval_z₀ :=
      fiberEvaluations 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (steps := steps) (i := i) (destIdx := midIdx)
        (h_destIdx := h_midIdx) (h_destIdx_le := by omega) (f := f) z₀
    let fiber_eval_z₁ : Fin (2 ^ steps) → L :=
      fiberEvaluations 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (steps := steps)
        (i := i) (destIdx := midIdx) (h_destIdx := h_midIdx) (h_destIdx_le := by omega) (f := f) z₁
    (fiberEvaluations 𝔽q β (steps := steps + 1) (i := i)
      h_destIdx h_destIdx_le f y) =
    mergeFinMap_PO2_left_right (n := steps) fiber_eval_z₀ fiber_eval_z₁ := by
  -- 1. Unfold definitions to expose `qMap_total_fiber`
  unfold fiberEvaluations mergeFinMap_PO2_left_right
  simp only
  funext fiber_y_idx -- fiber_y_idx is index of the `steps`-step fiber point of y (y ∈ S^{i+steps})
  -- 2. We need to show that the fiber point mapping splits correctly.
  -- Split into cases based on the MSB of fiber_y_idx
  set fiberMap := qMap_total_fiber 𝔽q β (i := midIdx) (steps := 1)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (h_destIdx := by omega) h_destIdx_le (y := y)
  set z₀ := fiberMap 0
  set z₁ := fiberMap 1
  set left_point := (qMap_total_fiber (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := i) (steps := steps + 1)
    h_destIdx h_destIdx_le) (y := y)
      fiber_y_idx
  -- ⊢ f left_point = if h : ↑fiber_y_idx < 2 ^ steps then
      -- f (qMap_total_fiber 𝔽q β ⟨↑i, ⋯⟩ steps ⋯ z₀ ⟨↑fiber_y_idx, ⋯⟩)
  --   else f (qMap_total_fiber 𝔽q β ⟨↑i, ⋯⟩ steps ⋯ z₁ ⟨↑fiber_y_idx - 2 ^ steps, ⋯⟩)
  let zᵢ : sDomain 𝔽q β h_ℓ_add_R_rate midIdx :=
    if h : fiber_y_idx.val < 2 ^ steps then z₀ else z₁
  let fiber_zᵢ_idx : Fin (2 ^ steps) :=
    if h : fiber_y_idx.val < 2 ^ steps then ⟨fiber_y_idx, by omega⟩
    else ⟨fiber_y_idx.val - 2 ^ steps, by omega⟩
  set right_point := qMap_total_fiber (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := i) (steps := steps) h_midIdx (h_destIdx_le := by omega)
    (y := zᵢ) fiber_zᵢ_idx
  have h_left_point_eq_right_point : left_point = right_point := by
    let basis := sDomain_basis 𝔽q β h_ℓ_add_R_rate i (Sdomain_bound (by omega))
    apply basis.repr.injective
    ext (coeffIdx : Fin (ℓ + 𝓡 - i))
    rw [qMap_total_fiber_repr_coeff 𝔽q β i (steps := steps + 1) (destIdx := destIdx)
      h_destIdx h_destIdx_le (y := y) (k := fiber_y_idx)]
    rw [qMap_total_fiber_repr_coeff 𝔽q β i (steps := steps) (destIdx := midIdx)
      (h_destIdx := h_midIdx) (h_destIdx_le := by omega) (y := zᵢ) (k := fiber_zᵢ_idx)]
    dsimp only [Fin.eta, fiber_coeff]
    unfold zᵢ fiber_zᵢ_idx
    --   ⊢ (if hj : ↑j < steps + 1 then if (↑j).getBit ↑fiber_y_idx = 0 then 0 else 1
    -- else ((S^(i+steps+1)).repr y) ⟨↑j - (steps + 1), ⋯⟩) =
    -- if hj : ↑j < steps then if (↑j).getBit ↑fiber_zᵢ_idx = 0 then 0 else 1
    -- else ((sDomain_basis 𝔽q β h_ℓ_add_R_rate ⟨↑i + steps, ⋯⟩ ⋯).repr zᵢ) ⟨↑j - steps, ⋯⟩
    have h_repr_z₀ := qMap_total_fiber_repr_coeff 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := midIdx) (steps := 1) (h_destIdx := by omega) (h_destIdx_le := by omega)
      (y := y) (k := 0)
    have h_repr_z₁ := qMap_total_fiber_repr_coeff 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := midIdx) (steps := 1) (h_destIdx := by omega) (h_destIdx_le := by omega)
      (y := y) (k := 1)
    by_cases h_fiber_y_idx_lt_2_pow_steps : fiber_y_idx.val < 2 ^ steps
    · -- right-point is qMap_total_fiber(z₀, fiber_y_idx)
      simp only [h_fiber_y_idx_lt_2_pow_steps, ↓reduceDIte]
      by_cases h_coeffIdx_lt_steps : coeffIdx.val < steps
      · have h_lt_succ : coeffIdx.val < steps + 1 := by omega
        simp only [h_lt_succ, ↓reduceDIte, h_coeffIdx_lt_steps]
      · simp only [h_coeffIdx_lt_steps, ↓reduceDIte]
        by_cases h_lt_succ : coeffIdx.val < steps + 1
        · simp only [h_lt_succ, ↓reduceDIte]
          have h_repr_z₀_rhs := h_repr_z₀ ⟨coeffIdx.val - steps, by omega⟩
          conv_rhs => rw [h_repr_z₀_rhs]
          unfold fiber_coeff
          simp only [lt_one_iff, reducePow, Fin.isValue, Fin.coe_ofNat_eq_mod, zero_mod]
          have h_coeffIdx_eq_steps : coeffIdx.val = steps := by omega
          simp only [h_coeffIdx_eq_steps, tsub_self, ↓reduceDIte]
          have h_steps_getBit_idx : Nat.getBit (n := fiber_y_idx) (k := steps) = 0 := by
            let res := Nat.getBit_of_lt_two_pow (k := steps) (n := steps)
              (a := ⟨fiber_y_idx, by omega⟩)
            simp only [lt_self_iff_false, ↓reduceIte] at res
            exact res
          rw [h_steps_getBit_idx, Nat.getBit]
          simp only [↓reduceIte, shiftRight_zero, and_one_is_mod, zero_mod]
        · simp only [h_lt_succ, ↓reduceDIte]
          have h_repr_z₀_rhs := h_repr_z₀ ⟨coeffIdx.val - steps, by omega⟩
          conv_rhs => rw [h_repr_z₀_rhs]
          unfold fiber_coeff
          simp only [lt_one_iff, reducePow, Fin.isValue, Fin.coe_ofNat_eq_mod, zero_mod]
          have h_sub_gt_0: coeffIdx.val - steps ≠ 0 := by omega
          simp only [h_sub_gt_0, ↓reduceDIte]
          rfl
    · -- right-point is qMap_total_fiber(z₁, fiber_y_idx - 2 ^ steps)
      have h_fiber_y_idx_ge_2_pow_steps : fiber_y_idx.val ≥ 2 ^ steps := by omega
      have h_fiber_y_idx_getBit_steps : Nat.getBit (k := steps) (n := fiber_y_idx) = 1 := by
        -- This is because 2^steps ≤ fiber_y_idx.val < 2^(steps + 1)
        have h_lt : fiber_y_idx.val < 2^(steps + 1) := by omega
        apply Nat.getBit_1_of_ge_two_pow_and_lt_two_pow_succ
        · omega
        · omega
      simp only [h_fiber_y_idx_lt_2_pow_steps, ↓reduceDIte]
      by_cases h_coeffIdx_lt_steps : coeffIdx.val < steps
      · have h_lt_succ : coeffIdx.val < steps + 1 := by omega
        simp only [h_lt_succ, ↓reduceDIte, h_coeffIdx_lt_steps]
        -- ⊢ (if (↑coeffIdx).getBit ↑fiber_y_idx = 0 then 0 else 1) =
        -- if (↑coeffIdx).getBit (↑fiber_y_idx - 2 ^ steps) = 0 then 0 else 1
        have h_getBit_eq: Nat.getBit (n := fiber_y_idx) (k := coeffIdx)
          = Nat.getBit (n := fiber_y_idx - 2 ^ steps) (k := coeffIdx) := by
          let getBit_Sub_2_pow_steps := Nat.getBit_of_sub_two_pow_of_bit_1 (n := fiber_y_idx)
            (i := steps) (h_getBit_eq_1 := h_fiber_y_idx_getBit_steps) (j := coeffIdx)
          rw [getBit_Sub_2_pow_steps]
          have h_ne : coeffIdx.val ≠ steps := by omega
          simp only [h_ne, ↓reduceIte]
        rw [h_getBit_eq]
      · simp only [h_coeffIdx_lt_steps, ↓reduceDIte]
        by_cases h_lt_succ : coeffIdx.val < steps + 1
        · simp only [h_lt_succ, ↓reduceDIte]
          have h_repr_z₁_rhs := h_repr_z₁ ⟨coeffIdx.val - steps, by omega⟩
          conv_rhs => rw [h_repr_z₁_rhs]
          unfold fiber_coeff
          simp only [lt_one_iff, reducePow, Fin.isValue, Fin.coe_ofNat_eq_mod, mod_succ]
          have h_coeffIdx_eq_steps : coeffIdx.val = steps := by omega
          simp only [h_coeffIdx_eq_steps, tsub_self, ↓reduceDIte]
          simp only [h_fiber_y_idx_getBit_steps, one_ne_zero, ↓reduceIte, right_eq_ite_iff,
            imp_false, ne_eq];
          simp only [getBit, shiftRight_zero, Nat.and_self, one_ne_zero, not_false_eq_true]
        · simp only [h_lt_succ, ↓reduceDIte]
          have h_repr_z₁_rhs := h_repr_z₁ ⟨coeffIdx.val - steps, by omega⟩
          conv_rhs => rw [h_repr_z₁_rhs]
          unfold fiber_coeff
          simp only [lt_one_iff, reducePow, Fin.isValue, Fin.coe_ofNat_eq_mod]
          have h_sub_gt_0: coeffIdx.val - steps ≠ 0 := by omega
          simp only [h_sub_gt_0, ↓reduceDIte]
          rfl
  rw [h_left_point_eq_right_point]
  unfold right_point zᵢ fiber_zᵢ_idx
  split_ifs with h_lt
  · simp only -- z₀
  · simp only -- z₁

end FiberMath

end Essentials

end
end Binius.BinaryBasefold
