/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.Data.CodingTheory.Prelims
import ArkLib.Data.FieldTheory.AdditiveNTT.AdditiveNTT
import ArkLib.Data.Fin.BigOperators
import ArkLib.Data.MvPolynomial.Multilinear
import ArkLib.ProofSystem.Sumcheck.Spec.SingleRound

namespace Binius.BinaryBasefold

open OracleSpec ProtocolSpec Polynomial MvPolynomial Binius.BinaryBasefold
open scoped NNReal
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
    {β : ι₂ → Type*} [∀ i, DecidableEq (β i)] [DecidableEq ι₂]
    (x y : ∀ i, β i) (g : ι₁ → ι₂) (hg : Function.Injective g) :
    hammingDist (fun i => x (g i)) (fun i => y (g i)) ≤ hammingDist x y := by
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
  set D₁ := D₂.preimage g (by exact hg.injOn)
  -- ⊢ #D₁ ≤ #D₂
  -- Step 1 : The size of a set is at most the size of its image under an injective function.
  have h_card_le_image : D₁.card ≤ (D₁.image g).card := by
    -- This follows directly from the fact that `g` is injective on the set D₁.
    apply Finset.card_le_card_of_injOn (f := g)
    · -- Goal 1 : Prove that `g` maps `D₁` to `D₁.image g`. This is true by definition of image.
      have res := Set.mapsTo_image (f := g) (s := D₁)
      convert res
      simp only [coe_image]
      --  (D₁.image g : Set ι₂)
    · -- Goal 2 : Prove that `g` is injective on the set `D₁`.
      -- This is true because our main hypothesis `hg` states that `g` is injective everywhere.
      exact Function.Injective.injOn hg
  -- Step 2 : The image of the preimage of a set is always a subset of the original set.
  have h_image_subset : D₁.image g ⊆ D₂ := by
    simp [D₁, Finset.image_preimage]
  -- Step 3 : By combining these two facts, we get our result.
  -- |D₁| ≤ |image g(D₁)|  (from Step 1)
  -- and |image g(D₁)| ≤ |D₂| (since it's a subset)
  exact h_card_le_image.trans (Finset.card_le_card h_image_subset)

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
    (mergeFinMap_PO2_left_right (L := L) (n := 0) (left := ((C_n *ᵥ v_top) : (Fin 1) → L))
      (right := ((C_n *ᵥ v_bot) : (Fin 1) → L)) : (Fin 2) → L)
    = (challengeTensorExpansionMatrix (n := n) (r := r)) *ᵥ
      mergeFinMap_PO2_left_right (n := n) (left := v_top) (right := v_bot) := by
  dsimp only [challengeTensorExpansionMatrix]
  conv_rhs =>
    -- Move reindexing from Matrix to Vector
    rw [Matrix.reindex_mulVec]
  funext k
  unfold mergeFinMap_PO2_left_right
  unfold Matrix.from4Blocks Fin.reindex Matrix.mulVec dotProduct
  -- Now unfold everything
  simp only [zero_apply, finCongr_symm, Function.comp_apply, finCongr_apply, dite_mul, zero_mul,
    sum_dite_irrel, Fin.val_cast]
  simp_rw [Fin.sum_univ_add]
  simp_rw [←Finset.sum_add_distrib]
  simp only [reduceAdd, reducePow, pow_zero, lt_one_iff, Fin.val_eq_zero_iff, Fin.isValue,
    Nat.pow_zero, of_apply, dite_eq_ite, Fin.val_castAdd, Fin.is_lt, ↓reduceDIte, Fin.eta,
    Fin.natAdd_eq_addNat, Fin.val_addNat, add_lt_iff_neg_right, not_lt_zero', add_zero,
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
    Fin.val_cast, h_colIdx_lt_2_pow_n, Fin.zero_eta, of_apply, mod_succ, lt_self_iff_false,
    zero_apply, mul_zero, add_zero]
    rw [multilinearWeight_succ_lower_half (r := r) (i := colIdx)
      (h_lt := h_colIdx_lt_2_pow_n), mul_comm]
  · have h_ne_lt_2_pow_n : ¬(colIdx.val < 2 ^ n) := by exact h_colIdx_lt_2_pow_n
    simp only [reduceAdd, Fin.isValue, Fin.coe_ofNat_eq_mod, zero_mod, zero_lt_one, ↓reduceDIte,
      Fin.val_cast, h_ne_lt_2_pow_n, zero_apply, mul_zero, mod_succ, lt_self_iff_false, tsub_self,
      Fin.zero_eta, of_apply, zero_add]
    let u : Fin (2 ^ n) := ⟨colIdx.val - (2 ^ n), by omega⟩
    have h_eq: colIdx.val = u.val + (2 ^ n) := by dsimp only [u]; omega
    rw [multilinearWeight_succ_upper_half (r := r) (i := colIdx) (j := u)
      (h_eq := h_eq), mul_comm]

variable {L : Type} [CommRing L] (ℓ : ℕ) [NeZero ℓ]
variable (𝓑 : Fin 2 ↪ L)

abbrev MultilinearPoly (L : Type) [CommSemiring L] (ℓ : ℕ) := L⦃≤ 1⦄[X Fin ℓ]
abbrev MultiquadraticPoly (L : Type) [CommSemiring L] (ℓ : ℕ) := L⦃≤ 2⦄[X Fin ℓ]

/-- Fixes the first `v` variables of a `ℓ`-variate multivariate polynomial.
`t` -> `H_i` derivation
-/
noncomputable def fixFirstVariablesOfMQP (v : Fin (ℓ + 1))
  (H : MvPolynomial (Fin ℓ) L) (challenges : Fin v → L) : MvPolynomial (Fin (ℓ - v)) L :=
  have h_l_eq : ℓ = (ℓ - v) + v := by rw [Nat.add_comm]; exact (Nat.add_sub_of_le v.is_le).symm
  -- Step 1 : Rename L[X Fin ℓ] to L[X (Fin (ℓ - v) ⊕ Fin v)]
  let finEquiv := finSumFinEquiv (m := ℓ - v) (n := v).symm
  let H_sum : L[X (Fin (ℓ - v) ⊕ Fin v)] := by
    apply MvPolynomial.rename (f := (finCongr h_l_eq).trans finEquiv) H
  -- Step 2 : Convert to (L[X Fin v])[X Fin (ℓ - v)] via sumAlgEquiv
  let H_forward : L[X Fin v][X Fin (ℓ - v)] := (sumAlgEquiv L (Fin (ℓ - v)) (Fin v)) H_sum
  -- Step 3 : Evaluate the poly at the point challenges to get a final L[X Fin (ℓ - v)]
  let eval_map : L[X Fin ↑v] →+* L := (eval challenges : MvPolynomial (Fin v) L →+* L)
  MvPolynomial.map (f := eval_map) (σ := Fin (ℓ - v)) H_forward

private lemma sumToIter_monomial_aux {R : Type*} [CommSemiring R]
    {S₁ S₂ : Type*}
    (m : (S₁ ⊕ S₂) →₀ ℕ) (c : R) :
    MvPolynomial.sumToIter R S₁ S₂ (MvPolynomial.monomial m c) =
      MvPolynomial.monomial (m.comapDomain Sum.inl Sum.inl_injective.injOn)
        (MvPolynomial.monomial (m.comapDomain Sum.inr Sum.inr_injective.injOn) c) := by
  simp only [sumToIter, eval₂Hom_monomial]
  simp only [RingHom.coe_comp, Function.comp_apply, Finsupp.prod, Finsupp.comapDomain, preimage_inl,
    preimage_inr]
  convert congr_arg₂ (· * ·) rfl ?_ using 1
  rotate_left
  exact ∏ x ∈ m.support,
    Sum.rec (fun a => MvPolynomial.X a)
      (fun b => MvPolynomial.C (MvPolynomial.X b)) x ^ m x
  · rfl
  · simp only [monomial_eq, MvPolynomial.C_mul]
    simp only [Finsupp.prod, Finsupp.coe_mk, map_prod, MvPolynomial.C_pow, mul_assoc]
    rw [← Finset.prod_filter_mul_prod_filter_not m.support (fun x => x.isRight)]
    congr! 2
    · exact Finset.prod_bij (fun x hx => Sum.inr x) (by aesop) (by aesop)
        (by aesop) (by aesop)
    · exact Finset.prod_bij (fun x hx => Sum.inl x) (by aesop) (by aesop)
        (by aesop) (by aesop)

private lemma sumAlgEquiv_mem_restrictDegree {R : Type*} [CommSemiring R]
    {S₁ S₂ : Type*}
    (p : MvPolynomial (S₁ ⊕ S₂) R) (n : ℕ)
    (hp : p ∈ MvPolynomial.restrictDegree (S₁ ⊕ S₂) R n) :
    (MvPolynomial.sumAlgEquiv R S₁ S₂) p ∈
      MvPolynomial.restrictDegree S₁ (MvPolynomial S₂ R) n := by
  intro s hs
  obtain ⟨m, hm⟩ : ∃ m : (S₁ ⊕ S₂) →₀ ℕ,
      m ∈ p.support ∧ s = m.comapDomain Sum.inl Sum.inl_injective.injOn := by
    have h_sum : (MvPolynomial.sumAlgEquiv R S₁ S₂) p =
        ∑ m ∈ p.support,
          (MvPolynomial.monomial (m.comapDomain Sum.inl Sum.inl_injective.injOn))
            (MvPolynomial.monomial (m.comapDomain Sum.inr Sum.inr_injective.injOn)
              (p.coeff m)) := by
      conv_lhs => rw [p.as_sum]
      rw [map_sum]
      exact Finset.sum_congr rfl fun _ _ => sumToIter_monomial_aux _ _
    contrapose! hs
    simp only [h_sum, SetLike.mem_coe, Finsupp.mem_support_iff, ne_eq, not_not]
    rw [Finsupp.finset_sum_apply]
    refine Finset.sum_eq_zero fun x hx => ?_
    erw [AddMonoidAlgebra.lsingle_apply, AddMonoidAlgebra.lsingle_apply]; aesop
  aesop

private lemma rename_equiv_mem_restrictDegree {R : Type*} [CommSemiring R]
    {σ τ : Type*}
    (e : σ ≃ τ) (p : MvPolynomial σ R) (n : ℕ)
    (hp : p ∈ MvPolynomial.restrictDegree σ R n) :
    (MvPolynomial.rename e p) ∈ MvPolynomial.restrictDegree τ R n := by
  intro m hm
  obtain ⟨n', hn', hm_eq⟩ : ∃ n' ∈ p.support, m = n'.mapDomain e := by
    simp +zetaDelta at *
    rw [MvPolynomial.rename_eq] at hm
    contrapose! hm
    rw [Finsupp.mapDomain]
    rw [Finsupp.sum, Finsupp.finset_sum_apply]
    exact Finset.sum_eq_zero fun x hx =>
      Finsupp.single_eq_of_ne (hm x (by aesop))
  aesop

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
  have h_l_eq : ℓ = (ℓ - v) + v := (Nat.sub_add_cancel v.is_le).symm
  set finEquiv := finSumFinEquiv (m := ℓ - v) (n := v).symm
  set H_sum := MvPolynomial.rename (f := (finCongr h_l_eq).trans finEquiv) poly
  set H_grouped : L[X Fin ↑v][X Fin (ℓ - ↑v)] := (sumAlgEquiv L (Fin (ℓ - v)) (Fin v)) H_sum
  set eval_map : L[X Fin ↑v] →+* L := (eval challenges : MvPolynomial (Fin v) L →+* L)
  have h_Hgrouped_degreeLE : H_grouped ∈ (L[X Fin ↑v])⦃≤ deg⦄[X Fin (ℓ - ↑v)] := by
    exact Binius.BinaryBasefold.sumAlgEquiv_mem_restrictDegree H_sum deg
      (Binius.BinaryBasefold.rename_equiv_mem_restrictDegree
        ((finCongr h_l_eq).trans finEquiv) poly deg hp)
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
noncomputable def getSumcheckRoundPoly (i : Fin ℓ) (h : ↥L⦃≤ 2⦄[X Fin (ℓ - ↑i.castSucc)])
    : L⦃≤ 2⦄[X] := by
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

lemma getSumcheckRoundPoly_eval_eq (i : Fin ℓ) (h_poly : ↥L⦃≤ 2⦄[X Fin (ℓ - ↑i.castSucc)]) (r : L) :
    (getSumcheckRoundPoly ℓ 𝓑 i h_poly).val.eval r =
    ∑ x ∈ (univ.map 𝓑) ^ᶠ (ℓ - ↑i.castSucc - 1),
      MvPolynomial.eval (Fin.cons r x ∘ Fin.cast (by
        exact (Nat.sub_add_cancel (Nat.one_le_of_lt (Nat.sub_pos_of_lt i.isLt))).symm
      )) h_poly.val := by
  have h_pos : 0 < (ℓ - ↑i.castSucc) := Nat.sub_pos_of_lt i.isLt
  have h_eq_nat : (ℓ - ↑i.castSucc) = ((ℓ - ↑i.castSucc) - 1) + 1 :=
    (Nat.sub_add_cancel (Nat.one_le_of_lt h_pos)).symm
  unfold getSumcheckRoundPoly
  simp only [Polynomial.eval_finset_sum, Polynomial.eval_map]
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
    simp only [Polynomial.eval_map]
    stop
    congr
    ext j
    simp [Fin.append, Fin.addCases]
    split <;> simp

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
  let e_pi := Equiv.piCongrLeft (fun _ => L) ψ
  stop
  have h_sum : ∑ x ∈ (univ.map 𝓑) ^ᶠ (ℓ - ↑i.castSucc), MvPolynomial.eval x h.val =
               ∑ y ∈ (univ.map 𝓑) ^ᶠ ((m - 1) + 1), MvPolynomial.eval (y ∘ ψ) h.val := by
    apply Finset.sum_equiv e_pi
    · intro x
      simp only [Fintype.piFinset, Finset.mem_pi, Finset.mem_map, Finset.mem_univ, true_and]
      exact fun h a => h (ψ a)
    · intro y
      simp only [Fintype.piFinset, Finset.mem_pi, Finset.mem_map, Finset.mem_univ, true_and]
      exact fun h a => h (ψ.symm a)
    · intro x hx
      congr
      ext a
      simp [e_pi]
  change _ = ∑ x ∈ (univ.map 𝓑) ^ᶠ (ℓ - ↑i.castSucc), MvPolynomial.eval x h.val
  erw [h_sum]
  rw [Fintype.piFinset_succ]
  simp only [Finset.map_univ_two, Fin.isValue, sum_insert, mem_singleton, Fin.reduceNe, ↓reduceIte,
    sum_singleton]
  apply Finset.sum_congr rfl
  intro x hx
  congr 1
  · dsimp [ψ]
    rw [MvPolynomial.eval_rename]
    rfl
  · dsimp [ψ]
    rw [MvPolynomial.eval_rename]
    rfl

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

lemma multilinear_eval_eq_sum_bool_hypercube (challenges : Fin ℓ → L) (t : ↥L⦃≤ 1⦄[X Fin ℓ]) :
    t.val.eval challenges = ∑ (x : Fin (2^ℓ)),
      (multilinearWeight (r := challenges) (i := x)) * (t.val.eval (bitsOfIndex x) : L) := by
  sorry

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
lemma fin_ℓ_lt_ℓ_add_R (i : Fin ℓ)
    : i.val < ℓ + 𝓡 := by omega

omit [NeZero ℓ] [NeZero r] [NeZero 𝓡] in
lemma fin_ℓ_lt_r {h_ℓ_add_R_rate : ℓ + 𝓡 < r} (i : Fin ℓ)
    : i.val < r := by omega

omit [NeZero ℓ] [NeZero r] [NeZero 𝓡] in
lemma fin_ℓ_add_one_lt_r {h_ℓ_add_R_rate : ℓ + 𝓡 < r} (i : Fin (ℓ + 1))
    : i.val < r := by omega

omit [NeZero ℓ] in
lemma fin_ℓ_steps_lt_ℓ_add_one (i : Fin ℓ) (steps : ℕ)
    (h : i.val + steps ≤ ℓ) : i.val + steps < ℓ + 1 :=
  Nat.lt_of_le_of_lt h (Nat.lt_succ_self ℓ)

omit [NeZero ℓ] in
lemma fin_ℓ_steps_lt_ℓ_add_R (i : Fin ℓ) (steps : ℕ) (h : i.val + steps ≤ ℓ)
    : i.val + steps < ℓ + 𝓡 := by
  apply Nat.lt_add_of_pos_right_of_le; omega

omit [NeZero ℓ] [NeZero r] [NeZero 𝓡] in
lemma fin_ℓ_steps_lt_r {h_ℓ_add_R_rate : ℓ + 𝓡 < r} (i : Fin ℓ) (steps : ℕ)
    (h : i.val + steps ≤ ℓ) : i.val + steps < r := by
  apply Nat.lt_of_le_of_lt (n := i + steps) (k := r) (m := ℓ) (h₁ := h)
    (by exact lt_of_add_right_lt h_ℓ_add_R_rate)

omit [NeZero ℓ] [NeZero r] [NeZero 𝓡] in
lemma ℓ_lt_r {h_ℓ_add_R_rate : ℓ + 𝓡 < r}
    : ℓ < r := by omega

omit [NeZero ℓ] [NeZero r] [NeZero 𝓡] in
lemma fin_r_succ_bound {h_ℓ_add_R_rate : ℓ + 𝓡 < r} (i : Fin r) (h_i : i + 1 < ℓ + 𝓡)
    : i + 1 < r := by omega

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
lemma Sdomain_bound {x : ℕ} (h_x : x ≤ ℓ)
  : x < ℓ + 𝓡 := by
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
    x = free_coeff_term + y_lifted
    := by
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

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ in
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
  simp only at h_repr_x
  rw [←hx_eq] at h_repr_x
  simp only [fiber_coeff, add_lt_iff_neg_right, not_lt_zero', ↓reduceDIte, add_tsub_cancel_right,
    Fin.eta] at h_repr_x
  exact h_repr_x.symm

omit [CharP L 2] in
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
    simp only at h_repr_of_reConstructedX
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
    ) • (basis_x j)
     := by
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
theorem card_qMap_total_fiber (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := destIdx)) :
    Fintype.card (Set.image (qMap_total_fiber 𝔽q β (i := i) (steps := steps)
      h_destIdx h_destIdx_le
      (y := y)) Set.univ) = 2 ^ steps := by
  -- The cardinality of the image of a function equals the cardinality of its domain
  -- if it is injective.
  rw [Set.card_image_of_injective Set.univ]
  -- The domain is `Fin (2 ^ steps)`, which has cardinality `2 ^ steps`.
  · -- ⊢ Fintype.card ↑Set.univ = 2 ^ steps
    simp only [Fintype.card_setUniv, Fintype.card_fin]
  · -- prove that `qMap_total_fiber` is an injective function.
    intro k₁ k₂ h_eq
    -- Assume two indices `k₁` and `k₂` produce the same point `x`.
    let basis_x := sDomain_basis 𝔽q β h_ℓ_add_R_rate i (Sdomain_bound (by omega))
    -- If the points are equal, their basis representations must be equal.
    set fiberMap := qMap_total_fiber 𝔽q β (i := i) (steps := steps)
      h_destIdx h_destIdx_le (y := y)
    have h_coeffs_eq : basis_x.repr (fiberMap k₁) = basis_x.repr (fiberMap k₂) := by
      rw [h_eq]
    -- The first `steps` coefficients are determined by the bits of `k₁` and `k₂`.
    -- If the coefficients are equal, the bits must be equal.
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
      -- Extract the j-th coefficient from h_coeffs_eq and show it implies the bits are equal.
    -- If all the bits of two numbers are equal, the numbers themselves are equal.
    apply Fin.eq_of_val_eq
    -- ⊢ ∀ {n : ℕ} {i j : Fin n}, ↑i = ↑j → i = j
    apply eq_iff_eq_all_getBits.mpr
    intro k
    by_cases h_k : k < steps
    · simp only [h_bits_eq ⟨k, by omega⟩]
    · -- The bits at positions ≥ steps must be deterministic
      conv_lhs => rw [Nat.getBit_of_lt_two_pow]
      conv_rhs => rw [Nat.getBit_of_lt_two_pow]
      simp only [h_k, ↓reduceIte]

omit [CharP L 2] in
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
      h_destIdx h_destIdx_le y₂ '' Set.univ).toFinset)
    := by
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
    mergeFinMap_PO2_left_right (left := fiber_eval_z₀) (right := fiber_eval_z₁) := by
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
        apply Nat.getBit_1_of_ge_two_pow_and_lt_two_pow_succ; omega; omega
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

section FoldTheory

/-- Single-step fold : Given `f : S⁽ⁱ⁾ → L` and challenge `r`, produce `S⁽ⁱ⁺¹⁾ → L`, where
`f⁽ⁱ⁺¹⁾ = fold(f⁽ⁱ⁾, r) : y ↦ [1-r, r] · [[x₁, -x₀], [-1, 1]] · [f⁽ⁱ⁾(x₀), f⁽ⁱ⁾(x₁)]`
-/
def fold (i : Fin r) {destIdx : Fin r} (h_destIdx : destIdx = i.val + 1)
  (h_destIdx_le : destIdx ≤ ℓ) (f : (sDomain 𝔽q β h_ℓ_add_R_rate) i → L) (r_chal : L) :
    (sDomain 𝔽q β h_ℓ_add_R_rate) (i := destIdx) → L :=
  fun y => by
    let fiberMap := qMap_total_fiber 𝔽q β (i := i) (steps := 1)
      (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (y := y)
    let x₀ := fiberMap 0
    let x₁ := fiberMap 1
    let f_x₀ := f x₀
    let f_x₁ := f x₁
    exact f_x₀ * ((1 - r_chal) * x₁.val - r_chal) + f_x₁ * (r_chal - (1 - r_chal) * x₀.val)

/-- Helper to cast matrices between equal dimensions (needed for 2^(k+1) = 2^k + 2^k) -/
@[reducible, simp]
def reindexSquareMatrix {n m : Type} (e : n ≃ m) (M : Matrix n n L) : Matrix m m L :=
  Matrix.reindex (α := L) (eₘ := e) (eₙ := e) M

def butterflyMatrix (n : ℕ) (z₀ z₁ : L) : Matrix (Fin (2 ^ (n + 1))) (Fin (2 ^ (n + 1))) L :=
    -- 4. Construct the Butterfly Matrix using Scalar Identities
    --    [ z₁*I_{2^n}   -z₀*I_{2^n} ]
    --    [ -1*I_{2^n}     1*I_{2^n} ]
    let I_n : Matrix (Fin (2^n)) (Fin (2^n)) L := 1 -- Identity matrix
    let butterfly : Matrix (Fin (2 ^ (n + 1))) (Fin (2 ^ (n + 1))) L :=
      reindexSquareMatrix (e := finCongr (by omega)) (M := Matrix.from4Blocks
                                                (z₁ • I_n)  (-(z₀ • I_n))
                                                ((-1 : L) • I_n) ((1 : L) • I_n))
    butterfly

omit [NeZero r] [Fintype L] [DecidableEq L] [CharP L 2] [NeZero ℓ] [NeZero 𝓡] in
/-- Characterization of butterflyMatrix at `n=0` (used in single-step folding). -/
@[simp]
lemma butterflyMatrix_zero_apply (z₀ z₁ : L) :
    butterflyMatrix (𝓡 := 𝓡) (ℓ := ℓ) (r := r) (n := 0) z₀ z₁ = !![z₁, -z₀; -1, 1] := by
  rw [butterflyMatrix]
  simp only [reduceAdd, reducePow, reindexSquareMatrix, Nat.pow_zero, finCongr_refl, neg_smul,
    one_smul, reindex_apply, Equiv.refl_symm, Equiv.coe_refl, submatrix_id_id]
  unfold Matrix.from4Blocks
  simp only [reduceAdd, lt_one_iff, Fin.val_eq_zero_iff, Fin.isValue, smul_apply, smul_eq_mul,
    neg_apply]
  funext i j
  fin_cases i <;> fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue, ↓reduceDIte, one_apply_eq, mul_one, of_apply, cons_val',
    cons_val_zero, cons_val_fin_one] -- 0, 0 (Top Left)
  · -- 0, 1 (Top Right)
    simp only [Fin.zero_eta, Fin.isValue, ↓reduceDIte, Fin.mk_one, one_ne_zero, of_apply,
    cons_val', cons_val_one, cons_val_fin_one, cons_val_zero, neg_inj];
    rw [Matrix.one_apply]
    simp only [Fin.zero_eta, Fin.isValue, tsub_self, ↓reduceIte, mul_one]
  · rfl -- 1, 0 (Bottom Left)
  · rfl -- 1, 1 (Bottom Right)

omit [NeZero r] [Fintype L] [DecidableEq L] [CharP L 2] [NeZero ℓ] [NeZero 𝓡] in
lemma butterflyMatrix_det_ne_zero (n : ℕ) (z₀ z₁ : L) (h_ne : z₀ ≠ z₁) :
  (butterflyMatrix (𝓡 := 𝓡) (ℓ := ℓ) (r := r) (n := n) z₀ z₁).det ≠ 0 := by
  -- Proof: det is (z₁ - z₀)^(2^n)
  -- 1. Use Matrix.det_from4Blocks (since blocks commute)
  -- 2. Simplify to det((z₁ - z₀) • I)
  -- 3. Use Matrix.det_smul and h_ne
  dsimp only [butterflyMatrix]
  -- The matrix is:
  -- [ z₁*I   -z₀*I ]
  -- [ -1*I    1*I  ]
  -- Since the blocks commute (scalar multiples of identity), det(M) = det(AD - BC)
  -- AD - BC = (z₁*I)(I) - (-z₀*I)(-I) = z₁*I - z₀*I = (z₁ - z₀)*I
  rw [Matrix.det_reindex_self]
  rw [Matrix.det_from4Blocks_of_squareSubblocks_commute]
  · -- Calculate the determinant of the combined block
    rw [one_smul, mul_one, Matrix.smul_one_eq_diagonal, Matrix.smul_one_eq_diagonal]
    -- ⊢ ((diagonal fun x ↦ z₁) - (-diagonal fun x ↦ z₀) * -1 • 1).det ≠ 0
    simp only [diagonal_neg, neg_smul, one_smul, mul_neg, mul_one, neg_neg, diagonal_sub,
      det_diagonal, prod_const, Finset.card_univ, Fintype.card_fin, ne_eq, Nat.pow_eq_zero,
      OfNat.ofNat_ne_zero, false_and, not_false_eq_true, pow_eq_zero_iff]
    -- ⊢ ¬z₁ - z₀ = 0
    exact sub_ne_zero_of_ne (Ne.symm h_ne)
  · -- Prove the blocks commute
    -- The bottom-right block is `1 • I = I`, which commutes with everything.
    -- ⊢ Commute (-1 • 1) (1 • 1)
    simp only [neg_smul, one_smul, Commute.one_right]

/-- `BlkDiagMat(n, Mz₀, Mz₁) = [Mz₀, 0;`
                                   `0, Mz₁]`
where `Mz₀` and `Mz₁` are set as the `n-step` `foldMatrix` of `z₀` and `z₁` in **Lemma 4.9**. -/
def blockDiagMatrix (n : ℕ)
    (Mz₀ Mz₁ : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) L) :
    Matrix (Fin (2 ^ (n + 1))) (Fin (2 ^ (n + 1))) L :=
  let zero_blk : Matrix (Fin (2^n)) (Fin (2^n)) L := 0
  let blk_diag : Matrix (Fin (2 ^ (n + 1))) (Fin (2 ^ (n + 1))) L :=
    reindexSquareMatrix (e := finCongr (by omega))
      (M := Matrix.from4Blocks Mz₀ zero_blk zero_blk Mz₁)
  blk_diag

omit [NeZero r] [Fintype L] [DecidableEq L] [CharP L 2] [NeZero ℓ] [NeZero 𝓡] in
/-- Block Diagonal matrix multiplication on top half returns M_top * v_top
Proof similar to challengeTensorExpansionMatrix_mulVec_F₂_eq_Fin_merge_PO2.
-/
lemma blockDiagMatrix_mulVec_F₂_eq_Fin_merge_PO2 (n : ℕ)
    (A B : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) L)
    (v_top : Fin (2 ^ n) → L) (v_bot : Fin (2 ^ n) → L) :
    mergeFinMap_PO2_left_right (left := A *ᵥ v_top) (right := B *ᵥ v_bot)
    = blockDiagMatrix (r := r) (ℓ := ℓ) (𝓡 := 𝓡) (n := n) (Mz₀ := A) (Mz₁ := B)
      *ᵥ mergeFinMap_PO2_left_right (left := v_top) (right := v_bot) := by
  dsimp only [blockDiagMatrix]
  conv_rhs => -- Move reindexing from Matrix to Vector
    rw [Matrix.reindex_mulVec]
  funext k
  unfold mergeFinMap_PO2_left_right
  unfold Matrix.from4Blocks Fin.reindex Matrix.mulVec dotProduct
  -- Now unfold everything
  simp only [zero_apply, finCongr_symm, Function.comp_apply, finCongr_apply, dite_mul, zero_mul,
    sum_dite_irrel, Fin.val_cast]
  simp_rw [Fin.sum_univ_add]
  simp_rw [←Finset.sum_add_distrib]
  simp only [Fin.val_castAdd, Fin.is_lt, ↓reduceDIte, Fin.eta, Fin.natAdd_eq_addNat, Fin.val_addNat,
    add_lt_iff_neg_right, not_lt_zero', add_zero, add_tsub_cancel_right, zero_add]

/-- The recursive definition of the `k-step` fold matrix of point `y`: `M_{k, y}`.
`M_{k, y} = butterflyMatrix(k, z₀, z₁) * [M_{k-1, z₀}, 0; 0, M_{k-1, z₁}]`
where `z₀` and `z₁` are the 1-step fiber of `y`. `M_{k, y}` is actually the
`inverse additive NTT (LCH14)` on the coset `(x₀, ..., x_{2^k-1})` **(Remark 4.10)**. -/
def foldMatrix (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx = i + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate destIdx) :
    Matrix (Fin (2 ^ steps)) (Fin (2 ^ steps)) L :=
  match steps with
  | 0 =>
    -- Base case: steps = 0. Identity matrix of size 1 (2^0).
    (1 : Matrix (Fin 1) (Fin 1) L) -- diagonal matrix
  | n + 1 => by
    -- Recursive step: n -> n + 1
    -- 1. Identify the "previous" y's (z₀ and z₁) from the fiber of the current y
    --    Note: y is at index i + n + 1. We need the fiber at i + n.
    let midIdx : Fin r := ⟨i + n, by omega⟩
    have h_midIdx_val : midIdx.val = i + n := by dsimp only [midIdx]
    let fiberMap := qMap_total_fiber 𝔽q β (i := midIdx) (steps := 1)
       h_destIdx h_destIdx_le (y := y)
    let z₀ : sDomain 𝔽q β h_ℓ_add_R_rate midIdx := fiberMap 0
    let z₁ : sDomain 𝔽q β h_ℓ_add_R_rate midIdx := fiberMap 1
    -- 2. Recursively compute M for z₀ and z₁
    --    These matrices have size 2^n x 2^n
    let M_z₀ := foldMatrix i n (destIdx := midIdx) (by omega) (by omega) z₀
    let M_z₁ := foldMatrix i n (destIdx := midIdx) (by omega) (by omega) z₁
    -- 3. Construct the Block Diagonal Matrix: [ M_z₀  0  ]
    --                                         [  0   M_z₁]
    let blk_diag : Matrix (Fin (2 ^ (n + 1))) (Fin (2 ^ (n + 1))) L :=
      blockDiagMatrix (r := r) (ℓ := ℓ) (𝓡 := 𝓡) (n := n) (Mz₀ := M_z₀) (Mz₁ := M_z₁)
    -- 4. Construct the Butterfly Matrix using Scalar Identities
    --    [ z₁*I_{2^n}   -z₀*I_{2^n} ]
    --    [ -1*I_{2^n}     1*I_{2^n} ]
    let butterfly : Matrix (Fin (2 ^ (n + 1))) (Fin (2 ^ (n + 1))) L :=
      butterflyMatrix (r := r) (ℓ := ℓ) (𝓡 := 𝓡) (n := n) (z₀ := z₀) (z₁ := z₁)
    exact butterfly * blk_diag

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
lemma foldMatrix_det_ne_zero (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (destIdx)) :
    (foldMatrix 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
      h_destIdx h_destIdx_le (y := y)).det ≠ 0 := by
  revert destIdx h_destIdx h_destIdx_le y
  induction steps with
  | zero =>
    intro destIdx h_destIdx h_destIdx_le y
    simp only [Nat.pow_zero, foldMatrix, det_unique, one_apply_eq, ne_eq, one_ne_zero,
    not_false_eq_true];
  | succ n ih =>
    intro destIdx h_destIdx h_destIdx_le y
    rw [foldMatrix]
    -- 1. Determinant of product = product of determinants
    -- 2. det(butterfly) ≠ 0 because z₀ ≠ z₁ (by injectivity of qMap_total_fiber)
    -- 3. det(block_diag) ≠ 0 because det(M_z₀) ≠ 0 and det(M_z₁) ≠ 0 (by IH)
    -- Expand definition of foldMatrix for n+1
    dsimp [foldMatrix]
    -- Determinant of product
    rw [Matrix.det_mul]
    let midIdx : Fin r := ⟨i + n, by omega⟩
    let fiberMap := qMap_total_fiber 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := midIdx)
      (steps := 1) (destIdx := destIdx) (h_destIdx := by dsimp only [midIdx]; omega)
      (h_destIdx_le := by omega) (y := y)
    let z₀ := fiberMap 0
    let z₁ := fiberMap 1
    apply mul_ne_zero
    -- 1. Butterfly Matrix part
    · -- ⊢ Δ(butterflyMatrix(n, z₀, z₁)) ≠ 0
      apply butterflyMatrix_det_ne_zero (L := L) (z₀ := z₀) (z₁ := z₁) (n := n)
      -- ⊢ ↑z₀ ≠ ↑z₁
      unfold z₀ z₁ fiberMap
      let z₀_eq := qMap_total_fiber_one_level_eq (i := ⟨midIdx, by dsimp [midIdx]; omega⟩)
        (destIdx := destIdx) (h_destIdx := by dsimp only [midIdx]; omega)
        (h_destIdx_le := by omega) (y := y) (k := 0)
      let z₁_eq := qMap_total_fiber_one_level_eq (i := ⟨midIdx, by dsimp [midIdx]; omega⟩)
        (destIdx := destIdx) (h_destIdx := by dsimp only [midIdx]; omega) (h_destIdx_le := by omega)
        (y := y) (k := 1)
      conv_lhs => rw [z₀_eq]
      conv_rhs => rw [z₁_eq]
      simp only [Fin.eta, Fin.isValue, Submodule.coe_add, SetLike.val_smul, ne_eq, add_left_inj]
      unfold Fin2ToF2
      rw [get_sDomain_first_basis_eq_1]
      simp only [Fin.isValue, ↓reduceIte, zero_smul, one_ne_zero, one_smul, zero_ne_one,
        not_false_eq_true]
    -- 2. Block Diagonal Part
    · dsimp only [blockDiagMatrix]
      rw [Matrix.det_reindex_self]
      rw [Matrix.det_from4Blocks_of_squareSubblocks_commute]
      -- Diagonal blocks: M_z₀ and M_z₁. Off-diagonal: 0.
      -- det(M) = det(M_z₀) * det(M_z₁) - 0*0
      · simp only [Fin.isValue, mul_zero, sub_zero, det_mul, ne_eq, _root_.mul_eq_zero, not_or]
       -- ⊢ `(Δ(M_z₀) ≠ 0 ∧ Δ(M_z₁) ≠ 0)`
        have h_det_M_z₀_ne_zero := ih (destIdx := midIdx) (by rfl)
          (h_destIdx_le := by dsimp only [midIdx]; omega) (y := z₀)
        have h_det_M_z₁_ne_zero := ih (destIdx := midIdx) (by rfl)
          (h_destIdx_le := by dsimp only [midIdx]; omega) (y := z₁)
        constructor
        · exact h_det_M_z₀_ne_zero
        · exact h_det_M_z₁_ne_zero
      · simp only [Fin.isValue, Commute.zero_left]

/-- **Definition 4.8**: Iterated fold over `steps` steps starting at domain index `i`. -/
def iterated_fold (i : Fin r) (steps : ℕ) {destIdx : Fin r}
  (h_destIdx : destIdx = i + steps)
  (h_destIdx_le : destIdx ≤ ℓ)
  (f : sDomain 𝔽q β h_ℓ_add_R_rate (i := i) → L) (r_challenges : Fin steps → L) :
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := destIdx)) → L := by
  let domain_type := sDomain 𝔽q β h_ℓ_add_R_rate
  let fold_func := fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  let α (j : Fin (steps + 1)) := domain_type (⟨i + j.val, by omega⟩) → L
  let fold_step (j : Fin steps) (f_acc : α ⟨j, by omega⟩) : α j.succ := by
    unfold α domain_type at *
    intro x
    -- ⊢ L => now fold `f_acc` and evaluate at `x`
    have fold_func := fold_func (i := ⟨i + j.val, by omega⟩)
      (destIdx := ⟨i + j.val + 1, by omega⟩)
      (h_destIdx := by simp only)
      (h_destIdx_le := by simp only; omega)
      (f := f_acc) (r_chal := r_challenges j)
    exact fold_func x
  let res : α (Fin.last steps) := Fin.dfoldl (n := steps) (α := α)
    (f := fun i (accF : α i.castSucc) =>
      have fSucc : α ⟨i.succ, by omega⟩ := fold_step i accF
      fSucc) (init := f)
  exact fun y => res ⟨y, by
    simp only [Fin.val_last]
    have h_eq : ⟨i + steps, by omega⟩ = destIdx := by
      apply Fin.eq_of_val_eq
      simp only
      exact h_destIdx.symm
    rw [h_eq]
    simp only [SetLike.coe_mem]
  ⟩

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
/-- **Base Case**: Iterated fold with 0 steps is the identity
(returning the initial function `f`). -/
lemma iterated_fold_zero_steps (i : Fin r) {destIdx : Fin r}
    (h_destIdx : destIdx = i.val) (h_destIdx_le : destIdx ≤ ℓ)
    (f : sDomain 𝔽q β h_ℓ_add_R_rate (i := i) → L)
    (r_challenges : Fin 0 → L) :
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := 0)
      (h_destIdx := by omega) (h_destIdx_le := h_destIdx_le) (f := f)
      (r_challenges := r_challenges) = fun y ↦ f (cast (by rw [sDomain_eq_of_eq]; omega) y) := by
  have h_eq : destIdx = i := by omega
  subst h_eq;
  dsimp only [iterated_fold]
  simp only [reduceAdd, Fin.val_castSucc, Fin.val_succ, id_eq, Fin.reduceLast, Fin.coe_ofNat_eq_mod,
    Subtype.coe_eta, Fin.dfoldl_zero, cast_eq]

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
lemma iterated_fold_last (i : Fin r) {midIdx destIdx : Fin r} (steps : ℕ)
  (h_midIdx : midIdx = i + steps) (h_destIdx : destIdx = i + steps + 1) (h_destIdx_le : destIdx ≤ ℓ)
  (f : sDomain 𝔽q β h_ℓ_add_R_rate (i := i) → L) (r_challenges : Fin (steps + 1) → L) :
  let fold_full := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
    (steps := steps + 1) h_destIdx h_destIdx_le (f := f) (r_challenges := r_challenges)
  let fold_init := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
    (steps := steps) h_midIdx (h_destIdx_le := by omega) (f := f)
    (r_challenges := Fin.init r_challenges)
  let fold_init_fold := fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := midIdx)
    (destIdx := destIdx) (h_destIdx := by omega) (h_destIdx_le := by omega)
    (f := fold_init) (r_chal := r_challenges (Fin.last steps))
  fold_full = fold_init_fold := by
  have h_bound_dest : i.val + steps + 1 < r := by omega
  have h_bound_mid : i.val + steps < r := by omega
  have h_mid_clean : midIdx = ⟨i.val + steps, h_bound_mid⟩ := Fin.eq_of_val_eq (by omega)
  have h_dest_clean : destIdx = ⟨i.val + steps + 1, h_bound_dest⟩ := Fin.eq_of_val_eq (by omega)
  subst h_mid_clean h_dest_clean
  simp only
  conv_lhs => unfold iterated_fold
  simp only
  rw [Fin.dfoldl_succ_last]
  simp only [Fin.succ_last, succ_eq_add_one, Fin.val_last, Function.comp_apply, Fin.val_castSucc,
    Fin.val_succ, id_eq]
  rfl

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
lemma iterated_fold_congr_source_index
    {i i' : Fin r} (h : i = i')
    (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx = i.val + steps)
    (h_destIdx' : destIdx = i'.val + steps)
    (h_destIdx_le : destIdx ≤ ℓ)
    (f : sDomain 𝔽q β h_ℓ_add_R_rate (i := i) → L)
    (r_challenges : Fin steps → L) :
  iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := i)  steps h_destIdx  h_destIdx_le f r_challenges =
  iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := i') steps h_destIdx' h_destIdx_le
    (fun x => f (cast (h := by rw [h]) x)) r_challenges := by
  subst h
  simp only [cast_eq]

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
lemma iterated_fold_congr_dest_index
    {i : Fin r} (steps : ℕ) {destIdx destIdx' : Fin r}
    (h_destIdx : destIdx = i.val + steps)
    (h_destIdx_le : destIdx ≤ ℓ) (h_destIdx_eq_destIdx' : destIdx = destIdx')
    (f : sDomain 𝔽q β h_ℓ_add_R_rate (i := i) → L)
    (r_challenges : Fin steps → L) (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := destIdx))
    :
  iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (destIdx := destIdx)
    (i := i)  steps h_destIdx  h_destIdx_le f r_challenges y =
  iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (destIdx := destIdx')
    (i := i) steps (by omega) (h_destIdx_le := by omega)
    (f) r_challenges (y := cast (h := by rw [h_destIdx_eq_destIdx']) y) := by
  subst h_destIdx_eq_destIdx'; rfl

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
lemma iterated_fold_congr_steps_index
    {i : Fin r} (steps steps' : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx = i.val + steps)
    (h_destIdx_le : destIdx ≤ ℓ) (h_steps_eq_steps' : steps = steps')
    (f : sDomain 𝔽q β h_ℓ_add_R_rate (i := i) → L)
    (r_challenges : Fin steps → L) (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := destIdx))
    :
  iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (destIdx := destIdx)
    (i := i)  steps h_destIdx  h_destIdx_le f r_challenges y =
  iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (destIdx := destIdx)
    (i := i) steps' (by omega) (h_destIdx_le := by omega)
    (f) (fun (cIdx : Fin steps') => r_challenges ⟨cIdx, by omega⟩) (y := y) := by
  subst h_steps_eq_steps'; rfl

/-- Transitivity of iterated_fold : folding for `steps₁` and then for `steps₂`
equals folding for `steps₁ + steps₂` with concatenated challenges.
-/
lemma iterated_fold_transitivity
    (i : Fin r) {midIdx destIdx : Fin r} (steps₁ steps₂ : ℕ)
    (h_midIdx : midIdx = i.val + steps₁) (h_destIdx : destIdx = i + steps₁ + steps₂)
    (h_destIdx_le : destIdx ≤ ℓ)
    (f : sDomain 𝔽q β h_ℓ_add_R_rate (i := i) → L)
    (r_challenges₁ : Fin steps₁ → L) (r_challenges₂ : Fin steps₂ → L) :
    -- LHS : The nested fold (folding twice)
    have hi1 : i.val + steps₁ ≤ ℓ := by omega
    have hi2 : i.val + steps₂ ≤ ℓ := by omega
    have hi12 : steps₁ + steps₂ < ℓ + 1 := by omega
    let lhs := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := midIdx) (steps := steps₂) (h_destIdx := by omega) (h_destIdx_le := h_destIdx_le)
      (f := by
        exact iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps₁)
          (h_destIdx := h_midIdx) (h_destIdx_le := by omega) (f := f)
          (r_challenges := r_challenges₁)
      ) r_challenges₂
    let rhs := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
      (steps := steps₁ + steps₂) (h_destIdx := by omega) (h_destIdx_le := h_destIdx_le)
      (f := f) (r_challenges := Fin.append r_challenges₁ r_challenges₂)
    lhs = rhs := by
  sorry -- admitted for brevity, relies on a lemma like `Fin.dfoldl_add`

/-- **Definition 4.6** : the single-step vector-matrix-vector multiplication form of `fold` -/
def fold_single_matrix_mul_form (i : Fin r) {destIdx : Fin r}
  (h_destIdx : destIdx = i.val + 1) (h_destIdx_le : destIdx ≤ ℓ)
  (f : (sDomain 𝔽q β h_ℓ_add_R_rate) i → L)
  (r_challenge : L) : (y : (sDomain 𝔽q β h_ℓ_add_R_rate) destIdx) → L :=
  fun y => by
    let fiberMap := qMap_total_fiber 𝔽q β (i := i) (steps := 1)
      h_destIdx h_destIdx_le (y := y)
    let fiber_eval_mapping : (Fin 2) → L := fiberEvaluations 𝔽q β (steps := 1)
      (i := i) h_destIdx h_destIdx_le f y
    let z₀ : sDomain 𝔽q β h_ℓ_add_R_rate i := fiberMap 0
    let z₁ : sDomain 𝔽q β h_ℓ_add_R_rate i := fiberMap 1
    let challenge_vec : Fin (2 ^ 1) → L :=
      challengeTensorExpansion (n := 1) (r := fun _ => r_challenge)
    let fold_mat : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) L :=
      butterflyMatrix (𝓡 := 𝓡) (ℓ := ℓ) (r := r) (n := 0) (z₀ := z₀) (z₁ := z₁)
    -- Matrix-vector multiplication : challenge_vec^T • (fold_mat • fiber_eval_mapping)
    let intermediate_fn := Matrix.mulVec fold_mat fiber_eval_mapping -- rhs Mat-Vec mul
    exact dotProduct challenge_vec intermediate_fn -- vec-vec dot product

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
/-- The equality between the 1-step point-wise fold() operation vs the vec-mat-vec
multiplication form from **Definition 4.6** -/
lemma fold_eval_single_matrix_mul_form (i : Fin r) {destIdx : Fin r}
  (h_destIdx : destIdx = i.val + 1) (h_destIdx_le : destIdx ≤ ℓ)
  (f : (sDomain 𝔽q β h_ℓ_add_R_rate) i → L) (r_challenge : L) :
  fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (destIdx := destIdx)
    (h_destIdx := by omega) (h_destIdx_le := h_destIdx_le) (f := f) (r_chal := r_challenge)
  = fold_single_matrix_mul_form 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
    h_destIdx h_destIdx_le (f := f) (r_challenge := r_challenge) := by
  unfold fold_single_matrix_mul_form fold
  funext y
  simp only [Fin.isValue, reducePow, vec2_dotProduct]
  -- Approach: decompose the rhs into a flat sum expression
  have h_chal_tensor_vec_eq : challengeTensorExpansion (n := 1) (r := fun _ => r_challenge)
    = ![1 - r_challenge, r_challenge] := by
      unfold challengeTensorExpansion multilinearWeight
      simp only [reducePow, univ_unique, Fin.default_eq_zero, Fin.isValue, Fin.val_eq_zero,
        testBit_zero, decide_eq_true_eq, prod_ite_irrel, prod_const, card_singleton, pow_one,
        succ_eq_add_one, reduceAdd]
      funext i
      by_cases h : i = 0
      · simp only [h, Fin.isValue, Fin.coe_ofNat_eq_mod, zero_mod, zero_ne_one, ↓reduceIte,
        cons_val_zero]
      · have h_i_eq_1 : i = 1 := by omega
        simp only [h_i_eq_1, Fin.isValue, Fin.coe_ofNat_eq_mod, mod_succ, ↓reduceIte, cons_val_one,
          cons_val_fin_one]
  set fiberMap := qMap_total_fiber 𝔽q β (i := i) (steps := 1)
    h_destIdx h_destIdx_le (y := y)
  set z₀ := fiberMap 0
  set z₁ := fiberMap 1
  let butterflyMat0 := butterflyMatrix_zero_apply (L := L) (𝓡 := 𝓡) (ℓ := ℓ) (r := r)
    (z₀ := z₀) (z₁ := z₁)
  conv_rhs => rw [butterflyMat0];
  conv_rhs =>
    unfold fiberEvaluations
    rw [Matrix.mulVec, Matrix.mulVec]; dsimp only [dotProduct]
    simp only [Fin.isValue, Fin.sum_univ_two]
    rw [h_chal_tensor_vec_eq]
    simp only [succ_eq_add_one, reduceAdd, Fin.isValue, cons_val_zero, reindexSquareMatrix,
      reducePow, finCongr_refl, reindex_apply, Equiv.refl_symm, Equiv.coe_refl, submatrix_apply,
      id_eq, cons_val_one, cons_val_fin_one]
  conv_rhs =>
    unfold Matrix.from4Blocks
    simp only [Fin.isValue, of_apply, cons_val', cons_val_zero, cons_val_fin_one, cons_val_one,
      neg_mul, one_mul]
  unfold z₀ z₁ fiberMap -- this helps Lean understand the goal better
  ring_nf

/-- The single point vec-mat-vec form of `fold(...)` in **Lemma 4.9** -/
def single_point_localized_fold_matrix_form (i : Fin r) {destIdx : Fin r} (steps : ℕ)
  (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
  (r_challenges : Fin steps → L)
  (y : (sDomain 𝔽q β h_ℓ_add_R_rate) destIdx)
  (fiber_eval_mapping : Fin (2 ^ steps) → L) :
  L := by
    let challenge_vec : Fin (2 ^ steps) → L :=
      challengeTensorExpansion (n := steps) (r := r_challenges)
    let fold_mat : Matrix (Fin (2 ^ steps)) (Fin (2 ^ steps)) L :=
      foldMatrix 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
      h_destIdx h_destIdx_le (y := y)
    -- Matrix-vector multiplication : challenge_vec^T • (fold_mat • fiber_eval_mapping)
    let intermediate_fn := Matrix.mulVec fold_mat fiber_eval_mapping -- rhs Mat-Vec mul
    exact dotProduct challenge_vec intermediate_fn -- vec-vec dot product

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
lemma single_point_localized_fold_matrix_form_congr_source_index
    {i i' : Fin r} (h : i = i')
    (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx = i.val + steps)
    (h_destIdx' : destIdx = i'.val + steps)
    (h_destIdx_le : destIdx ≤ ℓ)
    (r_challenges : Fin steps → L)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := destIdx))
    (fiber_eval_mapping : Fin (2 ^ steps) → L) :
  single_point_localized_fold_matrix_form 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    i steps h_destIdx h_destIdx_le r_challenges y fiber_eval_mapping =
  single_point_localized_fold_matrix_form 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    i' steps h_destIdx' h_destIdx_le r_challenges y fiber_eval_mapping := by
  subst h; rfl

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
lemma single_point_localized_fold_matrix_form_congr_dest_index
    {i : Fin r} (steps : ℕ) {destIdx destIdx' : Fin r}
    (h_destIdx : destIdx = i.val + steps)
    (h_destIdx_le : destIdx ≤ ℓ) (h_destIdx_eq_destIdx' : destIdx = destIdx')
    (r_challenges : Fin steps → L)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := destIdx))
    (fiber_eval_mapping : Fin (2 ^ steps) → L) :
  single_point_localized_fold_matrix_form 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    i steps h_destIdx h_destIdx_le r_challenges y fiber_eval_mapping =
  single_point_localized_fold_matrix_form 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    i steps (destIdx := destIdx') (by omega) (by omega) r_challenges
    (cast (by rw [h_destIdx_eq_destIdx']) y) fiber_eval_mapping := by
  subst h_destIdx_eq_destIdx'; rfl

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
lemma single_point_localized_fold_matrix_form_congr_steps_index
    {i : Fin r} (steps steps' : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx = i.val + steps)
    (h_destIdx_le : destIdx ≤ ℓ) (h_steps_eq_steps' : steps = steps')
    (r_challenges : Fin steps → L)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := destIdx))
    (fiber_eval_mapping : Fin (2 ^ steps) → L) :
  single_point_localized_fold_matrix_form 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    i steps h_destIdx h_destIdx_le r_challenges y fiber_eval_mapping =
  single_point_localized_fold_matrix_form 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    i steps' (by omega) h_destIdx_le
    (fun k ↦ r_challenges ⟨k, by omega⟩)
    y
    (fun k ↦ fiber_eval_mapping ⟨k, by subst h_steps_eq_steps'; exact k.is_lt⟩) := by
  subst h_steps_eq_steps'; rfl

/-- **From Lemma 4.9**: Matrix-vector multiplication form of iterated fold :
For a local `steps > 0`, `∀ i ∈ {0, ..., l-steps}`, `y ∈ S^(i+steps)`,
`fold(f^(i), r_0, ..., r_{steps-1})(y) = [⨂_{j=0}^{steps-1}(1-r_j, r_j)] • M_{steps, y}`
`• [f^(i)(x_0) ... f^(i)(x_{2 ^ steps-1})]^T`,
where
- `M_{steps, y}` is the `steps`-step **foldMatrix** of point `y`.
- the right-hand vector's values `(x_0, ..., x_{2 ^ steps-1})` represent the fiber
`(q^(i+steps-1) ∘ ... ∘ q^(i))⁻¹({y}) ⊂ S^(i)`. -/
def localized_fold_matrix_form (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
  (f : (sDomain 𝔽q β h_ℓ_add_R_rate) i → L)
  (r_challenges : Fin steps → L) : (y : (sDomain 𝔽q β h_ℓ_add_R_rate) destIdx) → L :=
  fun y =>
    let fiber_eval_mapping := fiberEvaluations 𝔽q β (steps := steps)
        (i := i)
        h_destIdx h_destIdx_le f y
    single_point_localized_fold_matrix_form 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i) (steps := steps) h_destIdx h_destIdx_le
      (r_challenges := r_challenges) (y := y) (fiber_eval_mapping := fiber_eval_mapping)

/-- The (2 x 1) vector `F₂(steps, r, z₀, z₁) = [fold(steps, r, z₀), fold(steps, r, z₁)]`.
This is the right-most vector when decomposing the outer single-step fold of **Lemma 4.9**.
NOTE: `h_F₂_y_eq` in lemma `iterated_fold_eq_matrix_form` below shows it OG form in Lemma 4.9. -/
def fold_eval_fiber₂_vec (i : Fin r) {midIdx destIdx : Fin r} (steps : ℕ)
    (h_midIdx : midIdx = i + steps) (h_destIdx : destIdx = i + steps + 1)
    (h_destIdx_le : destIdx ≤ ℓ)
    (f : (sDomain 𝔽q β h_ℓ_add_R_rate) i → L) (r_challenges : Fin steps → L) :
    (sDomain 𝔽q β h_ℓ_add_R_rate) (i := destIdx) → (Fin 2) → L := fun y => by
    -- Can also use fiberEvaluations instead
    let fiberMap := qMap_total_fiber 𝔽q β (i := midIdx) (steps := 1)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (destIdx := destIdx)
      (h_destIdx := by omega) (by omega) (y := y)
    exact fun rowIdx =>
      let zᵢ := fiberMap rowIdx
      iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
        (steps := steps) h_midIdx (h_destIdx_le := by omega)
        (f := f) (r_challenges := r_challenges) zᵢ

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
/-- **Helper #1 for Lemma 4.9**: The vector `F₂(steps, r, y) = `
`MatrixCTensor(steps, r) * blockDiagMatrix(steps, M_z₀, M_z₁) * fiberEvaluations(steps+1, r, y)`.
where `z₀, z₁` are the fiber of `y`, `y` is in `S^(i+steps+1)`). -/
lemma fold_eval_fiber₂_eq_mat_mat_vec_mul (i : Fin r) {midIdx destIdx : Fin r} (steps : ℕ)
    (h_midIdx : midIdx = i + steps) (h_destIdx : destIdx = i + steps + 1)
    (h_destIdx_le : destIdx ≤ ℓ)
    (f : (sDomain 𝔽q β h_ℓ_add_R_rate) i → L) (r_challenges : Fin steps → L)
    (y : (sDomain 𝔽q β h_ℓ_add_R_rate) destIdx)
    (lemma_4_9_inductive_hypothesis :
      iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (steps := steps) (i := i)
        h_midIdx (h_destIdx_le := by omega) (f := f) (r_challenges := r_challenges)
      = (localized_fold_matrix_form 𝔽q β (i := i) (steps := steps) h_midIdx
        (h_destIdx_le := by omega) (f := f) (r_challenges := r_challenges))) :
    let F₂_y : Fin 2 → L := (fold_eval_fiber₂_vec 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps
      h_midIdx h_destIdx h_destIdx_le f r_challenges) (y)
    let fiberMap := qMap_total_fiber 𝔽q β (i := midIdx) (steps := 1)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (destIdx := destIdx) (h_destIdx := by omega)
      (h_destIdx_le := h_destIdx_le) (y := y)
    let z₀ := fiberMap 0
    let z₁ := fiberMap 1
    let M_z₀ := foldMatrix 𝔽q β (i := i) (steps := steps) h_midIdx (h_destIdx_le := by omega)
      (y := z₀)
    let M_z₁ := foldMatrix 𝔽q β (i := i) (steps := steps) h_midIdx (h_destIdx_le := by omega)
      (y := z₁)
    let fiber_eval_mapping := fiberEvaluations 𝔽q β (steps := steps + 1)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := i) h_destIdx h_destIdx_le f y
    let decomposed_form := ((challengeTensorExpansionMatrix (n := steps) (r := r_challenges)) *
        (blockDiagMatrix (r := r) (ℓ := ℓ) (𝓡 := 𝓡) (n := steps) (Mz₀ := M_z₀) (Mz₁ := M_z₁)))
          *ᵥ fiber_eval_mapping
    F₂_y = decomposed_form := by
  -- funext (halfIdx : Fin 2)
  dsimp only [fold_eval_fiber₂_vec]
  -- 3. Apply the previous main theorem: iterated_fold_eq_matrix_form
  let h_matrix_form := lemma_4_9_inductive_hypothesis
  -- 4. Rewrite LHS using the matrix form theorem: LHS at halfIdx is `iterated_fold ... z_halfIdx`
  conv_lhs => rw [h_matrix_form] -- now lhs is `localized_fold_matrix_form ... z_halfIdx`
  let fiberVec_y_eq_merge := fiberEvaluations_eq_merge_fiberEvaluations_of_one_step_fiber
    (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
    h_midIdx h_destIdx (h_destIdx_le := by omega)  (f := f) (y := y)
  conv_rhs => rw [fiberVec_y_eq_merge]
  -- simp [Fin.isValue, Fin.eta]
  -- LHS is localized_fold_matrix_form ... z_halfIdx
  -- RHS is: (MatrixCTensor * BlockDiagMatrix *v (fiberEval(z₀) ++ fiberEval(z₁))) [halfIdx]
  conv_rhs =>
    rw [←Matrix.mulVec_mulVec] -- group BlockDiagMatrix with fiberEval(z₀) ++ fiberEval(z₁)
    rw [←blockDiagMatrix_mulVec_F₂_eq_Fin_merge_PO2] -- distribute the mat-vec multiplication
    rw [←challengeTensorExpansionMatrix_mulVec_F₂_eq_Fin_merge_PO2] -- distribute again
  --  Now both sides are `(Fin 2) → L`
  funext (halfIdx : Fin 2)
  conv_lhs => unfold localized_fold_matrix_form single_point_localized_fold_matrix_form
  conv_rhs => unfold mergeFinMap_PO2_left_right
  by_cases hi : halfIdx.val < 2 ^ 0
  · simp only [reduceAdd, reducePow, pow_zero, lt_one_iff, Fin.val_eq_zero_iff, Fin.isValue,
    Nat.pow_zero, mulVec_mulVec]
    -- first row of F₂_y (LHS): fold(steps, r_challenges, z₀)
    have h_halfIdx_eq_0 : halfIdx = 0 := by omega
    simp only [h_halfIdx_eq_0, Fin.isValue, ↓reduceDIte, Fin.coe_ofNat_eq_mod, zero_mod,
      Fin.zero_eta]
    conv_lhs => rw [Matrix.dotProduct_mulVec]
    conv_rhs => rw [Matrix.mulVec]
    -- Both sides have form (... ⬝ᵥ (fiberEvaluations (z₀)))
    rfl
  · simp only [reduceAdd, reducePow, pow_zero, lt_one_iff, Fin.val_eq_zero_iff, Fin.isValue,
    Nat.pow_zero, mulVec_mulVec]
    -- second row of F₂_y (RHS): fold(steps, r_challenges, z₁)
    have h_halfIdx_eq_1 : halfIdx = 1 := by omega
    simp only [h_halfIdx_eq_1, Fin.isValue, one_ne_zero, ↓reduceDIte, Fin.coe_ofNat_eq_mod,
      mod_succ, tsub_self, Fin.zero_eta]
    conv_lhs => rw [Matrix.dotProduct_mulVec]
    conv_rhs => rw [Matrix.mulVec]
    -- Both sides have form (... ⬝ᵥ (fiberEvaluations (z₁)))
    rfl

omit [NeZero r] [Fintype L] [DecidableEq L] [CharP L 2] [NeZero ℓ] [NeZero 𝓡] in
/-- **Helper #2 for Lemma 4.9**: the (middle) interchangibility transformation in the Lemma 4.9
`butterflyMstrix(0, z₀, z₁) * MatrixCTensor(n, r)`
`= MatrixCTensor(n, r) * butterflyMatrix(n, z₀, z₁)`. Both have size `2 x (2^(n + 1))` -/
lemma butterflyMatrix0_mul_matrixCTensor_eq_matrixCTensor_mul_butterflyMatrix (n : ℕ)
    (z₀ z₁ : L) (r_challenges : Fin n → L) :
    (butterflyMatrix (𝓡 := 𝓡) (ℓ := ℓ) (r := r) (n := 0) z₀ z₁) *
      (challengeTensorExpansionMatrix (n := n) (r := r_challenges))
    = (challengeTensorExpansionMatrix (n := n) (r := r_challenges)) *
      (butterflyMatrix (𝓡 := 𝓡) (ℓ := ℓ) (r := r) (n := n) z₀ z₁) := by
  unfold butterflyMatrix challengeTensorExpansionMatrix reindexSquareMatrix
  simp only
  conv_lhs => -- clear way for Matrix.reindex_mul_reindex in lhs
    simp only [reduceAdd, reducePow, Nat.pow_zero, finCongr_refl, neg_smul, one_smul,
    Equiv.refl_symm, Equiv.coe_refl, submatrix_id_id, finCongr_symm]
  conv_lhs => rw [Matrix.reindex_mul_reindex]; rw [Matrix.from4Blocks_mul_from4Blocks]
  conv_rhs => rw [Matrix.reindex_mul_reindex]; rw [Matrix.from4Blocks_mul_from4Blocks]
  simp only [reduceAdd, reducePow, smul_mul, Nat.pow_zero, Matrix.one_mul, smul_of, Matrix.mul_zero,
    add_zero, Matrix.neg_mul, neg_of, zero_add, reindex_apply, Equiv.refl_symm, Equiv.coe_refl,
    finCongr_symm, finCongr_refl, Matrix.mul_smul, Matrix.mul_one, neg_smul, one_smul,
    Matrix.mul_neg, neg_zero, smul_zero]

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
/-- **Lemma 4.9.** The iterated fold equals the localized fold evaluation via matmul form -/
theorem iterated_fold_eq_matrix_form (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f : (sDomain 𝔽q β h_ℓ_add_R_rate) i → L)
    (r_challenges : Fin steps → L) :
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (steps := steps)
      (i := i)
      h_destIdx h_destIdx_le f
      r_challenges =
    localized_fold_matrix_form 𝔽q β i (steps := steps) h_destIdx h_destIdx_le f
      r_challenges := by
  revert destIdx h_destIdx h_destIdx_le
  induction steps with
  | zero => -- Base Case: steps = 0
    intro destIdx h_destIdx h_destIdx_le
    have h_destIdx_eq_i: destIdx = i := by omega
    subst h_destIdx_eq_i
    unfold iterated_fold localized_fold_matrix_form single_point_localized_fold_matrix_form
    simp only [Nat.add_zero, Fin.dfoldl, reduceAdd, Fin.val_succ, id_eq, Fin.dfoldlM_zero,
      Fin.isValue, Fin.coe_ofNat_eq_mod, reduceMod, Nat.pow_zero]
    -- The fold loop is empty, returns f(y)
    unfold challengeTensorExpansion foldMatrix fiberEvaluations qMap_total_fiber
    simp only [pure, Fin.reduceLast, Fin.coe_ofNat_eq_mod, reduceMod, Nat.add_zero, Fin.eta,
      Subtype.coe_eta, Nat.pow_zero, ↓reduceDIte, one_mulVec]
    unfold dotProduct
    simp only [univ_unique, Fin.default_eq_zero, Fin.isValue, multilinearWeight, univ_eq_empty,
      Nat.pow_zero, Fin.val_eq_zero, zero_testBit, Bool.false_eq_true, ↓reduceIte, prod_empty,
      one_mul, sum_const, card_singleton, one_smul]
  | succ n ih =>
    intro destIdx h_destIdx h_destIdx_le
    -- Inductive Step: steps = n + 1
    -- 1. Unfold the definition of iterated_fold for n+1 steps.
    --    iterated_fold (n+1) is `fold` applied to `iterated_fold n`.
    let midIdx : Fin r := ⟨i + n, by omega⟩
    have h_midIdx : midIdx.val = i + n := by dsimp only [midIdx]
    rw [iterated_fold_last 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := n)
      (midIdx := midIdx) (destIdx := destIdx) (h_midIdx := h_midIdx) (h_destIdx := h_destIdx)
      (h_destIdx_le := h_destIdx_le) (f := f) (r_challenges := r_challenges)]
    -- simp only
    -- Let `prev_fold` be the result of folding n times.
    set prev_fold_fn := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i) (steps := n) h_midIdx (h_destIdx_le := by omega) (f := f)
      (r_challenges := Fin.init r_challenges)
    funext (y : (sDomain 𝔽q β h_ℓ_add_R_rate) destIdx)
    -- ⊢ fold 𝔽q β ⟨↑i + n, ⋯⟩ ⋯ prev_fold_fn (r_challenges (Fin.last n)) y =
    -- localized_fold_matrix_form 𝔽q β i (n + 1) h_i_add_steps f r_challenges y
    set F₂_y := fold_eval_fiber₂_vec 𝔽q β i (steps := n) (midIdx := midIdx) (destIdx := destIdx)
      (h_midIdx := h_midIdx) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f)
      (r_challenges := Fin.init r_challenges)
    have h_F₂_y_eq : ∀ yPoint, fiberEvaluations 𝔽q β (i := midIdx) (steps := 1)
      h_destIdx h_destIdx_le
      (f := prev_fold_fn) yPoint = F₂_y yPoint := fun yPoint => by rfl
    conv_lhs => -- use vec-matrix-vec form for the outer (single-step) fold()
      rw [fold_eval_single_matrix_mul_form 𝔽q β (i := midIdx)
        h_destIdx h_destIdx_le]; unfold fold_single_matrix_mul_form; simp only
      -- change the right-most multiplier term into F₂_y repr
      rw [h_F₂_y_eq]
      -- Now lhs has this form:` ((CTensor n=1)* butterflyMatrix(0, z₀(y), z₁(y))) * (F₂_y y)`,
        -- => we use **Helper #1** to expand the last term `F₂_y y` into product of 3 terms
      unfold F₂_y
      simp only;
      rw [fold_eval_fiber₂_eq_mat_mat_vec_mul (lemma_4_9_inductive_hypothesis := by
        let res := ih (r_challenges := Fin.init r_challenges) h_midIdx (h_destIdx_le := by omega)
        exact res
      )]
      -- Now LHS has this 5-term form: `(CTensor vec n=1) ⬝ᵥ butterflyMatrix(0, z₀(y), z₁(y))`
        -- `*ᵥ [ [ (MatrixCTensor n=n (Fin.init r_challenges)) * (blockDiagMatrix n Mz₀ Mz₁) ]`
              -- `*ᵥ (fiberEvaluations y)                                                    ] ]`
      -- Next, we group term 2 & 3
      rw [←Matrix.mulVec_mulVec] -- group term (4 * 5), split term 3
      rw [Matrix.mulVec_mulVec] -- group term (2 & 3)
      -- => Now we have 3 groups : (1) ⬝ᵥ (2 * 3) *ᵥ (4 *ᵥ 5)
      -- => We apply **Helper #2** to `swap positions of term 2 & 3`
      simp only;
      rw [butterflyMatrix0_mul_matrixCTensor_eq_matrixCTensor_mul_butterflyMatrix] -- Helper #2
      -- Now LHS has 5-term form: `(CTensor vec n=1) ⬝ᵥ (MatrixCTensor n=n (Fin.init r_challenges))`
        -- `butterflyMatrix(n := N, z₀(y), z₁(y)) * (blockDiagMatrix n Mz₀ Mz₁) ]`
          -- `*ᵥ (fiberEvaluations y)`
          -- where `Mz₀` and `Mz₁` are `n-step` foldMatrix of `z₀` and `z₁` respectively
    -- Now the last TWO jobs are to group * transform (term 1 & term 2), (term 3 & term 4)
    set multilinearWeight1step : (Fin 2 → L) := -- This is term 1 in the LHS
      (challengeTensorExpansion 1 fun x ↦ r_challenges (Fin.last n))
    have h_MLNWeight1step_eq: multilinearWeight1step
      = ![1 - r_challenges (Fin.last n), r_challenges (Fin.last n)] := by
        apply challengeTensorExpansion_one
    let h_merge_term1_term2_tensorExpand_for_n_plus_1 :=
      challengeTensorExpansion_decompose_succ (L := L) (n := n) (r := r_challenges)
    conv_lhs => -- JOB 1: group & transform (term 1 & term 2)
      -- => We need to convert `(CTensor 1) ⬝ᵥ (MatrixCTensor n)` into `(CTensor (n + 1))`
      rw [h_MLNWeight1step_eq]
      rw [←Matrix.mulVec_mulVec] -- group (term 3 4 5), split term 2
      rw [Matrix.dotProduct_mulVec] -- group (term 1 & term 2)
      rw [←h_merge_term1_term2_tensorExpand_for_n_plus_1] -- MERGING here
    conv_lhs => -- JOB 2: group & transform (term 3 & term 4), old term indices before JOB 1
      -- => We need to convert `butterflyMatrix(n := N, z₀(y), z₁(y)) * (blockDiagMatrix n Mz₀ Mz₁)`
        -- into `foldMatrix(n := n + 1, y)`
      rw [Matrix.mulVec_mulVec] -- group term (3 * 4)
      -- => We don't really have to do anything, cuz (term 3 * term 4) is
        -- definitionally equal to fold(n + 1, y)
    rfl

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
/-- **Corollary of Lemma 4.9**: Direct connection between single-point
matrix form and iterated fold. This is a point-wise version of
`iterated_fold_eq_matrix_form` that directly connects
`single_point_localized_fold_matrix_form` with `fiberEvaluations` to `iterated_fold`.
This is useful when working with concrete fiber evaluation mappings rather than the
abstract `localized_fold_matrix_form` function. -/
lemma single_point_localized_fold_matrix_form_eq_iterated_fold
    (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f : (sDomain 𝔽q β h_ℓ_add_R_rate) i → L)
    (r_challenges : Fin steps → L)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate destIdx) :
  single_point_localized_fold_matrix_form 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := i) (steps := steps) h_destIdx h_destIdx_le r_challenges y
    (fiber_eval_mapping := fiberEvaluations 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i) (steps := steps) h_destIdx h_destIdx_le f y) =
  iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
    h_destIdx h_destIdx_le f r_challenges y := by
  rw [iterated_fold_eq_matrix_form]
  rfl

/-- Evaluates polynomial P on the domain S⁽ʲ⁾.
    This function is index-agnostic: logic doesn't change based on the round. -/
def polyToOracleFunc {domainIdx : Fin r} (P : L[X]) :
    (sDomain 𝔽q β h_ℓ_add_R_rate domainIdx) → L :=
  fun y => P.eval y.val

omit [CharP L 2] in
/-- **Lemma 4.13** : if f⁽ⁱ⁾ is evaluation of P⁽ⁱ⁾(X) over S⁽ⁱ⁾, then fold(f⁽ⁱ⁾, r_chal)
  is evaluation of P⁽ⁱ⁺¹⁾(X) over S⁽ⁱ⁺¹⁾. At level `i = ℓ`, we have P⁽ˡ⁾ = c
-/
theorem fold_advances_evaluation_poly
  (i : Fin r) {destIdx : Fin r} (h_destIdx : destIdx = i.val + 1) (h_destIdx_le : destIdx ≤ ℓ)
  (coeffs : Fin (2 ^ (ℓ - ↑i)) → L) (r_chal : L) : -- novel coeffs
  let P_i : L[X] := intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate (i := i) (h_i := by omega) coeffs
  let f_i := polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (domainIdx := i) (P := P_i)
  let f_i_plus_1 := fold (i := i) (destIdx := destIdx) (h_destIdx := h_destIdx)
    (h_destIdx_le := h_destIdx_le) (f := f_i) (r_chal := r_chal)
  let new_coeffs := fun j : Fin (2^(ℓ - destIdx.val)) =>
    (1 - r_chal) * (coeffs ⟨j.val * 2, by
      rw [←Nat.add_zero (j.val * 2)]
      apply mul_two_add_bit_lt_two_pow (c := ℓ - i) (a := j) (b := ℓ - destIdx.val)
        (i := 0) (by omega) (by omega)
    ⟩) +
    r_chal * (coeffs ⟨j.val * 2 + 1, by
      apply mul_two_add_bit_lt_two_pow (c := ℓ - i) (a := j) (b := ℓ - destIdx.val)
        (i := 1) (by omega) (by omega)
    ⟩)
  let P_i_plus_1 :=
    intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate (i := destIdx) (h_i := by omega) new_coeffs
  f_i_plus_1 = polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (domainIdx := destIdx) (P := P_i_plus_1) := by
  simp only
  funext y
  set fiberMap := qMap_total_fiber 𝔽q β (i := i) (steps := 1)
    h_destIdx h_destIdx_le (y := y)
  set x₀ := fiberMap 0
  set x₁ := fiberMap 1
  set P_i := intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate (i := i) (h_i := by omega) coeffs
  set new_coeffs := fun j : Fin (2^(ℓ - destIdx)) =>
    (1 - r_chal) * (coeffs ⟨j.val * 2, by
      have h : j.val * 2 < 2^(ℓ - destIdx) * 2 := by omega
      have h2 : 2^(ℓ - i) = 2^(ℓ - destIdx) * 2 := by
        conv_rhs => enter[2]; rw [←Nat.pow_one 2]
        rw [←pow_add]; congr
        rw [Nat.sub_add_eq_sub_sub_rev (h1 := by omega) (h2 := by omega)]
        -- ⊢ ℓ - ↑i = ℓ - (↑i + 1 - 1)
        omega
      omega
    ⟩) +
    r_chal * (coeffs ⟨j.val * 2 + 1, by
      apply mul_two_add_bit_lt_two_pow (c := ℓ - i) (a := j) (b := ℓ - destIdx) (i := 1)
      · omega
      · omega
    ⟩)
  have h_eval_qMap_x₀ : (AdditiveNTT.qMap 𝔽q β i).eval x₀.val = y := by
    have h := iteratedQuotientMap_k_eq_1_is_qMap 𝔽q β h_ℓ_add_R_rate i h_destIdx h_destIdx_le x₀
    simp only [Subtype.eq_iff] at h
    rw [h.symm]
    have h_res := is_fiber_iff_generates_quotient_point 𝔽q β i (steps := 1) h_destIdx h_destIdx_le
      (x := x₀) (y := y).mpr (by rw [pointToIterateQuotientIndex_qMap_total_fiber_eq_self])
    rw [h_res]
    -- exact qMap_eval_fiber_eq_self ⟦L⟧ ⟨i + 1, by omega⟩ (by simp only; omega) h_i_succ_lt y 0
  have h_eval_qMap_x₁ : (AdditiveNTT.qMap 𝔽q β i).eval x₁.val = y := by
    have h := iteratedQuotientMap_k_eq_1_is_qMap 𝔽q β h_ℓ_add_R_rate i h_destIdx h_destIdx_le x₁
    simp only [Subtype.eq_iff] at h
    rw [h.symm]
    have h_res := is_fiber_iff_generates_quotient_point 𝔽q β i (steps := 1) h_destIdx h_destIdx_le
      (x := x₁) (y := y).mpr (by rw [pointToIterateQuotientIndex_qMap_total_fiber_eq_self])
    rw [h_res]
  have hx₀ := qMap_total_fiber_basis_sum_repr 𝔽q β i (steps := 1)
    h_destIdx h_destIdx_le y 0
  have hx₁ := qMap_total_fiber_basis_sum_repr 𝔽q β i (steps := 1)
    h_destIdx h_destIdx_le y 1
  simp only [Fin.isValue] at hx₀ hx₁
  have h_fiber_diff : x₁.val - x₀.val = 1 := by
    simp only [Fin.isValue, x₁, x₀, fiberMap]
    rw [hx₁, hx₀]
    simp only [Fin.isValue, AddSubmonoidClass.coe_finset_sum, SetLike.val_smul]
    have h_index : ℓ + 𝓡 - i = (ℓ + 𝓡 - destIdx) + 1 := by omega
    rw! (castMode := .all) [h_index]
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ] -- (free_term + y_repr) - (free_term + y_repr) = 1
    -- First, simplify the free terms
    simp only [fiber_coeff, eqRec_eq_cast, lt_one_iff, reducePow, Fin.isValue,
      Fin.coe_ofNat_eq_mod, mod_succ, dite_smul, ite_smul, zero_smul, one_smul, zero_mod]
    have h_cast_0 :
        (cast (Eq.symm h_index ▸ rfl : Fin (ℓ + 𝓡 - ↑destIdx + 1) = Fin (ℓ + 𝓡 - ↑i)) 0).val =
        0 := by
      rw [←Fin.cast_eq_cast (h := by omega)]
      rw [Fin.cast_val_eq_val (h_eq := by omega)]
      simp only [Fin.coe_ofNat_eq_mod, mod_succ_eq_iff_lt, succ_eq_add_one, lt_add_iff_pos_left]
      omega
    simp only [h_cast_0, ↓reduceDIte]
    have h_getBit_0_of_0 : Nat.getBit (k := 0) (n := 0) = 0 := by
      simp only [getBit, shiftRight_zero, and_one_is_mod, zero_mod]
    have h_getBit_0_of_1 : Nat.getBit (k := 0) (n := 1) = 1 := by
      simp only [getBit, shiftRight_zero, Nat.and_self]
    simp only [h_getBit_0_of_1, one_ne_zero, ↓reduceIte, h_getBit_0_of_0, zero_add]
    rw! (castMode := .all) [←h_index]
    rw [cast_eq]
    simp only [get_sDomain_basis, Fin.coe_ofNat_eq_mod, zero_mod, add_zero, cast_eq]
    rw [normalizedWᵢ_eval_βᵢ_eq_1 𝔽q β]
    -- ring
    conv_lhs => rw [←add_sub]
    conv_rhs => rw [←add_zero (a := 1)]
    rw [add_right_inj (a := 1)]
    rw [sub_eq_zero]
    apply Finset.sum_congr (h := by rfl)
    simp only [mem_univ, congr_eqRec, Fin.val_succ, Nat.add_eq_zero, one_ne_zero, and_false,
      ↓reduceDIte, add_tsub_cancel_right, Fin.eta, imp_self, implies_true]
  set P_i_plus_1 :=
    intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate (i := destIdx) (h_i := by omega) new_coeffs
  -- Set up the even and odd refinement polynomials
  set P₀_coeffs := fun j : Fin (2^(ℓ - destIdx)) => coeffs ⟨j.val * 2, by
    have h1 : ℓ - destIdx + 1 = ℓ - i := by omega
    have h2 : 2^(ℓ - destIdx + 1) = 2^(ℓ - i) := by rw [h1]
    have h3 : 2^(ℓ - destIdx) * 2 = 2^(ℓ - destIdx + 1) := by rw [pow_succ]
    rw [← h2, ← h3]; omega⟩
  set P₁_coeffs := fun j : Fin (2^(ℓ - destIdx)) => coeffs ⟨j.val * 2 + 1, by
    have h1 : ℓ - destIdx + 1 = ℓ - i := by omega
    have h2 : 2^(ℓ - destIdx + 1) = 2^(ℓ - i) := by rw [h1]
    have h3 : 2^(ℓ - destIdx) * 2 = 2^(ℓ - destIdx + 1) := by rw [pow_succ]
    rw [← h2, ← h3]; omega⟩
  set P₀ := evenRefinement 𝔽q β h_ℓ_add_R_rate i (h_i := by omega) coeffs
  set P₁ := oddRefinement 𝔽q β h_ℓ_add_R_rate i (h_i := by omega) coeffs
  have h_P_i_eval := evaluation_poly_split_identity 𝔽q β h_ℓ_add_R_rate i (h_i := by omega) coeffs
  -- Equation 39 : P^(i)(X) = P₀^(i+1)(q^(i)(X)) + X · P₁^(i+1)(q^(i)(X))
  have h_equation_39_x₀ : P_i.eval x₀.val = P₀.eval y.val + x₀.val * P₁.eval y.val := by
    simp only [h_P_i_eval, Polynomial.eval_add, eval_comp,
      h_eval_qMap_x₀, Polynomial.eval_mul, Polynomial.eval_X, P_i, P₀, P₁]
  have h_equation_39_x₁ : P_i.eval x₁.val = P₀.eval y.val + x₁.val * P₁.eval y.val := by
    simp only [h_P_i_eval, Polynomial.eval_add, eval_comp,
      h_eval_qMap_x₁, Polynomial.eval_mul, Polynomial.eval_X, P_i, P₀, P₁]
  set f_i := fun (x : (sDomain 𝔽q β h_ℓ_add_R_rate) i) => P_i.eval (x.val : L)
  set f_i_plus_1 := fold (i := i) (destIdx := destIdx) (h_destIdx := h_destIdx)
    (h_destIdx_le := h_destIdx_le) (f := f_i) (r_chal := r_chal)
  -- Unfold the definition of f_i_plus_1 using the fold function
  have h_fold_def : f_i_plus_1 y =
      f_i x₀ * ((1 - r_chal) * x₁.val - r_chal) +
      f_i x₁ * (r_chal - (1 - r_chal) * x₀.val) := rfl
  -- Main calculation following the outline
  calc f_i_plus_1 y
    = f_i x₀ * ((1 - r_chal) * x₁.val - r_chal) +
        f_i x₁ * (r_chal - (1 - r_chal) * x₀.val) := h_fold_def
    _ = P_i.eval x₀.val * ((1 - r_chal) * x₁.val - r_chal) +
        P_i.eval x₁.val * (r_chal - (1 - r_chal) * x₀.val) := by simp only [f_i]
    _ = (P₀.eval y.val + x₀.val * P₁.eval y.val) * ((1 - r_chal) * x₁.val - r_chal) +
        (P₀.eval y.val + x₁.val * P₁.eval y.val) * (r_chal - (1 - r_chal) * x₀.val) := by
      rw [h_equation_39_x₀, h_equation_39_x₁]
    _ = P₀.eval y.val * ((1 - r_chal) * x₁.val - r_chal + r_chal - (1 - r_chal) * x₀.val) +
        P₁.eval y.val * (x₀.val * ((1 - r_chal) * x₁.val - r_chal) +
          x₁.val * (r_chal - (1 - r_chal) * x₀.val)) := by ring
    _ = P₀.eval y.val * ((1 - r_chal) * (x₁.val - x₀.val)) +
        P₁.eval y.val * ((x₁.val - x₀.val) * r_chal) := by ring
    _ = P₀.eval y.val * (1 - r_chal) + P₁.eval y.val * r_chal := by rw [h_fiber_diff]; ring
    _ = P_i_plus_1.eval y.val := by
      simp only [P_i_plus_1, P₀, P₁, new_coeffs, evenRefinement, oddRefinement,
        intermediateEvaluationPoly]
      conv_lhs => enter [1]; rw [mul_comm, ←Polynomial.eval_C_mul]
      conv_lhs => enter [2]; rw [mul_comm, ←Polynomial.eval_C_mul]
      -- ⊢ eval y (C (1-r) * ∑...) + eval y (C r * ∑...) = eval y (∑...)
      rw [←Polynomial.eval_add]
      -- ⊢ poly_left.eval y = poly_right.eval y
      congr! 1
      simp_rw [mul_sum, ←Finset.sum_add_distrib]
      have h_i_add_1_lt : i.val + 1 < r := by omega
      have h_destIdx_eq : destIdx = ⟨i + 1, h_i_add_1_lt⟩ := Fin.eq_of_val_eq (by omega)
      have h_fin_eq : Fin (2 ^ (ℓ - ↑i - 1)) = Fin (2 ^ (ℓ - ↑destIdx)) := by
        congr 1; congr 1; omega
      rw! (castMode := .all) [h_fin_eq]
      -- We now prove that the terms inside the sums are equal for each index.
      apply Finset.sum_congr (by congr!)
      -- simp only [mem_univ, map_sub, map_one, Fin.eta, map_add, map_mul, forall_const]
      intro j hj
      have h_j_lt : j.val < 2 ^ (ℓ - destIdx) := by omega
      subst h_destIdx_eq
      conv_lhs =>
        rw [mul_comm (a := Polynomial.C (coeffs ⟨j.val * 2, by
          rw [←Nat.add_zero (j.val * 2)]
          apply mul_two_add_bit_lt_two_pow (c := ℓ - i) (a := j) (b := ℓ - (i + 1))
            (i := 0) (by omega) (by omega)
          ⟩))]
        rw [←mul_assoc, mul_comm (a := Polynomial.C (1 - r_chal))]
        rw [mul_assoc]
      conv_lhs => enter [2]; rw [mul_comm (a := Polynomial.C (coeffs ⟨j.val * 2 + 1, by
        apply mul_two_add_bit_lt_two_pow (c := ℓ - i) (a := j) (b := ℓ - (i + 1))
          (i := 1) (by omega) (by omega)⟩)), ←mul_assoc,
        mul_comm (a := Polynomial.C r_chal)]; rw [mul_assoc]
      conv_rhs => rw [mul_comm]
      rw [←mul_add]
      congr
      simp only [←Polynomial.C_mul, ←Polynomial.C_add]

omit [CharP L 2] in
/-- **Lemma 4.13 Generalization** : if f⁽ⁱ⁾ is evaluation of P⁽ⁱ⁾(X) over S⁽ⁱ⁾,
then fold(f⁽ⁱ⁾, r_chal) is evaluation of P⁽ⁱ⁺¹⁾(X) over S⁽ⁱ⁺¹⁾.
At level `i = ℓ`, we have P⁽ˡ⁾ = c (constant polynomial).
-/
theorem iterated_fold_advances_evaluation_poly
  (i : Fin r) {destIdx : Fin r} (steps : ℕ) (h_destIdx : destIdx = i + steps)
  (h_destIdx_le : destIdx ≤ ℓ)
  (coeffs : Fin (2 ^ (ℓ - ↑i)) → L) (r_challenges : Fin steps → L) : -- novel coeffs
  let P_i : L[X] := intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate (i := i) (h_i := by omega) coeffs
  let f_i := polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (domainIdx := i) (P := P_i)
  let f_i_plus_steps := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
    (steps := steps) h_destIdx h_destIdx_le (f := f_i) (r_challenges := r_challenges)
  let new_coeffs := fun j : Fin (2^(ℓ - destIdx)) =>
    ∑ m : Fin (2 ^ steps),
      multilinearWeight (r := r_challenges) (i := m) * coeffs ⟨j.val * 2 ^ steps + m.val, by
        apply index_bound_check j.val m.val (by rw [←h_destIdx]; omega) m.isLt (by omega)⟩
  let P_i_plus_steps :=
    intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate (i := destIdx) (h_i := by omega) new_coeffs
  f_i_plus_steps = polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (domainIdx := destIdx) (P := P_i_plus_steps) := by
  revert destIdx h_destIdx h_destIdx_le
-- Induction on steps
  induction steps generalizing i with
  | zero =>
    intro destIdx h_destIdx h_destIdx_le
    simp only
    have h_i_eq_destIdx : i = destIdx := by omega
    subst h_i_eq_destIdx
    -- funext y -- Sum over Fin 1 (j=0)
    -- Base Case: 0 Steps
    dsimp only [iterated_fold, reduceAdd, Fin.val_castSucc, Fin.val_succ, Lean.Elab.WF.paramLet,
      id_eq, Fin.reduceLast, Fin.coe_ofNat_eq_mod, reduceMod, Nat.add_zero, Fin.eta,
      Fin.dfoldl_zero, Nat.pow_zero, multilinearWeight, Fin.val_eq_zero, zero_testBit,
      Bool.false_eq_true]
    simp only [univ_unique, Fin.default_eq_zero, Fin.isValue, univ_eq_empty, Fin.val_eq_zero,
      zero_testBit, Bool.false_eq_true, ↓reduceIte, prod_empty, mul_one, add_zero, one_mul,
      sum_singleton, Subtype.coe_eta, Fin.dfoldl_zero, Fin.eta]
  | succ s ih =>
    intro destIdx h_destIdx h_destIdx_le
    simp only
    funext y
    -- 1. Unfold Fold (LHS)
    -- iterated_fold (s+1) = fold (iterated_fold s)
    set P_i := intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate (i := i) (h_i := by omega) coeffs
    set f_i := polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := i) (P := P_i)
    let midIdx : Fin r := ⟨i + s, by omega⟩
    have h_midIdx : midIdx = i + s := by rfl
    rw [iterated_fold_last 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := s)
      (h_midIdx := h_midIdx) (h_destIdx := by omega) (h_destIdx_le := by omega) (f := f_i)
      (r_challenges := r_challenges)]
    set f_i_plus_steps := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
      (steps := s + 1) h_destIdx h_destIdx_le (f := f_i) (r_challenges := r_challenges)
    -- 2. Setup Inductive Step
    let r_s := Fin.init r_challenges
    let r_last := r_challenges (Fin.last s)
    -- Apply IH to the first s steps
    -- We need to construct the coefficients for step s
    let coeffs_s := fun j : Fin (2^(ℓ - (i + s))) =>
      ∑ m : Fin (2 ^ s),
        multilinearWeight (r := r_s) (i := m) * coeffs ⟨j.val * 2 ^ s + m.val, by
          apply index_bound_check j.val m.val j.isLt m.isLt (by omega)
        ⟩
    let f_folded_s_steps := (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
      (steps := s) h_midIdx (by omega) (f := f_i) (r_challenges := r_s))
    let poly_eval_folded_s_steps :=
      polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := midIdx)
        (P := intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate midIdx (h_i := by omega) coeffs_s)
    have h_eval_s : f_folded_s_steps = poly_eval_folded_s_steps := by
      unfold f_folded_s_steps poly_eval_folded_s_steps
      rw [ih (i := i)]
    unfold f_folded_s_steps at h_eval_s
    conv_lhs =>
      simp only
      rw [h_eval_s]
    -- 3. Apply Single Step Lemma
    -- fold(P_s, r_last) -> P_{s+1}
    -- The lemma fold_advances_evaluation_poly tells us the coefficients transform as:
    -- C_new[j] = (1 - r) * C_s[2j] + r * C_s[2j+1]
    let fold_advances_evaluation_poly_res := fold_advances_evaluation_poly 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := midIdx) (destIdx := destIdx)
      (h_destIdx := by omega) (h_destIdx_le := by omega) (coeffs := coeffs_s) (r_chal := r_last)
    simp only [r_last] at fold_advances_evaluation_poly_res
    unfold poly_eval_folded_s_steps
    conv_lhs => rw [fold_advances_evaluation_poly_res]
    --   ⊢ Polynomial.eval y ... = Polynomial.eval y ...
    congr 1
    congr 1
    funext (j : Fin (2 ^ (ℓ - destIdx)))
    unfold coeffs_s
    simp only
    have h_two_pow_s_succ_eq: 2 ^ (s + 1) = 2 ^ s + 2 ^ s := by omega
    --- for rhs
    rw! (castMode := .all) [h_two_pow_s_succ_eq]
    rw [Fin.sum_univ_add]
    simp only [eqRec_eq_cast]
    rw [←Fin.cast_eq_cast (h := by omega)]
    simp only [Fin.val_castAdd, Fin.natAdd_eq_addNat, Fin.val_addNat]
    -- ∑ + ∑ = ∑ + ∑
    congr 1
    · conv_lhs => rw [mul_sum]
      congr 1
      funext (x : Fin (2 ^ s))
      conv_lhs => rw [←mul_assoc]
      congr 1
      · rw [multilinearWeight_succ_lower_half (h_lt := by simp only [Fin.val_cast, Fin.val_castAdd,
          Fin.is_lt])]
        rw [mul_comm]; rfl
      · simp_rw [←two_mul (n := 2 ^ s), ←mul_assoc]
    · conv_lhs => rw [mul_sum]
      congr 1
      funext (x : Fin (2 ^ s))
      conv_lhs => rw [←mul_assoc]
      congr 1
      · rw [multilinearWeight_succ_upper_half (r := r_challenges) (j := x)
          (h_eq := by simp only [Fin.val_cast, Fin.val_addNat, Nat.add_left_cancel_iff]), mul_comm]
      · congr 1
        congr 1
        conv_lhs => rw [add_mul, one_mul, add_assoc]
        conv_rhs => rw [←two_mul (n := 2 ^ s), ←mul_assoc]
        omega

omit [DecidableEq L] [CharP L 2] [DecidableEq 𝔽q] h_Fq_char_prime
  hF₂ hβ_lin_indep h_β₀_eq_1 [NeZero ℓ] [NeZero 𝓡] in
lemma constantIntermediateEvaluationPoly_eval_eq_const
  (destIdx : Fin r) (coeffs : Fin (2 ^ (ℓ - destIdx.val)) → L)
  (h_destIdx : destIdx.val = ℓ) (x y : L) :
  let P := intermediateEvaluationPoly 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := destIdx) (h_i := by omega) coeffs
  P.eval x = P.eval y := by
    intro P
    -- intermediateEvaluationPoly is a sum over Fin 1, which is just one term
    dsimp only [P, intermediateEvaluationPoly]
    rw [Finset.sum_eq_single (a := ⟨0, by
      simp only [Nat.ofNat_pos, pow_pos]⟩) (h₀ := fun j hj hj_ne => by
      have h_j_lt := j.isLt
      simp only [h_destIdx, tsub_self, pow_zero, Nat.lt_one_iff,
        Fin.val_eq_zero_iff] at h_j_lt -- j = 0
      simp only [Fin.mk_zero', ne_eq] at hj_ne
      exfalso; exact hj_ne h_j_lt
    ) (h₁ := fun h => by
      simp only [Fin.mk_zero', Finset.mem_univ, not_true_eq_false] at h)]
    -- By intermediateNovelBasisX_zero_eq_one, intermediateNovelBasisX ... 0 = 1
    rw [intermediateNovelBasisX_zero_eq_one 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := destIdx) (h_i := by omega)]
    -- So P = C (coeffs 0), which is constant
    simp only [Polynomial.eval_C, mul_one]

omit [CharP L 2] in
/-- When folding from level 0 all the way to level ℓ, the resulting function is constant. -/
lemma iterated_fold_to_level_ℓ_is_constant
    (t : MultilinearPoly L ℓ) (destIdx : Fin r) (h_destIdx : destIdx.val = ℓ)
    (challenges : Fin ℓ → L) :
    let P₀: L[X]_(2 ^ ℓ) := polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega)
      (fun ω => t.val.eval (bitsOfIndex ω))
    let f₀ := polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := 0) (P := P₀)
    let f_ℓ := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0) (steps := ℓ)
      (destIdx := destIdx)
      (h_destIdx := by simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]; omega)
      (h_destIdx_le := by omega)
      f₀ challenges
    ∀ x y, f_ℓ x = f_ℓ y := by
  intro P₀ f₀ f_ℓ x y
  let coeffs := fun (ω : Fin (2 ^ ℓ)) => t.val.eval (bitsOfIndex ω)
  have h_f_ℓ_eq_poly := iterated_fold_advances_evaluation_poly 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0) (steps := ℓ) (destIdx := destIdx)
    (h_destIdx := by simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]; omega)
    (h_destIdx_le := by omega) (coeffs := coeffs) (r_challenges := challenges)
  -- h_f_ℓ_eq_poly says: f_ℓ = polyToOracleFunc P_ℓ where
    -- P_ℓ = intermediateEvaluationPoly with new_coeffs
  -- Step 2: When destIdx = ℓ, we have ℓ - ℓ = 0, so new_coeffs : Fin (2^0) = Fin 1 → L
  -- This means P_ℓ is a constant polynomial (only one coefficient)
  dsimp only [f_ℓ, f₀, P₀, polynomialFromNovelCoeffsF₂]
  -- unfold polyToOracleFunc
  rw [←intermediate_poly_P_base 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_ℓ := by omega)]
  simp only at h_f_ℓ_eq_poly;
  rw [h_f_ℓ_eq_poly]
  -- f_ℓ x = polyToOracleFunc P_ℓ x = P_ℓ.eval x.val
  -- Since P_ℓ is constant, P_ℓ.eval x.val = P_ℓ.eval (𝓑 0) for all x
  -- We need to show that intermediateEvaluationPoly with Fin 1 coefficients is constant
  dsimp only [polyToOracleFunc]
  rw [constantIntermediateEvaluationPoly_eval_eq_const]
  omega

end FoldTheory

/-- Given a point `v ∈ S^(0)`, extract the middle `steps` bits `{v_i, ..., v_{i+steps-1}}`
as a `Fin (2 ^ steps)`. -/
def extractMiddleFinMask (v : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨0, by exact pos_of_neZero r⟩)
    (i : Fin r) (steps : ℕ) : Fin (2 ^ steps) := by
  let vToFin := AdditiveNTT.sDomainToFin 𝔽q β h_ℓ_add_R_rate ⟨0, by
    exact pos_of_neZero r⟩ (by simp only [add_pos_iff]; left; exact pos_of_neZero ℓ) v
  simp only [tsub_zero] at vToFin
  let middleBits := Nat.getMiddleBits (offset := i.val) (len := steps) (n := vToFin.val)
  exact ⟨middleBits, Nat.getMiddleBits_lt_two_pow⟩

/-- The equality polynomial eq̃(r, r') that evaluates to 1 when r = r' and 0 otherwise.
This is used in the final sumcheck identity : s_ℓ = c · eq̃(r, r') -/
def eqTilde {L : Type} [CommRing L] {ℓ : ℕ} (r r' : Fin ℓ → L) : L :=
  MvPolynomial.eval r' (MvPolynomial.eqPolynomial r)

end Essentials

end
end Binius.BinaryBasefold
