/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen
-/

import ArkLib.Data.MlPoly.Basic
import ArkLib.Data.MvPolynomial.Notation

/-!
  # Equivalence between `MlPoly` and multilinear polynomials in `MvPolynomial`

  This file establishes the mathematical foundations for `MlPoly` by proving:
  1. Basis properties for the coefficient representation
  2. Change-of-basis matrices between different representations
  3. Equivalences with mathlib's `MvPolynomial.restrictDegree`: `equivMvPolynomialDeg1`
  4. Arithmetic operation compatibilities
-/

open MvPolynomial

variable {R : Type*} [CommRing R] {n : ℕ}

noncomputable section

namespace MlPoly

/-! ### Equivalence with Mathlib MvPolynomial
- Note: maybe we have to add more restrictions on `MlPoly R n` and `MlPolyEval R n`
  so we can differentiate them?
-/

/--
Converts a natural number to a monomial with 0/1 exponents.
Uses little‑endian bit encoding: bit 0 is the least significant bit.
The exponent at variable j is `Nat.getBit j i ∈ {0,1}`.
-/
noncomputable def monomialOfNat (i : ℕ) : (Fin n) →₀ ℕ :=
  Finsupp.onFinset (s:=Finset.univ (α:=Fin n)) (fun j => Nat.getBit j.val i) (by
    simp only [ne_eq, Finset.mem_univ, implies_true]) -- the support set is exactly Finset.univ

theorem eq_monomialOfNat_iff_eq_bitRepr (m : Fin n →₀ ℕ)
  (h_binary : ∀ j: Fin n, m j ≤ 1) (i: Fin (2^n)) :
  monomialOfNat i = m ↔ i = Nat.binaryFinMapToNat m h_binary := by
  constructor
  · intro h_mono_eq
    rw [Finsupp.ext_iff] at h_mono_eq
    apply Fin.eq_of_val_eq
    apply Nat.eq_iff_eq_all_getBits.mpr
    intro k
    -- ⊢ (if k < n then k.getBit ↑i else 0) = k.getBit ↑(Nat.binaryFinMapToNat (⇑m) h_binary)
    rw [Nat.getBit_of_lt_two_pow (a:=i) (k:=k)]
    rw [Nat.getBit_of_lt_two_pow (a:=Nat.binaryFinMapToNat m h_binary) (k:=k)]
    if h_k: k < n then
      simp only [h_k, ↓reduceIte]
      have h_getBit_binaryFinMap := Nat.getBit_of_binaryFinMapToNat (n:=n)
        (m:=m) (h_binary:=h_binary) (k:=k)
      rw [h_getBit_binaryFinMap]
      have h_monomialOfNat_at_k := h_mono_eq ⟨k, by omega⟩
      simp only [h_k, ↓reduceDIte]
      rw [h_monomialOfNat_at_k.symm] -- ⊢ k.getBit ↑i = (monomialOfNat ↑i) ⟨k, h_k⟩
      rfl -- due to definition of `monomialOfNat`
    else
      simp only [h_k, ↓reduceIte]
  · intro h_i_eq_i_of_m
    -- ⊢ monomialOfNat ↑i = m
    rw [Finsupp.ext_iff]
    intro a
    have h_k_getBit_eq_mono: ∀ k: Fin n, (monomialOfNat (n:=n) i) k = Nat.getBit k i := by
      intro k
      rfl
    -- ⊢ (monomialOfNat ↑i) a = m a
    have h_lhs := h_k_getBit_eq_mono (k:=a); rw [h_lhs] -- convert lhs to bit access
    -- ⊢ (↑a).getBit ↑i = m a
    rw [h_i_eq_i_of_m] -- convert lhs to access bit of `binaryFinMapToNat`
    simp only [Nat.getBit_of_binaryFinMapToNat (⇑m) h_binary a, Fin.is_lt, ↓reduceDIte, Fin.eta]

/--
Converts an `MlPoly` to a mathlib multivariate polynomial.
Sums over all indices `i : Fin (2^n)` with monomial exponents from `monomialOfNat i`
and coefficients `p[i]`.
-/
def toMvPolynomial (p : MlPoly R n) : R[X Fin n] :=
  ∑ i : Fin (2 ^ n), MvPolynomial.monomial (monomialOfNat i) (a:=p[i])

-- #check (toMvPolynomial (MlPoly.mk 2 #v[(1: ℤ), 2, 3, 4]))

theorem toMvPolynomial_is_multilinear (p : MlPoly R n) :
  (toMvPolynomial p) ∈ R⦃≤ 1⦄[X Fin n] := by
  rw [toMvPolynomial]
    -- ⊢ (∑ i, C p[i] * ∏ j, if { toFin := i }.getLsb j = true then X j else 1) ∈ R⦃≤ 1⦄[X Fin n]
  simp only [MvPolynomial.mem_restrictDegree]
  intro s hs k -- s is a point X where the sum evaluates to non-zero
  rw [MvPolynomial.mem_support_iff] at hs
  rw [MvPolynomial.coeff_sum] at hs
  by_contra h_s_k_gt_1
  push_neg at h_s_k_gt_1 -- h_s_k_gt_1 : 1 < s k
  have h_invalid: ∀ x: Fin (2^n),
    (coeff s (MvPolynomial.monomial (R:=R) (monomialOfNat x) (a:=p[x]))) = 0 := by
    intro x
    rw [MvPolynomial.coeff_monomial]
    -- ⊢ (if monomialOfNat ↑x = s then p[x] else 0) = 0
    have h_monomialOfNat_x_ne_s: monomialOfNat x ≠ s := by
      by_contra h_s_eq_mx
      subst h_s_eq_mx
      simp_rw [monomialOfNat] at h_s_k_gt_1
      simp only [Finsupp.onFinset_apply] at h_s_k_gt_1
      have h_getBit_lt_2: Nat.getBit k x.val < 2 := by exact Nat.getBit_lt_2
      have h_ne_1_lt_getBit: ¬(1 < Nat.getBit k x.val) := by omega
      exact h_ne_1_lt_getBit h_s_k_gt_1
    simp only [h_monomialOfNat_x_ne_s, ↓reduceIte]
  have h_sum_zero: ∑ x: Fin (2^n), (coeff s (MvPolynomial.monomial
    (R:=R) (monomialOfNat x) (a:=p[x]))) = 0 := by
    simp_rw [h_invalid]
    exact Fintype.sum_eq_zero (fun a ↦ 0) (congrFun rfl)
  exact hs h_sum_zero

theorem coeff_of_toMvPolynomial_eq_coeff_of_MlPoly (p : MlPoly R n) (m : Fin n →₀ ℕ):
  coeff m (toMvPolynomial p) =
    if h_binary: (∀ j: Fin n, m j ≤ 1) then
      let i_of_m: ℕ := Nat.binaryFinMapToNat (m:=m) (h_binary:=h_binary)
      p[i_of_m]
    else
      0
  := by
  if h_binary: (∀ j: Fin n, m j ≤ 1) then
    unfold toMvPolynomial
    simp only [h_binary, implies_true, ↓reduceDIte]
    let i_of_m := Nat.binaryFinMapToNat m h_binary
    have h_mono_eq : monomialOfNat i_of_m = m := by
      ext j; simp only [monomialOfNat, Finsupp.onFinset_apply]
      have h_getBit := Nat.getBit_of_binaryFinMapToNat (n:=n) (m:=m)
        (h_binary:=h_binary) (k:=j)
      rw [h_getBit]
      simp only [j.isLt, ↓reduceDIte, Fin.eta]
    rw [MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_monomial]
    -- ⊢ (∑ x, if monomialOfNat ↑x = m then p[x] else 0) = p[↑(Nat.binaryFinMapToNat ⇑m ⋯)]
    set f := fun x: Fin (2^n) => if monomialOfNat x.val = m then p[x] else (0: R)
    -- ⊢ Finset.univ.sum f = p[↑(Nat.binaryFinMapToNat ⇑m ⋯)]
    rw [Finset.sum_eq_single (a:=⟨i_of_m, by omega⟩)]
    · -- Goal 1: Prove the main term is correct.
      simp only [h_mono_eq, ↓reduceIte, Fin.eta, Fin.getElem_fin];
      rfl
    · -- Goal 2: Prove all other terms are zero.
      intro j h_j_mem_univ h_ji_ne
      -- If `j ≠ i_of_m`, then `monomialOfNat j ≠ monomialOfNat i_of_m` (which is `m`).
      -- ⊢ (monomial (monomialOfNat ↑j)) p[j] = 0
      have h_mono_ne : monomialOfNat j.val ≠ m := by
        intro h_eq_contra
        have h_j_is_i_of_m := eq_monomialOfNat_iff_eq_bitRepr (m:=m)
          (h_binary:=h_binary) (i:=j).mp h_eq_contra
        exact h_ji_ne h_j_is_i_of_m
      simp only [h_mono_ne, ↓reduceIte]
    -- Goal 3: Prove `i` is in the summation set.
    · simp [Finset.mem_univ]
  else -- this case is similar to the proof of `right_inv` in `equivMvPolynomialDeg1`
    simp only [h_binary, ↓reduceDIte]
    -- ⊢ coeff m p.toMvPolynomial = 0
    have hv := toMvPolynomial_is_multilinear p
    let vMlPoly: R⦃≤ 1⦄[X Fin n] := ⟨p.toMvPolynomial, hv⟩
    have h_v_coeff_zero : vMlPoly.val.coeff m = 0 := by
      refine notMem_support_iff.mp ?_
      by_contra h_mem_support
      have hvMlPoly := vMlPoly.2
      rw [MvPolynomial.mem_restrictDegree] at hvMlPoly
      have h_deg_le_one: ∀ j: Fin n, (m j) ≤ 1 := by
        exact fun j ↦ hvMlPoly m h_mem_support j
      simp only [not_forall, not_le] at h_binary -- h_binary : ∃ x, 1 < m x
      obtain ⟨j, hj⟩ := h_binary
      have h_not_1_lt_m_j: ¬(1 < m j) := by exact Nat.not_lt.mpr (hv h_mem_support j)
      exact h_not_1_lt_m_j hj
    exact h_v_coeff_zero

/--
Converts an `MlPoly` to a mathlib restricted-degree multivariate polynomial.
Wraps `toMvPolynomial` with a proof that the result is multilinear (i.e. individual degrees ≤ 1).
-/
def toMvPolynomialDeg1 (p : MlPoly R n) : R⦃≤ 1⦄[X Fin n] :=
  ⟨toMvPolynomial p, by exact toMvPolynomial_is_multilinear p⟩

/--
Converts a mathlib restricted-degree multivariate polynomial to an `MlPoly`.
Extracts coefficients using `monomialOfNat` to map indices to monomials.
-/
def ofMvPolynomialDeg1 (p : R⦃≤ 1⦄[X Fin n]) : MlPoly R n :=
  Vector.ofFn (fun i : Fin (2 ^ n) => p.val.coeff (monomialOfNat i))

-- #eval finFunctionFinEquiv.invFun (⟨3, by omega⟩: Fin (2^2)) 4
-- #eval Nat.getBit (k:=4) (n:=3)

/--
Equivalence between `MlPoly` and mathlib's restricted-degree multivariate polynomials.
Establishes that both representations are isomorphic via coefficient extraction/insertion.
-/
def equivMvPolynomialDeg1 : MlPoly R n ≃ R⦃≤ 1⦄[X Fin n] where
  toFun := toMvPolynomialDeg1
  invFun := ofMvPolynomialDeg1
  left_inv v := by
    unfold ofMvPolynomialDeg1 toMvPolynomialDeg1
    apply Vector.ext; intro j x
    simp only [Vector.getElem_ofFn]
    simp only [toMvPolynomial, Fin.getElem_fin]
    -- ⊢ coeff (monomialOfNat j) (∑ x, (monomial (monomialOfNat ↑x)) v[↑x]) = v[j]
    rw [MvPolynomial.coeff_sum]
    -- ⊢ ∑ x, coeff (monomialOfNat j) ((monomial (monomialOfNat ↑x)) v[↑x]) = v[j]
    simp only [MvPolynomial.coeff_monomial]
    -- ⊢ (∑ x, if monomialOfNat ↑x = monomialOfNat j then v[↑x] else 0) = v[j]
    set f := fun x: Fin (2^n) => if monomialOfNat x.val = monomialOfNat j then v[x.val] else (0: R)
    -- ⊢ Finset.univ.sum f = v[j]
    have h_v_j: v[j] = f ⟨j, by omega⟩ := by
      simp only [f]
      simp only [↓reduceIte]
    rw [h_v_j]
    -- ⊢ Finset.univ.sum f = f ⟨j, x⟩
    rw [Finset.sum_eq_single (a:=⟨j, by omega⟩)]
      -- Goal 1: Prove the main term is correct.
    · intro b hb hb_ne
      have h_monominal_diff: monomialOfNat (n:=n) (i:=b.val) ≠ monomialOfNat (i:=j) := by
        simp only [monomialOfNat, ne_eq]
        -- ⊢ ¬Finsupp.onFinset Finset.univ (fun j ↦ (↑j).getBit ↑b) ⋯
        -- = Finsupp.onFinset Finset.univ (fun j_1 ↦ (↑j_1).getBit j) ⋯
        refine Finsupp.ne_iff.mpr ?_
        have h_exists_bit_diff := Nat.exist_bit_diff_if_diff (a:=b) (b:=⟨j, by omega⟩)
          (h_a_ne_b:=hb_ne)
        obtain ⟨k, h_getBit_k_diff⟩ := h_exists_bit_diff
        use k
        simp only [Finsupp.onFinset_apply, ne_eq]
        exact h_getBit_k_diff
      simp only [h_monominal_diff, ↓reduceIte]
    · intro h_jx_ne_in_univ
      have h_jx_in_univ: (⟨j, x⟩: Fin (2^n)) ∈ Finset.univ := by
        exact Finset.mem_univ (⟨j, x⟩: Fin (2^n))
      contradiction
  right_inv v := by
    unfold toMvPolynomialDeg1 ofMvPolynomialDeg1 toMvPolynomial
    simp only [Fin.getElem_fin, Vector.getElem_ofFn]
    -- ⊢ ⟨∑ x, (monomial (monomialOfNat ↑x)) (coeff (monomialOfNat ↑x) ↑v), ⋯⟩ = v
    ext m
    simp only
    rw [MvPolynomial.coeff_sum]
    simp_rw [MvPolynomial.coeff_monomial]
    -- ⊢ (∑ x, if monomialOfNat ↑x = m then coeff (monomialOfNat ↑x) ↑v else 0) = coeff m ↑v
    by_cases h_m_is_ML_mono: (∀ j : Fin n, m j ≤ 1) -- this cond could leads to m ∈ v.support
    · let i_of_m := Nat.binaryFinMapToNat m h_m_is_ML_mono
      -- We can prove that `monomialOfNat i.val` is indeed `m`.
      have h_mono_eq : monomialOfNat i_of_m = m := by
        ext j; simp only [monomialOfNat, Finsupp.onFinset_apply]
        have h_getBit := Nat.getBit_of_binaryFinMapToNat (n:=n) (m:=m)
          (h_binary:=h_m_is_ML_mono) (k:=j)
        rw [h_getBit]
        simp only [j.isLt, ↓reduceDIte, Fin.eta]
      rw [Finset.sum_eq_single (a:=i_of_m)]
      · simp only [h_mono_eq, ↓reduceIte] -- Goal 1: Prove the main term is correct.
      · intro j h_j_mem_univ h_ji_ne -- Goal 2: Prove all other terms are zero.
        -- If `j ≠ i`, then `monomialOfNat j ≠ monomialOfNat i` (which is `m`).
        have h_mono_ne : monomialOfNat j.val ≠ m := by
          intro h_eq_contra
          have h_j_is_i_of_m := eq_monomialOfNat_iff_eq_bitRepr (m:=m)
            (h_binary:=h_m_is_ML_mono) (i:=j).mp h_eq_contra
          exact h_ji_ne h_j_is_i_of_m
        simp only [h_mono_ne, ↓reduceIte]
      -- Goal 3: Prove `i` is in the summation set.
      · simp [Finset.mem_univ]
    · -- `m` is not a multilinear monomial => rhs = `coeff m v = 0`, since `v` is multilinear.
      push_neg at h_m_is_ML_mono
      obtain ⟨j, hj⟩ := h_m_is_ML_mono
      have h_v_coeff_zero : v.val.coeff m = 0 := by
        refine notMem_support_iff.mp ?_
        by_contra h_mem_support
        have hv := v.2
        simp only [MvPolynomial.mem_restrictDegree] at hv
        have h_deg_le_one: ∀ j: Fin n, (m j) ≤ 1 := by
          exact fun j ↦ hv m h_mem_support j
        have hj_le_1 := h_deg_le_one j
        linarith
      -- We now show the LHS is also zero.
      rw [h_v_coeff_zero]
      apply Finset.sum_eq_zero
      intro i hi
      -- `monomialOfNat i` is always multilinear. `m` is not.
      -- Therefore, `m` can never equal `monomialOfNat i`, so the `if` is always false.
      have h_mono_ne : monomialOfNat i.val ≠ m := by
        intro h_eq_contra
        have h_m_i_multi : ∀ j: Fin n, (monomialOfNat i.val) j ≤ 1 := by
          intro j; simp [monomialOfNat, Finsupp.onFinset_apply]
          have h := Nat.getBit_lt_2 (k:=j) (n:=i)
          omega
        rw [h_eq_contra] at h_m_i_multi
        have h_m_i_multi_j_le_1 := h_m_i_multi j
        linarith
      simp only [h_mono_ne, ↓reduceIte]

/-- Linear equivalence between `MlPoly` and `MvPolynomial.restrictDegree` -/
noncomputable def linearEquivMvPolynomialDeg1 : MlPoly R n ≃ₗ[R] R⦃≤ 1⦄[X Fin n] :=
  { toEquiv := equivMvPolynomialDeg1
    map_add' := by
      intro p q
      -- ⊢ (p + q).toMvPolynomialDeg1 = p.toMvPolynomialDeg1 + q.toMvPolynomialDeg1
      ext i
      -- ⊢ coeff i ↑(p + q).toMvPolynomialDeg1 =
      -- coeff i ↑(p.toMvPolynomialDeg1 + q.toMvPolynomialDeg1)
      unfold equivMvPolynomialDeg1 toMvPolynomialDeg1
      simp only [AddMemClass.mk_add_mk, coeff_add]
      simp only [coeff_of_toMvPolynomial_eq_coeff_of_MlPoly (p := p)]
      simp only [coeff_of_toMvPolynomial_eq_coeff_of_MlPoly (p := p + q)]
      simp only [coeff_of_toMvPolynomial_eq_coeff_of_MlPoly (p := q)]
      if h_binary: (∀ j: Fin n, i j ≤ 1) then
        simp only [h_binary, implies_true, ↓reduceDIte]
        conv_lhs => enter [1]; change MlPoly.add p q
        simp only [add, Vector.getElem_zipWith]
      else
        simp only [h_binary, ↓reduceDIte, add_zero]
    map_smul' := by
      intro r p
      ext i
      unfold equivMvPolynomialDeg1 toMvPolynomialDeg1
      simp only [RingHom.id_apply, SetLike.mk_smul_mk, coeff_smul, smul_eq_mul]
      simp only [coeff_of_toMvPolynomial_eq_coeff_of_MlPoly (p := p)]
      simp only [coeff_of_toMvPolynomial_eq_coeff_of_MlPoly (p := r • p)]
      if h_binary: (∀ j: Fin n, i j ≤ 1) then
        simp only [h_binary, implies_true, ↓reduceDIte]
        conv_lhs => enter [1]; change MlPoly.smul r p
        simp only [smul, Vector.getElem_map]
      else
        simp only [h_binary, ↓reduceDIte, mul_zero]
    }

end MlPoly

end
