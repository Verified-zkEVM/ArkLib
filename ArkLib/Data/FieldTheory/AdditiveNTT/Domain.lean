/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.Data.FieldTheory.AdditiveNTT.NovelPolynomialBasis
import Mathlib.Tactic
import Mathlib.Data.Finsupp.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# Additive NTT Domains

Foundational domain and quotient-map infrastructure used by the Additive NTT algorithm.

This file contains both abstract and computable domain-side definitions:

- executable point encodings `bitsToUValue`, `bitsToU`, `evalWAt`, `evalNormalizedWAt`
- canonical/computable domain pair `sDomain`, `sDomainComp`
- quotient-map and intermediate-domain structure
- domain basis, cardinality, and index/point conversion lemmas
- `AdditiveNTT.Comp` adapter story used downstream by Binius:
  `Comp.sDomain` (computable primary) and `Comp.canonicalSDomain` (explicit canonical alias)

## References

* [Diamond, B.E. and Posen, J., *Polylogarithmic proofs for multilinears over binary towers*][DP24]
  Reference the archived revision of [DP24] when comparing statement numbering.
* [Lin, S., Chung, W., and Han, Y.S., *Novel polynomial basis and its application to reed-solomon
    erasure codes*][LCH14]
* [Von zur Gathen, J. and Gerhard, J., *Arithmetic and factorization of polynomial over F2
    (extended abstract)*][GGJ96]

-/

set_option linter.style.longFile 3500

open Polynomial AdditiveNTT Module
namespace AdditiveNTT

universe u

-- We work over a generic field `L` which is an algebra over a ground field `𝔽q` of prime
-- characteristic.
variable {r : ℕ} [NeZero r]
variable {L : Type u} [Field L] [Fintype L] [DecidableEq L]
variable (𝔽q : Type u) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]

-- Let `β` be a basis of `L` over `𝔽q`, indexed by natural numbers.
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ R_rate : ℕ} [NeZero ℓ] (h_ℓ_add_R_rate : ℓ + R_rate < r)-- ℓ ∈ {1, ..., r-1}

omit h_Fq_char_prime [DecidableEq 𝔽q] in
lemma 𝔽q_element_eq_zero_or_eq_one : ∀ c: 𝔽q, c = 0 ∨ c = 1 := by
  classical
  intro c
  by_cases hc : c = 0
  · left; omega -- If c = 0, we're done.
  · right; -- If c ≠ 0, we must prove c = 1.
    -- The non-zero elements of 𝔽q form a multiplicative group, i.e. the "group of units".
    have h_card_units : Fintype.card 𝔽qˣ = 1 := by
      rw [Fintype.card_units, hF₂.out]
    -- A group with only one element must be the trivial group, containing only the identity (1).
    -- So, `c` (as an element of the group of units) must be 1.
    have h_c_is_one : Units.mk0 c hc = (1 : 𝔽qˣ) := by
      -- First, we prove that 𝔽qˣ is a Subsingleton.
      -- The `haveI` keyword creates a local typeclass instance.
      haveI : Subsingleton 𝔽qˣ := by
        apply Fintype.card_le_one_iff_subsingleton.mp
        exact Nat.le_of_eq h_card_units
      -- Now that the instance is available, Subsingleton.elim will work.
      apply Subsingleton.elim
    -- Now, we apply `Units.val` to both sides of h_c_is_one to "unbox" the equality `c = 1`
    exact congr_arg Units.val h_c_is_one

section ComputableDomainPrimitives

/-- Product over `List.finRange` is definitionaly equal to product over `Finset.univ`. -/
lemma List.prod_finRange_eq_finset_prod {M : Type*} [CommMonoid M] {n : ℕ}
    (f : Fin n → M) :
    ((List.finRange n).map f).prod = ∏ i : Fin n, f i := rfl

/-- Explicit value-level encoding of a point in `U i` from a bit-index. -/
def bitsToUValue (i : Fin r) (k : Fin (2 ^ i.val)) : L :=
  (Finset.univ : Finset (Fin i)).sum fun j =>
    if Nat.getBit (n := k.val) (k := j.val) == 1 then
      β ⟨j.val, by exact Nat.lt_trans j.isLt i.isLt⟩
    else
      0

/-- Explicit subtype-level encoding of points in `U i` by bit-index. -/
def bitsToU (i : Fin r) (k : Fin (2 ^ i.val)) : U 𝔽q β i :=
  ⟨bitsToUValue (β := β) i k, by
    classical
    unfold bitsToUValue U
    have hsum :
        (∑ j ∈ (Finset.univ : Finset (Fin i)),
            if Nat.getBit (n := k.val) (k := j.val) = 1 then
              β ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩
            else
              (0 : L))
          ∈ Submodule.span 𝔽q (β '' Set.Ico 0 i) := by
      refine Submodule.sum_mem (p := Submodule.span 𝔽q (β '' Set.Ico 0 i)) ?_
      intro j hj
      by_cases hbit : Nat.getBit (n := k.val) (k := j.val) = 1
      · simp [hbit]
        exact Submodule.subset_span
          (Set.mem_image_of_mem β (Set.mem_Ico.mpr
            ⟨Nat.zero_le j.val, j.isLt⟩))
      · simp [hbit]
    simp only [beq_iff_eq]
    exact hsum⟩

omit [DecidableEq 𝔽q] h_Fq_char_prime h_β₀_eq_1 in
/-- Bijection witness for executable encoding `bitsToU`. -/
theorem bitsToU_bijective (i : Fin r) : Function.Bijective (bitsToU (𝔽q := 𝔽q) (β := β) i) := by
  apply (Fintype.bijective_iff_injective_and_card
    (f := bitsToU (𝔽q := 𝔽q) (β := β) i)).mpr
  constructor
  · intro k1 k2 h_eq
    unfold bitsToU at h_eq
    simp only [Subtype.mk.injEq] at h_eq
    let c (k : ℕ) (j : Fin i) : 𝔽q := if (Nat.getBit (n := k) (k := j.val) == 1) then 1 else 0
    have h_sum (k : Fin (2 ^ i.val)) :
        bitsToUValue (β := β) i k = Finset.univ.sum fun j => (c k.val j) • β ⟨j, by omega⟩ := by
      unfold bitsToUValue
      apply Finset.sum_congr rfl
      intro j _
      dsimp [bitsToUValue, c]
      split_ifs <;> simp
    rw [h_sum k1, h_sum k2] at h_eq
    rw [← sub_eq_zero] at h_eq
    rw [← Finset.sum_sub_distrib] at h_eq
    simp_rw [← sub_smul] at h_eq
    rw [← sub_eq_zero] at h_eq
    have h_lin_indep := hβ_lin_indep.out
    have h_indep_restricted := LinearIndependent.comp h_lin_indep
      (Fin.castLE (Nat.le_of_lt i.isLt) : Fin i → Fin r)
      (Fin.castLE_injective _)
    simp only [sub_zero] at h_eq
    have h_coeffs_zero : ∀ j : Fin i, j ∈ Finset.univ → c k1.val j - c k2.val j = 0 :=
      linearIndependent_iff'.mp h_indep_restricted
        Finset.univ
        (fun j => c k1.val j - c k2.val j)
        h_eq
    ext
    apply Nat.eq_iff_eq_all_getBits.mpr
    intro n
    have h_bit_k1_lt_2 := Nat.getBit_lt_2 (n := k1) (k := n)
    have h_bit_k2_lt_2 := Nat.getBit_lt_2 (n := k2) (k := n)
    by_cases hn : n < i.val
    · let j : Fin i := ⟨n, hn⟩
      have h_c_diff_zero := h_coeffs_zero j (Finset.mem_univ j)
      simp only [sub_eq_zero] at h_c_diff_zero
      dsimp only [beq_iff_eq, c] at h_c_diff_zero
      interval_cases hk1 : Nat.getBit (n := k1) (k := j)
      · interval_cases hk2 : Nat.getBit (n := k2) (k := j)
        · rfl
        · simp only [Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte, BEq.rfl,
          zero_ne_one] at h_c_diff_zero
      · interval_cases hk2 : Nat.getBit (n := k2) (k := j)
        · simp only [BEq.rfl, ↓reduceIte, Nat.reduceBEq, Bool.false_eq_true,
          one_ne_zero] at h_c_diff_zero
        · rfl
    · have h_k1 := Nat.getBit_of_lt_two_pow (n := i) (a := k1) (k := n)
      have h_k2 := Nat.getBit_of_lt_two_pow (n := i) (a := k2) (k := n)
      simp only [hn, ↓reduceIte] at h_k1 h_k2
      rw [h_k1, h_k2]
  · rw [Fintype.card_fin, AdditiveNTT.U_card (𝔽q := 𝔽q) (β := β) (i := i), hF₂.out]

/-- Executable enumeration of all elements in `U i`. -/
def getUElements (i : Fin r) : List L :=
  (List.finRange (2 ^ i.val)).map
    (fun k : Fin (2 ^ i.val) => bitsToUValue (β := β) (i := i) (k := k))

/-- Executable evaluation of the subspace-vanishing polynomial at a point. -/
def evalWAt (i : Fin r) (x : L) : L :=
  ((getUElements (β := β) (i := i)).map (fun u => x - u)).prod

/-- Executable evaluation of `Ŵᵢ` at a point. -/
def evalNormalizedWAt (i : Fin r) (x : L) : L :=
  let W_x := evalWAt (β := β) (i := i) x
  let W_beta := evalWAt (β := β) (i := i) (β i)
  W_x * W_beta⁻¹

/-- Bridge theorem: executable `evalWAt` agrees with `W.eval`. -/
lemma evalWAt_eq_W (i : Fin r) (x : L) :
    evalWAt (β := β) (i := i) x = (W 𝔽q β i).eval x := by
  unfold evalWAt getUElements
  rw [List.map_map]
  rw [List.prod_finRange_eq_finset_prod]
  rw [AdditiveNTT.W, Polynomial.eval_prod]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  apply Finset.prod_bij (s := ((Finset.univ (α := (Fin (2 ^ i.val))))))
    (t := (Finset.univ : Finset (U 𝔽q β i)))
    (i := fun k _ => bitsToU (𝔽q := 𝔽q) (β := β) (i := i) k)
    (hi := by
      intro a _
      exact Finset.mem_univ _)
    (i_inj := by
      intro a₁ _ a₂ _ h_eq
      exact (bitsToU_bijective (𝔽q := 𝔽q) (β := β) (i := i)).1 h_eq)
    (i_surj := by
      intro b _
      obtain ⟨a, ha_eq⟩ := (bitsToU_bijective (𝔽q := 𝔽q) (β := β) (i := i)).2 b
      use a
      constructor
      · exact ha_eq
      · exact Finset.mem_univ a
    )
    (h := by
      intro a ha_univ
      rfl
    )

/-- Bridge theorem: executable `evalNormalizedWAt` agrees with `normalizedW.eval`. -/
lemma evalNormalizedWAt_eq_normalizedW (i : Fin r) (x : L) :
    evalNormalizedWAt (β := β) (i := i) x
      = (normalizedW 𝔽q β i).eval x := by
  unfold evalNormalizedWAt
  rw [evalWAt_eq_W (𝔽q := 𝔽q) (β := β) (i := i) (x := x)]
  simp only
  rw [evalWAt_eq_W (𝔽q := 𝔽q) (β := β) (i := i) (x := β i)]
  rw [AdditiveNTT.normalizedW]
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  simp only [one_div]
  apply mul_comm

/-- Computable linear map given by executable evaluation of `Ŵᵢ`. -/
def evalNormalizedWLinearMap (i : Fin r) : L →ₗ[𝔽q] L :=
{ toFun := fun x => evalNormalizedWAt (β := β) (i := i) x
  map_add' := by
    intro x y
    calc
      evalNormalizedWAt (β := β) (i := i) (x + y)
          = (normalizedW 𝔽q β i).eval (x + y) := by
            exact evalNormalizedWAt_eq_normalizedW
              (𝔽q := 𝔽q) (β := β) (i := i) (x := x + y)
      _ = (normalizedW 𝔽q β i).eval x + (normalizedW 𝔽q β i).eval y := by
            exact (AdditiveNTT.normalizedW_is_additive (𝔽q := 𝔽q) (β := β) i).map_add x y
      _ = evalNormalizedWAt (β := β) (i := i) x
          + evalNormalizedWAt (β := β) (i := i) y := by
            rw [← evalNormalizedWAt_eq_normalizedW
              (𝔽q := 𝔽q) (β := β) (i := i) (x := x)]
            rw [← evalNormalizedWAt_eq_normalizedW
              (𝔽q := 𝔽q) (β := β) (i := i) (x := y)]
  map_smul' := by
    intro c x
    calc
      evalNormalizedWAt (β := β) (i := i) (c • x)
          = (normalizedW 𝔽q β i).eval (c • x) := by
            exact evalNormalizedWAt_eq_normalizedW
              (𝔽q := 𝔽q) (β := β) (i := i) (x := c • x)
      _ = c • (normalizedW 𝔽q β i).eval x := by
            exact (AdditiveNTT.normalizedW_is_additive (𝔽q := 𝔽q) (β := β) i).map_smul c x
      _ = c • evalNormalizedWAt (β := β) (i := i) x := by
            rw [← evalNormalizedWAt_eq_normalizedW
              (𝔽q := 𝔽q) (β := β) (i := i) (x := x)]
}

@[simp] lemma evalNormalizedWLinearMap_apply (i : Fin r) (x : L) :
    evalNormalizedWLinearMap (𝔽q := 𝔽q) (β := β) (i := i) x
      = (normalizedW 𝔽q β i).eval x := by
  unfold evalNormalizedWLinearMap
  exact evalNormalizedWAt_eq_normalizedW
    (𝔽q := 𝔽q) (β := β) (i := i) (x := x)

end ComputableDomainPrimitives

section IntermediateStructures

/-! ## 1. Intermediate Structures: Domains, Maps, and Bases

This section defines the intermediate evaluation domains, quotient maps, and the structure
of the subspace vanishing polynomials and their bases. These are the core algebraic objects
underlying the Additive NTT algorithm.
-/

/-- The intermediate evaluation domain `S⁽ⁱ⁾`, defined as the image of the full evaluation space
under the normalized subspace vanishing polynomial `Ŵᵢ(X)`.
`∀ i ∈ {0, ..., r-1}`, we define `Uᵢ:= <β₀, ..., βᵢ₋₁>_{𝔽q}`, note that `Uᵣ` is not used.
`∀ i ∈ {0, ..., r-1}, S⁽ⁱ⁾` is the image of the subspace `U_{ℓ+R}`
  under the `𝔽q`-linear map `x ↦ Ŵᵢ(x)`. -/
noncomputable def sDomain (i : Fin r) : Subspace 𝔽q L :=
  let W_i_norm := normalizedW 𝔽q β i
  let h_W_i_norm_is_additive : IsLinearMap 𝔽q (fun x : L => W_i_norm.eval x) :=
    AdditiveNTT.normalizedW_is_additive 𝔽q β i
  Submodule.map (polyEvalLinearMap W_i_norm h_W_i_norm_is_additive)
    (U 𝔽q β ⟨ℓ + R_rate, h_ℓ_add_R_rate⟩)

/-- Computable companion of `sDomain`, using executable evaluation primitives. -/
def sDomainComp (i : Fin r) : Subspace 𝔽q L :=
  Submodule.map
    (evalNormalizedWLinearMap (𝔽q := 𝔽q) (β := β) (i := i))
    (U 𝔽q β ⟨ℓ + R_rate, h_ℓ_add_R_rate⟩)

noncomputable def sDomain_cast {i j : Fin r} (h : i = j) :
  sDomain 𝔽q β h_ℓ_add_R_rate i ≃ₗ[𝔽q] sDomain 𝔽q β h_ℓ_add_R_rate j := by
  subst h
  exact LinearEquiv.refl 𝔽q (sDomain 𝔽q β h_ℓ_add_R_rate i)

omit [DecidableEq 𝔽q] [NeZero ℓ] hF₂ h_β₀_eq_1 in
lemma mem_sDomain_of_eq {i j : Fin r} (h : i.val = j.val)
    {y : L} (hy : y ∈ sDomain 𝔽q β h_ℓ_add_R_rate i) :
    y ∈ sDomain 𝔽q β h_ℓ_add_R_rate j := by
  have h_eq : i = j := by exact Fin.eq_of_val_eq h
  subst h_eq -- or `rw [h]`
  exact hy

omit [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
lemma sDomain_eq_of_eq {i j : Fin r} (h : i = j) :
  sDomain 𝔽q β h_ℓ_add_R_rate i = sDomain 𝔽q β h_ℓ_add_R_rate j := by
  subst h
  rfl

/-- The quotient map `q⁽ⁱ⁾(X)` that relates successive domains.
`q⁽ⁱ⁾(X) := (Wᵢ(βᵢ)^q / Wᵢ₊₁(βᵢ₊₁)) * ∏_{c ∈ 𝔽q} (X - c)`. Usable range is `∀ i ∈ {0, ..., r-2}` -/
noncomputable def qMap (i : Fin r) : L[X] :=
  let constMultiplier := ((W 𝔽q β i).eval (β i))^(Fintype.card 𝔽q)
    / ((W 𝔽q β (i + 1)).eval (β (i + 1)))
  C constMultiplier * ∏ c: 𝔽q, (X - C (algebraMap 𝔽q L c))

omit [DecidableEq L] [DecidableEq 𝔽q] h_Fq_char_prime h_β₀_eq_1 in
/-- Helper: The natDegree of qMap is |𝔽q| = 2. -/
lemma natDegree_qMap (i : Fin r) : (qMap 𝔽q β i).natDegree = 2 := by
  let q := Fintype.card 𝔽q
  let constMultiplier := ((W 𝔽q β i).eval (β i))^q / ((W 𝔽q β (i + 1)).eval (β (i + 1)))
  -- 1. Establish the polynomial form: C * (X^q - X)
  have h_q_poly_form : qMap 𝔽q β i = C constMultiplier * (X ^ q - X) := by
    rw [qMap, prod_poly_sub_C_eq_poly_pow_card_sub_poly_in_L (p:=X)]
  rw [h_q_poly_form]
  -- 2. Use natDegree rules
  -- natDegree (C * P) = natDegree P (if C ≠ 0)
  rw [Polynomial.natDegree_C_mul]
  · -- natDegree (X^q - X) = q
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
    · rw [Polynomial.natDegree_X_pow]; unfold q; rw [hF₂.out];
    · -- Proof that natDegree X < natDegree X^q
      rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X]
      have hq_ge_2 : Fintype.card 𝔽q ≥ 2 := by rw [hF₂.out]
      exact hq_ge_2
  · -- Proof that constMultiplier ≠ 0 (Standard non-zero evaluation argument)
    intro h_zero
    have h_num_ne_zero : ((W 𝔽q β i).eval (β i)) ^ q ≠ 0 := by
      exact pow_ne_zero q (AdditiveNTT.Wᵢ_eval_βᵢ_neq_zero 𝔽q β i)
    rw [div_eq_zero_iff] at h_zero
    cases h_zero with
    | inl h => contradiction
    | inr h =>
       have h_den_ne_zero : ((W 𝔽q β (i + 1)).eval (β (i + 1))) ≠ 0 :=
         AdditiveNTT.Wᵢ_eval_βᵢ_neq_zero 𝔽q β (i + 1)
       contradiction

omit [DecidableEq L] [DecidableEq 𝔽q] h_Fq_char_prime h_β₀_eq_1 in
lemma qMap_ne_zero (i : Fin r) : (qMap 𝔽q β i) ≠ 0 := by
  apply Polynomial.ne_zero_of_natDegree_gt (n := 0)
  rw [natDegree_qMap 𝔽q β i]; exact Nat.zero_lt_two

omit [DecidableEq L] [DecidableEq 𝔽q] h_Fq_char_prime h_β₀_eq_1 in
/-- The degree of the quotient map is |𝔽q| (which is 2). -/
lemma degree_qMap (i : Fin r) : (qMap 𝔽q β i).degree = 2 := by
  conv_rhs => change ((2 : ℕ) : WithBot ℕ)
  rw [←natDegree_qMap 𝔽q β i]
  rw [Polynomial.degree_eq_natDegree (hp := qMap_ne_zero 𝔽q β i)]

omit [DecidableEq L] [DecidableEq 𝔽q] h_Fq_char_prime hF₂ hβ_lin_indep h_β₀_eq_1 in
theorem qMap_eval_𝔽q_eq_0 (i : Fin r) :
  ∀ c: 𝔽q, (qMap 𝔽q β i).eval (algebraMap 𝔽q L c) = 0 := by
  intro u
  rw [qMap]
  set vpoly𝔽q := ∏ c: 𝔽q, (X - C ((algebraMap 𝔽q L) c)) with h_vpoly𝔽q
  have h_right_term_vanish: eval ((algebraMap 𝔽q L) u) (vpoly𝔽q) = 0 := by
    simp only [eval_prod, eval_sub, eval_X, eval_C, vpoly𝔽q]
    rw [Finset.prod_eq_zero_iff]
    -- ⊢ ∃ a ∈ Finset.univ, (algebraMap 𝔽q L) u - (algebraMap 𝔽q L) a = 0
    have hu: u ∈ (Finset.univ: Finset 𝔽q) := by simp only [Finset.mem_univ]
    use u
    constructor
    · exact hu
    · simp only [sub_self]
  simp only [eval_mul, eval_C, h_right_term_vanish, mul_zero]

omit [DecidableEq 𝔽q] [DecidableEq L] hF₂ h_β₀_eq_1 in
/-- **Lemma 4.2.** The quotient maps compose with the `Ŵ` polynomials.
`q⁽ⁱ⁾ ∘ Ŵᵢ = Ŵᵢ₊₁, ∀ i ∈ {0, ..., r-2}`. -/
lemma qMap_comp_normalizedW (i : Fin r) (h_i_add_1 : i + 1 < r) :
  (qMap 𝔽q β i).comp (normalizedW 𝔽q β i) = normalizedW 𝔽q β (i + 1) := by
  classical
  let q := Fintype.card 𝔽q
  -- `q⁽ⁱ⁾ ∘ Ŵᵢ = ((Wᵢ(βᵢ)^q / Wᵢ₊₁(βᵢ₊₁)) * ∏_{c ∈ 𝔽q} (X - c)) ∘ Ŵᵢ`
  -- `= ((Wᵢ(βᵢ)^q / Wᵢ₊₁(βᵢ₊₁)) * (X^q - X)) ∘ Ŵᵢ` -- X^q - X = ∏_{c ∈ 𝔽q} (X - c)
  -- `= (Wᵢ(βᵢ)^q / Wᵢ₊₁(βᵢ₊₁)) * (Ŵᵢ(X)^q - Ŵᵢ(X))` -- composition
  -- `= (Wᵢ(βᵢ)^q / Wᵢ₊₁(βᵢ₊₁)) * (Wᵢ(X)^q/Wᵢ(βᵢ)^q - Wᵢ(X)/Wᵢ(βᵢ))`
  -- `= (Wᵢ(βᵢ)^q / Wᵢ₊₁(βᵢ₊₁)) * (Wᵢ(X)^q/Wᵢ(βᵢ)^q - Wᵢ(X) * Wᵢ(βᵢ)^(q-1)/Wᵢ(βᵢ)^q)`
  -- `= (Wᵢ(βᵢ)^q / Wᵢ₊₁(βᵢ₊₁)) * (Wᵢ(X)^q - Wᵢ(X) * Wᵢ(βᵢ)^(q-1)) / Wᵢ(βᵢ)^q`
  -- `= (Wᵢ(βᵢ)^q * (Wᵢ(X)^q - Wᵢ(X) * Wᵢ(βᵢ)^(q-1))) / (Wᵢ₊₁(βᵢ₊₁) * Wᵢ(βᵢ)^q)`
  -- `= (Wᵢ(X)^q - Wᵢ(βᵢ)^(q-1) * Wᵢ(X)) / Wᵢ₊₁(βᵢ₊₁)`
  -- `= Wᵢ₊₁(X)` -- Q.E.D via AdditiveNTT.W_linear_comp_decomposition

  -- Define aliases for mathematical objects to improve readability
  set q := Fintype.card 𝔽q
  set W_i := W 𝔽q β i with h_W_i
  set W_i_plus_1 := W 𝔽q β (i + 1) with h_W_i_plus_1
  set val_i := W_i.eval (β i) with h_val_i
  set val_i_plus_1 := W_i_plus_1.eval (β (i + 1)) with h_val_i_plus_1
  -- Establish that the denominators in the definitions are non-zero
  have h_val_i_ne_zero : val_i ≠ 0 :=
    AdditiveNTT.Wᵢ_eval_βᵢ_neq_zero 𝔽q β i
  have h_val_i_plus_1_ne_zero : val_i_plus_1 ≠ 0 :=
    AdditiveNTT.Wᵢ_eval_βᵢ_neq_zero 𝔽q β (i + 1)
  -- The proof proceeds by a chain of equalities
  calc
    (qMap 𝔽q β i).comp (normalizedW 𝔽q β i)
    _ = C (val_i ^ q / val_i_plus_1)
    * (∏ c:𝔽q, (X - C (algebraMap 𝔽q L c))).comp (normalizedW 𝔽q β i) := by
      rw [qMap, mul_comp, C_comp]
    _ = C (val_i ^ q / val_i_plus_1) * ((normalizedW 𝔽q β i) ^ q - normalizedW 𝔽q β i) := by
      simp_rw [prod_comp, sub_comp, X_comp, C_comp]
      rw [prod_poly_sub_C_eq_poly_pow_card_sub_poly_in_L]
    _ = C (1 / val_i_plus_1) * (W_i ^ q - C (val_i ^ (q - 1)) * W_i) := by
      rw [normalizedW, mul_sub, mul_pow, C_pow]
      have hq_pos : q > 0 := by exact Fintype.card_pos
      have h_C: C (val_i ^ q / val_i_plus_1) = C (1 / val_i_plus_1) * C (val_i ^ q) := by
        rw [←C_mul]
        ring_nf
      rw [h_C]
      conv_lhs =>
        rw [mul_assoc, mul_assoc]
        rw [←mul_sub]
      rw [←h_val_i, ←h_W_i]
      rw [←C_pow]
      rw [←mul_assoc, ←C_mul]
      have h_mul: val_i ^ q * (1 / val_i) ^ q = 1 := by
        rw [←mul_pow (n:=q)]
        rw [←inv_eq_one_div]
        rw [mul_inv_cancel₀ (h:=h_val_i_ne_zero), one_pow]
      rw [h_mul, C_1, one_mul]
      rw [←mul_assoc, ←C_mul]
      have h_mul_2: val_i ^ q * (1 / val_i) = val_i ^ (q - 1) := by
        rw [←inv_eq_one_div]
        rw [←mul_pow_sub_one (hn:=by omega), mul_comm (a:=val_i), mul_assoc]
        rw [mul_inv_cancel₀ (h:=h_val_i_ne_zero), mul_one]
      rw [h_mul_2, C_pow]
    _ = C (1 / val_i_plus_1) * W_i_plus_1 := by -- `W_i^q - C(val_i^(q-1)) * W_i` = `W_{i+1}`
      have W_linear := AdditiveNTT.W_linear_comp_decomposition 𝔽q β
        i (p:=X)
      simp_rw [comp_X] at W_linear
      simp_rw [q, val_i, W_i, W_i_plus_1]
      rw [W_linear]
      · simp only [one_div, map_pow]
      · omega
    _ = normalizedW 𝔽q β (i + 1) := by -- Q.E.D.
      rw [normalizedW]

omit [DecidableEq L] [DecidableEq 𝔽q] hF₂ hβ_lin_indep h_β₀_eq_1 in
/-- The evaluation of the quotient map `q⁽ⁱ⁾(X)` is an `𝔽q`-linear map.
  Usable range is `∀ i ∈ {0, ..., r-2}`. -/
theorem qMap_is_linear_map (i : Fin r) :
  IsLinearMap 𝔽q (f:=fun inner_p ↦ (qMap 𝔽q β i).comp inner_p) := by
  set q := Fintype.card 𝔽q
  set constMultiplier := ((W 𝔽q β i).eval (β i))^q / ((W 𝔽q β (i + 1)).eval (β (i + 1)))
  have h_q_poly_form : qMap 𝔽q β i = C constMultiplier * (X ^ q - X) := by
    rw [qMap, prod_poly_sub_C_eq_poly_pow_card_sub_poly_in_L (p:=X)]
  -- Linearity of `x ↦ c * (x^q - x)` over `𝔽q`
  constructor
  · intro f g
    -- `q⁽ⁱ⁾ ∘ (f + g) = ((Wᵢ(βᵢ)^q / Wᵢ₊₁(βᵢ₊₁)) * ∏_{c ∈ 𝔽q} (X - c)) ∘ (f + g)` -- definition
    calc
      _ = (C constMultiplier * (X ^ q - X)).comp (f + g) := by
        rw [h_q_poly_form]
      _ = ((C constMultiplier).comp (f + g)) * (((X: L[X]) ^ q - X).comp (f+g)) := by
        rw [mul_comp]
      _ = (C constMultiplier) * ((X ^ q).comp (f+g) - X.comp (f+g)) := by
        rw [C_comp, sub_comp]
      _ = (C constMultiplier) * ((X ^ q).comp (f+g) - (X.comp f + X.comp g)) := by
        rw [X_comp]
        conv_lhs =>
          enter [2, 2]
          rw [←X_comp (p:=f), ←X_comp (p:=g)]
      _ = (C constMultiplier) * (f^q + g^q - (X.comp f + X.comp g)) := by
        rw [pow_comp, X_comp]
        unfold q
        rw [Polynomial.frobenius_identity_in_algebra (f:=f) (g:=g)]
      _ = (C constMultiplier) * (((X^q).comp f - X.comp f) + ((X^q).comp g - X.comp g)) := by
        rw [pow_comp, X_comp, X_comp, pow_comp, X_comp]
        ring
      _ = (C constMultiplier) * (((X: L[X]) ^ q - X).comp (f) + ((X: L[X]) ^ q - X).comp (g)) := by
        rw [←sub_comp, ←sub_comp]
      _ = (qMap 𝔽q β i).comp f + (qMap 𝔽q β i).comp g := by
        rw [h_q_poly_form]
        rw [mul_add]
        rw [mul_comp, mul_comp, C_comp, C_comp]
  · intro c f
      -- `q⁽ⁱ⁾ ∘ (c • f) = ((Wᵢ(βᵢ)^q / Wᵢ₊₁(βᵢ₊₁)) * ∏_{c ∈ 𝔽q} (X - c)) ∘ (c • f)` -- definition
    calc
      _ = (C constMultiplier * (X ^ q - X)).comp (c • f) := by
        rw [h_q_poly_form]
      _ = (C constMultiplier).comp (c • f) * ((c • f) ^ q - (c • f)) := by
        rw [mul_comp, sub_comp, pow_comp, X_comp]
      _ = (C constMultiplier).comp (c • f) * (c ^ q • f ^ q - c • f) := by
        rw [C_comp, smul_pow]
      _ = (C constMultiplier).comp (c • f) * (c • f^q - c • f) := by
        rw [FiniteField.pow_card]
      _ = (C constMultiplier).comp (c • f) * (C (algebraMap 𝔽q L c) * (f^q - f)) := by
        conv_lhs =>
          enter [2]
          rw [algebra_compatible_smul L c, algebra_compatible_smul L c]
          rw [smul_eq_C_mul, smul_eq_C_mul]
          rw [←mul_sub]
      _ = c • ((C constMultiplier).comp (c • f) * (f^q - f)) := by
        rw [←mul_assoc, mul_comm (a:=(C constMultiplier).comp (c • f)), mul_assoc]
        rw [←smul_eq_C_mul]
        rw [←algebra_compatible_smul L c]
      _ = c • (((C constMultiplier) * ((X: L[X])^q - X)).comp f) := by
        rw [C_comp]
        conv_lhs =>
          enter [2, 2]
          rw [←X_comp (p:=f)]
        rw [←pow_comp, ←sub_comp]
        rw [C_mul_comp]
      _ = c • (qMap 𝔽q β i).comp f := by
        rw [h_q_poly_form]

omit [DecidableEq 𝔽q] [NeZero ℓ] hF₂ h_β₀_eq_1 in
/-- **Theorem 4.3.** The quotient map `q⁽ⁱ⁾` maps the domain `S⁽ⁱ⁾` to `S⁽ⁱ⁺¹⁾`.
  Usable range is `∀ i ∈ {0, ..., r-2}`. -/
theorem qMap_maps_sDomain (i : Fin r) (h_i_add_1 : i + 1 < r) :
  have q_comp_linear_map := qMap_is_linear_map 𝔽q β i
  have q_eval_linear_map := linear_map_of_comp_to_linear_map_of_eval
    (f:=qMap 𝔽q β i) q_comp_linear_map
  let q_i_map := polyEvalLinearMap (qMap 𝔽q β i) q_eval_linear_map
  let S_i := sDomain 𝔽q β h_ℓ_add_R_rate i
  let S_i_plus_1 := sDomain 𝔽q β h_ℓ_add_R_rate (i+1)
  Submodule.map q_i_map S_i = S_i_plus_1 :=
by
  set q_comp_linear_map := qMap_is_linear_map 𝔽q β i
  set q_eval_linear_map := linear_map_of_comp_to_linear_map_of_eval
    (f:=qMap 𝔽q β i) q_comp_linear_map
  -- Unfold definitions and apply submodule and polynomial composition properties
  simp_rw [sDomain]
  -- `q⁽ⁱ⁾(S⁽ⁱ⁾) = q⁽ⁱ⁾(Ŵᵢ(⟨β₀, ..., β_{ℓ+R-1}⟩))`
  -- `= Ŵᵢ₊₁(⟨β₀, ..., β_{ℓ+R-1}⟩)`
  -- `= S⁽ⁱ⁺¹⁾`
  -- `⊢ map (q_i_map ∘ₗ Ŵᵢ_map) U = map (Ŵᵢ₊₁) U`
  rw [←Submodule.map_comp] -- for two nested maps (composition) over the same subspace
  -- The goal becomes `q_i_map ∘ₗ Ŵᵢ_map = Ŵᵢ₊₁`
  congr
  -- ⊢ polyEvalLinearMap (qMap 𝔽q β i) ⋯ ∘ₗ polyEvalLinearMap (normalizedW 𝔽q β i) ⋯ =
  -- polyEvalLinearMap (normalizedW 𝔽q β (i + 1)) ⋯

  -- We now have `(qMap ...).eval ((normalizedW ... i).eval x) = (normalizedW ... (i + 1)).eval x`.
  -- The `Polynomial.eval_comp` lemma states `p.eval (q.eval x) = (p.comp q).eval x`.
  set f := polyEvalLinearMap (qMap 𝔽q β i) q_eval_linear_map
  set g := polyEvalLinearMap (normalizedW 𝔽q β i)
    (normalizedW_is_additive 𝔽q β i)
  set t := polyEvalLinearMap (normalizedW 𝔽q β (i + 1))
    (normalizedW_is_additive 𝔽q β (i + 1))
  -- change f ∘ₗ g = t -- equality on composition of linear maps
  ext x
  -- => equality on evaluation at x
  -- (this automatically matches linearity of f ∘ g with linearity of t)
  rw [LinearMap.comp_apply]
  -- ⊢ f (g x) = t x
  simp_rw [f, g, t, polyEvalLinearMap]
  -- unfold the linearmaps into their definitions (toFun, map_add, map_smul)
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  -- NOTE: `LinearMap.coe_mk` and `AddHom.coe_mk` convert linear maps into their functions
  -- ⊢ eval (eval x (normalizedW 𝔽q β i)) (qMap 𝔽q β i) = eval x (normalizedW 𝔽q β (i + 1))
  rw [←Polynomial.eval_comp]
  rw [qMap_comp_normalizedW 𝔽q β i h_i_add_1]

/-- The composition `q⁽ⁱ⁻¹⁾ ∘ ... ∘ q⁽⁰⁾ ∘ X`. -/
noncomputable def qCompositionChain (i : Fin r) : L[X] :=
  match i with
  | ⟨0, _⟩ => X
  | ⟨k + 1, h_k_add_1⟩ => (qMap 𝔽q β ⟨k, by omega⟩).comp (qCompositionChain ⟨k, by omega⟩)

omit [DecidableEq L] [NeZero ℓ] [DecidableEq 𝔽q] h_Fq_char_prime hF₂ hβ_lin_indep h_β₀_eq_1 in
/-- Prove the equality between the recursive definition
of `qCompositionChain` and the Fin.foldl form. -/
lemma qCompositionChain_eq_foldl (i : Fin r) :
  qCompositionChain 𝔽q β (ℓ:=ℓ) (R_rate:=R_rate) i =
  Fin.foldl (n:=i) (fun acc j =>
    (qMap 𝔽q β ⟨j, by omega⟩).comp acc) (X) := by
  induction i using Fin.succRecOnSameFinType with
  | zero =>
    rw [qCompositionChain.eq_def]
    simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, Fin.foldl_zero]
    rfl
  | succ k k_h i_h =>
    rw [qCompositionChain.eq_def]
    have h_eq: ⟨k.val.succ, k_h⟩ = k + 1 := by
      rw [Fin.mk_eq_mk]
      rw [Fin.val_add_one']
      exact k_h
    simp only [h_eq.symm, Nat.succ_eq_add_one, Fin.eta]
    simp only [Fin.val_cast, Fin.foldl_succ_last, Fin.val_last, Fin.eta, Fin.val_castSucc]
    congr

omit [DecidableEq 𝔽q] [DecidableEq L] hF₂ in
/--
**Corollary 4.4.** For each `i ∈ {0, ..., r-1}`, we have `Ŵᵢ = q⁽ⁱ⁻¹⁾ ∘ ... ∘ q⁽⁰⁾`
(with the convention that for `i = 0`, this is just `X`).
-/
lemma normalizedW_eq_qMap_composition (ℓ R_rate : ℕ) (i : Fin r) :
    normalizedW 𝔽q β i = qCompositionChain 𝔽q β (ℓ:=ℓ) (R_rate:=R_rate) i :=
by
  -- We proceed by induction on i.
  induction i using Fin.succRecOnSameFinType with
  | zero =>
    -- Base case: i = 0
    -- We need to show `normalizedW ... 0 = qCompositionChain 0`.
    -- The RHS is `X` by definition of the chain.
    rw [qCompositionChain.eq_def]
    -- The LHS is `C (1 / eval (β 0) (W ... 0)) * (W ... 0)`.
    rw [normalizedW, W₀_eq_X, eval_X, h_β₀_eq_1.out, div_one, C_1, one_mul]
    rfl
  | succ k k_h i_h =>
    -- Inductive step: Assume the property holds for k, prove for k+1.
    -- The goal is `normalizedW ... (k+1) = qCompositionChain (k+1)`.
    -- The RHS is `(qMap k).comp (qCompositionChain k)` by definition.
    rw [qCompositionChain.eq_def]
    -- From Lemma 4.2, we know `normalizedW ... (k+1) = (qMap k).comp (normalizedW ... k)`.
    -- How to choose the rhs?
    have h_eq: ⟨k.val.succ, k_h⟩ = k + 1 := by
      rw [Fin.mk_eq_mk]
      rw [Fin.val_add_one']
      exact k_h
    simp only [h_eq.symm, Nat.succ_eq_add_one, Fin.eta]
    have h_res := qMap_comp_normalizedW 𝔽q β k k_h
    -- ⊢ normalizedW 𝔽q β ⟨↑k + 1, k_h⟩ = (qMap 𝔽q β k).comp (qCompositionChain 𝔽q β k)
    rw [←i_h]
    rw [h_res]
    simp only [h_eq]

/-- The vectors `y_j^{(i)} = Ŵᵢ(β_j)` for `j ∈ {i, ..., ℓ+R-1}`. -/
noncomputable def sDomainBasisVectors (i : Fin r) : Fin (ℓ + R_rate - i) → L :=
  fun k => (normalizedW 𝔽q β i).eval (β ⟨i + k.val, by omega⟩)

omit [DecidableEq 𝔽q] [NeZero ℓ] hF₂ h_β₀_eq_1 in
/-- The vectors `sDomainBasisVectors` are indeed elements of the subspace `sDomain`,
  `∀ i ∈ {0, ..., r-1}`. -/
lemma sDomainBasisVectors_mem_sDomain (i : Fin r) (k : Fin (ℓ + R_rate - i)) :
  sDomainBasisVectors 𝔽q β h_ℓ_add_R_rate i k
    ∈ sDomain 𝔽q β h_ℓ_add_R_rate i := by
  have h_i_add_k_lt_r : i + k.val < r := by
    omega
  have h_i_add_k_lt_ℓ_add_R_rate : i + k.val < ℓ + R_rate := by
    omega
  have h_i_add_k_lt_ℓ_add_R_rate : i + k.val < ℓ + R_rate := by
    omega
  simp_rw [sDomain, sDomainBasisVectors]
  -- The vector is `eval Ŵᵢ (β (i + k.val))`
  -- We must show it's in the image of U_{ℓ+R} under `eval Ŵᵢ`.
  -- This is true if the input `β (i + k.val)` is in `U_{ℓ+R}`.
  apply Submodule.mem_map_of_mem
  -- ⊢ β (i + ↑k) ∈ U 𝔽q β (ℓ + R_rate)
  have h_β_i_in_U: β ⟨i + k.val, h_i_add_k_lt_r⟩ ∈ β '' Set.Ico 0 ⟨ℓ + R_rate, h_ℓ_add_R_rate⟩ := by
    exact Set.mem_image_of_mem β (Set.mem_Ico.mpr ⟨by norm_num, by omega⟩)
  exact Submodule.subset_span h_β_i_in_U

/-- The S basis -/
def sBasis (i : Fin r) (h_i : i < ℓ + R_rate) : Fin (ℓ + R_rate - i) → L :=
  fun k => β ⟨i + k.val, by omega⟩

omit [NeZero r] [NeZero ℓ] [Field L] [Fintype L] [DecidableEq L] [Field 𝔽q] [Algebra 𝔽q L] in
lemma sBasis_range_eq (i : Fin r) (h_i : i < ℓ + R_rate) :
    β '' Set.Ico i ⟨ℓ + R_rate, h_ℓ_add_R_rate⟩
    = Set.range (sBasis β h_ℓ_add_R_rate i h_i):= by
  ext x
  constructor
  · intro hx -- hx : x ∈ β '' Set.Ico i ⟨ℓ + R_rate, h_ℓ_add_R_rate⟩
    -- ⊢ x ∈ Set.range fun k ↦ β ⟨↑i + ↑k, ⋯⟩
    rcases hx with ⟨j, hj, rfl⟩
    simp only [Set.mem_Ico] at hj
    simp only [Set.mem_range] -- ⊢ ∃ y : Fin (ℓ + R_rate - ↑i), β ⟨↑i + ↑y, ⋯⟩ = β j
    have h_j_sub_i: j.val - i.val < ℓ + R_rate - i.val := by
      apply Nat.lt_sub_of_add_lt
      rw [Nat.sub_add_cancel]
      · exact hj.2
      · omega
    use ⟨j - i, h_j_sub_i⟩
    unfold sBasis
    simp only
    have h_i_add_j_sub_i : i.val + (j.val - i.val) = j.val := by
      omega
    congr
  · intro hx -- hx : x ∈ Set.range fun k ↦ β ⟨↑i + ↑k, ⋯⟩
    -- ⊢ x ∈ β '' Set.Ico i ⟨ℓ + R_rate, h_ℓ_add_R_rate⟩
    rcases hx with ⟨j, hj, rfl⟩ -- hj : β ⟨↑i + ↑j, ⋯⟩ = x
    simp only [Set.mem_image, Set.mem_Ico]
    use ⟨i.val + j.val, by omega⟩
    constructor
    · -- ⊢ i ≤ ⟨↑i + ↑j, ⋯⟩ ∧ ⟨↑i + ↑j, ⋯⟩ < ⟨ℓ + R_rate, h_ℓ_add_R_rate⟩
      constructor
      · -- ⊢ i ≤ ⟨↑i + ↑j, ⋯⟩
        have h_j := j.2
        have h_i_add_j: i.val + j.val < ℓ + R_rate := by omega
        have h_i_add_j_lt_r: i.val + j.val < r := by omega
        apply Fin.mk_le_of_le_val
        conv_rhs => simp only -- remove ↑ in rhs
        omega
      · apply Fin.mk_lt_of_lt_val
        conv_rhs => simp only -- remove ↑ in rhs
        omega
    · rfl

omit [DecidableEq 𝔽q] [NeZero ℓ] hF₂ h_β₀_eq_1 in
/-- S⁽ⁱ⁾ is the image over `Wᵢ(X)` of the the subspace spanned by `{βᵢ, ..., β_{ℓ+R-1}}`.
  Usable range is `∀ i ∈ {0, ..., ℓ+R-1}`. -/
lemma sDomain_eq_image_of_upper_span (i : Fin r) (h_i : i < ℓ + R_rate) :
    let V_i := Submodule.span 𝔽q (Set.range (sBasis β h_ℓ_add_R_rate i h_i))
    let W_i_map := polyEvalLinearMap (normalizedW 𝔽q β i)
      (normalizedW_is_additive 𝔽q β i)
    sDomain 𝔽q β h_ℓ_add_R_rate i
    = Submodule.map W_i_map V_i :=
by
  -- Proof: U_{ℓ+R} is the direct sum of Uᵢ and Vᵢ.
  -- Any x in U_{ℓ+R} can be written as u + v where u ∈ Uᵢ and v ∈ Vᵢ.
  -- Ŵᵢ(x) = Ŵᵢ(u+v) = Ŵᵢ(u) + Ŵᵢ(v) = 0 + Ŵᵢ(v) = Ŵᵢ(v).
  -- So the image of U_{ℓ+R} is the same as the image of Vᵢ.

  -- Define V_i and W_i_map for use in the proof
  set V_i := Submodule.span 𝔽q (Set.range (sBasis β h_ℓ_add_R_rate i h_i))
  set W_i_map := polyEvalLinearMap (normalizedW 𝔽q β i)
    (normalizedW_is_additive 𝔽q β i)
  -- First, show that U_{ℓ+R} = U_i ⊔ V_i (direct sum)
  have h_span_supremum_decomposition : U 𝔽q β ⟨ℓ + R_rate, h_ℓ_add_R_rate⟩
    = U 𝔽q β i ⊔ V_i := by
    unfold U
    -- U_{ℓ+R} is the span of {β₀, ..., β_{ℓ+R-1}}
    -- U_i is the span of {β₀, ..., β_{i-1}}
    -- V_i is the span of {β_i, ..., β_{ℓ+R-1}}
    have h_ico : Set.Ico 0 ⟨ℓ + R_rate, h_ℓ_add_R_rate⟩
      = Set.Ico 0 i ∪ Set.Ico i ⟨ℓ + R_rate, h_ℓ_add_R_rate⟩ := by
      ext k
      simp only [Set.mem_Ico, Fin.zero_le, true_and, Set.mem_union]
      constructor
      · intro h
        by_cases hk : k < i
        · left; omega
        · right; exact ⟨Nat.le_of_not_lt hk, by omega⟩
      · intro h
        cases h with
        | inl h => exact Fin.lt_trans h h_i
        | inr h => exact h.2
    rw [h_ico, Set.image_union, Submodule.span_union]
    congr
    -- ⊢ β '' Set.Ico i (ℓ + R_rate)
    -- = Set.range (sBasis β (h_ℓ_add_R_rate:=h_ℓ_add_R_rate) i h_i)
    -- Now how that the image of Set.Ico i (ℓ + R_rate)
    -- (from the definition of U_{ℓ+R}) is the same as V_i
    rw [sBasis_range_eq β h_ℓ_add_R_rate i h_i]
  -- Now show that the image of U_{ℓ+R} under W_i_map is the same as the image of V_i
  rw [sDomain, h_span_supremum_decomposition, Submodule.map_sup]
  -- The image of U_i under W_i_map is {0} because W_i vanishes on U_i
  have h_U_i_image : Submodule.map W_i_map (U 𝔽q β i) = ⊥ := by
    -- Show that any element in the image is 0
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    -- x ∈ Submodule.map W_i_map (U 𝔽q β i) means x = W_i_map(y) for some y ∈ U_i
    rcases Submodule.mem_map.mp hx with ⟨y, hy, rfl⟩
    -- Show that W_i_map y = 0 for any y ∈ U_i
    have h_eval_zero : (normalizedW 𝔽q β i).eval y = 0 :=
      normalizedWᵢ_vanishing 𝔽q β i y hy
    exact h_eval_zero
  -- Combine the results: ⊥ ⊔ V = V
  rw [h_U_i_image]
  rw [bot_sup_eq]

/-- **Corollary 4.5.** The set `{Ŵᵢ(βᵢ), ..., Ŵᵢ(β_{ℓ+R-1})}` is an `𝔽q`-basis for `S⁽ⁱ⁾`. -/
noncomputable def sDomain_basis (i : Fin r) (h_i : i < ℓ + R_rate) :
    Basis (Fin (ℓ + R_rate - i)) 𝔽q (
      sDomain 𝔽q β h_ℓ_add_R_rate i) := by
  -- Let V_i be the "upper" subspace spanned by {βᵢ, ..., β_{ℓ+R-1}}.
  let V_i := Submodule.span 𝔽q (Set.range (sBasis β h_ℓ_add_R_rate i h_i))
  -- Let W_i_map be the linear map given by evaluating the polynomial Ŵᵢ.
  let W_i_map := polyEvalLinearMap (normalizedW 𝔽q β i) (
      normalizedW_is_additive 𝔽q β i)
  have h_disjoint : Disjoint (U 𝔽q β i) V_i := by
    -- Uᵢ is span of β over Ico 0 i
    -- Vᵢ is span of β over Ico i (ℓ + R_rate)
    -- The index sets are disjoint.
    have h_set_disjoint : Disjoint (Set.Ico 0 i) (Set.Ico i ⟨ℓ + R_rate, h_ℓ_add_R_rate⟩) := by
      simp only [Set.disjoint_iff, Set.subset_empty_iff]
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Ico, Fin.zero_le, true_and,
        Set.mem_empty_iff_false, iff_false, not_and, not_lt]
      intro hx hi
      omega
    -- Since β is linearly independent, the spans of its images over disjoint sets are disjoint.
    unfold V_i
    have h_res := hβ_lin_indep.out.disjoint_span_image h_set_disjoint
    rw [sBasis_range_eq β h_ℓ_add_R_rate i h_i] at h_res
    exact h_res
  have h_ker_eq_U : LinearMap.ker W_i_map = U 𝔽q β i := by
    rw [kernel_normalizedW_eq_U 𝔽q β i]
  -- The vectors {βᵢ, ...} form a basis for Vᵢ because β is linearly independent.
  let V_i_basis : Basis (Fin (ℓ + R_rate - i)) 𝔽q V_i :=
    Basis.span (by
      -- This is the proof of linear independence for the vectors {βᵢ, ...}.
      -- It follows because they are a subset of the LI family β.
      have h_sub_li : LinearIndependent 𝔽q (
          v := fun (k : Fin (ℓ + R_rate - i)) => β ⟨i + k.val, by omega⟩) :=
        hβ_lin_indep.out.comp (fun (k : Fin (ℓ + R_rate - i))
          => ⟨i + k.val, by omega⟩) (by  -- ⊢ Function.Injective fun k ↦ ⟨↑i + ↑k, ⋯⟩
          intro k₁ k₂ h_eq
          simp at h_eq
          apply Fin.eq_of_val_eq
          omega
        )
      exact h_sub_li)
  -- We construct the isomorphism between Vᵢ and S⁽ⁱ⁾.
  -- S⁽ⁱ⁾ is the image of Vᵢ under W_i_map, and the map is injective on Vᵢ.
  set S_i := sDomain 𝔽q β h_ℓ_add_R_rate i
  let iso : V_i ≃ₗ[𝔽q] S_i :=
    LinearEquiv.ofBijective
      (LinearMap.codRestrict S_i (W_i_map.comp (Submodule.subtype V_i))
        (by -- ⊢ ∀ (c : ↥V_i), (W_i_map ∘ₗ V_i.subtype) c ∈ S_i
          intro x
          -- ⊢ (W_i_map ∘ₗ V_i.subtype) x ∈ S_i
          have h_x_in_S_i : (W_i_map.comp (Submodule.subtype V_i)) x ∈ S_i := by
            simp only [LinearMap.coe_comp, Submodule.coe_subtype, Function.comp_apply, S_i]
            rw [sDomain_eq_image_of_upper_span 𝔽q β h_ℓ_add_R_rate i h_i]
            exact
              Submodule.apply_coe_mem_map
                (polyEvalLinearMap (normalizedW 𝔽q β i)
                  (normalizedW_is_additive 𝔽q β i))
                x
          exact h_x_in_S_i
        )) (by
        -- ⊢ Function.Bijective ⇑(LinearMap.codRestrict S_i (W_i_map ∘ₗ V_i.subtype) ⋯)
          constructor
          · -- INJECTIVITY
            intro v1 v2 h_v1_v2
            -- ⊢ v1 = v2
          -- First, simplify the hypothesis by unpacking the map definitions.
            simp only [LinearMap.codRestrict_apply, LinearMap.coe_comp, Submodule.coe_subtype,
              Function.comp_apply, Subtype.ext_iff] at h_v1_v2
            -- The hypothesis is now `W_i_map ↑v1 = W_i_map ↑v2`.
            -- By linearity, this is equivalent to `W_i_map (↑v1 - ↑v2) = 0`.
            rw [← sub_eq_zero, ← LinearMap.map_sub] at h_v1_v2
            -- To show v1 = v2, we show v1 - v2 = 0.
            -- coercion from a subtype is injective => we show the coerced difference is 0
            apply Subtype.ext
            -- The element `↑(v1 - v2)` is in the kernel of `W_i_map`.
            have h_mem_ker : ↑(v1 - v2) ∈ LinearMap.ker W_i_map := h_v1_v2
            -- The kernel of the evaluation map is the vanishing subspace `Uᵢ`.
            -- Add this before the have h_mem_U line:
            have h_mem_U : ↑(v1 - v2) ∈ U 𝔽q β i := h_ker_eq_U ▸ h_mem_ker
            -- The element `v1 - v2` is in `Vᵢ` since it's a submodule.
            have h_mem_V : ↑(v1 - v2) ∈ V_i := Submodule.sub_mem V_i v1.property v2.property
            -- Thus, the element is in the intersection of `Uᵢ` and `Vᵢ`.
            -- Thus, the element is in the intersection of `Uᵢ` and `Vᵢ`.
            have h_mem_inf : ↑(v1 - v2) ∈ (U 𝔽q β i) ⊓ V_i :=
              Submodule.mem_inf.mpr ⟨h_mem_U, h_mem_V⟩
            -- The subspaces `Uᵢ` and `Vᵢ` are disjoint because they are spanned by
            -- disjoint subsets of the linearly independent set `β`.

            -- Since the intersection is the trivial subspace {0}, our element must be 0.
            rw [h_disjoint.eq_bot] at h_mem_inf
            simp only [Submodule.mem_bot] at h_mem_inf
            simp only [AddSubgroupClass.coe_sub] at h_mem_inf
            rw [sub_eq_zero] at h_mem_inf
            exact h_mem_inf
          · -- SURJECTIVITY
            -- We need to prove that for any `y ∈ S_i`,
            -- there exists an `x ∈ V_i` such that `W_i_map x = y`.
            -- This is essentially the definition of the image of a map.
            -- The goal is to show `Submodule.map W_i_map V_i = S_i`.
            intro y
            -- `y` is an element of `S_i` (which is a subtype).
            have h_y_in_image : y.val ∈ Submodule.map W_i_map V_i := by
              have h_y := y.property
              -- From the lemma `sDomain_eq_image_of_upper_span`,
              -- we know that S_i is *exactly* the image of V_i under W_i_map.
              unfold W_i_map V_i
              have h_S_i: S_i = Submodule.map W_i_map V_i := by
                unfold S_i
                rw [sDomain_eq_image_of_upper_span 𝔽q β h_ℓ_add_R_rate i h_i]
              rw [←h_S_i]
              exact h_y
            rcases h_y_in_image with ⟨x, hx_in_Vi, hx_maps_to_y⟩
            -- We have found our `x` in `V_i`.
            -- We need to lift `x` from the submodule `V_i` to a term of the subtype `↥V_i`.
            use ⟨x, hx_in_Vi⟩
            apply Subtype.ext
            exact hx_maps_to_y
        )
  -- A linear isomorphism maps a basis to a basis.
  -- We map the basis of Vᵢ through our isomorphism to get the desired basis for S⁽ⁱ⁾.
  exact V_i_basis.map iso

omit [DecidableEq 𝔽q] [NeZero ℓ] hF₂ h_β₀_eq_1 in
lemma get_sDomain_basis (i : Fin r) (h_i : i < ℓ + R_rate) :
    ∀ (k : Fin (ℓ + R_rate - i)),
    (sDomain_basis 𝔽q β h_ℓ_add_R_rate
      i (by omega)) k = eval (β ⟨i + k.val, by omega⟩) (normalizedW 𝔽q β i) := by
  intro k
  unfold sDomain_basis
  simp only [polyEvalLinearMap, eq_mpr_eq_cast, cast_eq, Basis.map_apply,
    LinearEquiv.ofBijective_apply, LinearMap.codRestrict_apply, LinearMap.coe_comp,
    LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_subtype, Function.comp_apply]
  congr -- ⊢ ↑((Basis.span ⋯) k) = β ⟨↑i + ↑k, ⋯⟩
  rw [Basis.span_apply]
  dsimp only [sBasis]

omit [DecidableEq 𝔽q] [NeZero ℓ] hF₂ h_β₀_eq_1 in
lemma get_sDomain_first_basis_eq_1 (i : Fin r) (h_i : i < ℓ + R_rate) :
    (sDomain_basis 𝔽q β h_ℓ_add_R_rate
    i (by omega)) ⟨0, by omega⟩ = (1: L) := by
  rw [get_sDomain_basis]
  simp only [add_zero, Fin.eta]
  exact normalizedWᵢ_eval_βᵢ_eq_1 𝔽q β

noncomputable instance fintype_sDomain (i : Fin r) :
  Fintype (sDomain 𝔽q β h_ℓ_add_R_rate i) := by
  exact Fintype.ofFinite (sDomain 𝔽q β h_ℓ_add_R_rate i)

omit [DecidableEq 𝔽q] [NeZero ℓ] hF₂ h_β₀_eq_1 in
-- The cardinality of the subspace `S⁽ⁱ⁾` is `|𝔽q|^(l + R - i)`, which follows from its dimension.
lemma sDomain_card (i : Fin r) (h_i : i < ℓ + R_rate) :
    Fintype.card (sDomain 𝔽q β h_ℓ_add_R_rate i) = (Fintype.card 𝔽q)^(ℓ + R_rate - i) := by
  -- The cardinality of a vector space V is |F|^(dim V).
  rw [Module.card_eq_pow_finrank (K := 𝔽q) (V := sDomain 𝔽q β h_ℓ_add_R_rate i)]
  -- We need to show that the finrank of sDomain is ℓ + R_rate - i
  -- This follows from the fact that sDomain has a basis of size ℓ + R_rate - i
  -- We can use the basis we constructed
  let b := sDomain_basis 𝔽q β h_ℓ_add_R_rate i h_i
  -- The finrank equals the cardinality of the basis
  rw [Module.finrank_eq_card_basis b]
  -- The basis has cardinality ℓ + R_rate - i
  simp only [Fintype.card_fin]

noncomputable section DomainBijection
/-!
## Domain-Index Bijections

Bijections between elements in `S^(i)` and `Fin (2^(ℓ + R_rate - i))` for use in
Binary Basefold protocol implementations.
-/

def splitPointIntoCoeffs (i : Fin r) (h_i : i < ℓ + R_rate)
  (x : sDomain 𝔽q β h_ℓ_add_R_rate i) :
  Fin (ℓ + R_rate - i.val) → ℕ := fun j =>
    if ((sDomain_basis 𝔽q β
    h_ℓ_add_R_rate i h_i).repr x j = 0) then
      0 else 1

/-- Convert an element of `S^(i)` to its index in `Fin (2^(ℓ + R_rate - i))`.
This uses the basis representation of elements in the domain.
This requires `𝔽q = 𝔽₂` for the bijection to work. -/
noncomputable def sDomainToFin (i : Fin r) (h_i : i < ℓ + R_rate)
  (x : sDomain 𝔽q β h_ℓ_add_R_rate i) :
  Fin (2^(ℓ + R_rate - i.val)) := by
  apply Nat.binaryFinMapToNat (n:=ℓ + R_rate - i.val)
    (m:=splitPointIntoCoeffs 𝔽q β h_ℓ_add_R_rate i h_i x) (by
    intro j
    simp only [splitPointIntoCoeffs];
    split_ifs
    · norm_num
    · norm_num
  )

def finToBinaryCoeffs (i : Fin r) (idx : Fin (2 ^ (ℓ + R_rate - i.val))) :
  Fin (ℓ + R_rate - i.val) → 𝔽q := fun j =>
    if (Nat.getBit (k:=j) (n:=idx)) = 1 then (1 : 𝔽q) else (0 : 𝔽q)

omit [NeZero ℓ] h_β₀_eq_1 in
lemma finToBinaryCoeffs_sDomainToFin (i : Fin r) (h_i : i < ℓ + R_rate)
    (x : sDomain 𝔽q β h_ℓ_add_R_rate i) :
    let pointFinIdx := (sDomainToFin 𝔽q β h_ℓ_add_R_rate i h_i) x
    finToBinaryCoeffs 𝔽q (i := i) (idx :=pointFinIdx) =
    (sDomain_basis 𝔽q β
    h_ℓ_add_R_rate i h_i).repr x:= by
  simp only
  ext j
  -- Unfold the definitions to get to the core logic
  dsimp [sDomainToFin, finToBinaryCoeffs, splitPointIntoCoeffs]
  -- `Nat.getBit` is the inverse of `Nat.binaryFinMapToNat`
  rw [Nat.getBit_of_binaryFinMapToNat]
  -- Let `c` be the j-th coefficient we are considering
  set c := (sDomain_basis 𝔽q β
    h_ℓ_add_R_rate i h_i).repr x j
  -- Since the field has card 2, `c` must be 0 or 1
  have hc : c = 0 ∨ c = 1 := by exact 𝔽q_element_eq_zero_or_eq_one 𝔽q c
    -- exact ((Fintype.card_eq_two_iff _).mp h_Fq_card_eq_2).right c
  -- We can now split on whether c is 0 or 1
  rcases hc with h_c_zero | h_c_one
  · -- Case 1: The coefficient is 0
    simp only [Fin.is_lt, ↓reduceDIte, Fin.eta, h_c_zero, ite_eq_right_iff, one_ne_zero, imp_false,
      ne_eq]
    unfold splitPointIntoCoeffs
    simp only [ite_eq_right_iff, zero_ne_one, imp_false, Decidable.not_not]
    omega
  · -- Case 2: The coefficient is 1
    simp only [Fin.is_lt, ↓reduceDIte, Fin.eta, h_c_one, ite_eq_left_iff, zero_ne_one, imp_false,
      Decidable.not_not]
    unfold splitPointIntoCoeffs
    simp only [ite_eq_right_iff, zero_ne_one, imp_false, ne_eq]
    change ¬(c) = 0
    rw [h_c_one]
    exact one_ne_zero

/-- Convert an index in `Fin (2 ^ (ℓ + R_rate - i))` to an element of `S^(i)`.
This is the inverse of `sDomainToFin`. -/
noncomputable def finToSDomain (i : Fin r) (h_i : i < ℓ + R_rate)
  (idx : Fin (2 ^ (ℓ + R_rate - i.val))) :
  sDomain 𝔽q β h_ℓ_add_R_rate i := by
  -- Get the basis
  let basis := sDomain_basis 𝔽q
    β h_ℓ_add_R_rate i h_i
  -- Convert the index to binary coefficients
  let coeffs : Fin (ℓ + R_rate - i.val) → 𝔽q := finToBinaryCoeffs 𝔽q i idx
  -- Construct the element using the basis
  exact basis.repr.symm ((Finsupp.equivFunOnFinite).symm coeffs)
  -- Finsupp.onFinset
    -- (Set.toFinset (Set.univ : Set (Fin (ℓ + R_rate - i.val))))
    -- coeffs (by simp only [ne_eq, Set.toFinset_univ, Finset.mem_univ, implies_true]))

/-- The bijection between `S^(i)` and `Fin (2^(ℓ + R_rate - i))`.
This requires `𝔽q = 𝔽₂` for the bijection to work properly. -/
noncomputable def sDomainFinEquiv (i : Fin r) (h_i : i < ℓ + R_rate)
:
  (sDomain 𝔽q β h_ℓ_add_R_rate i) ≃
  Fin (2^(ℓ + R_rate - i.val)) := by
  -- Use the fact that the cardinalities match
  have h_card_eq : Fintype.card (sDomain 𝔽q
    β h_ℓ_add_R_rate i) = Fintype.card (Fin (2^(ℓ + R_rate - i.val))) := by
    rw [sDomain_card 𝔽q β h_ℓ_add_R_rate i h_i, hF₂.out]
    simp only [Fintype.card_fin]
  exact {
    toFun := sDomainToFin 𝔽q β h_ℓ_add_R_rate i h_i,
    invFun := finToSDomain 𝔽q β h_ℓ_add_R_rate i h_i,
    left_inv := fun x => by
      let basis := sDomain_basis 𝔽q β
        h_ℓ_add_R_rate i h_i
      let coeffs := basis.repr x
      apply (LinearEquiv.injective basis.repr)
      ext j
      simp only [finToSDomain, Basis.repr_symm_apply]
      rw [finToBinaryCoeffs_sDomainToFin]
      simp only [Finsupp.equivFunOnFinite_symm_coe, Basis.linearCombination_repr]
    right_inv := fun y => by
      apply Fin.eq_of_val_eq
      -- Unfold definitions to get to the `binaryFinMapToNat` expression.
      unfold sDomainToFin splitPointIntoCoeffs
      apply Nat.eq_iff_eq_all_getBits.mpr
      intro k
      rw [Nat.getBit_of_binaryFinMapToNat]
      by_cases h_k : k < ℓ + R_rate - ↑i
      · simp only [h_k, ↓reduceDIte]
        simp only [finToSDomain, Basis.repr_symm_apply, Basis.repr_linearCombination,
          Finsupp.equivFunOnFinite_symm_apply_apply]
        simp only [finToBinaryCoeffs, ite_eq_right_iff, one_ne_zero, imp_false, ite_not]
        rw  [Nat.getBit_of_lt_two_pow (k:=k) (a:=y)]
        simp only [h_k, ↓reduceIte]
        have h_getBit_lt_2: k.getBit y < 2 := by exact Nat.getBit_lt_2
        interval_cases k.getBit y
        · simp only [zero_ne_one, ↓reduceIte]
        · simp only [↓reduceIte]
      · rw [Nat.getBit_of_lt_two_pow (k:=k) (a:=y)]
        simp only [h_k, ↓reduceDIte, ↓reduceIte]
  }

omit [NeZero ℓ] h_β₀_eq_1 in
theorem sDomainFin_bijective (i : Fin r) (h_i : i < ℓ + R_rate)
: Function.Bijective
  (sDomainFinEquiv 𝔽q β h_ℓ_add_R_rate i h_i) := by
  exact
    Equiv.bijective
      (sDomainFinEquiv 𝔽q β h_ℓ_add_R_rate i h_i)

end DomainBijection

/-! ### 2. Intermediate Novel Polynomial Bases `Xⱼ⁽ⁱ⁾`  and evaluation polynomials `P⁽ⁱ⁾`-/

/-- `∀ i ∈ {0, ..., ℓ}`, The `i`-th order subspace vanishing polynomials `Ŵₖ⁽ⁱ⁾`,
`Ŵₖ⁽ⁱ⁾ := q⁽ⁱ⁺ᵏ⁻¹⁾ ∘ ⋯ ∘ q⁽ⁱ⁾` for `k ∈ {1, ..., ℓ - i -1}`, and `X` for `k = 0`.
-- k ∈ {0, ..., ℓ-i-1}. Note that when `i = ℓ`, `k ∈ Fin 0` does not exists.
-/
noncomputable def intermediateNormVpoly
    -- Assuming you have this hypothesis available from the context:
    (i: Fin r) {k : ℕ} (h_k : i.val + k ≤ ℓ) : L[X] :=
  -- This definition requires strict order
  Fin.foldl (n:=k) (fun acc j =>
    (qMap 𝔽q β ⟨(i : ℕ) + (j : ℕ), by omega⟩).comp acc) (X)

omit [DecidableEq L] [NeZero ℓ] [DecidableEq 𝔽q] hF₂ hβ_lin_indep h_β₀_eq_1 in
lemma intermediateNormVpoly_eval_is_linear_map (i : Fin r) {k : ℕ} (h_k : i.val + k ≤ ℓ) :
  IsLinearMap 𝔽q (fun x : L =>
    (intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate i h_k).eval x) := by
  -- We proceed by induction on k, the number of compositions.
  -- induction k using Fin.induction with
  induction k with
  | zero => -- For k=0, the polynomial is just `X`.
    unfold intermediateNormVpoly
    simp only [Fin.foldl_zero]
    -- The evaluation map `fun x => X.eval x` is just the identity function `id`.
    simp only [Polynomial.eval_X]
    exact { map_add := fun x ↦ congrFun rfl, map_smul := fun c ↦ congrFun rfl }
  | succ k' ih =>
    unfold intermediateNormVpoly
    simp only [intermediateNormVpoly] at ih
    conv =>
      enter [2, x, 2];
      simp only [Fin.val_succ]
      rw [Fin.foldl_succ_last]
    simp only [Fin.val_last, Fin.val_castSucc, eval_comp]
    set q_eval_is_linear_map := linear_map_of_comp_to_linear_map_of_eval
      (f:=qMap 𝔽q β ⟨i + k', by omega⟩) (h_f_linear := qMap_is_linear_map 𝔽q β
      (i := ⟨i + k', by omega⟩))
    set innerFold := fun x: L ↦ eval x (Fin.foldl (↑k') (fun acc j ↦ (qMap 𝔽q β
      ⟨↑i + ↑j, by omega⟩).comp acc) X)
    set qmap_eval := fun x : L => (qMap 𝔽q β ⟨i + k', by omega⟩).eval x
    set isLinearMap_innerFold : IsLinearMap 𝔽q innerFold := ih (h_k := by omega)
    set isLinearMap_qmap_eval : IsLinearMap 𝔽q qmap_eval := q_eval_is_linear_map
    change IsLinearMap 𝔽q fun x ↦ qmap_eval.comp innerFold x
    exact {
      map_add := fun x y => by
        dsimp only [Function.comp_apply]
        rw [isLinearMap_innerFold.map_add, isLinearMap_qmap_eval.map_add]
      map_smul := fun c x => by
        dsimp only [Function.comp_apply]
        rw [isLinearMap_innerFold.map_smul, isLinearMap_qmap_eval.map_smul]
    }

omit [DecidableEq 𝔽q] [NeZero ℓ] [DecidableEq L] hF₂ in
-- Ŵₖ⁽⁰⁾(X) = Ŵ(X)
theorem base_intermediateNormVpoly
  (k : Fin r) (h_k : k.val ≤ ℓ) :
  intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate 0 (k := k)
    (h_k := by simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]; omega) =
  normalizedW 𝔽q β k := by
  classical
  unfold intermediateNormVpoly
  simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]
  rw [normalizedW_eq_qMap_composition 𝔽q β ℓ R_rate k]
  rw [qCompositionChain_eq_foldl 𝔽q β]

omit [DecidableEq L] [NeZero ℓ] [DecidableEq 𝔽q] h_Fq_char_prime h_β₀_eq_1 in
/-- The natDegree of `Ŵₖ⁽ⁱ⁾(X)` is `2^k`. -/
lemma natDegree_intermediateNormVpoly (i : Fin r) {k : ℕ} (h_k : i.val + k ≤ ℓ) :
  (intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate i (k := k) (h_k := h_k)).natDegree = 2 ^ k := by
  induction k with
  | zero =>
    -- Base Case: X
    unfold intermediateNormVpoly
    simp only [Fin.foldl_zero, natDegree_X, pow_zero]
  | succ k' ih =>
    -- Inductive Step
    unfold intermediateNormVpoly
    -- simp only [Fin.val_succ]
    rw [Fin.foldl_succ_last]
    simp only [Fin.val_last, Fin.val_castSucc]
    -- 1. Apply natDegree_comp
    rw [Polynomial.natDegree_comp]
    -- 2. Handle qMap part
    rw [natDegree_qMap]
    -- 3. Handle Accumulator part (use IH)
    -- We match the accumulator definition to the IH term
    have h_acc_eq_prev :
      Fin.foldl (↑k') (fun acc j ↦ (qMap 𝔽q β ⟨↑i + ↑j, by omega⟩).comp acc) X
      = intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate i (k := k') (h_k := by omega) := rfl
    unfold intermediateNormVpoly at ih
    let ih_prev := ih (h_k := by omega)
    rw [h_acc_eq_prev] at ih_prev ⊢
    rw [ih_prev]
    -- 4. Arithmetic: 2 * 2^k' = 2^(k'+1)
    rw [pow_succ']

omit [DecidableEq L] [NeZero ℓ] [DecidableEq 𝔽q] h_Fq_char_prime h_β₀_eq_1 in
/-- The degree of `Ŵₖ⁽ⁱ⁾(X)` is `2^k`. -/
lemma degree_intermediateNormVpoly (i : Fin r) {k : ℕ} (h_k : i.val + k ≤ ℓ) :
  (intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate i (k := k) (h_k := h_k)).degree = 2 ^ k := by
  rw [Polynomial.degree_eq_natDegree]
  · rw [natDegree_intermediateNormVpoly]; norm_cast
  · apply Polynomial.ne_zero_of_natDegree_gt (n := 0);
    rw [natDegree_intermediateNormVpoly]; simp only [Nat.ofNat_pos, pow_pos]

-- i = 0->l: Ŵᵢ = q(i-1) ∘ ⋯ ∘ q(0)
-- Ŵᵢ is actually Ŵᵢ⁽⁰⁾ => deg(Ŵᵢ) = 2^i = |Uᵢ|, and it vanishes on Uᵢ = Uᵢ⁽⁰⁾ = ⟨β₀, ..., β_{i-1}⟩

-- `q⁽ⁱ⁾(X) := ( Wᵢ(βᵢ)^{2} / W_{i+1}(β_{i+1}) ) ⬝ X ⬝ (X+1)` => deg(q⁽ⁱ⁾) = 2 = |𝔽q|
-- => each composition of q⁽ⁱ⁾(X) brings a multiplicity of |𝔽q| for the degree
-- => k times of composition of q⁽ⁱ⁾(X) brings a multiplicity of |𝔽q|^k for the degree

-- q⁽ⁱ⁾ ∘ Ŵᵢ⁽⁰⁾ = Ŵᵢ+1⁽⁰⁾
-- Ŵₖ⁽ⁱ⁾ := q⁽ⁱ⁺ᵏ⁻¹⁾ ∘ ⋯ ∘ q⁽ⁱ⁾: this receives an element at space S⁽ⁱ⁾
-- and returns an element at space S⁽ⁱ⁺ᵏ⁾ => go through k subspaces in transit (fold k times)
-- => deg(Ŵₖ⁽ⁱ⁾) => |𝔽q|^k, vanishes on the |𝔽q|^k-size subspace Uₖ⁽ⁱ⁾ = ⟨β_{i}, ..., β_{i+k-1}⟩???
  -- S⁽ⁱ⁾ := ⟨Ŵᵢ(βᵢ), ..., Ŵᵢ(β_{ℓ+R-1})⟩ => size of S⁽ⁱ⁾ = 2^(ℓ+R-i)
  -- q⁽ⁱ⁾(S⁽ⁱ⁾) = S⁽ⁱ⁺¹⁾

omit [Fintype L] [DecidableEq L] in
theorem Polynomial.foldl_comp (n : ℕ) (f : Fin n → L[X]) : ∀ initInner initOuter: L[X],
    Fin.foldl (n:=n) (fun acc j => (f j).comp acc) (initOuter.comp initInner)
    = (Fin.foldl (n:=n) (fun acc j => (f j).comp acc) (initOuter)).comp initInner := by
  induction n with
  | zero =>
    simp only [Fin.foldl_zero, implies_true]
  | succ n' ih =>
    intro iIn iOut
    rw [Fin.foldl_succ, Fin.foldl_succ]
    set g := fun i : Fin n' => f i.succ
    have h_left := ih g (iOut.comp iIn) (f 0)
    rw [h_left]
    have h_right := ih g iOut (f 0)
    rw [h_right]
    rw [comp_assoc]

omit [Fintype L] [DecidableEq L] in
theorem Polynomial.comp_same_inner_eq_if_same_outer (f g : L[X]) (h_f_eq_g : f = g) :
  ∀ x, f.comp x = g.comp x := by
  intro x
  rw [h_f_eq_g]

omit [DecidableEq L] [NeZero ℓ] [DecidableEq 𝔽q] h_Fq_char_prime hF₂ hβ_lin_indep h_β₀_eq_1 in
-- ∀ i ∈ {0, ..., ℓ-1}, ∀ k ∈ {0, ..., ℓ-i-2}, `Ŵₖ₊₁⁽ⁱ⁾ = Ŵₖ⁽ⁱ⁺¹⁾ ∘ q⁽ⁱ⁾`
theorem intermediateNormVpoly_comp_qmap (i : Fin r)
    {destIdx : Fin r} (h_destIdx : destIdx = i.val + 1)
    (k : ℕ) (h_k : i.val + k + 1 ≤ ℓ) :
    -- corresponds to intermediateNormVpoly_comp where `k = k, l = 1`
    intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate (i := i) (k := k + 1) (h_k := by omega)=
    (intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate (i := destIdx)
      (k := k) (h_k := by omega)).comp (qMap 𝔽q β i) := by
  unfold intermediateNormVpoly
  -- simp only -- Fin.foldl (↑k+1) ... = Fin.foldl (↑k+1) ...
  rw [Fin.foldl_succ] -- convert Fin.foldl (↑k+1) ... into (Fin.foldl (↑k) ...).comp (init value)
  simp only [Fin.val_succ, Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero, comp_X]
  conv_lhs =>
    rw [←X_comp (p:=qMap 𝔽q β ⟨↑i, by omega⟩)]
    rw [Polynomial.foldl_comp]
  congr -- convert Fin.foldl equality into equality of accumulator functions
  -- ⊢ (fun acc j ↦ (qMap 𝔽q β ⟨↑i + (↑j + 1), ⋯⟩).comp acc)
  -- = fun acc j ↦ (qMap 𝔽q β ⟨↑(i + 1) + ↑j, ⋯⟩).comp acc
  funext acc j
  have h_id_eq: i.val + (j.val + 1) = i.val + 1 + j.val := by omega
  simp_rw [h_id_eq]
  simp only [h_destIdx]

/-- The clean replacement for Fin-based recursion.
    We recurse on the Nat value `i`, carrying the proof `h` along. -/
def Nat.boundedRecOn {r : ℕ} {motive : (k : ℕ) → k < r → Sort _}
    (i : ℕ) (h_i : i < r) -- The loose index and its bound
    (zero : motive 0 (by omega))
    (succ : ∀ k (h_next : k + 1 < r), motive k (by omega) → motive (k + 1) h_next)
    : motive i h_i :=
  match i with
  | 0 => zero
  | k + 1 =>
    -- 1. We know k + 1 < r, so k < r must hold.
    have h_k : k < r := by omega
    -- 2. Compute the previous value recursively
    let prev := Nat.boundedRecOn k h_k zero succ
    -- 3. Apply the success step
    succ k h_i prev

omit [DecidableEq L] [NeZero ℓ] [DecidableEq 𝔽q] h_Fq_char_prime hF₂ hβ_lin_indep h_β₀_eq_1 in
theorem intermediateNormVpoly_comp (i : Fin r) {destIdx : Fin r}
  {k l : ℕ} (h_destIdx : destIdx = i.val + k)
  (h_k : i.val + k ≤ ℓ) (h_l : i.val + k + l ≤ ℓ) :
  intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate (i := i) (k:=k + l) (h_k := by omega) =
    (intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate (i := destIdx) (k:=l) (h_k := by omega)).comp (
  intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate (i := i) (k:=k) (h_k := by omega)) := by
    -- (l : Fin (ℓ - (i.val + k.val) + 1)) :
  induction l with
  | zero =>
    simp only [add_zero]
    have h_eq_X : intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate (i := destIdx)
      (k := 0) (h_k := by omega) = X := by
      simp only [intermediateNormVpoly, Fin.foldl_zero]
    simp only [h_eq_X, X_comp]
  | succ j ih =>
      -- Inductive case: l = j + 1
      -- Following the pattern from concreteTowerAlgebraMap_assoc:
      -- A = |i| --- (k) --- |i+k| --- (j+1) --- |i+k+j+1|
      -- Proof: A = (j+1) ∘ (k) (direct) = ((1) ∘ (j)) ∘ (k) (succ decomposition)
      --        = (1) ∘ ((j) ∘ (k)) (associativity) = (1) ∘ (jk) (induction hypothesis)
      have h_left := ih (h_l := by omega)
      unfold intermediateNormVpoly at ⊢ h_left
      conv_lhs =>
        simp only [←Nat.add_assoc (n:=k) (m:=j) (k:=1)]
        simp only [Fin.cast_eq_self]
        rw [Fin.foldl_succ_last] -- split the outer comp
        simp only [Fin.val_last, Fin.val_castSucc]
        rw [h_left]
        simp only [←Nat.add_assoc (n:=i.val) (m:=k) (k:=j)]
        simp only [h_destIdx]
      conv_rhs =>
        rw [Fin.foldl_succ_last] -- split the outer comp
        simp only [Fin.val_last, Fin.val_castSucc]
        simp only [h_destIdx]
      rw [Polynomial.comp_assoc]

/-- Iterated quotient map W_k⁽ⁱ⁾: Maps a point from S⁽ⁱ⁾ to S⁽ⁱ⁺ᵏ⁾ by evaluating
the intermediate norm vanishing polynomial at that point. This one mainly proves that
the `intermediateNormVpoly` works with points in the restricted sDomains,
instead of the whole field L.
-/
noncomputable def iteratedQuotientMap [NeZero ℓ] (i : Fin r) {destIdx : Fin r} {k : ℕ}
    (h_destIdx : destIdx = i.val + k) (h_destIdx_le : destIdx.val ≤ ℓ)
    (x : (sDomain 𝔽q β h_ℓ_add_R_rate) i) :
    (sDomain 𝔽q β h_ℓ_add_R_rate) destIdx := by
  let quotient_poly := intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate (i := i) (k := k) (h_k := by omega)
  let y := quotient_poly.eval (x.val : L)
  have h_x_mem : x.val ∈ sDomain 𝔽q β h_ℓ_add_R_rate i := x.property
  have h_mem : y ∈ sDomain 𝔽q β h_ℓ_add_R_rate destIdx := by
    unfold sDomain at h_x_mem
    simp only [Submodule.mem_map] at h_x_mem
    obtain ⟨u, hu_mem, hu_eq⟩ := h_x_mem
    have h_comp_eq : quotient_poly.comp (normalizedW 𝔽q β i)
      = normalizedW 𝔽q β destIdx := by
      simp only [quotient_poly]
      rw [←base_intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate (k:=i)]
      · rw [←base_intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate (k:=destIdx)]
        · have h_comp := intermediateNormVpoly_comp 𝔽q β h_ℓ_add_R_rate (i := 0)
            (k:=i) (l:=k) (destIdx := i) (h_destIdx := by
              simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]) (h_k := by
                simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]; omega) (h_l := by
                simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]; omega)
          simp only at h_comp
          convert h_comp.symm
        · omega
      · omega
    -- Now we can show membership
    unfold sDomain
    simp only [Submodule.mem_map]
    use u
    constructor
    · exact hu_mem
    · -- ⊢ (polyEvalLinearMap (normalizedW 𝔽q β ⟨↑i + k, ⋯⟩) ⋯) u = y
      rw [eq_comm]
      calc y = quotient_poly.eval (x.val) := rfl
        _ = quotient_poly.eval ((normalizedW 𝔽q β i).eval u) := by
          rw [← hu_eq]; congr
        _ = (quotient_poly.comp (normalizedW 𝔽q β i)).eval u := by
          rw [Polynomial.eval_comp]
        _ = (normalizedW 𝔽q β destIdx).eval u := by rw [h_comp_eq]
  exact ⟨y, h_mem⟩

omit [DecidableEq 𝔽q] hF₂ in
lemma iteratedQuotientMap_congr_k
    (i : Fin r) {destIdx : Fin r} {k₁ k₂ : ℕ}
    (hk : k₁ = k₂)
    (h_destIdx₁ : destIdx.val = i.val + k₁)
    (h_destIdx₂ : destIdx.val = i.val + k₂)
    (h_destIdx_le : destIdx.val ≤ ℓ)
    (x : sDomain 𝔽q β h_ℓ_add_R_rate i) :
    iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate
      (i := i) (k := k₁) (h_destIdx := h_destIdx₁) (h_destIdx_le := h_destIdx_le) x
    =
    iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate
      (i := i) (k := k₂) (h_destIdx := h_destIdx₂) (h_destIdx_le := h_destIdx_le) x := by
  subst hk; rfl

omit [DecidableEq 𝔽q] hF₂ in
/-- Composing one quotient step with a `steps`-step quotient map equals the
`steps + 1` step quotient map. -/
theorem iteratedQuotientMap_succ_comp
    (i : Fin r) {midIdx destIdx : Fin r} (steps : ℕ)
    (h_midIdx : midIdx.val = i.val + 1)
    (h_destIdx : destIdx.val = i.val + (steps + 1))
    (h_destIdx_le : destIdx ≤ ℓ)
    (x : sDomain 𝔽q β h_ℓ_add_R_rate i) :
    iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate
      (i := i) (k := steps + 1) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) x
    =
    iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate
      (i := midIdx) (k := steps)
      (h_destIdx := by omega)
      (h_destIdx_le := h_destIdx_le)
      (iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate
        (i := i) (k := 1) (h_destIdx := h_midIdx) (h_destIdx_le := by omega) x) := by
  apply Subtype.ext
  simp only [iteratedQuotientMap]
  have h_poly_comp := intermediateNormVpoly_comp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := i) (destIdx := midIdx) (k := 1) (l := steps)
    (h_destIdx := by exact h_midIdx) (h_k := by omega) (h_l := by omega)
  have h_poly_comp' :
      intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate (i := i) (k := steps + 1) (h_k := by omega) =
        (intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate (i := midIdx) (k := steps)
          (h_k := by omega)).comp
        (intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate (i := i) (k := 1) (h_k := by omega)) := by
    have h_poly_comp' := h_poly_comp
    simp only [Nat.add_comm] at h_poly_comp'
    exact h_poly_comp'
  rw [h_poly_comp']
  simp only [Polynomial.eval_comp]

omit [DecidableEq 𝔽q] [NeZero ℓ] hF₂ h_β₀_eq_1 in
/-- The evaluation of qMap on an element from sDomain i belongs to sDomain (i+1).
This is a key property that qMap maps between successive domains. -/
lemma qMap_eval_mem_sDomain_succ (i : Fin r) {destIdx : Fin r}
    (h_destIdx : destIdx = i.val + 1) (x : (sDomain 𝔽q β h_ℓ_add_R_rate) i) :
    (qMap 𝔽q β i).eval (x.val : L) ∈ sDomain 𝔽q β h_ℓ_add_R_rate destIdx := by
  have h_x_mem := x.property
  unfold sDomain at h_x_mem
  simp only [Submodule.mem_map] at h_x_mem
  obtain ⟨u, hu_mem, hu_eq⟩ := h_x_mem
  -- Use the fact that qMap maps sDomain i to sDomain (i+1)
  have h_maps := qMap_maps_sDomain 𝔽q β h_ℓ_add_R_rate i (by omega)
  have h_index: (((⟨i.val, by omega⟩: Fin r) + 1): Fin r) = ⟨i.val + 1, by omega⟩ := by
    refine Fin.eq_mk_iff_val_eq.mpr ?_
    rw [Fin.val_add_one' (h_a_add_1:=by simp only; omega)]
  simp only [h_index] at h_maps
  rw! [h_destIdx.symm] at h_maps
  rw [←h_maps]
  simp only [polyEvalLinearMap, Submodule.mem_map, LinearMap.coe_mk, AddHom.coe_mk]
  use x
  constructor
  · simp only [SetLike.coe_mem] -- x ∈ sDomain i
  · rfl

omit [DecidableEq 𝔽q] hF₂ in
/-- When k = 1, iteratedQuotientMap reduces to evaluating qMap directly.
This shows that iteratedQuotientMap with k = 1 is equivalent to the single-step quotient map. -/
theorem iteratedQuotientMap_k_eq_1_is_qMap (i : Fin r) {destIdx : Fin r}
    (h_destIdx : destIdx = i.val + 1) (h_destIdx_le : destIdx.val ≤ ℓ)
    (x : (sDomain 𝔽q β h_ℓ_add_R_rate) i) :
    (iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := i) (k := 1) (h_destIdx := h_destIdx)
      (h_destIdx_le := h_destIdx_le) x : sDomain 𝔽q β h_ℓ_add_R_rate destIdx)
    = ⟨(qMap 𝔽q β i).eval (x.val : L),
      qMap_eval_mem_sDomain_succ 𝔽q β h_ℓ_add_R_rate i h_destIdx x⟩ := by
  unfold iteratedQuotientMap
  simp only
  have h_intermediate_eq_qMap : intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate
    (i := i) (k := 1) (h_k := by omega) = qMap 𝔽q β i := by
    unfold intermediateNormVpoly
    simp only [Fin.foldl_succ, Fin.foldl_zero, Fin.coe_ofNat_eq_mod, Nat.zero_mod]
    simp only [add_zero, comp_X]
  -- We need to show that the two expressions are equal
  -- The first component is the evaluation, which we can rewrite
  congr 1
  · rw [h_intermediate_eq_qMap]

omit [DecidableEq 𝔽q] [NeZero ℓ] hF₂ h_β₀_eq_1 in
lemma getSDomainBasisCoeff_of_sum_repr [NeZero R_rate] (i : Fin r) (h_i : i ≤ ℓ)
    (x : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (x_coeffs : Fin (ℓ + R_rate - i) → 𝔽q)
    (hx : x = ∑ j_x, (x_coeffs j_x) • (sDomain_basis 𝔽q β
      h_ℓ_add_R_rate (i := ⟨i, by omega⟩) (h_i := by
        simp only; apply Nat.lt_add_of_pos_right_of_le; omega) j_x).val) :
    ∀ (j: Fin (ℓ + R_rate - i)), ((sDomain_basis 𝔽q β
      h_ℓ_add_R_rate (i := ⟨i, by omega⟩) (h_i := by
        simp only; apply Nat.lt_add_of_pos_right_of_le; omega)).repr x) j = x_coeffs j := by
  simp only
  intro j
  set b := sDomain_basis 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩)
    (h_i := by simp only; apply Nat.lt_add_of_pos_right_of_le; omega)
  -- By definition of a basis, `x` can also be written as a sum using its `repr` coefficients.
  have h_sum_repr : x.val = ∑ j', ((b.repr x) j') • (b j').val := by
    have hx := (b.sum_repr x).symm
    conv_lhs =>
      rw [hx]; rw [Submodule.coe_sum] -- move the Subtype.val embedding into the function body
    congr
  have h_sums_equal : ∑ j', ((b.repr x) j') • (b j').val = ∑ j_x, (x_coeffs j_x) • (b j_x).val := by
    rw [←h_sum_repr]
    exact hx
  -- The basis vectors `.val` are linearly independent in the ambient space `L`.
  have h_li : LinearIndependent 𝔽q (fun j' => (b j').val) := by
    exact b.linearIndependent.map' (Submodule.subtype _) (Submodule.ker_subtype _)
  -- Since the basis vectors are linearly independent, the representation of `x.val` as a
  -- linear combination is unique. Therefore, the coefficients must be equal.
  have h_coeffs_eq : b.repr x = Finsupp.equivFunOnFinite.symm x_coeffs := by
    classical
    -- `repr` on basis vectors is Kronecker: repr (b j_x) = Finsupp.single j_x 1
    have h_repr_basis :
        ∀ j_x, b.repr (b j_x) = Finsupp.single j_x (1 : 𝔽q) := by
      intro j_x; simp only [Basis.repr_self]
    -- Reduce the RHS sum at coordinate j to the unique matching index
    have hx_at_j_simplified :
        (∑ j_x, x_coeffs j_x • (b.repr (b j_x))) j = x_coeffs j := by
      simp only [h_repr_basis, Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.coe_finset_sum,
        Finset.sum_apply, Finsupp.single_apply, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    -- The hypothesis `hx_val` gives `x.val` as a sum. We need to lift this to an
    -- equality of elements in the submodule `C_i`.
    let x_coeffs_fs := Finsupp.equivFunOnFinite.symm x_coeffs
    -- Let's construct the sum on the right-hand side
      -- of `hx_val` as an element of the submodule `C_i`.
    let rhs_sum := ∑ j_x, (x_coeffs_fs j_x) • (b j_x)
    -- Now, show that `x` is equal to this `rhs_sum`.
      -- We do this by showing their `.val`'s are equal.
    have h_x_eq_rhs_sum : x = rhs_sum := by
      apply Subtype.ext -- Two elements of a subtype are equal if their values are equal.
      -- The value of `rhs_sum` is a sum of the values of its components.
      have h_rhs_sum_val : rhs_sum.val = ∑ j_x, (x_coeffs_fs j_x) • (b j_x).val := by
        rw [Submodule.coe_sum]; apply Finset.sum_congr rfl; intro j_x _; rw [Submodule.coe_smul]
      -- We started with `hx_val`, which we can rewrite with the Finsupp `x_coeffs_fs`.
      have hx_val_fs : x.val = ∑ j_x, (x_coeffs_fs j_x) • (b j_x).val := by
        simp only [hx]
        congr
      -- Since `x.val` and `rhs_sum.val` are equal to the same sum, they are equal.
      rw [hx_val_fs, h_rhs_sum_val]
    -- Now we can rewrite `x` in our goal.
    rw [h_x_eq_rhs_sum]
    -- The goal is now `b.repr (∑ j_x, ... • b j_x) = x_coeffs_fs`.
    -- This is exactly what `Basis.repr_sum_self` states.
    have h_coe_eq := b.repr_sum_self x_coeffs_fs
    -- h : ⇑(b.repr (∑ i_1, x_coeffs_fs i_1 • b i_1)) = ⇑x_coeffs_fs
    have h_eq: b.repr (∑ i_1, x_coeffs_fs i_1 • b i_1) = x_coeffs_fs := by
      simp only [map_sum, map_smul, Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one,
        Finsupp.univ_sum_single]
    rw [h_eq]
  -- Applying `j` to both sides of the `Finsupp` equality gives the goal.
  rw [h_coeffs_eq]
  -- ⊢ (Finsupp.equivFunOnFinite.symm x_coeffs) j = x_coeffs j
  simp only [Finsupp.equivFunOnFinite_symm_apply_apply]

omit [DecidableEq 𝔽q] hF₂ in
lemma getSDomainBasisCoeff_of_iteratedQuotientMap
    [NeZero R_rate] (i : Fin r) (k : ℕ)
    {destIdx : Fin r} (h_destIdx : destIdx = i.val + k) (h_destIdx_le : destIdx.val ≤ ℓ)
    (x : (sDomain 𝔽q β h_ℓ_add_R_rate) i) :
    let y : (sDomain 𝔽q β h_ℓ_add_R_rate destIdx) := iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate
      (i := i) (k:=k) (h_destIdx:=h_destIdx) (h_destIdx_le:=h_destIdx_le) (x:=x)
    ∀ (j: Fin (ℓ + R_rate - destIdx)),
    ((sDomain_basis 𝔽q β h_ℓ_add_R_rate (i := destIdx) (h_i := by
      apply Nat.lt_add_of_pos_right_of_le; omega)).repr y) j =
    ((sDomain_basis 𝔽q β h_ℓ_add_R_rate (i := i)
      (h_i := by apply Nat.lt_add_of_pos_right_of_le; omega)).repr x) ⟨j + k, by omega⟩:= by
  simp only
  intro j -- Let's define our bases and coefficient maps for clarity.
  let basis_source := sDomain_basis 𝔽q β h_ℓ_add_R_rate
    (i := i) (h_i := by apply Nat.lt_add_of_pos_right_of_le; omega)
  let basis_target := sDomain_basis 𝔽q β h_ℓ_add_R_rate
    (i := destIdx) (h_i := by apply Nat.lt_add_of_pos_right_of_le; omega)
  let x_coeffs := basis_source.repr x
  set y : (sDomain 𝔽q β h_ℓ_add_R_rate destIdx) := iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate
    (i := i) (k:=k) (h_destIdx:=h_destIdx) (h_destIdx_le:=h_destIdx_le) (x:=x)
  let y_coeffs := basis_target.repr y
  -- The proof relies on the uniqueness of basis representation
  have hx_sum : x.val = ∑ j_x, (x_coeffs j_x) • (basis_source j_x).val := by
    simp only [x_coeffs]
    conv_lhs => rw [← basis_source.sum_repr x]; rw [Submodule.coe_sum]
    simp_rw [Submodule.coe_smul]
  have hy_sum : y.val = ∑ j_y, (y_coeffs j_y) • (basis_target j_y).val := by
    simp only [y_coeffs]
    conv_lhs => rw [← basis_target.sum_repr y]; rw [Submodule.coe_sum]
    simp_rw [Submodule.coe_smul]
  -- Derive y's expression from the definition of `iteratedQuotientMap`.
  have hy_sum_from_x : y = ∑ j_x, (x_coeffs j_x) •
      ((intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate (i := i)
        (k := k) (h_k := by omega)).eval (basis_source j_x).val) := by
    -- Start with `y = eval(x)`
    have hy_eval : y.val = (intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate
      (i := i) (k := k) (h_k := by omega)).eval x.val := by rfl
    rw [hx_sum] at hy_eval
    -- simp only at hy_eval
    rw [hy_eval]
    have h_res: eval (∑ x : Fin (ℓ + R_rate - i), x_coeffs x • (basis_source x).val)
      (intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate (i := i) (k := k) (h_k := by omega))
      = ∑ j_x : Fin (ℓ + R_rate - i), x_coeffs j_x • eval ((basis_source j_x).val)
          (intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate (i := i) (k := k) (h_k := by omega)) := by
      have eval_interW_IsLinearMap :
        IsLinearMap 𝔽q (fun x : L =>
          (intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate
            (i := i) (k := k) (h_k := by omega)).eval x) := by
        exact intermediateNormVpoly_eval_is_linear_map 𝔽q β h_ℓ_add_R_rate
          (i := i) (k:=k) (h_k := by omega)
      let eval_interW_LinearMap := polyEvalLinearMap (intermediateNormVpoly 𝔽q β
        h_ℓ_add_R_rate (i := i) (k := k) (h_k := by omega)) eval_interW_IsLinearMap
      -- Use map_sum with a LinearMap (not a plain function)
      change eval_interW_LinearMap (∑ x_1 : Fin (ℓ + R_rate - i),
        x_coeffs x_1 • (basis_source x_1).val) = _
      rw [map_sum (g:=eval_interW_LinearMap) (s:=(Finset.univ : Finset (Fin (ℓ + R_rate - i))))]
      simp_rw [eval_interW_LinearMap.map_smul]
      rfl
    rw [h_res]
  -- Now, we simplify the term inside the second sum to show it's a basis vector of `basis_target`.
  have h_eval_basis_i : ∀ j_x, (intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate
    (i := i) (k:=k) (h_k := by omega)).eval (basis_source j_x).val
      = (normalizedW 𝔽q β destIdx).eval (β ⟨i.val + j_x.val, by omega⟩) := by
      -- TODO: how to make this cleaner?
    intro j_x
    let interW_i_k := intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate (i := i) (k:=k) (h_k := by omega)
    let W_i := normalizedW 𝔽q β i
    let W_i_add_k := normalizedW 𝔽q β destIdx
    have h_comp_eq : interW_i_k.comp W_i = W_i_add_k := by
      have hi := base_intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate (k:=i) (h_k := by omega)
      have hi_add_k := base_intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate (k:=destIdx) (h_k := by omega)
      simp only at hi hi_add_k
      simp_rw [W_i, W_i_add_k, interW_i_k, ←hi, ←hi_add_k]
      have h_interW_comp := intermediateNormVpoly_comp 𝔽q β h_ℓ_add_R_rate
        (i := 0) (k:=i) (l:=k) (destIdx := i) (h_destIdx := by
          simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add])
        (h_k := by simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]; omega)
        (h_l := by simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]; omega)
      rw! [←h_destIdx] at h_interW_comp
      -- simp only [Fin.mk_zero'] at h_interW_comp
      rw [h_interW_comp]
    rw [get_sDomain_basis, ←Polynomial.eval_comp, h_comp_eq]
  -- Using this, we rewrite `hy_sum_from_x`.
  simp_rw [h_eval_basis_i] at hy_sum_from_x
  -- hy_sum_from_x : ↑y = ∑ x, x_coeffs x • eval (β ⟨↑i + ↑x, ⋯⟩) (normalizedW 𝔽q β ⟨↑i + k, ⋯⟩)
  let final_y_coeffs: Fin (ℓ + R_rate - destIdx) → 𝔽q :=
    fun j_x: Fin (ℓ + R_rate - destIdx) => x_coeffs ⟨j_x + k, by omega⟩
  have final_hy_sum : y = ∑ j_x: Fin (ℓ + R_rate - destIdx),
    (final_y_coeffs j_x) • (basis_target j_x).val := by
    rw [hy_sum_from_x]
    -- ⊢ ∑ x, x_coeffs x • eval (β ⟨↑i + ↑x, ⋯⟩) (normalizedW 𝔽q β ⟨↑i + k, ⋯⟩)
      -- = ∑ j_x, final_y_coeffs j_x • ↑(basis_target j_x)
    let a := k
    let b := ℓ + R_rate - destIdx
    have h_index_add: ℓ + R_rate - ↑i = a + b := by omega
    rw! (castMode := .all) [h_index_add];
    conv_lhs => -- split the sum in LHS into two parts
      rw [Fin.sum_univ_add]
      simp only [Fin.val_castAdd, Fin.val_natAdd]
    -- Eliminate the first sum of LHS
    have hβ: ∀ x: Fin a, β ⟨↑i + x, by omega⟩ ∈ U 𝔽q β (i := destIdx) := by
      intro x
      apply β_lt_mem_U 𝔽q β (i := destIdx) (j:=⟨i.val + x, by omega⟩)
    have h_eval_W_at_β: ∀ x: Fin a, eval (β ⟨↑i + ↑x, by omega⟩)
      (normalizedW 𝔽q β destIdx) = 0 := by
      intro x
      rw [normalizedWᵢ_vanishing 𝔽q β destIdx]
      exact hβ x
    -- simp only [Function.const_apply]
    conv_lhs => simp only [h_eval_W_at_β, smul_zero, Finset.sum_const_zero, zero_add]
    -- Convert the second sum of LHS
    congr
    simp only [b]
    funext j2
    rw [get_sDomain_basis]
    have h: i + k < r := by omega
    have h2: i.val + (a + ↑j2) = i + k + j2 := by omega
    simp_rw [h2]
    congr 1
    · simp only [final_y_coeffs, a]
      rw! (castMode:=.all) [h_index_add.symm];
      -- simp only
      apply congrArg
      rw [eqRec_eq_cast, ←Fin.cast_eq_cast (h := by omega)]
      apply Fin.eq_of_val_eq
      simp only [Fin.val_cast, Fin.val_natAdd];
      rw [Nat.add_comm]
    · simp_rw [h_destIdx]
  rw [getSDomainBasisCoeff_of_sum_repr 𝔽q β h_ℓ_add_R_rate
    (i := ⟨i.val, by omega⟩) (h_i := by simp only; omega) (x:=x) (hx:=by exact hx_sum)]
  rw [getSDomainBasisCoeff_of_sum_repr 𝔽q β h_ℓ_add_R_rate
    (i := destIdx) (h_i := by omega) (x:=y) (x_coeffs := final_y_coeffs) (hx:=final_hy_sum)]

/-- Lifts a point `y` from a higher-indexed domain `sDomain j` to the canonical
base point of its fiber in a lower-indexed domain `sDomain i`,
by retaining all coeffs for the corresponding basis elements -/
noncomputable def sDomain.lift (i j : Fin r) (h_j : j < ℓ + R_rate) (h_le : i ≤ j)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate j) :
    sDomain 𝔽q β h_ℓ_add_R_rate i := by
  let basis_y := sDomain_basis 𝔽q β h_ℓ_add_R_rate (i := j) (h_i := by exact
    h_j)
  let basis_x := sDomain_basis 𝔽q β h_ℓ_add_R_rate (i := i) (h_i := by omega)
  let ϑ := j.val - i.val
  let x_coeffs : Fin (ℓ + R_rate - i) → 𝔽q := fun k =>
    if hk: k.val < ϑ then 0
    else
      basis_y.repr y ⟨k.val - ϑ, by omega⟩  -- Shift indices to match y's basis
  exact basis_x.repr.symm ((Finsupp.equivFunOnFinite).symm x_coeffs)

omit [DecidableEq 𝔽q] [NeZero ℓ] hF₂ h_β₀_eq_1 in
/-- Applying the forward map to a lifted point returns the original point. -/
theorem basis_repr_of_sDomain_lift (i j : Fin r) (h_j : j < ℓ + R_rate) (h_le : i ≤ j)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := j)) :
    let x₀ := sDomain.lift 𝔽q β h_ℓ_add_R_rate i j (by omega) (by omega) y
    ∀ k: Fin (ℓ + R_rate - i),
      (sDomain_basis 𝔽q β h_ℓ_add_R_rate (i := i) (h_i := by omega)).repr x₀ k =
        if hk: k < (j.val - i.val) then 0
        else (sDomain_basis 𝔽q β h_ℓ_add_R_rate (i := j)
          (h_i := by omega)).repr y ⟨k - (j.val - i.val), by omega⟩ := by
  simp only;
  intro k
  simp only [sDomain.lift, Basis.repr_symm_apply, Basis.repr_linearCombination,
    Finsupp.equivFunOnFinite_symm_apply_apply]

omit [DecidableEq L] [NeZero ℓ] [DecidableEq 𝔽q] h_Fq_char_prime hF₂ hβ_lin_indep h_β₀_eq_1 in
-- A helper derivation for intermediateNormVpoly_comp_qmap
-- i is now in Fin (ℓ-1) instead of Fin ℓ, and k is in Fin (ℓ - (↑i + 1))
theorem intermediateNormVpoly_comp_qmap_helper (i : Fin r) (h_i : i < ℓ)
    (k : Fin (ℓ - (↑i + 1))) :
    (intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate
      ⟨↑i + 1, by omega⟩ (k:=k) (h_k := by simp only; omega)).comp (qMap 𝔽q β ⟨↑i, by omega⟩) =
    intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate
      ⟨↑i, by omega⟩ (k:=k + 1) (h_k := by simp only; omega):= by
    rw [intermediateNormVpoly_comp_qmap 𝔽q β h_ℓ_add_R_rate (i := i)
      (destIdx := (⟨↑i + 1, by omega⟩ : Fin r)) (h_destIdx := by simp only)
      (k := k) (h_k := by omega)]

/-- ∀ `i` ∈ {0, ..., ℓ}, The `i`-th order novel polynomial basis `Xⱼ⁽ⁱ⁾`.
`Xⱼ⁽ⁱ⁾ := Π_{k=0}^{ℓ-i-1} (Ŵₖ⁽ⁱ⁾)^{jₖ}`, ∀ j ∈ {0, ..., 2^(ℓ-i)-1} -/
noncomputable def intermediateNovelBasisX (i : Fin r) (h_i : i ≤ ℓ)
    (j : Fin (2 ^ (ℓ - i))) : L[X] :=
  (Finset.univ: Finset (Fin (ℓ - i)) ).prod (fun k =>
    (intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate i (k:=k.val) (h_k:=by omega)) ^ (Nat.getBit k j))
-- NOTE: possibly we state some Basis for `(Xⱼ⁽ⁱ⁾)  `

omit [DecidableEq 𝔽q] [DecidableEq L] [NeZero ℓ] hF₂ in
-- Xⱼ⁽⁰⁾ = Xⱼ
theorem base_intermediateNovelBasisX (j : Fin (2 ^ ℓ)) :
  intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate 0 (h_i := by simp only [Fin.coe_ofNat_eq_mod,
    Nat.zero_mod, zero_le]) j =
  Xⱼ 𝔽q β ℓ (by omega) j := by
  classical
  unfold intermediateNovelBasisX Xⱼ
  simp only [Fin.coe_ofNat_eq_mod]
  have h_res := base_intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate
  simp only at h_res
  conv_lhs =>
    enter [2, x, 1]
    rw [h_res ⟨x, by omega⟩ (h_k := by simp only; omega)]
  congr

omit [DecidableEq L] [NeZero ℓ] [DecidableEq 𝔽q] h_Fq_char_prime hF₂ hβ_lin_indep h_β₀_eq_1 in
lemma intermediateNovelBasisX_zero_eq_one (i : Fin r) (h_i : i ≤ ℓ) :
    intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate i h_i ⟨0, by
      exact Nat.two_pow_pos (ℓ - ↑i)⟩ = 1 := by
  unfold intermediateNovelBasisX
  simp only [Nat.getBit_zero_eq_zero, pow_zero]
  exact Finset.prod_const_one

omit h_Fq_char_prime [NeZero ℓ] [DecidableEq L] [DecidableEq 𝔽q] h_β₀_eq_1 in
/-- The degree of an `i`-th order novel polynomial basis element `Xⱼ⁽ⁱ⁾(X)` is exactly `j`.
Somewhat similar to proof of `degree_Xⱼ`. -/
lemma degree_intermediateNovelBasisX (i : Fin r) (h_i : i ≤ ℓ) (j : Fin (2 ^ (ℓ - i))) :
  (intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate (i := i) (h_i := h_i) (j := j)).degree = j := by
  rw [intermediateNovelBasisX, degree_prod]
  set rangeL := Fin ℓ
  -- ⊢ ∑ i ∈ rangeL, (normalizedW 𝔽q β i ^ bit (↑i) j).degree = ↑j
  by_cases h_ℓ_0: ℓ = 0
  · have h_ℓ_sub_i : ℓ - i = 0 := by omega
    rw! (castMode:=.all) [h_ℓ_sub_i]
    rw! (castMode:=.all) [h_ℓ_0]
    simp only [Finset.univ_eq_empty, Nat.pow_zero, Fin.val_eq_zero, degree_pow,
      nsmul_eq_mul, Finset.sum_empty, WithBot.coe_zero]
  · push_neg at h_ℓ_0
    have deg_each: ∀ (k : Fin (ℓ - i)), ((intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate (i := i)
        (k:=k) (h_k := by omega))^(Nat.getBit k j)).degree
      = if Nat.getBit (k := k.val) (n := j.val) = 1 then (2:ℕ)^k.val else 0 := by
      intro (k : Fin (ℓ - i))
      rw [degree_pow]
      have h_deg_norm_vpoly: (intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate (i := i)
        (k:=k) (h_k := by omega)).degree = 2 ^ k.val := by rw [degree_intermediateNormVpoly]
      rw [h_deg_norm_vpoly]
      simp only [nsmul_eq_mul, Nat.cast_ite, Nat.cast_pow,
        Nat.cast_ofNat, CharP.cast_eq_zero]
      have h_get_bit_lt_2 := Nat.getBit_lt_2 (k:=k.val) (n:=j.val)
      by_cases h: Nat.getBit (k := k.val) (n := j.val) = 1
      · simp only [h, Nat.cast_one, one_mul, ↓reduceIte];
      · simp only [h, ↓reduceIte, mul_eq_zero, Nat.cast_eq_zero, pow_eq_zero_iff',
        OfNat.ofNat_ne_zero, ne_eq, false_and, or_false]
        omega
    simp_rw [deg_each]
    -- ⊢ ∑ x, ↑(if (↑x).getBit ↑j = 1 then 2 ^ ↑i else 0) = ↑↑j
    set f:= fun x: ℕ => if Nat.getBit x j = 1 then (2: ℕ) ^ (x: ℕ) else 0
    simp only [Nat.cast_ite, Nat.cast_pow, Nat.cast_ofNat, CharP.cast_eq_zero]
    conv_rhs =>
      rw [Nat.getBit_repr_univ (ℓ := ℓ - i) (j := j.val) (by omega)]
    simp only [WithBot.coe_sum, WithBot.coe_mul, WithBot.coe_pow, WithBot.coe_ofNat]
    congr 1
    funext (x : Fin (ℓ - i))
    have h_getBit_lt_2 := Nat.getBit_lt_2 (k:=x) (n:=j.val)
    by_cases h: Nat.getBit (k := x) (n := j.val) = 1
    · simp only [h, ↓reduceIte, WithBot.coe_one, one_mul];
    · simp only [h, ↓reduceIte, zero_eq_mul, WithBot.coe_eq_zero, pow_eq_zero_iff',
      OfNat.ofNat_ne_zero, ne_eq, false_and, or_false]; omega

omit [DecidableEq L] [DecidableEq 𝔽q] h_Fq_char_prime hF₂ hβ_lin_indep h_β₀_eq_1 [NeZero ℓ] in
/-- `X₂ⱼ⁽ⁱ⁾ = Xⱼ⁽ⁱ⁺¹⁾(q⁽ⁱ⁾(X)) ∀ j ∈ {0, ..., 2^(ℓ-i)-1}, ∀ i ∈ {0, ..., ℓ-1}` -/
lemma even_index_intermediate_novel_basis_decomposition (i : Fin r)
    (h_i : i < ℓ) (j : Fin (2 ^ (ℓ - i - 1))) :
  intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate (i := i) (h_i := by omega) ⟨j * 2, by
    apply mul_two_add_bit_lt_two_pow j (ℓ-i-1) (ℓ-i) ⟨0, by omega⟩ (by omega) (by omega)
  ⟩  = (intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate (i := ⟨i.val+1, by omega⟩)
    (h_i := by simp only; omega) ⟨j, by
    apply lt_two_pow_of_lt_two_pow_exp_le j (ℓ-i-1) (ℓ-(i+1)) (by omega) (by omega)
  ⟩).comp (qMap 𝔽q β i) := by
  unfold intermediateNovelBasisX
  rw [prod_comp]
  -- ∏ k ∈ Fin (ℓ - i), (Wₖ⁽ⁱ⁾(X))^((2j)ₖ) = ∏ k ∈ Fin (ℓ - (i+1)), (Wₖ⁽ⁱ⁺¹⁾(X))^((j)ₖ) ∘ q⁽ⁱ⁾(X)
  simp only [pow_comp]
  conv_rhs =>
    enter [2, x]
    rw [intermediateNormVpoly_comp_qmap_helper 𝔽q (h_i := h_i)]
  -- ⊢ ∏ x, intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate ⟨↑i, ⋯⟩ x ^ Nat.getBit (↑x) (↑j * 2) =
  -- ∏ x, intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate ⟨↑i, ⋯⟩ ⟨↑x + 1, ⋯⟩ ^ Nat.getBit ↑x ↑j
  set fleft := fun x : Fin (ℓ - ↑i) =>
    (intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate (i := i)
      (k := x) (h_k := by omega)) ^ Nat.getBit (↑x) (↑j * 2)
  have h_n_shift: ℓ - (↑i + 1) + 1 = ℓ - ↑i := by omega
  have h_fin_n_shift: Fin (ℓ - (↑i + 1) + 1) = Fin (ℓ - ↑i) := by
    rw [h_n_shift]
  have h_left_prod_shift :=
  Fin.prod_univ_succ (M:=L[X]) (n:=ℓ - (↑i + 1)) (f:=fun x => fleft ⟨x, by omega⟩)
  have h_lhs_prod_eq: ∏ x : Fin (ℓ - ↑i),
    fleft x = ∏ x : Fin (ℓ - (↑i + 1) + 1), fleft ⟨x, by omega⟩ := by
    exact Eq.symm (Fin.prod_congr' fleft h_n_shift)
  rw [←h_lhs_prod_eq] at h_left_prod_shift
  rw [h_left_prod_shift]
  have fleft_0_eq_0: fleft ⟨(0: Fin (ℓ - (↑i + 1) + 1)), by omega⟩ = 1 := by
    unfold fleft
    simp only
    have h_exp: Nat.getBit (0: Fin (ℓ - (↑i + 1) + 1)) (↑j * 2) = 0 := by
      simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod]
      have res := Nat.getBit_zero_of_two_mul (n:=j.val)
      rw [mul_comm] at res
      exact res
    rw [h_exp]
    simp only [pow_zero]
  rw [fleft_0_eq_0, one_mul]
  apply Finset.prod_congr rfl
  intro x hx
  simp only [Fin.val_succ]
  unfold fleft
  simp only
  have h_exp_eq: Nat.getBit (↑x + 1) (↑j * 2) = Nat.getBit ↑x ↑j := by
    have h_num_eq: j.val * 2 = 2 * j.val := by omega
    rw [h_num_eq]
    apply Nat.getBit_eq_succ_getBit_of_mul_two (k:=↑x) (n:=↑j)
  rw [h_exp_eq]

omit [DecidableEq L] [NeZero ℓ] [DecidableEq 𝔽q] h_Fq_char_prime hF₂ hβ_lin_indep h_β₀_eq_1 in
/-- `X₂ⱼ₊₁⁽ⁱ⁾ = X * (Xⱼ⁽ⁱ⁺¹⁾(q⁽ⁱ⁾(X))) ∀ j ∈ {0, ..., 2^(ℓ-i)-1}, ∀ i ∈ {0, ..., ℓ-1}` -/
lemma odd_index_intermediate_novel_basis_decomposition
    (i : Fin r) (h_i : i < ℓ) (j : Fin (2 ^ (ℓ - i - 1))) :
    intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate (i := i) (h_i := by omega) ⟨j * 2 + 1, by
      apply mul_two_add_bit_lt_two_pow j (ℓ-i-1) (ℓ-i) ⟨1, by omega⟩ (by omega) (by omega)
    ⟩  = X * (intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate (i := ⟨i.val+1, by omega⟩)
    (h_i := by simp only; omega) ⟨j, by
      apply lt_two_pow_of_lt_two_pow_exp_le j (ℓ-i-1) (ℓ-(i+1)) (by omega) (by omega)
    ⟩).comp (qMap 𝔽q β i) := by
  unfold intermediateNovelBasisX
  rw [prod_comp]
  -- ∏ k ∈ Fin (ℓ - i), (Wₖ⁽ⁱ⁾(X))^((2j₊₁)ₖ)
  -- = X * ∏ k ∈ Fin (ℓ - (i+1)), (Wₖ⁽ⁱ⁺¹⁾(X))^((j)ₖ) ∘ q⁽ⁱ⁾(X)
  simp only [pow_comp]
  conv_rhs =>
    enter [2]
    enter [2, x, 1]
    rw [intermediateNormVpoly_comp_qmap_helper 𝔽q β h_ℓ_add_R_rate
      (i := i) (h_i := by omega) (k := ⟨x, by omega⟩)]
  -- ⊢ ∏ x, intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate ⟨↑i, ⋯⟩ x ^ Nat.getBit (↑x) (↑j * 2 + 1) =
  -- X * ∏ x, intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate ⟨↑i, ⋯⟩ ⟨↑x + 1, ⋯⟩ ^ Nat.getBit ↑x ↑j
  set fleft := fun x : Fin (ℓ - ↑i) =>
    (intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate (i := i) (k := x)
      (h_k := by omega)) ^ Nat.getBit (↑x) (↑j * 2 + 1)
  have h_n_shift: ℓ - (↑i + 1) + 1 = ℓ - ↑i := by omega
  have h_fin_n_shift: Fin (ℓ - (↑i + 1) + 1) = Fin (ℓ - ↑i) := by
    rw [h_n_shift]
  have h_left_prod_shift :=
  Fin.prod_univ_succ (M:=L[X]) (n:=ℓ - (↑i + 1)) (f:=fun x => fleft ⟨x, by omega⟩)
  have h_lhs_prod_eq: ∏ x : Fin (ℓ - ↑i),
    fleft x = ∏ x : Fin (ℓ - (↑i + 1) + 1), fleft ⟨x, by omega⟩ := by
    exact Eq.symm (Fin.prod_congr' fleft h_n_shift)
  rw [←h_lhs_prod_eq] at h_left_prod_shift
  rw [h_left_prod_shift]
  have fleft_0_eq_X: fleft ⟨(0: Fin (ℓ - (↑i + 1) + 1)), by omega⟩ = X := by
    unfold fleft
    simp only
    have h_exp: Nat.getBit (0: Fin (ℓ - (↑i + 1) + 1)) (↑j * 2 + 1) = 1 := by
      simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod]
      unfold Nat.getBit
      simp only [Nat.shiftRight_zero, Nat.and_one_is_mod, Nat.mul_add_mod_self_right, Nat.mod_succ]
    rw [h_exp]
    simp only [pow_one, Fin.coe_ofNat_eq_mod, Nat.zero_mod]
    unfold intermediateNormVpoly
    simp only [Fin.foldl_zero]
  rw [fleft_0_eq_X]
  congr -- apply Finset.prod_congr rfl
  funext x
  simp only [Fin.val_succ]
  unfold fleft
  simp only
  have h_exp_eq: Nat.getBit (↑x + 1) (↑j * 2 + 1) = Nat.getBit ↑x ↑j := by
    have h_num_eq: j.val * 2 = 2 * j.val := by omega
    rw [h_num_eq]
    apply Nat.getBit_eq_succ_getBit_of_mul_two_add_one (k:=↑x) (n:=↑j)
  rw [h_exp_eq]

/-- ∀ `i` ∈ {0, ..., ℓ}, The `i`-th order evaluation polynomial
`P⁽ⁱ⁾(X) := ∑_{j=0}^{2^(ℓ-i)-1} coeffsⱼ ⋅ Xⱼ⁽ⁱ⁾(X)` over the domain `S⁽ⁱ⁾`.
  where the polynomial `P⁽⁰⁾(X)` over the domain `S⁽⁰⁾` is exactly the original
  polynomial `P(X)` we need to evaluate,
  and `coeffs` is the list of `2^(ℓ-i)` coefficients of the polynomial.
-/
noncomputable def intermediateEvaluationPoly (i : Fin r) (h_i : i ≤ ℓ)
    (coeffs : Fin (2 ^ (ℓ - i)) → L) : L[X] :=
  ∑ (j: Fin (2^(ℓ-i))), C (coeffs j) *
    (intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate i h_i j)

omit [DecidableEq L] [NeZero ℓ] [DecidableEq 𝔽q] h_Fq_char_prime h_β₀_eq_1 in
lemma degree_intermediateEvaluationPoly_lt (i : Fin r) (h_i : i ≤ ℓ)
    (coeffs : Fin (2 ^ (ℓ - i)) → L) :
  (intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate i h_i coeffs).degree < 2 ^ (ℓ - i) := by
  rw [intermediateEvaluationPoly]
  -- simp only
  apply (Polynomial.degree_sum_le Finset.univ (fun (j : Fin (2^(ℓ-i))) => C (coeffs ⟨j, by omega⟩)
    * (intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate i (h_i := h_i) ⟨j, by omega⟩))).trans_lt
  apply (Finset.sup_lt_iff ?_).mpr ?_
  · -- ⊢ ⊥ < 2 ^ ℓ
    exact compareOfLessAndEq_eq_lt.mp rfl
  · -- ∀ b ∈ univ, (C (a b) * Xⱼ 𝔽q β ℓ h_ℓ b).degree < 2 ^ ℓ
    intro (j : Fin (2 ^ (ℓ - ↑i))) _
    -- ⊢ (C (a j) * Xⱼ 𝔽q β ℓ h_ℓ j).degree < 2 ^ ℓ
    calc (C (coeffs ⟨j, by omega⟩) * intermediateNovelBasisX 𝔽q β
      h_ℓ_add_R_rate i h_i ⟨j, by omega⟩).degree
      _ ≤ (C (coeffs ⟨j, by omega⟩)).degree + (intermediateNovelBasisX 𝔽q β
        h_ℓ_add_R_rate i h_i ⟨j, by omega⟩).degree := by apply Polynomial.degree_mul_le
      _ ≤ 0 + (intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate i h_i ⟨j, by omega⟩).degree := by
        gcongr; exact Polynomial.degree_C_le
      _ = ↑j.val := by
        rw [degree_intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate i h_i ⟨j, by omega⟩];
        simp only [zero_add]; rfl
      _ < ↑(2^(ℓ-i)) := by norm_cast; exact j.isLt

section IntermediateNovelPolynomialBasis

/-- The basis vectors for the intermediate level `i`. -/
noncomputable def intermediateBasisVectors (i : Fin r) (h_i : i ≤ ℓ) :
  Fin (2 ^ (ℓ - i)) → L⦃<2^(ℓ - i)⦄[X] :=
  fun j => ⟨intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate i h_i j, by
    apply Polynomial.mem_degreeLT.mpr
    rw [degree_intermediateNovelBasisX]
    -- Proof that j < 2^(ℓ-i)
    change (j.val: WithBot ℕ) < ((2: WithBot ℕ) ^ (ℓ - i))
    norm_cast
    exact j.isLt
  ⟩

/-- The vector space of coefficients for polynomials of degree < 2^(ℓ-i). -/
abbrev IntermediateCoeffVecSpace (i : Fin r) := Fin (2^(ℓ - i)) → L

/-- The linear map from polynomials (in the subtype) to their coefficient vectors at level `i`. -/
def intermediateToCoeffsVec (i : Fin r) : -- (h_i : i ≤ ℓ)
    L⦃<2^(ℓ - i)⦄[X] →ₗ[L] IntermediateCoeffVecSpace (L := L) (ℓ := ℓ) i where
  toFun := fun p => fun k => p.val.coeff k.val
  map_add' := fun p q => by ext k; simp [coeff_add]
  map_smul' := fun c p => by ext k; simp [coeff_smul, smul_eq_mul]

/-- The Change-of-Basis Matrix from the Intermediate Novel Basis to the Monomial Basis.
    A_jk = coeff of X^k in intermediate basis vector X_j. -/
noncomputable def intermediateChangeOfBasisMatrix (i : Fin r) (h_i : i ≤ ℓ) :
    Matrix (Fin (2 ^ (ℓ - i))) (Fin (2 ^ (ℓ - i))) L :=
  fun j k => (intermediateToCoeffsVec (L := L) i
    (intermediateBasisVectors 𝔽q β h_ℓ_add_R_rate i h_i j)) k

omit h_Fq_char_prime [NeZero ℓ] [DecidableEq L] [DecidableEq 𝔽q] h_β₀_eq_1 in
theorem intermediateChangeOfBasisMatrix_lower_triangular (i : Fin r) (h_i : i ≤ ℓ) :
    (intermediateChangeOfBasisMatrix 𝔽q β h_ℓ_add_R_rate i h_i).BlockTriangular
      ⇑OrderDual.toDual := by
  intro j k h_jk
  simp only [OrderDual.toDual_lt_toDual] at h_jk
  dsimp [intermediateChangeOfBasisMatrix, intermediateToCoeffsVec, intermediateBasisVectors]
  -- We need coeff(X_j, k) = 0 when j < k
  -- This holds because deg(X_j) = j < k
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  rw [Polynomial.natDegree_eq_of_degree_eq_some
    (degree_intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate i (by omega) j)]
  exact h_jk

omit h_Fq_char_prime [NeZero ℓ] [DecidableEq L] [DecidableEq 𝔽q] h_β₀_eq_1 in
theorem intermediateChangeOfBasisMatrix_diag_ne_zero (i : Fin r) (h_i : i ≤ ℓ) :
    (∀ j, (intermediateChangeOfBasisMatrix 𝔽q β h_ℓ_add_R_rate i h_i) j j ≠ 0) := by
  intro j
  dsimp [intermediateChangeOfBasisMatrix, intermediateToCoeffsVec, intermediateBasisVectors]
  -- The diagonal entry is the leading coefficient
  apply Polynomial.coeff_ne_zero_of_eq_degree
  exact degree_intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate i h_i j

omit [DecidableEq L] [NeZero ℓ] [DecidableEq 𝔽q] h_Fq_char_prime h_β₀_eq_1 in
theorem intermediateChangeOfBasisMatrix_det_ne_zero (i : Fin r) (h_i : i ≤ ℓ) :
    (intermediateChangeOfBasisMatrix 𝔽q β h_ℓ_add_R_rate i h_i).det ≠ 0 := by
  rw [Matrix.det_of_lowerTriangular]
  · apply Finset.prod_ne_zero_iff.mpr
    intro j hj_mem_univ
    let res := intermediateChangeOfBasisMatrix_diag_ne_zero 𝔽q β h_ℓ_add_R_rate i h_i j
    exact res
  · exact intermediateChangeOfBasisMatrix_lower_triangular 𝔽q β h_ℓ_add_R_rate i h_i

/-- The intermediate change-of-basis matrix is invertible. -/
noncomputable instance intermediateChangeOfBasisMatrix_invertible (i : Fin r) (h_i : i ≤ ℓ) :
    Invertible (intermediateChangeOfBasisMatrix 𝔽q β h_ℓ_add_R_rate i h_i) := by
  refine Matrix.invertibleOfIsUnitDet _ ?_
  exact Ne.isUnit (intermediateChangeOfBasisMatrix_det_ne_zero 𝔽q β h_ℓ_add_R_rate i h_i)

/-- Convert monomial coefficients to novel coefficients at level `i`.
    n = m * A⁻¹ -/
noncomputable def monomialToINovelCoeffs (i : Fin r) (h_i : i ≤ ℓ)
    (monomial_coeffs : Fin (2 ^ (ℓ - i)) → L) : Fin (2 ^ (ℓ - i)) → L :=
  let A := intermediateChangeOfBasisMatrix 𝔽q β h_ℓ_add_R_rate i h_i
  Matrix.vecMul monomial_coeffs (⅟A)

/-- Convert novel coefficients to monomial coefficients at level `i`.
    m = n * A -/
noncomputable def iNovelToMonomialCoeffs (i : Fin r) (h_i : i ≤ ℓ)
    (novel_coeffs : Fin (2 ^ (ℓ - i)) → L) : Fin (2 ^ (ℓ - i)) → L :=
  let A := intermediateChangeOfBasisMatrix 𝔽q β h_ℓ_add_R_rate i h_i
  Matrix.vecMul novel_coeffs A

noncomputable def getINovelCoeffs (i : Fin r) (h_i : i ≤ ℓ)
    (P : L[X]) : Fin (2 ^ (ℓ - i.val)) → L :=
  let mono_coefs : Fin (2 ^ (ℓ - i.val)) → L := fun k => P.coeff k.val
  monomialToINovelCoeffs 𝔽q β h_ℓ_add_R_rate i h_i mono_coefs

omit h_Fq_char_prime [DecidableEq L] [NeZero ℓ] [DecidableEq 𝔽q] h_β₀_eq_1 in
/-- Round trip inverse property: Monomial -> Novel -> Monomial -/
theorem monomialToINovel_iNovelToMonomial_inverse (i : Fin r) (h_i : i ≤ ℓ)
  (coeffs : Fin (2 ^ (ℓ - i)) → L) :
    iNovelToMonomialCoeffs 𝔽q β h_ℓ_add_R_rate i h_i
      (monomialToINovelCoeffs 𝔽q β h_ℓ_add_R_rate i h_i coeffs) = coeffs := by
  unfold monomialToINovelCoeffs iNovelToMonomialCoeffs
  dsimp
  let A := intermediateChangeOfBasisMatrix 𝔽q β h_ℓ_add_R_rate i
  rw [Matrix.vecMul_vecMul]
  simp only [Matrix.invOf_eq_nonsing_inv, Matrix.inv_mul_of_invertible, Matrix.vecMul_one]

omit [DecidableEq L] [NeZero ℓ] [DecidableEq 𝔽q] h_Fq_char_prime h_β₀_eq_1 in
theorem iNovelToMonomial_monomialToINovel_inverse (i : Fin r) (h_i : i ≤ ℓ)
  (coeffs : Fin (2 ^ (ℓ - i)) → L) :
    monomialToINovelCoeffs 𝔽q β h_ℓ_add_R_rate i h_i
      (iNovelToMonomialCoeffs 𝔽q β h_ℓ_add_R_rate i h_i coeffs) = coeffs := by
  unfold monomialToINovelCoeffs iNovelToMonomialCoeffs
  dsimp
  let A := intermediateChangeOfBasisMatrix 𝔽q β h_ℓ_add_R_rate i
  rw [Matrix.vecMul_vecMul]
  simp only [Matrix.invOf_eq_nonsing_inv, Matrix.mul_inv_of_invertible, Matrix.vecMul_one]

-- TODO: intermediate counterpart of `novelPolynomialBasis` for arbitrary subspace level `i`

omit [DecidableEq L] [NeZero ℓ] [DecidableEq 𝔽q] h_Fq_char_prime h_β₀_eq_1 in
/-- **Reconstruction Lemma**:
    If `P` has degree < 2^(ℓ-i), and we convert its coefficients to the intermediate novel basis,
    the resulting `intermediateEvaluationPoly` is exactly `P`.
-/
lemma intermediateEvaluationPoly_from_inovel_coeffs_eq_self
    (i : Fin r) (h_i : i ≤ ℓ) (P : L[X])
    (hP_deg : P.degree < 2 ^ (ℓ - i.val)) :
    intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate (i := i) (h_i := h_i)
      (coeffs := getINovelCoeffs 𝔽q β h_ℓ_add_R_rate i h_i P) = P := by
  -- 1. Apply extensionality (two polys are equal if all coeffs are equal)
  apply Polynomial.ext
  intro k
  let N := 2 ^ (ℓ - i.val)
  set novel_coeffs := getINovelCoeffs 𝔽q β h_ℓ_add_R_rate i h_i P
  -- 2. Case Analysis on k
  by_cases hk : k < N
  · let k_fin : Fin N := ⟨k, hk⟩
    -- LHS expansion
    conv_lhs => rw [intermediateEvaluationPoly]
    -- coeff (∑ C * X_basis) = ∑ coeff (C * X_basis) = ∑ C * coeff (X_basis)
    simp only [finset_sum_coeff, coeff_C_mul]
    -- Crucial Step: Recognize this sum as Matrix Multiplication
    -- ∑_j (novel_j * coeff(Basis_j, k)) is exactly the k-th component of (novel * A)
    -- where A is the intermediateChangeOfBasisMatrix.
    let A := intermediateChangeOfBasisMatrix 𝔽q β h_ℓ_add_R_rate i h_i
    -- By definition of A, A_jk = coeff(Basis_j, k)
    have h_matrix_def : ∀ j, (intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate (i := i)
      (h_i := h_i) (j := j)).coeff k = A j k_fin := fun j => by
      dsimp only [intermediateChangeOfBasisMatrix, intermediateToCoeffsVec,
        intermediateBasisVectors, LinearMap.coe_mk, AddHom.coe_mk, A]
    simp_rw [h_matrix_def]
    -- `⊢ ∑ x, novel_coeffs x * A x k_fin = P.coeff k`, which is (vecMul novel_coeffs A) k_fin
    have h_left_eq : ∑ x, novel_coeffs x * A x k_fin = Matrix.vecMul novel_coeffs A k_fin := by
      dsimp only [Matrix.vecMul, dotProduct]
    conv_lhs => rw [h_left_eq] -- change to vecMul notation
    -- Apply the Inversion Logic
    -- novel_coeffs was defined as (monomial * A⁻¹)
    -- So we have (monomial * A⁻¹) * A
    unfold novel_coeffs getINovelCoeffs monomialToINovelCoeffs
    -- We need to unfold the let binding inside the goal
    -- It is easier to rewrite the vector multiplication: (v * A⁻¹) * A = v * (A⁻¹ * A) = v * I = v
    rw [Matrix.vecMul_vecMul]
    rw [invOf_mul_self]
    rw [Matrix.vecMul_one]
  · -- Case k >= N (Out of bounds)
    push_neg at hk
    -- RHS is 0 because P has degree < N
    rw [Polynomial.coeff_eq_zero_of_degree_lt (n := k) (p := intermediateEvaluationPoly 𝔽q β
      h_ℓ_add_R_rate i h_i novel_coeffs) (h := by
      let res := degree_intermediateEvaluationPoly_lt 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := i) h_i (coeffs := novel_coeffs)
      calc
        _ < (2 : WithBot ℕ) ^ (ℓ - i.val) := by omega
        _ ≤ k := by norm_cast
    )]
    rw [Polynomial.coeff_eq_zero_of_degree_lt (n := k) (p := P) (h := by
      calc
        _ < (2 : WithBot ℕ) ^ (ℓ - i.val) := by omega
        _ ≤ k := by norm_cast
    )]

end IntermediateNovelPolynomialBasis


/-- The even and odd refinements of `P⁽ⁱ⁾(X)` which are polynomials in the `(i+1)`-th basis.
`P₀⁽ⁱ⁺¹⁾(Y) = ∑_{j=0}^{2^{ℓ-i-1}-1} a_{2j} ⋅ Xⱼ⁽ⁱ⁺¹⁾(Y)`
`P₁⁽ⁱ⁺¹⁾(Y) = ∑_{j=0}^{2^{ℓ-i-1}-1} a_{2j+1} ⋅ Xⱼ⁽ⁱ⁺¹⁾(Y)` -/
noncomputable def evenRefinement (i : Fin r) (h_i : i < ℓ)
    (coeffs : Fin (2 ^ (ℓ - i)) → L) : L[X] :=
  ∑ (⟨j, hj⟩: Fin (2^(ℓ-i-1))), C (coeffs ⟨j*2, by
    calc _ < 2 ^ (ℓ - i - 1) * 2 := by omega
      _ = 2 ^ (ℓ - i) := Nat.two_pow_pred_mul_two (w:=ℓ - i) (h:=by omega)
  ⟩) * (intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate (i := ⟨i.val+1, by omega⟩)
    (h_i := by simp only; omega) ⟨j, hj⟩)

noncomputable def oddRefinement (i : Fin r) (h_i : i < ℓ)
    (coeffs : Fin (2 ^ (ℓ - i)) → L) : L[X] :=
  ∑ (⟨j, hj⟩: Fin (2^(ℓ-i-1))), C (coeffs ⟨j*2+1, by
    calc _ < 2 ^ (ℓ - i - 1) * 2 := by omega
      _ = 2 ^ (ℓ - i) := Nat.two_pow_pred_mul_two (w:=ℓ - i) (h:=by omega)
  ⟩) * (intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate (i := ⟨i.val+1, by omega⟩)
    (h_i := by simp only; omega) ⟨j, hj⟩)

omit [DecidableEq 𝔽q] [DecidableEq L] [NeZero ℓ] h_Fq_char_prime hF₂ hβ_lin_indep h_β₀_eq_1 in
/-- **Key Polynomial Identity (Equation 39)**. This identity is the foundation for the
butterfly operation in the Additive NTT. It relates a polynomial in the `i`-th basis to
its even and odd parts expressed in the `(i+1)`-th basis via the quotient map `q⁽ⁱ⁾`.
`∀ i ∈ {0, ..., ℓ-1}, P⁽ⁱ⁾(X) = P₀⁽ⁱ⁺¹⁾(q⁽ⁱ⁾(X)) + X ⋅ P₁⁽ⁱ⁺¹⁾(q⁽ⁱ⁾(X))` -/
theorem evaluation_poly_split_identity (i : Fin r) (h_i : i < ℓ)
    (coeffs : Fin (2 ^ (ℓ - i)) → L) :
  let P_i: L[X] := intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate (i := i) (h_i := by omega) coeffs
  let P_even_i_plus_1: L[X] := evenRefinement 𝔽q β h_ℓ_add_R_rate i h_i coeffs
  let P_odd_i_plus_1: L[X] := oddRefinement 𝔽q β h_ℓ_add_R_rate i h_i coeffs
  let q_i: L[X] := qMap 𝔽q β i
  P_i = (P_even_i_plus_1.comp q_i) + X * (P_odd_i_plus_1.comp q_i) := by
  simp only [intermediateEvaluationPoly]
  simp only [evenRefinement, Fin.eta, sum_comp, mul_comp, C_comp, oddRefinement]
  set leftEvenTerm := ∑ ⟨j, hj⟩ : Fin (2 ^ (ℓ - ↑i - 1)), C (coeffs ⟨j * 2, by
    exact mul_two_add_bit_lt_two_pow j (ℓ-i-1) (ℓ-i) ⟨0, by omega⟩ (by omega) (by omega)
  ⟩) * intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate (i := i) (h_i := by omega) ⟨j * 2, by
    exact mul_two_add_bit_lt_two_pow j (ℓ-i-1) (ℓ-i) ⟨0, by omega⟩ (by omega) (by omega)
  ⟩
  set leftOddTerm := ∑ ⟨j, hj⟩ : Fin (2 ^ (ℓ - ↑i - 1)), C (coeffs ⟨j * 2 + 1, by
    apply mul_two_add_bit_lt_two_pow j (ℓ-i-1) (ℓ-i) ⟨1, by omega⟩ (by omega) (by omega)
  ⟩) * intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate (i := i) (h_i := by omega) ⟨j * 2 + 1, by
    exact mul_two_add_bit_lt_two_pow j (ℓ-i-1) (ℓ-i) ⟨1, by omega⟩ (by omega) (by omega)
  ⟩
  have h_split_P_i: ∑ ⟨j, hj⟩ : Fin (2 ^ (ℓ - ↑i)), C (coeffs ⟨j, by
    apply lt_two_pow_of_lt_two_pow_exp_le j (ℓ-i) (ℓ-i) (by omega) (by omega)
  ⟩) * intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate (i := i) (h_i := by omega) ⟨j, by omega⟩ =
  leftEvenTerm + leftOddTerm
  := by
    unfold leftEvenTerm leftOddTerm
    simp only [Fin.eta]
    -- ⊢ ∑ k ∈ Fin (2 ^ (ℓ - ↑i)), C (coeffsₖ) * Xₖ⁽ⁱ⁾(X) = -- just pure even odd split
    -- ∑ k ∈ Fin (2 ^ (ℓ - ↑i - 1)), C (coeffs₂ₖ) * X₂ₖ⁽ⁱ⁾(X) +
    -- ∑ k ∈ Fin (2 ^ (ℓ - ↑i - 1)), C (coeffs₂ₖ+1) * X₂ₖ+1⁽ⁱ⁾(X)
    set f1 := fun x: ℕ => -- => use a single function to represent the sum
      if hx: x < 2 ^ (ℓ - ↑i) then
        C (coeffs ⟨x, hx⟩) *
          intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate (i := i) (h_i := by omega) (j := ⟨x, by omega⟩)
      else 0
    have h_x: ∀ x: Fin (2 ^ (ℓ - ↑i)), f1 x.val =
      C (coeffs ⟨x.val, by omega⟩) *
        intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate (i := i) (h_i := by omega) (j := ⟨x.val, by omega⟩)  := by
      intro x
      unfold f1
      simp only [Fin.is_lt, ↓reduceDIte, Fin.eta]
    conv_lhs =>
      enter [2, x]
      rw [←h_x x]
    have h_x_2: ∀ x: Fin (2 ^ (ℓ - ↑i - 1)), f1 (x*2) =
      C (coeffs ⟨x.val * 2, by
        calc _ < 2 ^ (ℓ - i - 1) * 2 := by omega
          _ = 2 ^ (ℓ - i) := Nat.two_pow_pred_mul_two (w:=ℓ - i) (h:=by omega)
      ⟩) *
        intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate (i := i) (h_i := by omega) (j := ⟨x.val * 2, by
          exact mul_two_add_bit_lt_two_pow x.val (ℓ-i-1) (ℓ-i) ⟨0, by omega⟩ (by omega) (by omega)
        ⟩) := by
      intro x
      unfold f1
      -- simp only
      have h_x_lt_2_pow_i_minus_1 :=
        mul_two_add_bit_lt_two_pow x.val (ℓ-i-1) (ℓ-i) ⟨0, by omega⟩ (by omega) (by omega)
      simp at h_x_lt_2_pow_i_minus_1
      simp only [h_x_lt_2_pow_i_minus_1, ↓reduceDIte]
    conv_rhs =>
      enter [1, 2, x]
      rw [←h_x_2 x]
    have h_x_3: ∀ x: Fin (2 ^ (ℓ - ↑i - 1)), f1 (x*2+1) =
      C (coeffs ⟨x.val * 2 + 1, by
        calc _ < 2 ^ (ℓ - i - 1) * 2 := by omega
          _ = 2 ^ (ℓ - i) := Nat.two_pow_pred_mul_two (w:=ℓ - i) (h:=by omega)
      ⟩) *
        intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate (i := i) (h_i := by omega) (j := ⟨x.val * 2 + 1, by
          exact mul_two_add_bit_lt_two_pow x.val (ℓ-i-1) (ℓ-i) ⟨1, by omega⟩ (by omega) (by omega)
        ⟩) := by
      intro x
      unfold f1
      -- simp only
      have h_x_lt_2_pow_i_minus_1 := mul_two_add_bit_lt_two_pow x.val
        (ℓ-i-1) (ℓ-i) ⟨1, by omega⟩ (by omega) (by omega)
      simp only [h_x_lt_2_pow_i_minus_1, ↓reduceDIte]
    conv_rhs =>
      enter [2, 2, x]
      rw [←h_x_3 x]
    -- ⊢ ∑ x, f1 ↑x = ∑ x, f1 (↑x * 2) + ∑ x, f1 (↑x * 2 + 1)
    have h_1: ∑ i ∈ Finset.range (2 ^ (ℓ - ↑i)), f1 i
      = ∑ i ∈ Finset.range (2 ^ (ℓ - ↑i - 1 + 1)), f1 i := by
      congr
      omega
    have res := Fin.sum_univ_odd_even (f:=f1) (n:=(ℓ - ↑i - 1))
    conv_rhs at res =>
      rw [Fin.sum_univ_eq_sum_range]
      rw [←h_1]
      rw [←Fin.sum_univ_eq_sum_range]
    rw [←res]
    congr
    · funext i
      rw [mul_comm]
    · funext i
      rw [mul_comm]
  conv_lhs => rw [h_split_P_i]
  set rightEvenTerm := ∑ ⟨j, hj⟩ : Fin (2 ^ (ℓ - ↑i - 1)),
      C (coeffs ⟨j * 2, by
        calc _ < 2 ^ (ℓ - i - 1) * 2 := by omega
          _ = 2 ^ (ℓ - i) := Nat.two_pow_pred_mul_two (w:=ℓ - i) (h:=by omega)
      ⟩) *
        (intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate (i := ⟨i.val+1, by omega⟩) (h_i := by simp only; omega) ⟨j, by
          apply lt_two_pow_of_lt_two_pow_exp_le (x:=j)
            (i := ℓ-↑i-1) (j:=ℓ-↑i-1) (by omega) (by omega)
        ⟩).comp (qMap 𝔽q β i)
  set rightOddTerm :=
    X *
      ∑ ⟨j, hj⟩ : Fin (2 ^ (ℓ - ↑i - 1)),
        C (coeffs ⟨j * 2 + 1, by
          calc _ < 2 ^ (ℓ - i - 1) * 2 := by omega
            _ = 2 ^ (ℓ - i) := Nat.two_pow_pred_mul_two (w:=ℓ - i) (h:=by omega)
        ⟩) *
          (intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate (i := ⟨i.val+1, by omega⟩) (h_i := by simp only; omega) ⟨j, by
            apply lt_two_pow_of_lt_two_pow_exp_le (x:=j)
              (i := ℓ-↑i-1) (j:=ℓ-↑i-1) (by omega) (by omega)
          ⟩).comp (qMap 𝔽q β i)
  conv_rhs => change rightEvenTerm + rightOddTerm
  have h_right_even_term: leftEvenTerm = rightEvenTerm := by
    unfold rightEvenTerm leftEvenTerm
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Fin.eta, mul_eq_mul_left_iff, map_eq_zero]
    --  X₂ⱼ⁽ⁱ⁾ = Xⱼ⁽ⁱ⁺¹⁾(q⁽ⁱ⁾(X)) ∨ a₂ⱼ = 0
    by_cases h_a_j_eq_0: coeffs ⟨j * 2, by
      calc _ < 2 ^ (ℓ - i - 1) * 2 := by omega
        _ = 2 ^ (ℓ - i) := Nat.two_pow_pred_mul_two (w:=ℓ - i) (h:=by omega)
    ⟩ = 0
    · simp only [h_a_j_eq_0, or_true]
    · simp only [h_a_j_eq_0, or_false]
      --  X₂ⱼ⁽ⁱ⁾ = Xⱼ⁽ⁱ⁺¹⁾(q⁽ⁱ⁾(X))
      exact even_index_intermediate_novel_basis_decomposition (L := L)
        𝔽q β h_ℓ_add_R_rate (i := i) (h_i := h_i) j
  have h_right_odd_term: rightOddTerm = leftOddTerm := by
    unfold rightOddTerm leftOddTerm
    simp only [Fin.eta]
    conv_rhs =>
      simp only [Fin.is_lt, Fin.eta]
      enter [2, x];
      rw [odd_index_intermediate_novel_basis_decomposition 𝔽q β (h_i := h_i)]
      rw [mul_comm (a:=X)]
    rw [Finset.mul_sum]
    congr
    funext x
    ring_nf -- just associativity and commutativity of multiplication in L[X]
    rfl
  rw [h_right_even_term, h_right_odd_term]

omit [DecidableEq 𝔽q] [DecidableEq L] [NeZero ℓ] hF₂ in
-- P⁽⁰⁾(X) = P(X)
lemma intermediate_poly_P_base (h_ℓ : ℓ ≤ r) (coeffs : Fin (2 ^ ℓ) → L) :
  intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate (i := 0)
    (h_i := by simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_le]) coeffs =
    polynomialFromNovelCoeffs 𝔽q β ℓ h_ℓ coeffs := by
  unfold polynomialFromNovelCoeffs intermediateEvaluationPoly
  simp only [Fin.coe_ofNat_eq_mod]
  conv_rhs =>
    enter [2, j]
    rw [←base_intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate j]
  congr

end IntermediateStructures
section AlgorithmCorrectness

/-! ## 2. The Additive NTT Algorithm and Correctness

This section describes the construction of the evaluation points,
the tiling of coefficients, the main loop invariant, and the final
correctness theorem for the Additive NTT algorithm.
-/

/-- Constructs an evaluation point `ω` in the domain `S⁽ⁱ⁾` from a Nat.getBit representation.
This uses the `𝔽q`-basis of `S⁽ⁱ⁾` from `sDomain_basis`.
`ω_{u,b,i} = b⋅Ŵᵢ(βᵢ) + ∑_{k=0}^{|u|-1} uₖ ⋅ Ŵᵢ(β_{i+1+k})`
where `(u,b)` is a Nat.getBit string of length `ℓ + R - i`.
Computes the twiddle factor `t` for a given stage `i` and high-order bits `u`.
`t := Σ_{k=0}^{ℓ+R-i-1} u_k ⋅ Ŵᵢ(β_{i+k})`.
This corresponds to the `x₀` term in the recursive butterfly identity.
-/
noncomputable def evaluationPointω (i : Fin r) (h_i : i ≤ ℓ)
    (x : Fin (2 ^ (ℓ + R_rate - i))) : L := -- x = u || b
    -- Add the linear combination of the remaining basis vectors
  ∑ (⟨k, hk⟩: Fin (ℓ + R_rate - i)),
    if Nat.getBit k x.val = 1 then
      (normalizedW 𝔽q β ⟨i, by omega⟩).eval (β ⟨i + k, by omega⟩)
    else
      0

end AlgorithmCorrectness
end AdditiveNTT

namespace AdditiveNTT.Comp

universe u

open Polynomial AdditiveNTT Module

variable {r : ℕ} [NeZero r]
variable {L : Type u} [Field L] [Fintype L] [DecidableEq L]
variable {𝔽q : Type u} [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
variable [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ R_rate : ℕ} [NeZero ℓ] (h_ℓ_add_R_rate : ℓ + R_rate < r)

/-- Executable value-level encoding of points in `U i` by bit-index. -/
abbrev bitsToUValue (i : Fin r) (k : Fin (2 ^ i.val)) : L :=
  AdditiveNTT.bitsToUValue (β := β) i k

/-- Executable subtype-level encoding of points in `U i` by bit-index. -/
abbrev bitsToU (i : Fin r) (k : Fin (2 ^ i.val)) :
    AdditiveNTT.U (L := L) (𝔽q := 𝔽q) (β := β) i :=
  AdditiveNTT.bitsToU (𝔽q := 𝔽q) (β := β) i k

omit [DecidableEq 𝔽q] h_Fq_char_prime h_β₀_eq_1 in
/-- Bijection witness for executable encoding `bitsToU`. -/
theorem bitsToU_bijective (i : Fin r) :
    Function.Bijective (bitsToU (𝔽q := 𝔽q) (β := β) i) := by
  exact AdditiveNTT.bitsToU_bijective (𝔽q := 𝔽q) (β := β) i

/-- Executable enumeration of all elements in `U i`. -/
abbrev getUElements (i : Fin r) : List L :=
  AdditiveNTT.getUElements (β := β) i

/-- Executable evaluation of `Wᵢ` at a point. -/
abbrev evalWAt (i : Fin r) (x : L) : L :=
  AdditiveNTT.evalWAt (β := β) i x

/-- Executable evaluation of `Ŵᵢ` at a point. -/
abbrev evalNormalizedWAt (i : Fin r) (x : L) : L :=
  AdditiveNTT.evalNormalizedWAt (β := β) i x

/-- Computable domain companion with loose indexing (`Fin r`). -/
abbrev sDomain (i : Fin r) : Subspace 𝔽q L :=
  AdditiveNTT.sDomainComp (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i

/-- Explicit canonical domain alias in `Comp` namespace. -/
noncomputable abbrev canonicalSDomain (i : Fin r) : Subspace 𝔽q L :=
  AdditiveNTT.sDomain (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i

/-- Upper-domain index `ℓ + R_rate`, used to decode query points from `Fin` indices. -/
def upperDomainIndex : Fin r := ⟨ℓ + R_rate, h_ℓ_add_R_rate⟩

/-- Decode a global domain index into a point in `Comp.sDomain i` (computable carrier). -/
def indexToSDomain (i : Fin r) (k : Fin (2 ^ (ℓ + R_rate))) :
    sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i :=
  let uTop : AdditiveNTT.U (L := L) (𝔽q := 𝔽q) (β := β)
      (upperDomainIndex (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
    bitsToU (𝔽q := 𝔽q) (β := β)
      (i := upperDomainIndex (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) k
  ⟨AdditiveNTT.evalNormalizedWLinearMap (𝔽q := 𝔽q) (β := β) i (uTop : L), by
    change
      AdditiveNTT.evalNormalizedWLinearMap (𝔽q := 𝔽q) (β := β) i
        (uTop : L)
        ∈ AdditiveNTT.sDomainComp (𝔽q := 𝔽q) (β := β)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
    unfold AdditiveNTT.sDomainComp
    exact ⟨(uTop : L), uTop.property, rfl⟩⟩

/-- Decode a global domain index into the query domain (`i = 0`). -/
def indexToSDomainZero (k : Fin (2 ^ (ℓ + R_rate))) :
    sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 :=
  indexToSDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0) k

/-- Embed a local stage-`i` index into a global loose index by padding `i` low bits with `0`. -/
def localIndexToGlobalIndex (i : Fin r) (h_i : i < ℓ + R_rate)
    (idx : Fin (2 ^ (ℓ + R_rate - i.val))) :
    Fin (2 ^ (ℓ + R_rate)) := by
  let lowZeros : Fin (2 ^ i.val) := 0
  let fullIdx : Fin (2 ^ ((ℓ + R_rate - i.val) + i.val)) :=
    Nat.joinBits (low := lowZeros) (high := idx)
  have h_bits : (ℓ + R_rate - i.val) + i.val = ℓ + R_rate := by
    exact Nat.sub_add_cancel (Nat.le_of_lt h_i)
  exact cast (by rw [h_bits]) fullIdx

/-- Decode a local stage-`i` index to a point in `Comp.sDomain i` (computable carrier). -/
def localIndexToSDomain (i : Fin r) (h_i : i < ℓ + R_rate)
    (idx : Fin (2 ^ (ℓ + R_rate - i.val))) :
    sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i :=
  indexToSDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
    (localIndexToGlobalIndex (i := i) h_i idx)

/-- Deterministic local-index decoder for points in `Comp.sDomain`.
Falls back to `0` only if exhaustive search unexpectedly fails. -/
def sDomainPointToLocalIndex (i : Fin r) (h_i : i < ℓ + R_rate)
    (x : sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :
    Fin (2 ^ (ℓ + R_rate - i.val)) :=
  match (List.finRange (2 ^ (ℓ + R_rate - i.val))).find? (fun idx =>
      decide (((localIndexToSDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i h_i idx : sDomain (𝔽q := 𝔽q) (β := β)
        (ℓ := ℓ) (R_rate := R_rate) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) : L) = x.val)) with
  | some idx => idx
  | none => 0

/-- At stage `0`, the executable normalized evaluation map is the identity. -/
lemma evalNormalizedWLinearMap_zero_apply (x : L) :
    AdditiveNTT.evalNormalizedWLinearMap (𝔽q := 𝔽q) β (0 : Fin r) x = x := by
  rw [AdditiveNTT.evalNormalizedWLinearMap_apply]
  rw [AdditiveNTT.normalizedW, AdditiveNTT.W₀_eq_X, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X]
  rw [h_β₀_eq_1.out, div_one]
  simp

/-- At stage `0`, the computable query domain is exactly the top additive subspace. -/
lemma sDomainZero_eq_upperDomain :
    sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 =
    AdditiveNTT.U (𝔽q := 𝔽q) (β := β)
      (upperDomainIndex (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨u, hu, rfl⟩
    rw [evalNormalizedWLinearMap_zero_apply (𝔽q := 𝔽q) (β := β) u]
    exact hu
  · intro hx
    refine ⟨x, hx, ?_⟩
    rw [evalNormalizedWLinearMap_zero_apply (𝔽q := 𝔽q) (β := β) x]

/-- The executable zero-stage decoder agrees with the explicit bit encoding on values. -/
lemma indexToSDomainZero_val_eq_bitsToU_val (k : Fin (2 ^ (ℓ + R_rate))) :
    ((indexToSDomainZero (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) k : sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ)
        (R_rate := R_rate) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0) : L) =
      (bitsToU (𝔽q := 𝔽q) (β := β)
        (i := upperDomainIndex (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) k : L) := by
  unfold indexToSDomainZero indexToSDomain
  dsimp
  rw [evalNormalizedWLinearMap_zero_apply (𝔽q := 𝔽q) (β := β)
    ((bitsToU (𝔽q := 𝔽q) (β := β)
      (i := upperDomainIndex (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) k : L))]

/-- The zero-stage decoder is a computable bijection from global indices to query-domain points. -/
theorem indexToSDomainZero_bijective :
    Function.Bijective
      (indexToSDomainZero (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) := by
  let upperIdx : Fin r := upperDomainIndex (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  constructor
  · intro a b hab
    have hsub :
        bitsToU (𝔽q := 𝔽q) (β := β) (i := upperIdx) a =
          bitsToU (𝔽q := 𝔽q) (β := β) (i := upperIdx) b := by
      apply Subtype.ext
      have hval := congrArg Subtype.val hab
      rw [indexToSDomainZero_val_eq_bitsToU_val (𝔽q := 𝔽q) (β := β)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)] at hval
      rw [indexToSDomainZero_val_eq_bitsToU_val (𝔽q := 𝔽q) (β := β)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)] at hval
      exact hval
    exact (bitsToU_bijective (𝔽q := 𝔽q) (β := β) (i := upperIdx)).injective hsub
  · intro x
    have hxU : x.1 ∈ AdditiveNTT.U (𝔽q := 𝔽q) (β := β) upperIdx := by
      rw [← sDomainZero_eq_upperDomain (𝔽q := 𝔽q) (β := β)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)]
      exact x.2
    let uTop : AdditiveNTT.U (𝔽q := 𝔽q) (β := β) upperIdx := ⟨x.1, hxU⟩
    obtain ⟨k, hk⟩ := (bitsToU_bijective (𝔽q := 𝔽q) (β := β)
      (i := upperIdx)).surjective uTop
    refine ⟨k, ?_⟩
    apply Subtype.ext
    rw [indexToSDomainZero_val_eq_bitsToU_val (𝔽q := 𝔽q) (β := β)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)]
    exact congrArg Subtype.val hk

/-- Directional bridge: points in `Comp.sDomain` are points in canonical `sDomain`. -/
theorem mem_canonicalSDomain_of_mem_compSDomain {i : Fin r} {x : L}
    (hx : x ∈ sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :
    x ∈ canonicalSDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i := by
  rcases hx with ⟨u, hu, rfl⟩
  refine ⟨u, hu, ?_⟩
  exact (AdditiveNTT.evalNormalizedWLinearMap_apply
    (𝔽q := 𝔽q) (β := β) (i := i) (x := u)).symm

/-- Directional bridge: canonical `sDomain` points are points in `Comp.sDomain`. -/
theorem mem_compSDomain_of_mem_canonicalSDomain {i : Fin r} {x : L}
    (hx : x ∈ canonicalSDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :
    x ∈ sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i := by
  rcases hx with ⟨u, hu, rfl⟩
  refine ⟨u, hu, ?_⟩
  exact AdditiveNTT.evalNormalizedWLinearMap_apply
    (𝔽q := 𝔽q) (β := β) (i := i) (x := u)

/-- Directional bridge equality between `Comp.sDomain` and canonical `sDomain` carriers. -/
theorem compSDomain_eq_canonicalSDomain (i : Fin r) :
    sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i =
    canonicalSDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i := by
  ext x
  constructor
  · exact mem_canonicalSDomain_of_mem_compSDomain (𝔽q := 𝔽q) (β := β)
      (ℓ := ℓ) (R_rate := R_rate) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  · exact mem_compSDomain_of_mem_canonicalSDomain (𝔽q := 𝔽q) (β := β)
      (ℓ := ℓ) (R_rate := R_rate) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)

/-- Bridge: equality transport for `Comp.sDomain` across equal indices. -/
lemma compSDomain_eq_of_eq {i j : Fin r} (h : i = j) :
    AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i =
    AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j := by
  subst h
  rfl

/-- Basis on the computable carrier, transported from canonical basis via carrier equality.
Noncomputable because transport uses `LinearEquiv.ofEq` on the canonical basis. -/
noncomputable abbrev compSDomainBasisViaCanonical (i : Fin r) (h_i : i < ℓ + R_rate) :
    Basis (Fin (ℓ + R_rate - i)) 𝔽q (
      AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) := by
  let e :
      AdditiveNTT.sDomain (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i ≃ₗ[𝔽q]
        AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i :=
    LinearEquiv.ofEq _ _ (compSDomain_eq_canonicalSDomain (𝔽q := 𝔽q) (β := β)
      (ℓ := ℓ) (R_rate := R_rate) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).symm
  exact (AdditiveNTT.sDomain_basis (𝔽q := 𝔽q) (β := β) h_ℓ_add_R_rate i h_i).map e

/-- Basis point formula for `compSDomainBasisViaCanonical`. -/
lemma get_compSDomainBasisViaCanonical (i : Fin r) (h_i : i < ℓ + R_rate) :
    ∀ k : Fin (ℓ + R_rate - i),
      (compSDomainBasisViaCanonical (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i h_i) k =
      Polynomial.eval (β ⟨i + k.val, by omega⟩) (normalizedW 𝔽q β i) := by
  intro k
  unfold compSDomainBasisViaCanonical
  simp only [Basis.map_apply, LinearEquiv.coe_ofEq_apply]
  exact AdditiveNTT.get_sDomain_basis (𝔽q := 𝔽q) (β := β) h_ℓ_add_R_rate i h_i k

/-- Bridge: `Fintype` instance for the `Comp.sDomain` carrier. -/
noncomputable instance fintype_comp_sDomain (i : Fin r) :
    Fintype (AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) := by
  rw [compSDomain_eq_canonicalSDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i]
  infer_instance

lemma compSDomain_card (i : Fin r) (h_i : i < ℓ + R_rate) :
    Fintype.card (
      AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) =
      (Fintype.card 𝔽q) ^ (ℓ + R_rate - i) := by
  have h_eq :=
    compSDomain_eq_canonicalSDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
  let e :
      AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i ≃
      AdditiveNTT.sDomain (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i :=
    Equiv.cast (congrArg (fun S : Subspace 𝔽q L => ↥S) h_eq)
  rw [Fintype.card_congr e]
  exact AdditiveNTT.sDomain_card (𝔽q := 𝔽q) (β := β) h_ℓ_add_R_rate i h_i

@[deprecated compSDomain_eq_canonicalSDomain (since := "2026-04-16")]
alias computableSDomain_eq_canonicalSDomain := compSDomain_eq_canonicalSDomain

@[deprecated mem_canonicalSDomain_of_mem_compSDomain (since := "2026-04-16")]
alias mem_canonicalSDomain_of_mem_computableSDomain := mem_canonicalSDomain_of_mem_compSDomain

@[deprecated mem_compSDomain_of_mem_canonicalSDomain (since := "2026-04-16")]
alias mem_computableSDomain_of_mem_canonicalSDomain := mem_compSDomain_of_mem_canonicalSDomain

@[deprecated compSDomain_eq_of_eq (since := "2026-04-16")]
alias computableSDomain_eq_of_eq := compSDomain_eq_of_eq

@[deprecated compSDomain_card (since := "2026-04-16")]
alias computableSDomain_card := compSDomain_card

/-- Index encoding on computable carrier via canonical `sDomainToFin`.
Noncomputable because it reuses canonical noncomputable encoding after membership bridge. -/
noncomputable def compSDomainToFinViaCanonical (i : Fin r) (h_i : i < ℓ + R_rate)
    (x : AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :
    Fin (2 ^ (ℓ + R_rate - i.val)) :=
  AdditiveNTT.sDomainToFin (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i h_i
    ⟨x.1, by
      exact mem_canonicalSDomain_of_mem_compSDomain
        (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) x.2⟩

noncomputable section

@[deprecated compSDomainBasisViaCanonical (since := "2026-04-16")]
abbrev computableSDomainBasis (i : Fin r) (h_i : i < ℓ + R_rate) :
    Basis (Fin (ℓ + R_rate - i)) 𝔽q (
      AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :=
  compSDomainBasisViaCanonical (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i h_i

@[deprecated get_compSDomainBasisViaCanonical (since := "2026-04-16")]
alias get_computableSDomainBasis := get_compSDomainBasisViaCanonical

@[deprecated compSDomainToFinViaCanonical (since := "2026-04-16")]
abbrev computableSDomainToFin (i : Fin r) (h_i : i < ℓ + R_rate)
    (x : AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :
    Fin (2 ^ (ℓ + R_rate - i.val)) :=
  compSDomainToFinViaCanonical (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i h_i x

end

/-- Cast from `Comp.sDomain` (computable carrier) to canonical `sDomain` carrier. -/
def toCanonicalSDomain (i : Fin r)
    (x : sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :
    AdditiveNTT.sDomain (𝔽q := 𝔽q) (β := β)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i :=
  ⟨x.1, mem_canonicalSDomain_of_mem_compSDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ)
    (R_rate := R_rate) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) x.2⟩

@[deprecated compSDomain_eq_canonicalSDomain (since := "2026-04-16")]
alias sDomainComp_eq_sDomain := compSDomain_eq_canonicalSDomain

@[deprecated mem_canonicalSDomain_of_mem_compSDomain (since := "2026-04-16")]
alias mem_sDomain_of_mem_sDomainComp := mem_canonicalSDomain_of_mem_compSDomain

@[deprecated mem_compSDomain_of_mem_canonicalSDomain (since := "2026-04-16")]
alias mem_sDomainComp_of_mem_sDomain := mem_compSDomain_of_mem_canonicalSDomain

@[deprecated compSDomain_eq_of_eq (since := "2026-04-16")]
alias sDomain_eq_of_eq := compSDomain_eq_of_eq

@[deprecated compSDomainBasisViaCanonical (since := "2026-04-16")]
alias sDomain_basis := compSDomainBasisViaCanonical

@[deprecated get_compSDomainBasisViaCanonical (since := "2026-04-16")]
alias get_sDomain_basis := get_compSDomainBasisViaCanonical

@[deprecated compSDomain_card (since := "2026-04-16")]
alias sDomain_card := compSDomain_card

@[deprecated compSDomainToFinViaCanonical (since := "2026-04-16")]
alias sDomainToFin := compSDomainToFinViaCanonical

end AdditiveNTT.Comp
