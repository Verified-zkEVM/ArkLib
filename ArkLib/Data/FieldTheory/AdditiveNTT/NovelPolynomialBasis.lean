/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import CompPoly.Data.Nat.Bitwise
import CompPoly.Data.Polynomial.Frobenius
import CompPoly.Data.Polynomial.MonomialBasis
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Algebra.Polynomial.Degree.Definitions

/-!
# Novel Polynomial Basis

This file defines the components of a novel polynomial basis over a field `L` with degree `r` as an
algebra over its prime-characteristic subfield `𝔽q`, and an `𝔽q`-basis `β` for `L`.

## Main Definitions
- `Uᵢ`: `𝔽q`-linear span of the initial `i` vectors of our basis `β`
- `Wᵢ(X)`: subspace vanishing polynomial over `Uᵢ`, with normalized form `Ŵᵢ(X)`
- `{Xⱼ(X), j ∈ Fin 2^ℓ}`: basis vectors of `L⦃<2^ℓ⦄[X]` over `L` constructed from `Ŵᵢ(X)`
- `novelPolynomialBasis`: the novel polynomial basis for `L⦃<2^ℓ⦄[X]`
- `W_prod_comp_decomposition`: decomposition of `Wᵢ` into a product of compositions `Π c ∈ Uᵢ, (Wᵢ₋₁
  ∘ (X - c • βᵢ₋₁))`
- `W_linearity`: `Wᵢ` is `𝔽q`-linear and satisfies the recursion formula `Wᵢ = (Wᵢ₋₁)^|𝔽q| -
  ((Wᵢ₋₁)(βᵢ₋₁))^(|𝔽q|-1) * Wᵢ₋₁`

## TODOs
- Computable novel polynomial basis

## References

* [Lin, S., Chung, W., and Han, Y.S, *Novel polynomial basis and its application to
    Reed–Solomon erasure codes*][LCH14]
* [Von zur Gathen, J., and Gerhard, J., *Arithmetic and factorization of polynomial
    over F2 (extended abstract)*][GGJ96]
-/

set_option linter.style.longFile 1600

open Polynomial FiniteDimensional Finset Module

namespace AdditiveNTT

universe u

-- Fix a field `L` of degree `r` as an algebra over its prime-characteristic subfield `𝔽q`
variable {r : ℕ} [NeZero r]
variable {L : Type u} [Field L] [Fintype L] [DecidableEq L]
variable (𝔽q : Type u) [Field 𝔽q] [Fintype 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (h_dim : Module.finrank 𝔽q L = r)

-- We assume an `𝔽q`-basis for `L`, denoted by `(β₀, β₁, ..., β_{r-1})`, indexed by natural numbers.
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]

section LinearSubspaces

lemma fintype_card_gt_one_of_field (K : Type*) [Field K] [Fintype K] :
  1 < Fintype.card K :=
by
  exact Fintype.one_lt_card_iff.mpr ⟨(0 : K), 1, by simp only [ne_eq, zero_ne_one,
    not_false_eq_true]⟩

/-- **𝔽q-linear subspaces `Uᵢ`**

`∀ i ∈ {0, ..., r-1}`, we define `Uᵢ:= <β₀, ..., βᵢ₋₁>_{𝔽q}`
as the `𝔽q`-linear span of the initial `i` vectors of our basis `β`.

NOTE: We might allow `i = r` in the future if needed. -/
def U (i : Fin r) : Subspace 𝔽q L := Submodule.span 𝔽q (β '' (Set.Ico 0 i))

instance {i : Fin r} : Module (R := 𝔽q) (M := U 𝔽q β i) := Submodule.module _
instance {i : Fin r} : DecidableEq (U 𝔽q β i) := by exact instDecidableEqOfLawfulBEq
noncomputable instance {i : Fin r} (x : L) : Decidable (x ∈ (U 𝔽q β i : Set L)) := by
  exact Classical.propDecidable (x ∈ ↑(U 𝔽q β i))
-- e.g. prop => boolean

-- The dimension of `U i` is `i`.
omit [Fintype L] [Fintype 𝔽q] h_Fq_char_prime in
lemma finrank_U (i : Fin r) :
  Module.finrank 𝔽q (U 𝔽q β i) = i := by
  -- The dimension of the span of linearly independent vectors is the number of vectors.
  unfold U
  set basisUᵢ := β '' Set.Ico 0 i
  -- how to show that basis is of form: ι → L
  have h_basis_card: Fintype.card (basisUᵢ) = i := by
    unfold basisUᵢ -- ⊢ Fintype.card ↑(β '' Set.Ico 0 i) = ↑i
    rw [Set.card_image_of_injective] -- card of image of inj function = card of domain
    simp only [Fintype.card_ofFinset, Fin.card_Ico, Fin.coe_ofNat_eq_mod, Nat.zero_mod, tsub_zero]
    -- β is injective
    have h_inj : Function.Injective β := LinearIndependent.injective (hv := hβ_lin_indep.out)
    exact h_inj

  change Module.finrank 𝔽q (Submodule.span 𝔽q (basisUᵢ)) = i

  have h_linear_indepdendent_basis: LinearIndepOn 𝔽q id (β '' Set.Ico 0 i) := by
    have h_inj : Set.InjOn β (Set.Ico 0 i) := by
      intros x hx y hy hxy
      apply LinearIndependent.injective hβ_lin_indep.out
      exact hxy
    let ι : Set.Ico (0: Fin r) i → β '' Set.Ico 0 i := fun x => ⟨β x, Set.mem_image_of_mem β x.2⟩
    have h_bij : Function.Bijective ι := by
      constructor
      · intros x y hxy
        simp only [ι, Subtype.mk_eq_mk] at hxy
        -- ⊢ x - y
        apply Subtype.ext -- bring to equality in extension type: ⊢ ↑x = ↑y
        exact h_inj x.2 y.2 hxy
      · intro y
        rcases y with ⟨y, hy⟩
        obtain ⟨x, hx, hxy⟩ := (Set.mem_image β (Set.Ico 0 i) y).mp hy
        use ⟨x, hx⟩
        simp only [ι, hxy]
    let h_li := hβ_lin_indep.out.comp (Subtype.val : (Set.Ico (0: Fin r) i) → Fin r)
      Subtype.coe_injective
    have eq_subset : Set.range (β ∘ (Subtype.val : (Set.Ico (0: Fin r) i) → Fin r))
      = β '' Set.Ico 0 i := by
      rw [Set.range_comp]
      -- ⊢ β '' Set.range Subtype.val = β '' Set.Icc 0 (i - 1)
      rw [Subtype.range_coe] -- alternatively, we can unfold all defs & simp
    rw [←eq_subset]
    exact h_li.linearIndepOn_id
  rw [finrank_span_set_eq_card (R := 𝔽q) (M := L) (s := Set.image β (Set.Ico 0 i))
    (hs := h_linear_indepdendent_basis)]
  rw [Set.toFinset_card]
  exact h_basis_card

noncomputable instance fintype_U (i : Fin r) : Fintype (U 𝔽q β i) := by
  exact Fintype.ofFinite (U 𝔽q β i)

omit h_Fq_char_prime hF₂ in
-- The cardinality of the subspace `Uᵢ` is `2ⁱ`, which follows from its dimension.
lemma U_card (i : Fin r) :
    Fintype.card (U 𝔽q β i) = (Fintype.card 𝔽q)^i.val := by
  -- The cardinality of a vector space V is |F|^(dim V).
  rw [Module.card_eq_pow_finrank (K := 𝔽q) (V := U 𝔽q β i)]
  rw [finrank_U]

omit [Fintype L] [DecidableEq L] [Fintype 𝔽q] h_Fq_char_prime hβ_lin_indep in
/--
An essential helper lemma showing that `Uᵢ` is the union of all cosets of `Uᵢ₋₁`
generated by scaling `βᵢ₋₁` by elements of `𝔽q`.
-/
lemma U_i_is_union_of_cosets (i : Fin r) (hi : 0 < i) :
    (U 𝔽q β i : Set L) = ⋃ (c : 𝔽q), (fun u => c • β (i-1) + u) '' (U 𝔽q β (i - 1)) := by

  have h_decomp : U 𝔽q β i = U 𝔽q β (i-1) ⊔ Submodule.span 𝔽q {β (i-1)} := by
    unfold U
    have h_ico : Set.Ico 0 i = Set.Ico 0 (i - 1) ∪ {i - 1} := by
      ext k;
      simp only [Set.mem_Ico, Fin.zero_le, true_and, Set.union_singleton, Set.Ico_insert_right,
        Set.mem_Icc]
      -- ⊢ k < i ↔ k ≤ i - 1
      exact Fin.lt_iff_le_pred (a := k) (b := i) (h_b := by omega)
    rw [h_ico, Set.image_union, Set.image_singleton, Submodule.span_union]
  ext x
  conv_lhs => rw [h_decomp]
  -- ⊢ x ∈ ↑(U 𝔽q β (i - 1) ⊔ Submodule.span 𝔽q {β (i - 1)})
  -- ↔ x ∈ ⋃ c, (fun u ↦ c • β (i - 1) + u) '' ↑(U 𝔽q β (i - 1))
  rw [Submodule.coe_sup, Set.mem_add]
  constructor
  · rintro ⟨u, hu, v, hv, rfl⟩
    simp only [SetLike.mem_coe] at hu hv
    rw [Submodule.mem_span_singleton] at hv
    rcases hv with ⟨c, rfl⟩
    simp only [Set.mem_iUnion, Set.mem_image]
    exact ⟨c, u, hu, by rw [add_comm]⟩
  · intro hx
    simp only [Set.mem_iUnion, Set.mem_image] at hx
    rcases hx with ⟨c, u, hu, rfl⟩
    rw [add_comm]
    -- ⊢ ∃ x ∈ ↑(U 𝔽q β (i - 1)), ∃ y ∈ ↑(Submodule.span 𝔽q {β (i - 1)}), x + y = u + c • β (i - 1)
    exact ⟨u, hu, c • β (i-1), Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), rfl⟩

omit [Fintype L] [DecidableEq L] [Fintype 𝔽q] h_Fq_char_prime in
/-- The basis vector `βᵢ` is not an element of the subspace `Uᵢ`. -/
lemma βᵢ_not_in_Uᵢ (i : Fin r) :
    β i ∉ U 𝔽q β i := by
  -- `βᵢ` cannot be expressed as a linear combination of `<β₀, ..., βᵢ₋₁>`.
  -- This follows from the definition of linear independence of `β`
  have h_li := linearIndependent_iff_notMem_span.mp hβ_lin_indep.out i
  -- Uᵢ is the span of a subset of the "other" vectors.
  have h_subset : (Set.image β (Set.Ico 0 i)) ⊆ (Set.image β {i}ᶜ) := by
    if h_i : i > 0 then
      rw [Set.image_subset_image_iff (LinearIndependent.injective hβ_lin_indep.out)]
      simp only [Set.subset_compl_singleton_iff, Set.mem_Ico]
      omega
    else
      push_neg at h_i
      have h_i_eq_0: i = 0 := by exact Fin.le_zero_iff'.mp h_i
      have set_empty: Set.Ico 0 i = ∅ := by
        rw [h_i_eq_0]
        simp only [Set.Ico_eq_empty_iff]
        exact Nat.not_lt_zero 0
      -- ⊢ β '' Set.Ico 0 i ⊆ β '' {i}ᶜ
      rw [set_empty]
      simp only [Set.image_empty]
      simp only [Set.empty_subset]
  -- Since `span` is monotonic, if `βᵢ` were in the smaller span `Uᵢ`,
  -- it would be in the larger one.
  exact fun h_in_U => h_li (by
    -- ⊢ β i ∈ Submodule.span 𝔽q (β '' (Set.univ \ {i}))
    have res := Submodule.span_mono h_subset h_in_U
    rw [Set.compl_eq_univ_diff] at res
    exact res
  )

-- The main theorem
omit [Fintype L] [DecidableEq L] [Fintype 𝔽q] h_Fq_char_prime in
theorem root_U_lift_down
  (i : Fin r) (h_i_add_1 : i + 1 < r) (a : L) :
  a ∈ (U 𝔽q β (i+1)) → ∃! x: 𝔽q, a - x • β i ∈ (U 𝔽q β i) := by
  intro h_a_mem_U_i_plus_1
  apply existsUnique_of_exists_of_unique
  · -- PART 1: Existence -- ⊢ ∃ x, a - x • β i ∈ U 𝔽q β i
    have h_ico : Set.Ico 0 (i+1) = Set.Ico 0 i ∪ {i} := by
      ext k; simp only [Set.mem_Ico, Fin.zero_le, true_and, Set.union_singleton,
        Set.Ico_insert_right, Set.mem_Icc]
      -- ⊢ k < i + 1 ↔ k ≤ i
      exact Fin.le_iff_lt_succ (a := k) (b := i) (h_b := h_i_add_1).symm
    rw [U, h_ico, Set.image_union, Set.image_singleton, Submodule.span_union] at h_a_mem_U_i_plus_1
    -- h_a_mem_U_i_plus_1 : a ∈ Submodule.span 𝔽q (β '' Set.Ico 0 i) ⊔ Submodule.span 𝔽q {β i}
    rw [Submodule.mem_sup] at h_a_mem_U_i_plus_1
    rcases h_a_mem_U_i_plus_1 with ⟨u, h_u_mem_U_i, v, h_v_mem, h_a_eq⟩
    rw [Submodule.mem_span_singleton] at h_v_mem
    rcases h_v_mem with ⟨x, rfl⟩
    -- ⊢ ∃ x, a - x • β i ∈ U 𝔽q β i
    use x -- ⊢ a - x • β i ∈ U 𝔽q β i, h_a_eq : u + x • β i = a
    have h_a_sub_x_smul_β_i_mem_U_i : a - x • β i = u := by
      rw [h_a_eq.symm]
      norm_num
    rw [h_a_sub_x_smul_β_i_mem_U_i]
    exact h_u_mem_U_i
  · -- PART 2: Uniqueness
    intros x y hx hy -- ⊢ x = y
    -- Let x and y be two scalars that satisfy the property.
    -- hx: `a - x • β i ∈ U i`
    -- hy: `a - y • β i ∈ U i`
    -- Since `U i` is a subspace, the difference of these two vectors is also in `U i`.
    let u_x := a - x • β i
    let u_y := a - y • β i
    have h_diff_mem : u_y - u_x ∈ U 𝔽q β i := Submodule.sub_mem (U 𝔽q β i) hy hx

    -- Let's simplify the difference: `(a - y•βi) - (a - x•βi) = x•βi - y•βi = (x-y)•βi`.
    rw [sub_sub_sub_cancel_left] at h_diff_mem -- h_diff_mem : x • β i - y • β i ∈ U 𝔽q β i
    rw [←sub_smul] at h_diff_mem
    -- So, we have `(x - y) • β i ∈ U i`.
    by_cases h_eq : x - y = 0
    -- If `x - y = 0`, then `x = y` and we're done.
    · exact sub_eq_zero.mp h_eq
    -- Otherwise, we have a contradiction.
    · exfalso
      have h_β_i_mem := (Submodule.smul_mem_iff _ h_eq).mp h_diff_mem
      have h_β_i_not_in_U_i := βᵢ_not_in_Uᵢ (𝔽q:=𝔽q) (β:=β) (i :=i)
      exact h_β_i_not_in_U_i h_β_i_mem

omit [Fintype L] [DecidableEq L] [Fintype 𝔽q] h_Fq_char_prime hβ_lin_indep in
theorem root_U_lift_up (i : Fin r) (h_i_add_1 : i + 1 < r) (a : L) (x : 𝔽q) :
  a - x • β i ∈ (U 𝔽q β i) → a ∈ (U 𝔽q β (i+1)) := by
  intro h_a_sub_x_smul_β_i_mem_U_i
   -- We want to show `a ∈ U(i+1)`. We can rewrite `a` as `(a - x • β i) + x • β i`.
  rw [← sub_add_cancel a (x • β i)]
  -- Now we just need to prove that both parts of the sum are in the subspace `U(i+1)`.
  apply Submodule.add_mem
  · -- Part 1: Prove `a - x • β i ∈ U(i+1)`
    apply Submodule.span_mono
    · apply Set.image_mono
      · apply Set.Ico_subset_Ico_right (Fin.le_succ (a := i) (h_a_add_1 := h_i_add_1))
    · exact h_a_sub_x_smul_β_i_mem_U_i
  · -- Part 2: Prove `x • β i ∈ U(i+1)`
    -- A scaled basis vector `x • β i` is in the span `U(i+1)` if the basis vector `β i` is.
    apply Submodule.smul_mem
    -- `β i` is in the span `U(i+1)` because it's one of its generators.
    apply Submodule.subset_span
    apply Set.mem_image_of_mem
    simp only [Set.mem_Ico, Fin.zero_le, true_and]
    exact Fin.lt_succ' (a := i) (h_a_add_1 := h_i_add_1)

/--
The subspace vanishing polynomial `Wᵢ(X) := ∏_{u ∈ Uᵢ} (X - u), ∀ i ∈ {0, ..., r-1}`.
The degree of `Wᵢ(X)` is `|Uᵢ| = 2^i`.
- [LCH14, Lemma 1]: `Wᵢ(X)` is an `𝔽q`-linearized polynomial, i.e.,
  `Wᵢ(x) = ∑_{j=0}^i a_{i, j} x^{2^j}` for some constants `a_{i, j} ∈ L` (Equation (3)).
- The additive property: `Wᵢ(x + y) = Wᵢ(x) + Wᵢ(y)` for all `x, y ∈ L` (Equation (4)).
- For all `y ∈ Uᵢ`, `Wᵢ(x + y) = Wᵢ(x)` (Equation (14)).
-/
noncomputable def W (i : Fin r) : L[X] :=
  ∏ u : U 𝔽q β i, (X - C u.val)

omit h_Fq_char_prime hF₂
/-- The degree of the subspace vanishing polynomial `Wᵢ(X)` is `2ⁱ`. -/
lemma degree_W (i : Fin r) : (W 𝔽q β i).degree = (Fintype.card 𝔽q)^i.val := by
  have h_monic : ∀ (u: U 𝔽q β i), Monic (X - C u.val) :=
    fun _ => Polynomial.monic_X_sub_C _
  have h_monic_Fin_univ: ∀ u ∈ (univ (α := U (𝔽q := 𝔽q) (β := β) (i :=i))),
    Monic (X - C u.val) := by
    intros u hu
    have h_monic_u := h_monic u
    have h_monic_u_Fin_univ : Monic (X - C u.val) := h_monic_u
    exact h_monic_u_Fin_univ
  have h_deg : ∀ (u : U (𝔽q := 𝔽q) (β := β) (i :=i)), (X - C u.val).degree = 1 :=
    fun _ => degree_X_sub_C _
  unfold W
  rw [degree_prod_of_monic (h := h_monic_Fin_univ)]
  -- ⊢ ∑ i_1, (X - C ↑i_1).degree = 2 ^ i
  simp only [degree_X_sub_C, sum_const, card_univ, nsmul_eq_mul, mul_one]
  -- ⊢ ↑(Fintype.card ↥(U β i)) = 2 ^ i
  rw [U_card (𝔽q := 𝔽q) (β := β) (i :=i)]
  rfl

omit [DecidableEq L] [Fintype 𝔽q] hβ_lin_indep in
/-- The subspace vanishing polynomial `Wᵢ(X)` is monic. -/
lemma W_monic (i : Fin r) : (W 𝔽q β i).Monic := by
  unfold W
  apply Polynomial.monic_prod_of_monic
  intros u hu
  exact Polynomial.monic_X_sub_C u.val

omit [DecidableEq L] [Fintype 𝔽q] hβ_lin_indep in
lemma W_ne_zero (i : Fin r) : (W 𝔽q β i) ≠ 0 := by
  unfold W
  by_contra h_zero
  rw [prod_eq_zero_iff] at h_zero
  rcases h_zero with ⟨c, hc, h_zero⟩
  have X_sub_c_ne_Zero: X - C (c: L) ≠ (0: L[X]) := by
    exact Polynomial.X_sub_C_ne_zero (c: L)
  contradiction

example (i : Fin r) (h_i_eq_0 : i = 0) : Set.Ico 0 i = ∅ := by
  rw [h_i_eq_0] -- ⊢ Set.Ico 0 0 = ∅
  simp only [Set.Ico_eq_empty_iff]
  exact Nat.not_lt_zero 0

omit [DecidableEq L] [Fintype 𝔽q]  in
/-- The evaluation of `Wᵢ(X)` at `βᵢ` is non-zero. -/
lemma Wᵢ_eval_βᵢ_neq_zero
    (i : Fin r): (W 𝔽q β i).eval (β i) ≠ 0 := by
  -- Since `βᵢ ∉ Uᵢ`, `eval (Wᵢ(X)) (βᵢ)` cannot be zero.
  -- `eval(P*Q, x) = eval(P,x) * eval(Q,x)`. A product is non-zero iff all factors are non-zero.
  rw [W, eval_prod, prod_ne_zero_iff]
  intro u _
  -- We need to show `(β i - u.val) ≠ 0`, which is `β i ≠ u.val`.
  -- This is true because `βᵢ ∉ Uᵢ`.
  have h := βᵢ_not_in_Uᵢ 𝔽q β i
  intro eq
  have : β i = u.val := by
    have poly_eq: ((X - C u.val) : L[X]) = (1: L[X]) * (X - C u.val) := by
      rw [one_mul (X - C u.val)]
    rw [poly_eq] at eq
    simp only [one_mul, eval_sub, eval_X, eval_C] at eq
    -- eq: eq : β i - ↑u = 0
    rw [sub_eq_zero] at eq
    exact eq
  exact h (this ▸ u.2)

omit [DecidableEq L] [Fintype 𝔽q] hβ_lin_indep in
-- `Wᵢ(X)` vanishes on `Uᵢ`
lemma Wᵢ_vanishing (i : Fin r) :
  ∀ u ∈ U 𝔽q β i, (W 𝔽q β i).eval u = 0 := by
  -- The roots of `Wᵢ(X)` are precisely the elements of `Uᵢ`.
   -- For any `u ∈ Uᵢ`, the product `Wᵢ(X)` contains the factor `(X - u)`.
  intro u hu
  rw [W, eval_prod, prod_eq_zero_iff]
  -- We use `u` itself, which is in the set of factors, to make the product zero.
  use ⟨u, hu⟩
  simp only [mem_univ, eval_sub, eval_X, eval_C, sub_self, and_self]

omit [DecidableEq L] [Fintype 𝔽q] hβ_lin_indep in
lemma W₀_eq_X : W 𝔽q β 0 = X := by
  -- By definition, U ... 0 = {0}, so the vanishing polynomial is X
  rw [W]
  have : (univ : Finset (U 𝔽q β 0)) = {0} := by
    ext x
    simp only [U, Set.Ico, mem_univ, mem_singleton, true_iff]
    --x : ↥(U 𝔽q β 0), ⊢ x = 0
    unfold U at x
    have h_empty : Set.Ico 0 (0: Fin r) = ∅ := by
      exact Set.Ico_self 0
    have h_x := x.property -- NOTE: should take x.property explicity and rw on it
    simp_rw [h_empty] at h_x
    simp only [Set.image_empty, Submodule.span_empty, Submodule.mem_bot] at h_x
    exact Submodule.coe_eq_zero.mp h_x

  rw [this]
  simp only [prod_singleton, ZeroMemClass.coe_zero, map_zero, sub_zero]

end LinearSubspaces

section LinearityOfSubspaceVanishingPolynomials
/-!
### Formalization of linearity of subspace vanishing polynomials

This section formalizes the key properties of the subspace vanishing polynomials `Wᵢ`,
including their recursive structure and `𝔽q`-linearity as described in Lemma 2.3 of [GGJ96].
The proofs are done by simultaneous induction on `i`.
-/

omit [DecidableEq L] [Fintype 𝔽q] h_Fq_char_prime hβ_lin_indep in
/-- The subspace vanishing polynomial `Wᵢ(X)` splits into linear factors over `L`. -/
lemma W_splits (i : Fin r) : (W 𝔽q β i).Splits (RingHom.id L) := by
  unfold W
  -- The `W` polynomial is a product of factors. A product splits if every factor splits.
  apply Polynomial.splits_prod
  -- Now we must show that each factor `(X - C j.val)` splits.
  intros j hj
  -- A polynomial of the form `X - a` is linear and therefore always splits.
  -- The lemma for this is `Polynomial.splits_X_sub_C`.
  apply Polynomial.splits_X_sub_C

omit [Fintype 𝔽q] h_Fq_char_prime hβ_lin_indep in
/-- The roots of `Wᵢ(X)` are precisely the elements of the subspace `Uᵢ`. -/
lemma roots_W (i : Fin r) : -- converts root Multiset into (univ: Uᵢ.val.map)
  (W 𝔽q β i).roots = (univ : Finset (U 𝔽q β i)).val.map (fun u => u.val) := by
  unfold W -- must unfold to reason on the form of `prod (X-C)`
  let f_inner : U 𝔽q β i → L := Subtype.val
  let f_outer : L → L[X] := fun y => X - C y
  have h_inj : Function.Injective f_inner := Subtype.val_injective
  -- ⊢ (∏ u, (X - C ↑u)).roots = Multiset.map (fun u ↦ ↑u) univ.val
  rw [← prod_image (g := f_inner) (f := f_outer)]
  · -- ⊢ (∏ x ∈ image f_inner univ, f_outer x).roots =
    -- Multiset.map (fun u ↦ ↑u) univ.val
    let s := (univ : Finset (U 𝔽q β i)).image f_inner
    rw [Polynomial.roots_prod_X_sub_C (s := s)]
    -- ⊢ s.val = Multiset.map (fun u ↦ ↑u) univ.val
    apply image_val_of_injOn -- (H : Set.InjOn f s) : (image f s).1 = s.1.map f
    -- ⊢ Set.InjOn f_inner ↑Finset.univ
    unfold Set.InjOn
    intro u hu x2 hx2 h_u_eq_x2
    exact h_inj h_u_eq_x2
  · -- ⊢ ∀ x ∈ univ, ∀ y ∈ univ, f_inner x = f_inner y → x = y
    intro x hx y hy hfx_eq_fy
    exact h_inj hfx_eq_fy

@[simps!]
noncomputable def algEquivAevalXSubC {R : Type*} [CommRing R] (t : R) : R[X] ≃ₐ[R] R[X] := by
  -- Reference: Polynomial.algEquivAevalXAddC
  have h_comp_X_sub_C : (X - C t).comp (X + C t) = X := by
    simp only [sub_comp, X_comp, C_comp, add_sub_cancel_right]
  have h_comp_X_add_C : (X + C t).comp (X - C t) = X := by
    simp only [add_comp, X_comp, C_comp, sub_add_cancel]
  exact algEquivOfCompEqX (p := X - C t) (q := X + C t)
    (hpq := h_comp_X_sub_C) (hqp := h_comp_X_add_C)

omit [Fintype L] [DecidableEq L] in
lemma comp_X_sub_C_eq_zero_iff (p : L[X]) (a : L) :
  p.comp (X - C a) = 0 ↔ p = 0 := EmbeddingLike.map_eq_zero_iff (f := algEquivAevalXSubC a)
  -- Reference: Polynomial.comp_X_add_C_eq_zero_iff

omit [Fintype L] in
/--
The multiplicity of a root `x` in a polynomial `p` composed with `(X - a)` is equal to the
multiplicity of the root `x - a` in `p`.
-/
lemma rootMultiplicity_comp_X_sub_C (p : L[X]) (a x : L) :
    rootMultiplicity x (p.comp (X - C a)) = rootMultiplicity (x - a) p := by
  -- Reference: rootMultiplicity_eq_rootMultiplicity
  classical
  simp only [rootMultiplicity_eq_multiplicity]
  simp only [comp_X_sub_C_eq_zero_iff, map_sub]
  -- ⊢ (if p = 0 then 0 else multiplicity (X - C x) (p.comp (X - C a)))
  -- = if p = 0 then 0 else multiplicity (X - (C x - C a)) p
  -- `(X - C x)^n | (p.comp (X - C a)) <=> (X - (C x - C a))^n | p`
  by_cases hp_zero : p = 0
  · simp only [hp_zero, if_true]
  · simp only [hp_zero, if_false]
    have h_p_comp_zero: p.comp (X - C a) ≠ 0 := by
      by_contra h_p_comp_zero_contra
      simp only [comp_X_sub_C_eq_zero_iff] at h_p_comp_zero_contra
      contradiction
    -- ⊢ multiplicity (X - C x) (p.comp (X - C a)) = multiplicity (X - (C x - C a)) p
    have res : multiplicity (X - (C x - C a)) p = multiplicity (X - C x) (p.comp (X - C a)):= by
      convert (multiplicity_map_eq <| algEquivAevalXSubC a).symm using 2
      -- ⊢ X - C x = (algEquivAevalXSubC a) (X - (C x - C a))
      simp only [algEquivAevalXSubC, algEquivOfCompEqX_apply]
      simp only [map_sub, aeval_X, aeval_C, algebraMap_eq]
      simp only [sub_sub_sub_cancel_right]
    exact res.symm

omit [Fintype L] in
-- The main helper lemma, now proven using the multiplicity lemma above.
lemma roots_comp_X_sub_C (p : L[X]) (a : L) :
    (p.comp (X - C a)).roots = p.roots.map (fun r => r + a) := by
  -- To prove two multisets are equal, we show that for any element `s`,
  -- its count is the same in both sets.
  ext s
  rw [Polynomial.count_roots, rootMultiplicity_comp_X_sub_C] -- transform the LHS
  -- ⊢ rootMultiplicity (s - a) p = Multiset.count s (p.roots.map (fun r ↦ r + a))
  rw [Multiset.count_map]
  -- ⊢ rootMultiplicity (s - a) p = (Multiset.filter (fun a_1 ↦ s = a_1 + a) p.roots).card
  -- Use `filter_congr` to rewrite the predicate inside the filter to isolate `r`.
  rw [Multiset.filter_congr (p := fun r => s = r + a) (q := fun r => s - a = r) (by {
    intro r hr_root
    simp only
    -- ⊢ s = r + a ↔ s - a = r
    rw [add_comm]
    have res := eq_sub_iff_add_eq (a := r) (b := s) (c := a)
    rw [eq_comm] at res
    conv_rhs at res => rw [eq_comm, add_comm]
    exact Iff.symm res
  })]
  -- ⊢ rootMultiplicity (s - a) p = (Multiset.filter (fun r ↦ s - a = r) p.roots).card
  rw [←Multiset.countP_eq_card_filter]
  -- ⊢ rootMultiplicity (s - a) p = Multiset.count (s - a) p.roots
  rw [← Polynomial.count_roots, Multiset.count]

-- The main helper lemma, now proven using the multiplicity lemma above.

omit [DecidableEq L] h_Fq_char_prime hF₂ hβ_lin_indep in
lemma Prod_W_comp_X_sub_C_ne_zero (i : Fin r) :
    (univ : Finset 𝔽q).prod (fun c => (W 𝔽q β i).comp (X - C (c • β i))) ≠ 0 := by
  by_contra h_zero
  rw [prod_eq_zero_iff] at h_zero
  rcases h_zero with ⟨c, hc, h_zero⟩
  rw [Polynomial.comp_eq_zero_iff] at h_zero
  cases h_zero with
  | inl h1 =>
    exact (W_ne_zero 𝔽q β i) h1
  | inr h1 =>
    simp only [coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, map_neg, sub_eq_neg_self,
      X_ne_zero, and_false] at h1

omit [Fintype 𝔽q] h_Fq_char_prime hβ_lin_indep in
/--
The polynomial `Wᵢ(X)` has simple roots (multiplicity 1) for each element in the
subspace `Uᵢ`, and no other roots.
-/
lemma rootMultiplicity_W (i : Fin r) (a : L) :
    rootMultiplicity a (W 𝔽q β i) = if a ∈ (U 𝔽q β i : Set L) then 1 else 0 := by
  -- The multiplicity of root `a` is its count in the multiset of roots.
  rw [←Polynomial.count_roots, roots_W]
  -- The roots of `W` are the image of `Subtype.val` over the elements of the subspace `Uᵢ`.
  -- So we need to count `a` in the multiset `map Subtype.val ...`
  rw [Multiset.count_map]
  -- ⊢ (Multiset.filter (fun a_1 ↦ a = ↑a_1) univ.val).card = if a ∈ ↑(U 𝔽q β i) then 1 else 0
-- The goal is now:
  -- ⊢ (Multiset.filter (fun u ↦ a = u.val) ...).card = if a ∈ Uᵢ then 1 else 0

  -- We prove this by cases, depending on whether `a` is in the subspace `Uᵢ`.
  by_cases h_mem : a ∈ U 𝔽q β i

  · -- Case 1: `a` is in the subspace `Uᵢ`.
    -- The RHS of our goal becomes 1.
    simp only [SetLike.mem_coe, h_mem, ↓reduceIte]

    -- We need to prove the cardinality of the filtered multiset is 1.
    -- The filter keeps only those elements `u` from `Uᵢ` whose value is `a`.
    -- Since `a ∈ Uᵢ`, we know there is at least one such `u`.
    -- ⊢ (Multiset.filter (fun a_1 ↦ a = ↑a_1) univ.val).card = 1

    -- Since `a ∈ Uᵢ`, there exists some `u : Uᵢ` such that `u.val = a`
    have h_exists : ∃ u : U 𝔽q β i, u.val = a := by
      exact CanLift.prf a h_mem
    rcases h_exists with ⟨u, rfl⟩ -- This gives us the `u` such that `u.val = a`.

    -- The filter now becomes: filter (fun u₁ => u.val = u₁.val) univ.val
    -- This is equivalent to counting how many elements in univ have the same value as u
    -- Since Subtype.val is injective, there can be at most one such element
    -- And since u is in univ, there is exactly one such element
    have h_filter_eq_singleton : Multiset.filter (fun u₁ => u.val = u₁.val) univ.val = {u} := by
      -- Use count-based equality for multisets
      ext v
      -- ⊢ count v (filter (fun u₁ => u.val = u₁.val) univ.val) = count v {u}
      rw [Multiset.count_filter, Multiset.count_singleton]
      by_cases h_v_eq_u : v = u
      · -- If v = u, then count should be 1
        rw [h_v_eq_u]
        simp only [↓reduceIte, Multiset.count_univ]
      · -- If v ≠ u, then count should be 0
        simp only [SetLike.coe_eq_coe, Multiset.count_univ]
        -- ⊢ (if u = v then 1 else 0) = if v = u then 1 else 0
        simp only [h_v_eq_u, if_false]
        simp only [ite_eq_right_iff, one_ne_zero, imp_false]
        exact fun a ↦ h_v_eq_u (id (Eq.symm a))
    rw [h_filter_eq_singleton, Multiset.card_singleton]
  · -- Case 2: `a` is not in the subspace `Uᵢ`.
    -- The RHS of our goal becomes 0.
    simp only [SetLike.mem_coe, h_mem, ↓reduceIte]

    -- Since `a ∈ Uᵢ`, there exists some `u : Uᵢ` such that `u.val = a`
    have h_ne_exists_a : ¬∃ u : U 𝔽q β i, u.val = a := by
      by_contra h_u_val_eq_a -- h_u_val_eq_a : ∃ u, ↑u = a
      rcases h_u_val_eq_a with ⟨u, rfl⟩ -- This gives us the `u` such that `u.val = a`.
      exact h_mem u.property -- lift from `U 𝔽q β i` to `L` to get a contradiction
    have h_filter_eq_empty :
      Multiset.filter (fun (u₁ : U 𝔽q β i) => a = u₁.val) univ.val = 0 := by
      -- Use count-based equality for multisets
      ext v
      -- ⊢ count v (filter (fun u₁ => a = u₁.val) univ.val) = count v 0
      rw [Multiset.count_filter, Multiset.count_zero]
      simp only [Multiset.count_univ]
      simp only [ite_eq_right_iff, one_ne_zero, imp_false]
      by_contra h_v_eq_a
      exact h_ne_exists_a ⟨v, h_v_eq_a.symm⟩
    rw [h_filter_eq_empty, Multiset.card_zero]

omit [Fintype 𝔽q] h_Fq_char_prime hβ_lin_indep in
lemma eval_W_eq_zero_iff_in_U (i : Fin r) (a : L) :
  (W 𝔽q β i).eval a = 0 ↔ a ∈ U 𝔽q β i := by
  constructor
  · -- Forward direction: Wᵢ(a) = 0 → a ∈ Uᵢ
    intro h_eval_zero -- h_eval_zero : eval a (W 𝔽q β i) = 0
    -- If Wᵢ(a) = 0, then a is a root of Wᵢ
    have h_root_W : (W 𝔽q β i).IsRoot a := by
      rw [IsRoot.def]
      exact h_eval_zero
    -- theorem rootMultiplicity_pos {p : R[X]} (hp : p ≠ 0) {x : R} :
    -- 0 < rootMultiplicity x p ↔ IsRoot p x :=
    have h_root_W_pos : 0 < rootMultiplicity a (W 𝔽q β i) := by
      simp only [rootMultiplicity_pos', ne_eq, IsRoot.def]
      constructor
      · push_neg; exact W_ne_zero 𝔽q β i
      · exact h_root_W
    rw [rootMultiplicity_W] at h_root_W_pos
    by_cases h_a_in_U : a ∈ U 𝔽q β i
    · simp only [h_a_in_U]
    · simp only [SetLike.mem_coe, h_a_in_U, ↓reduceIte, lt_self_iff_false] at h_root_W_pos
  · -- Reverse direction: a ∈ Uᵢ → Wᵢ(a) = 0
    intro h_a_in_U
    -- This is exactly what Wᵢ_vanishing proves
    exact Wᵢ_vanishing 𝔽q β i a h_a_in_U

omit h_Fq_char_prime hF₂ in
lemma rootMultiplicity_prod_W_comp_X_sub_C
    (i : Fin r) (h_i_add_1 : i + 1 < r) (a : L) :
    rootMultiplicity a ((univ : Finset 𝔽q).prod (fun c => (W 𝔽q β i).comp (X - C (c • β i)))) =
    if a ∈ (U 𝔽q β (i+1) : Set L) then 1 else 0 := by
  rw [←Polynomial.count_roots]
  set f := fun c: 𝔽q => (W 𝔽q β i).comp (X - C (c • β i)) with hf
  -- ⊢ Multiset.count a (univ.prod f).roots = if a ∈ ↑(U 𝔽q β (i + 1)) then 1 else 0
  have h_prod_ne_zero: univ.prod f ≠ 0 := Prod_W_comp_X_sub_C_ne_zero 𝔽q β i
  rw [roots_prod (f := f) (s := univ (α := 𝔽q)) h_prod_ne_zero]
  set roots_f := fun c: 𝔽q => (f c).roots with hroots_f
  rw [Multiset.count_bind]
  -- ⊢ (Multiset.map (fun b ↦ Multiset.count a (roots_f b)) univ.val).sum
  -- = if a ∈ ↑(U 𝔽q β (i + 1)) then 1 else 0
  have h_roots_f_eq_roots_W : ∀ b : 𝔽q,
    roots_f b = (W 𝔽q β i).roots.map (fun r => r + (b • β i)) := by
    intro b
    rw [hroots_f, hf]
    exact roots_comp_X_sub_C (p := (W 𝔽q β i)) (a := (b • β i))
  simp_rw [h_roots_f_eq_roots_W]

  set shift_up := fun x: 𝔽q => fun r: L => r + x • β i with hshift_up
  have h_shift_up_all: ∀ x: 𝔽q, ∀ r: L, shift_up x r = r + x • β i := by
    intro x r
    rw [hshift_up]
  simp only [sum_map_val, SetLike.mem_coe]
  have h_a: ∀ x: 𝔽q, a = shift_up x (a - x • β i) := by
    intro x
    rw [hshift_up]
    simp_all only [ne_eq, implies_true, sub_add_cancel, f, roots_f, shift_up]
  conv_lhs =>
    enter [2, x] -- focus on the inner Multiset.count
    rw [h_a x]
    enter [2]
    enter [1]
    enter [r]
    rw [←h_shift_up_all x r] -- rewrite to another notation
  -- ⊢ ∑ x, Multiset.count (shift_up x (a - x • β i)) (Multiset.map (shift_up x) (W 𝔽q β i).roots)
  -- = if a ∈ ↑(U 𝔽q β (i + 1)) then 1 else 0
  have h_shift_up_inj: ∀ x: 𝔽q, Function.Injective (shift_up x) := by
    intro x
    unfold shift_up
    exact add_left_injective (x • β i)
  have h_count_map: ∀ x: 𝔽q,
    Multiset.count (shift_up x (a - x • β i)) (Multiset.map (shift_up x) (W 𝔽q β i).roots) =
    Multiset.count (a - x • β i) (W 𝔽q β i).roots := by
    -- transform to counting (a - x • β i) in the roots of Wᵢ
    intro x
    have h_shift_up_inj_x: Function.Injective (shift_up x) := h_shift_up_inj x
    simp only [Multiset.count_map_eq_count' (hf := h_shift_up_inj_x), count_roots]
  conv_lhs =>
    enter [2, x]
    rw [h_count_map x]
  -- ⊢ ∑ x, Multiset.count (a - x • β i) (W 𝔽q β i).roots
  -- = if a ∈ ↑(U 𝔽q β (i + 1)) then 1 else 0
  have h_root_lift_down := root_U_lift_down 𝔽q β i h_i_add_1 a
  have h_root_lift_up := root_U_lift_up 𝔽q β i h_i_add_1 a
  conv_lhs =>
    enter [2, x]
    simp only [count_roots]
    rw [rootMultiplicity_W]
  by_cases h_a_mem_U_i : a ∈ ↑(U 𝔽q β (i + 1))
  · -- ⊢ (∑ x, if a - x • β i ∈ ↑(U 𝔽q β i) then 1 else 0)
    -- = if a ∈ ↑(U 𝔽q β (i + 1)) then 1 else 0
    have h_true: (a ∈ ↑(U 𝔽q β (i + 1))) = True := by simp only [h_a_mem_U_i]
    rcases h_root_lift_down h_a_mem_U_i with ⟨x0, hx0, hx0_unique⟩
    conv =>
      rhs
      -- | if a ∈ ↑(U 𝔽q β (i + 1)) then 1 else 0 => reduce this to 1
      enter [1]
      exact h_true -- maybe there can be a better way to do this
    rw [ite_true]
    classical
    -- ⊢ (∑ x, if a - x • β i ∈ ↑(U 𝔽q β i) then 1 else 0) = 1
    have h_true: ∀ x: 𝔽q,
      if x = x0 then a - x • β i ∈ ↑(U 𝔽q β i) else a - x • β i ∉ ↑(U 𝔽q β i) := by
      intro x
      by_cases h_x_eq_x0 : x = x0
      · rw [if_pos h_x_eq_x0] -- ⊢ a - x • β i ∈ U 𝔽q β i
        rw [←h_x_eq_x0] at hx0
        exact hx0
      · rw [if_neg h_x_eq_x0] -- ⊢ a - x • β i ∉ U 𝔽q β i
        by_contra h_mem
        have h1 := hx0_unique x
        simp only [h_mem, forall_const] at h1
        contradiction

    have h_true_x: ∀ x: 𝔽q, (a - x • β i ∈ ↑(U 𝔽q β i)) = if x = x0 then True else False := by
      intro x
      by_cases h_x_eq_x0 : x = x0
      · rw [if_pos h_x_eq_x0]
        rw [←h_x_eq_x0] at hx0
        simp only [hx0]
      · rw [if_neg h_x_eq_x0]
        by_contra h_mem
        push_neg at h_mem
        simp only [ne_eq, eq_iff_iff, iff_false, not_not] at h_mem
        have h2 := hx0_unique x
        simp only [h_mem, forall_const] at h2
        contradiction
    conv =>
      lhs
      enter [2, x]
      simp only [SetLike.mem_coe, h_true_x x, if_false_right, and_true]
    rw [sum_ite_eq']
    simp only [mem_univ, ↓reduceIte]
  · -- ⊢ (∑ x, if a - x • β i ∈ ↑(U 𝔽q β i) then 1 else 0)
    -- = if a ∈ ↑(U 𝔽q β (i + 1)) then 1 else 0
    have h_false: (a ∈ ↑(U 𝔽q β (i + 1))) = False := by simp only [h_a_mem_U_i]
    conv =>
      rhs -- | if a ∈ ↑(U 𝔽q β (i + 1)) then 1 else 0 => reduce this to 1
      enter [1]
      exact h_false -- maybe there can be a better way to do this
    rw [ite_false]

    have h_zero_x: ∀ x: 𝔽q, (a - x • β i ∈ ↑(U 𝔽q β i)) = False := by
      intro x
      by_contra h_mem
      simp only [eq_iff_iff, iff_false, not_not] at h_mem -- h_mem : a - x • β i ∈ U 𝔽q β i
      have h_a_mem_U_i := h_root_lift_up x h_mem
      contradiction

    conv =>
      lhs
      enter [2, x]
      simp only [SetLike.mem_coe, h_zero_x x, if_false_right, and_true]
    simp only [↓reduceIte, sum_const_zero]

omit h_Fq_char_prime hF₂ in
/--
The generic product form of the recursion for `Wᵢ`.
This follows the first line of the proof for (i) in the description.
`Wᵢ(X) = ∏_{c ∈ 𝔽q} Wᵢ₋₁ ∘ (X - cβᵢ₋₁)`.
-/
lemma W_prod_comp_decomposition
    (i : Fin r) (hi : i > 0) :
    (W 𝔽q β i) = ∏ c: 𝔽q, (W 𝔽q β (i-1)).comp (X - C (c • β (i-1))) := by
  -- ⊢ W 𝔽q β i = ∏ c, (W 𝔽q β (i - 1)).comp (X - C (c • β (i - 1)))
  -- Define P and Q for clarity
  set P := W 𝔽q β i
  set Q := ∏ c: 𝔽q, (W 𝔽q β (i-1)).comp (X - C (c • β (i-1)))

-- c : 𝔽q => univ
-- c ∈ finsetX

  -- STRATEGY: Prove P = Q by showing they are monic, split, and have the same roots.

  -- 1. Show P and Q are MONIC.
  have hP_monic : P.Monic := W_monic (𝔽q := 𝔽q) (β := β) (i :=i)
  have hQ_monic : Q.Monic := by
    apply Polynomial.monic_prod_of_monic; intro c _
    apply Monic.comp
    · exact W_monic (𝔽q := 𝔽q) (β := β) (i :=(i-1))
    · -- ⊢ (X - C (c • β (i - 1))).Monic
      exact Polynomial.monic_X_sub_C (c • β (i - 1))
    · conv_lhs => rw [natDegree_sub_C, natDegree_X]
      norm_num
  -- 2. Show P and Q SPLIT over L.
  have hP_splits : P.Splits (RingHom.id L) := W_splits 𝔽q β i
  have hQ_splits : Q.Splits (RingHom.id L) := by
    apply Polynomial.splits_prod
    intro c _
    -- Composition of a splitting polynomial with a linear polynomial also splits.
    -- ⊢ Splits (RingHom.id L) ((W 𝔽q β (i - 1)).comp (X - C (c • β (i - 1))))
    apply Splits.comp_of_degree_le_one
    · exact degree_X_sub_C_le (c • β (i - 1))
    · -- ⊢ Splits (RingHom.id L) (W 𝔽q β (i - 1))
      exact W_splits 𝔽q β (i-1)

  -- 3. Show P and Q have the same ROOTS.
  have h_roots_eq : P.roots = Q.roots := by
    -- First, characterize the roots of P. They are the elements of Uᵢ.
    unfold P Q
    ext u
    rw [Polynomial.count_roots, Polynomial.count_roots]
    rw [rootMultiplicity_W]
    conv_rhs =>
      rw [rootMultiplicity_prod_W_comp_X_sub_C 𝔽q β (h_i_add_1 := by
        rw [Fin.val_sub_one (a := i) (h_a_sub_1 := by omega)]
        omega
      )]
    -- ⊢ (if u ∈ ↑(U 𝔽q β i) then 1 else 0) = if u ∈ ↑(U 𝔽q β (i - 1 + 1)) then 1 else 0
    have h_i : i - 1 + 1 = i := by simp only [sub_add_cancel]
    rw [h_i]

  -- 4. CONCLUSION: Since P and Q are monic, split, and have the same roots, they are equal.
  have hP_eq_prod := Polynomial.eq_prod_roots_of_monic_of_splits_id hP_monic hP_splits
  have hQ_eq_prod := Polynomial.eq_prod_roots_of_monic_of_splits_id hQ_monic hQ_splits
  rw [hP_eq_prod, hQ_eq_prod, h_roots_eq]

omit [Fintype L] [DecidableEq L] [Fintype 𝔽q] h_Fq_char_prime hβ_lin_indep in
-- A helper lemma that IsLinearMap implies the composition property.
-- This follows from the fact that a polynomial whose evaluation map is linear
-- must be a "linearized polynomial" (or q-polynomial).
lemma comp_sub_C_of_linear_eval (p : L[X])
  (h_lin : IsLinearMap 𝔽q (f := fun inner_p ↦ p.comp inner_p)) (a : L) :
    p.comp (X - C a) = p - C (eval a p) := by -- linearity: p ∘ (X - a) = p(X) - p(a)
  have h_comp_left: p.comp (X - C a) = p.comp X - p.comp (C a) := by
    rw [sub_eq_add_neg]
    have h_comp_add := h_lin.map_add (X: L[X]) (-C a)
    rw [h_comp_add]
    conv_rhs => rw [sub_eq_add_neg]
    rw [add_right_inj (a := p.comp X) (b := p.comp (-C a)) (c := -p.comp (C a))]
    exact h_lin.map_neg (C a)

  rw [h_comp_left]
  rw [comp_X]
  rw [sub_right_inj]
  exact comp_C


omit h_Fq_char_prime hF₂ in
lemma inductive_rec_form_W_comp (i : Fin r) (h_i_add_1 : i + 1 < r)
    (h_prev_linear_map : IsLinearMap (R := 𝔽q) (M := L[X]) (M₂ := L[X])
      (f := fun inner_p ↦ (W 𝔽q β i).comp inner_p))
    : ∀ p: L[X], (W 𝔽q β (i + 1)).comp p =
      ((W 𝔽q β i).comp p) ^ Fintype.card 𝔽q -
        C (eval (β i) (W 𝔽q β i)) ^ (Fintype.card 𝔽q - 1) * ((W 𝔽q β i).comp p) := by
  intro p
  set W_i := W 𝔽q β i
  set q := Fintype.card 𝔽q
  set v := W_i.eval (β i)

  -- First, we must prove that v is non-zero to use its inverse.
  have hv_ne_zero : v ≠ 0 := by
    unfold v W_i
    exact Wᵢ_eval_βᵢ_neq_zero 𝔽q β i

  -- Proof flow:
  -- `Wᵢ₊₁(X) = ∏_{c ∈ 𝔽q} (Wᵢ ∘ (X - c • βᵢ))` -- from W_prod_comp_decomposition
    -- `= ∏_{c ∈ 𝔽q} (Wᵢ(X) - c • Wᵢ(βᵢ))` -- linearity of Wᵢ
    -- `= ∏_{c ∈ 𝔽q} (Wᵢ(X) - c • v)`
    -- `= v² ∏_{c ∈ 𝔽q} (v⁻¹ • Wᵢ(X) - c)`
    -- `= v² (v⁻² • Wᵢ(X)² - v⁻¹ • Wᵢ(X))` => FLT (prod_X_sub_C_eq_X_pow_card_sub_X_in_L)
    -- `= Wᵢ(X)² - v • Wᵢ(X)` => Q.E.D

  have h_scalar_smul_eq_C_v_mul: ∀ s: L, ∀ p: L[X], s • p = C s * p := by
    intro s p
    exact smul_eq_C_mul s
  have h_v_smul_v_inv_eq_one: v • v⁻¹ = 1 := by
    simp only [smul_eq_mul]
    exact CommGroupWithZero.mul_inv_cancel v hv_ne_zero
  have h_v_mul_v_inv_eq_one: v * v⁻¹ = 1 := by
    exact h_v_smul_v_inv_eq_one
  -- The main proof using a chain of equalities (the `calc` block).
  calc
    (W 𝔽q β (i + 1)).comp p
    _ = (∏ c: 𝔽q, (W_i).comp (X - C (c • β i))).comp p := by
      have h_res := W_prod_comp_decomposition 𝔽q β (i+1) (by
        apply Fin.mk_lt_of_lt_val
        rw [Fin.val_add_one' (a := i) (h_a_add_1 := h_i_add_1), Nat.zero_mod]
        omega
      )
      rw [h_res]
      simp only [add_sub_cancel_right]
      rfl
    -- Step 2: Apply the linearity property of Wᵢ as a polynomial.
    _ = (∏ c: 𝔽q, (W_i - C (W_i.eval (c • β i)))).comp p := by
      congr
      funext c
      -- We apply the transformation inside the product for each element `c`.
      -- apply Finset.prod_congr rfl
      -- ⊢ W_i.comp (X - C (c • β i)) = W_i - C (eval (c • β i) W_i)
      exact comp_sub_C_of_linear_eval (p := W_i) (h_lin := h_prev_linear_map) (a := (c • β i))
    -- Step 3: Apply the linearity of Wᵢ's *evaluation map* to the constant term.
    -- Hypothesis: `h_prev_linear_map.map_smul`
    _ = (∏ c: 𝔽q, (W_i - C (c • v))).comp p := by
      congr
      funext c
      -- ⊢ W_i - C (eval (c • β i) W_i) = W_i - C (c • v)
      congr
      -- ⊢ eval (c • β i) W_i = c • v
      -- Use the linearity of the evaluation map, not the composition map
      have h_eval_linear := Polynomial.linear_map_of_comp_to_linear_map_of_eval (f := (W 𝔽q β i))
        (h_f_linear := h_prev_linear_map)
      exact h_eval_linear.map_smul c (β i)
    -- Step 4: Perform the final algebraic transformation.
    _ = (C (v^q) * (∏ c: 𝔽q, (C (v⁻¹) * W_i - C (algebraMap 𝔽q L c)))).comp p := by
      congr
      calc
        _ = ∏ c: 𝔽q, (v • (v⁻¹ • W_i - C (algebraMap 𝔽q L c))) := by
          apply Finset.prod_congr rfl
          intro c _
          rw [smul_sub]
          -- ⊢ W_i - C (c • v) = v • v⁻¹ • W_i - v • C ((algebraMap 𝔽q L) c)
          rw [smul_C, smul_eq_mul, map_mul]
          rw [←smul_assoc]
          rw [h_v_smul_v_inv_eq_one]
          rw [one_smul]
          rw [sub_right_inj]
          -- ⊢ C (c • v) = C v * C ((algebraMap 𝔽q L) c)
          rw [←C_mul]
          -- ⊢ C (c • v) = C (v * (algebraMap 𝔽q L) c)
          have h_c_smul_v: c • v = (algebraMap 𝔽q L c) • v := by
            exact algebra_compatible_smul L c v
          rw [h_c_smul_v]
          rw [mul_comm]
          rw [smul_eq_mul]
        _ = ∏ c: 𝔽q, (C v * (v⁻¹ • W_i - C (algebraMap 𝔽q L c))) := by
          apply Finset.prod_congr rfl
          intro c _
          rw [h_scalar_smul_eq_C_v_mul]
        _ = C (v^q) * (∏ c: 𝔽q, (C v⁻¹ * W_i - C (algebraMap 𝔽q L c))) := by
          -- rw [Finset.prod_mul_distrib]
          -- rw [Finset.prod_const, Finset.card_univ]
          rw [Finset.prod_mul_distrib]
          conv_lhs =>
            enter [2]
            enter [2]
            rw [h_scalar_smul_eq_C_v_mul]
          congr
          -- ⊢ ∏ (x: 𝔽q), C v = C (v ^ q)
          rw [Finset.prod_const, Finset.card_univ]
          unfold q
          exact Eq.symm C_pow
    _ = (C (v^q) * ((C v⁻¹ * W_i)^q - (C v⁻¹ * W_i))).comp p := by
      congr
      -- ⊢ ∏ c, (C v⁻¹ * W_i - C ((algebraMap 𝔽q L) c)) = (C v⁻¹ * W_i) ^ q - C v⁻¹ * W_i
      rw [Polynomial.prod_poly_sub_C_eq_poly_pow_card_sub_poly_in_L (p := C v⁻¹ * W_i)]
    _ = (C (v^q) * C (v⁻¹^q) * W_i^q - C (v^q) * C v⁻¹ * W_i).comp p := by
      congr
      rw [mul_sub]
      conv_lhs =>
        rw [mul_pow, ←mul_assoc, ←mul_assoc, ←C_pow]
    _ = (W_i^q - C (v^(q-1)) * W_i).comp p := by
      congr
      · rw [←C_mul, ←mul_pow, h_v_mul_v_inv_eq_one, one_pow, C_1, one_mul]
      · rw [←C_mul]
        have h_v_pow_q_minus_1: v^q * v⁻¹ = v^(q-1) := by
          rw [pow_sub₀ (a := v) (m := q) (n := 1) (ha := hv_ne_zero) (h := by exact NeZero.one_le)]
          -- ⊢ v ^ q * v⁻¹ = v ^ q * (v ^ 1)⁻¹
          congr
          norm_num
        rw [h_v_pow_q_minus_1]
    _ = (W_i^q - C (eval (β i) W_i) ^ (q - 1) * W_i).comp p := by
      simp only [map_pow, W_i, q, v]
    _ = (W_i^q).comp p - (C (eval (β i) W_i) ^ (q - 1) * W_i).comp p := by
      rw [sub_comp]
    _ = (W_i.comp p)^q - (C (eval (β i) W_i) ^ (q - 1)) * (W_i.comp p) := by
      rw [pow_comp, mul_comp]
      conv_lhs =>
        rw [pow_comp]
        rw [C_comp (a := (eval (β i) W_i)) (p := p)]

omit hF₂ in
lemma inductive_linear_map_W (i : Fin r) (h_i_add_1 : i + 1 < r)
    (h_prev_linear_map : IsLinearMap 𝔽q (f := fun inner_p ↦ (W 𝔽q β i).comp inner_p))
    : IsLinearMap 𝔽q (f := fun inner_p ↦ (W 𝔽q β (i + 1)).comp inner_p) := by

  have h_rec_form := inductive_rec_form_W_comp
    (hβ_lin_indep := hβ_lin_indep) (h_prev_linear_map := h_prev_linear_map) (i :=i)

  set q := Fintype.card 𝔽q
  set v := (W 𝔽q β i).eval (β i)

  -- `∀ f(X), f(X) ∈ L[X]`:
  constructor
  · intro f g
    -- 1. Proof flow
    -- `Wᵢ₊₁(f(X)+g(X)) = Wᵢ(f(X)+g(X))² - v • Wᵢ(f(X)+g(X))` -- h_rec_form
    -- `= (Wᵢ(f(X)) + Wᵢ(g(X)))² - v • (Wᵢ(f(X)) + Wᵢ(g(X)))`
    -- `= (Wᵢ(f(X))² + (Wᵢ(g(X)))² - v • Wᵢ(f(X)) - v • Wᵢ(g(X)))` => Freshman's Dream
    -- `= (Wᵢ(f(X))² - v • Wᵢ(f(X))) + (Wᵢ(g(X))² - v • Wᵢ(g(X)))` -- h_rec_form
    -- `= Wᵢ₊₁(f(X)) + Wᵢ₊₁(g(X))` -- Q.E.D.

    -- ⊢ (W 𝔽q β (i + 1)).comp (x + y) = (W 𝔽q β (i + 1)).comp x + (W 𝔽q β (i + 1)).comp y
    calc
      _ = ((W 𝔽q β i).comp (f + g))^q - C v ^ (q - 1) * ((W 𝔽q β i).comp (f + g)) := by
        rw [h_rec_form h_i_add_1]
      _ = ((W 𝔽q β i).comp f)^q + ((W 𝔽q β i).comp g)^q
        - C v ^ (q - 1) * ((W 𝔽q β i).comp f) - C v ^ (q - 1) * ((W 𝔽q β i).comp g) := by
        rw [h_prev_linear_map.map_add]
        rw [Polynomial.frobenius_identity_in_algebra]
        rw [left_distrib]
        unfold q
        abel_nf
      _ = (((W 𝔽q β i).comp f)^q - C v ^ (q - 1) * ((W 𝔽q β i).comp f))
        + (((W 𝔽q β i).comp g)^q - C v ^ (q - 1) * ((W 𝔽q β i).comp g)) := by
        abel_nf
      _ = (W 𝔽q β (i+1)).comp f + (W 𝔽q β (i+1)).comp g := by
        unfold q
        rw [h_rec_form h_i_add_1 f]
        rw [h_rec_form h_i_add_1 g]
  · intro c f
    -- 2. Proof flow
    -- `Wᵢ₊₁(c • f(X)) = Wᵢ(c • f(X))² - v • Wᵢ(c • f(X))` -- h_rec_form
    -- `= c² • Wᵢ(f(X))² - v • c • Wᵢ(f(X))`
    -- `= c • Wᵢ(f(X))² - v • c • Wᵢ(f(X))` via Fermat's Little Theorem (X^q = X)
    -- `= c • (Wᵢ(f(X))² - v • Wᵢ(f(X)))` -- h_rec_form
    -- `= c • Wᵢ₊₁(f(X))` -- Q.E.D.
    have h_c_smul_to_algebraMap_smul: ∀ t: L[X], c • t = (algebraMap 𝔽q L c) • t := by
      exact algebra_compatible_smul L c
    have h_c_smul_to_C_algebraMap_mul: ∀ t: L[X], c • t = C (algebraMap 𝔽q L c) * t := by
      intro t
      rw [h_c_smul_to_algebraMap_smul]
      exact smul_eq_C_mul ((algebraMap 𝔽q L) c)
    -- ⊢ (W 𝔽q β (i + 1)).comp (c • x) = c • (W 𝔽q β (i + 1)).comp x
    calc
      _ = ((W 𝔽q β i).comp (c • f))^q - C v ^ (q - 1) * ((W 𝔽q β i).comp (c • f)) := by
        rw [h_rec_form h_i_add_1 (c • f)]
      _ = (C (algebraMap 𝔽q L c) * (W 𝔽q β i).comp f)^q
        - C v ^ (q - 1) * (C (algebraMap 𝔽q L c) * (W 𝔽q β i).comp f) := by
        rw [h_prev_linear_map.map_smul]
        rw [mul_pow]
        simp_rw [h_c_smul_to_C_algebraMap_mul]
        congr
        rw [mul_pow]
      _ = C (algebraMap 𝔽q L (c^q)) * ((W 𝔽q β i).comp f)^q
        - C v ^ (q - 1) * (C (algebraMap 𝔽q L c) * (W 𝔽q β i).comp f) := by
        rw [mul_pow]
        congr -- ⊢ C ((algebraMap 𝔽q L) c) ^ q = C ((algebraMap 𝔽q L) (c ^ q))
        rw [←C_pow]
        simp_rw [algebraMap.coe_pow c q]
      _ = C (algebraMap 𝔽q L (c^q)) * ((W 𝔽q β i).comp f)^q
        - C v ^ (q - 1) * (C (algebraMap 𝔽q L c) * (W 𝔽q β i).comp f) := by
        -- use Fermat's Little Theorem (X^q = X)
        simp only [map_pow]
      _ = C (algebraMap 𝔽q L (c)) * ((W 𝔽q β i).comp f)^q
        - C v ^ (q - 1) * (C (algebraMap 𝔽q L c) * (W 𝔽q β i).comp f) := by
        rw [FiniteField.pow_card]
      _ = C (algebraMap 𝔽q L c) * (((W 𝔽q β i).comp f)^q
        - C v ^ (q - 1) * (W 𝔽q β i).comp f) := by
        rw [←mul_assoc]
        conv_lhs => rw [mul_comm (a := C v ^ (q - 1)) (b := C (algebraMap 𝔽q L c))]; rw [mul_assoc]
        exact
          Eq.symm
            (mul_sub_left_distrib (C ((algebraMap 𝔽q L) c)) ((W 𝔽q β i).comp f ^ q)
              (C v ^ (q - 1) * (W 𝔽q β i).comp f))
      _ = C (algebraMap 𝔽q L c) * (W 𝔽q β (i + 1)).comp f := by
        rw [h_rec_form h_i_add_1 f]
      _ = _ := by
        rw [h_c_smul_to_C_algebraMap_mul]

omit hF₂ in
/--
**Simultaneous Proof of Linearity for `Wᵢ`** from the paper [GGJ96] (Lemma 2.3)
`Wᵢ` is an 𝔽q-linearized polynomial. This means for all polynomials `f, g` with coefficients
  in `L` (i.e. `L[X]`) and for all `c ∈ 𝔽q`, we have: `Wᵢ(f + g) = Wᵢ(f) + Wᵢ(g)` and
  `Wᵢ(c * f) = c * Wᵢ(f)`. As a corollary of this, `Wᵢ` is 𝔽q-linear when evaluated on elements
  of `L`: `Wᵢ(x + y) = Wᵢ(x) + Wᵢ(y)` for all `x, y ∈ L`.
-/
theorem W_linearity (i : Fin r)
    : IsLinearMap 𝔽q (f := fun inner_p ↦ (W 𝔽q β i).comp inner_p) := by
  induction i using Fin.succRecOnSameFinType with
  | zero =>
    -- Base Case: i = 0 => Prove W₀ is linear.
    unfold W
    have h_U0 : (univ : Finset (U 𝔽q β 0)) = {0} := by
      ext u -- u : ↥(U 𝔽q β 0)
      simp only [mem_univ, true_iff, mem_singleton]
      -- ⊢ u = 0
      by_contra h
      have h_u := u.property
      -- only U and Submodule.span_empty is enough for simp
      simp only [U, lt_self_iff_false, not_false_eq_true, Set.Ico_eq_empty, Set.image_empty,
        Submodule.span_empty, Submodule.mem_bot, ZeroMemClass.coe_eq_zero] at h_u
      contradiction

    rw [h_U0, prod_singleton, Submodule.coe_zero, C_0, sub_zero]
    -- ⊢ IsLinearMap 𝔽q fun x ↦ eval x X
    exact { -- can also use `refine` with exact same syntax
      map_add := fun x y => by
        rw [X_comp, X_comp, X_comp]
      map_smul := fun c x => by
        rw [X_comp, X_comp]
    }
  | succ j jh p =>
    -- Inductive Step: Assume properties hold for `j`, prove for `j+1`.
    have h_linear_map: (IsLinearMap 𝔽q (f := fun inner_p ↦ (W 𝔽q β (j + 1)).comp inner_p)) := by
      exact inductive_linear_map_W 𝔽q β (i := j)
        (h_i_add_1 := by omega) (h_prev_linear_map := p)

    exact h_linear_map

/-- Helper function to create a linear map from a polynomial whose evaluation is additive. -/
noncomputable def polyEvalLinearMap {L 𝔽q : Type*} [Field L] [Field 𝔽q] [Algebra 𝔽q L]
  (p : L[X]) (hp_add : IsLinearMap 𝔽q (fun x : L => p.eval x)) : L →ₗ[𝔽q] L :=
{
  toFun    := fun x => p.eval x,
  map_add' := hp_add.map_add,
  map_smul' := hp_add.map_smul
}

omit hF₂ in
theorem W_linear_comp_decomposition (i : Fin r) (h_i_add_1 : i + 1 < r) :
    ∀ p: L[X], (W 𝔽q β (i + 1)).comp p =
      ((W 𝔽q β i).comp p) ^ Fintype.card 𝔽q -
        C (eval (β i) (W 𝔽q β i)) ^ (Fintype.card 𝔽q - 1) * ((W 𝔽q β i).comp p) := by
  have h_linear := W_linearity 𝔽q β (i :=i)
  exact inductive_rec_form_W_comp 𝔽q β h_i_add_1 (i :=i) h_linear

omit hF₂ in
/-- The additive property of `Wᵢ`: `Wᵢ(x + y) = Wᵢ(x) + Wᵢ(y)`. -/
lemma W_is_additive
  (i : Fin r) :
  IsLinearMap (R := 𝔽q) (M := L) (M₂ := L) (f := fun x ↦ (W 𝔽q β i).eval x) := by
  exact Polynomial.linear_map_of_comp_to_linear_map_of_eval (f := (W 𝔽q β i))
    (h_f_linear := W_linearity 𝔽q β (i :=i))

omit hF₂ in
theorem kernel_W_eq_U (i : Fin r) :
  LinearMap.ker (polyEvalLinearMap (W 𝔽q β i)
    (W_is_additive 𝔽q β i)) = U 𝔽q β i := by
  ext x
  -- Unfold the definition of kernel membership and polynomial evaluation.
  simp_rw [LinearMap.mem_ker, polyEvalLinearMap]
  simp only [LinearMap.coe_mk, AddHom.coe_mk] -- simp?
  simp only [eval_W_eq_zero_iff_in_U]

omit hF₂ in
/-- For all `y ∈ Uᵢ`, `Wᵢ(x + y) = Wᵢ(x)`. -/
lemma W_add_U_invariant
  (i : Fin r) :
  ∀ x : L, ∀ y ∈ U 𝔽q β i, (W 𝔽q β i).eval (x + y) = (W 𝔽q β i).eval x := by
  intro x y hy
  rw [(W_is_additive 𝔽q β (i :=i)).map_add]
  rw [Wᵢ_vanishing 𝔽q β i y hy, add_zero]

/-! # Normalized Subspace Vanishing Polynomials `Ŵᵢ(X) := Wᵢ(X) / Wᵢ(βᵢ), ∀ i ∈ {0, ..., r-1}` -/
noncomputable def normalizedW (i : Fin r) : L[X] :=
  C (1 / (W 𝔽q β i).eval (β i)) * W 𝔽q β i

omit [DecidableEq L] [Fintype 𝔽q] h_Fq_char_prime in
/-- The evaluation of the normalized polynomial `Ŵᵢ(X)` at `βᵢ` is 1. -/
lemma normalizedWᵢ_eval_βᵢ_eq_1 {i : Fin r} :
    (normalizedW (𝔽q := 𝔽q) (β := β) (i :=i)).eval (β i) = 1 := by
  rw [normalizedW, eval_mul, eval_C]
  -- This simplifies to `(1 / y) * y`, which is `1`.
  simp only [one_div]
  set u: L := eval (β i) (W (𝔽q := 𝔽q) (β := β) (i :=i))
  rw [←mul_comm]
  -- ⊢ u * u⁻¹ = 1
  refine CommGroupWithZero.mul_inv_cancel u ?_
  -- ⊢ u ≠ 0
  exact Wᵢ_eval_βᵢ_neq_zero (𝔽q := 𝔽q) (β := β) (i :=i)

omit [DecidableEq L] [Fintype 𝔽q] h_Fq_char_prime hβ_lin_indep in
lemma normalizedW₀_eq_1_div_β₀ : normalizedW (𝔽q := 𝔽q) (β := β) (i :=0) = X * C (1 / (β 0)) := by
  -- By definition, U ... 0 = {0}, so the vanishing polynomial is X
  rw [normalizedW]
  rw [W₀_eq_X, eval_X]
  rw [mul_comm]

omit [Fintype 𝔽q] h_Fq_char_prime hβ_lin_indep in
/-- The evaluation `Ŵᵢ₊₁(βᵢ)` is 0. This is because `Ŵᵢ₊₁ = q⁽ⁱ⁾ ∘ Ŵᵢ` and `q⁽ⁱ⁾(1) = 0`. -/
lemma eval_normalizedW_succ_at_beta_prev (i : Fin r) (h_i_add_1 : i + 1 < r) :
  (normalizedW 𝔽q β (i + 1)).eval (β i) = 0 := by
  have h_W_eval: (W 𝔽q β (i+1)).eval (β i) = 0 := by
    rw [eval_W_eq_zero_iff_in_U]
    unfold U
    have h_β_i_in_U: β i ∈ β '' Set.Ico 0 (i + 1) := by
      exact Set.mem_image_of_mem β (Set.mem_Ico.mpr ⟨Nat.zero_le i, Fin.lt_succ' (a:=i) h_i_add_1⟩)
    exact Submodule.subset_span h_β_i_in_U
  unfold normalizedW
  rw [eval_mul]
  rw [h_W_eval, mul_zero]

omit h_Fq_char_prime hF₂ in
/-- The degree of `Ŵᵢ(X)` remains `|𝔽q|ⁱ`. -/
lemma degree_normalizedW (i : Fin r) :
  (normalizedW 𝔽q β i).degree = (Fintype.card 𝔽q)^(i.val) := by
   -- Multiplication by a non-zero constant does not change the degree of a polynomial.
  let c := (1 / (W 𝔽q β i).eval (β i))
  have c_eq: c = (eval (β i) (W 𝔽q β i))⁻¹ := by
    rw [←one_div]
  have hc : c ≠ 0 := by
    have eval_ne_0 := Wᵢ_eval_βᵢ_neq_zero (𝔽q := 𝔽q) (β := β) (i :=i)
    have inv_ne_0 := inv_ne_zero eval_ne_0
    rw [←c_eq] at inv_ne_0
    exact inv_ne_0
  rw [normalizedW, degree_C_mul hc]
  exact degree_W (𝔽q := 𝔽q) (β := β) (i :=i)

omit [Fintype L] [DecidableEq L] [Fintype 𝔽q] h_Fq_char_prime hβ_lin_indep in
lemma β_lt_mem_U (i : Fin r) (j : Fin i) :
  β ⟨j, by omega⟩ ∈ U 𝔽q β (i:=i) := by
  unfold U
  -- It suffices to show the index lies in the generator set `β '' Set.Ico 0 i`.
  apply Submodule.subset_span
  -- Show the index is in `Set.Ico 0 i`, then lift through the image by `β`.
  exact Set.mem_image_of_mem β (Set.mem_Ico.mpr ⟨by simp only [Fin.zero_le], by
    apply Fin.mk_lt_of_lt_val; omega⟩)

omit [DecidableEq L] [Fintype 𝔽q] h_Fq_char_prime hβ_lin_indep in
/-- The normalized polynomial `Ŵᵢ(X)` vanishes on `Uᵢ`. -/
lemma normalizedWᵢ_vanishing (i : Fin r) :
  ∀ u ∈ U 𝔽q β i, (normalizedW 𝔽q β i).eval u = 0 := by
  -- The roots of `Ŵᵢ(X)` are precisely the elements of `Uᵢ`.
  -- `Ŵᵢ` is just a constant multiple of `Wᵢ`, so they share the same roots.
  intro u hu
  rw [normalizedW, eval_mul, eval_C, Wᵢ_vanishing 𝔽q β i u hu, mul_zero]

omit hF₂ in
/-- The normalized subspace vanishing polynomial `Ŵᵢ(X)` is `𝔽q`-linear. -/
theorem normalizedW_is_linear_map (i : Fin r) :
  IsLinearMap 𝔽q (f := fun inner_p ↦ (normalizedW 𝔽q β i).comp inner_p) := by
  let c := 1 / (W 𝔽q β i).eval (β i)
  have hW_lin : IsLinearMap 𝔽q (f := fun inner_p ↦ (W 𝔽q β i).comp inner_p) :=
    W_linearity 𝔽q β (i :=i)
  have h_comp_add := hW_lin.map_add
  have h_comp_smul := hW_lin.map_smul
  -- ⊢ IsLinearMap 𝔽q fun inner_p ↦ (normalizedW 𝔽q β i).comp inner_p
  -- We are given that the composition map for W_i is 𝔽q-linear.
  have h_comp_add := hW_lin.map_add
  have h_comp_smul := hW_lin.map_smul

  -- A crucial helper lemma is understanding how composition distributes over
  -- multiplication by a constant polynomial. (p * C c).comp(q) = p.comp(q) * (C c).comp(q)
  -- Since (C c).comp(q) is just C c, this simplifies nicely.
  have comp_C_mul (f g : L[X]) : (C c * f).comp g = C c * f.comp g := by
    simp only [Polynomial.comp] -- comp to eval₂
    simp only [eval₂_mul, eval₂_C]

  -- To prove `IsLinearMap`, we must prove two properties: `map_add` and `map_smul`.
  -- We construct the IsLinearMap structure directly.
  refine {
    map_add := by {
      intro p q
      -- Unfold the definition of normalizedW to show the structure C c * W_i
      dsimp only [normalizedW]
      -- Apply our helper lemma to the LHS and both terms on the RHS
      rw [comp_C_mul, comp_C_mul, comp_C_mul]
      -- Now use the given linearity of W_i's composition map
      rw [h_comp_add]
      -- The rest is just distribution of multiplication over addition
      rw [mul_add]
    },
    map_smul := by {
      intro k p
      -- Unfold the definition
      dsimp only [normalizedW]
      -- Apply our helper lemma on both sides
      rw [comp_C_mul, comp_C_mul]
      -- Use the given smul-linearity of W_i's composition map
      rw [h_comp_smul]
      -- The rest is showing that scalar multiplication by `k` and polynomial
      -- multiplication by `C c` commute, which follows from ring axioms.
      -- `C c * (k • W_i.comp p)` should equal `k • (C c * W_i.comp p)`.
      -- ⊢ C c * k • (W 𝔽q β i).comp p = k • (C c * (W 𝔽q β i).comp p)
      rw [Algebra.smul_def, Algebra.smul_def]
      -- ⊢ C c * ((algebraMap 𝔽q L[X]) k * (W 𝔽q β i).comp p)
      -- = (algebraMap 𝔽q L[X]) k * (C c * (W 𝔽q β i).comp p)
      -- The `algebraMap` converts the scalar k from 𝔽q into a constant polynomial.
      rw [Algebra.algebraMap_eq_smul_one]
      -- ⊢ C c * (k • 1 * (W 𝔽q β i).comp p) = k • 1 * (C c * (W 𝔽q β i).comp p)
      ac_rfl
    }
  }

omit hF₂ in
theorem normalizedW_is_additive (i : Fin r) :
  IsLinearMap 𝔽q (f := fun x ↦ (normalizedW 𝔽q β i).eval x) := by
  exact Polynomial.linear_map_of_comp_to_linear_map_of_eval (f := (normalizedW 𝔽q β i))
    (h_f_linear := normalizedW_is_linear_map 𝔽q β (i :=i))

omit hF₂ in
theorem kernel_normalizedW_eq_U (i : Fin r) :
    LinearMap.ker (polyEvalLinearMap (normalizedW 𝔽q β i)
    (normalizedW_is_additive 𝔽q β i))
    = U 𝔽q β i := by
  ext x
  -- Unfold the definition of kernel membership and polynomial evaluation.
  simp_rw [LinearMap.mem_ker, polyEvalLinearMap]
  simp_rw [normalizedW, Polynomial.eval_mul, Polynomial.eval_C]
  simp only [one_div, LinearMap.coe_mk, AddHom.coe_mk, mul_eq_zero, inv_eq_zero] -- simp?
  simp only [AdditiveNTT.Wᵢ_eval_βᵢ_neq_zero 𝔽q β i, false_or]
  -- ⊢ eval x (W 𝔽q β i) = 0 ↔ x ∈ U 𝔽q β i
  simp only [eval_W_eq_zero_iff_in_U]

end LinearityOfSubspaceVanishingPolynomials

section NovelPolynomialBasisProof

-- ℓ ≤ r
/-- The Novel Polynomial Basis {`Xⱼ(X)`, j ∈ Fin 2^ℓ} for the space `L⦃<2^ℓ⦄[X]` over `L` -/
-- Definition of Novel Polynomial Basis: `Xⱼ(X) := Π_{i=0}^{ℓ-1} (Ŵᵢ(X))^{jᵢ}`
noncomputable def Xⱼ (ℓ : ℕ) (h_ℓ : ℓ ≤ r) (j : Fin (2 ^ ℓ)) : L[X] :=
  (Finset.univ : Finset (Fin ℓ)).prod
    (fun i => (normalizedW 𝔽q β (Fin.castLE h_ℓ i))^(Nat.getBit i j))

omit [DecidableEq L] [Fintype 𝔽q] h_Fq_char_prime hβ_lin_indep in
/-- The zero-th element of the novel polynomial basis is the constant 1 -/
lemma Xⱼ_zero_eq_one (ℓ : ℕ) (h_ℓ : ℓ ≤ r) :
  Xⱼ 𝔽q β ℓ h_ℓ ⟨0, by exact Nat.two_pow_pos ℓ⟩ = 1 := by
  unfold Xⱼ
  simp only [Nat.getBit_zero_eq_zero, pow_zero]
  exact Finset.prod_const_one

omit h_Fq_char_prime in
/-- The degree of `Xⱼ(X)` is `j`:
  `deg(Xⱼ(X)) = Σ_{i=0}^{ℓ-1} jᵢ * deg(Ŵᵢ(X)) = Σ_{i=0}^{ℓ-1} jᵢ * 2ⁱ = j` -/
lemma degree_Xⱼ (ℓ : ℕ) (h_ℓ : ℓ ≤ r) (j : Fin (2 ^ ℓ)) :
  (Xⱼ 𝔽q β ℓ h_ℓ j).degree = j := by
  rw [Xⱼ, degree_prod]
  set rangeL := Fin ℓ
  -- ⊢ ∑ i ∈ rangeL, (normalizedW 𝔽q β i ^ bit (↑i) j).degree = ↑j
  by_cases h_ℓ_0: ℓ = 0
  · simp only [degree_pow, nsmul_eq_mul];
    -- ⊢ ∑ x, ↑(bit (↑x) j) * (normalizedW 𝔽q β (Fin.castLE h_ℓ✝ x)).degree = ↑j
    simp only [h_ℓ_0, Fin.isEmpty', univ_eq_empty, sum_empty, WithBot.zero_eq_coe,
      Fin.val_eq_zero_iff]
    have h_j := j.isLt
    simp only [h_ℓ_0, pow_zero, Nat.lt_one_iff, Fin.val_eq_zero_iff] at h_j
    exact h_j
  · push_neg at h_ℓ_0
    have deg_each: ∀ i ∈ (Finset.univ : Finset (Fin ℓ)),
      ((normalizedW 𝔽q β (Fin.castLE h_ℓ i))^(Nat.getBit i j)).degree
      = if Nat.getBit i j = 1 then (2:ℕ)^i.val else 0 := by
      intro i _
      rw [degree_pow]
      rw [degree_normalizedW 𝔽q β (i :=Fin.castLE h_ℓ i)]
      simp only [Nat.getBit, Nat.and_one_is_mod, Fin.coe_castLE, nsmul_eq_mul, Nat.cast_ite,
        Nat.cast_pow, Nat.cast_ofNat, CharP.cast_eq_zero, hF₂.out]
      -- ⊢ ↑(↑j >>> ↑i % 2) * 2 ^ ↑i = if ↑j >>> ↑i % 2 = 1 then 2 ^ ↑i else 0
      by_cases h: (j.val >>> i.val) % 2 = 1
      · simp only [h, Nat.cast_one, one_mul, ↓reduceIte];
      · simp only [h, if_false];
        have h_0: (j.val >>> i.val) % 2 = 0 := by
          exact Nat.mod_two_ne_one.mp h
        rw [h_0]
        exact mul_eq_zero_comm.mp rfl
    rw [Finset.sum_congr rfl deg_each] -- .degree introduces (WithBot ℕ)
    -- ⊢ ⊢ ∑ x, ↑(if bit ↑x ↑j = 1 then 2 ^ ↑x else 0) = ↑↑j
    set f:= fun x: ℕ => if Nat.getBit x j = 1 then (2: ℕ) ^ (x: ℕ) else 0
    norm_cast -- from WithBot ℕ to ℕ
    change (∑ x : Fin ℓ, f x) = (j.val: WithBot ℕ)
    norm_cast
    -- ⊢ (∑ x ∈ Icc 0 (ℓ - 1), if bit x j = 1 then 2 ^ x else 0) = ↑j => in Withbot ℕ
    rw [Fin.sum_univ_eq_sum_range (n:=ℓ)] -- switch to sum over Finset.range ℓ
    have h_range: range ℓ = Icc 0 (ℓ-1) := by
      rw [←Nat.range_succ_eq_Icc_zero (n:=ℓ - 1)]
      congr
      rw [Nat.sub_add_cancel]
      omega
    rw [h_range]
    have h_sum: (∑ x ∈ Icc 0 (ℓ - 1), f x)
      = (∑ x ∈ Icc 0 (ℓ - 1), (Nat.getBit x j) * 2^x) := by
      apply sum_congr rfl (fun x hx => by
        have h_res: (if Nat.getBit x j = 1 then 2 ^ x else 0) = (Nat.getBit x j) * 2^x := by
          by_cases h: Nat.getBit x j = 1
          · simp only [h, if_true]; norm_num
          · simp only [h, if_false]; push_neg at h;
            have h_bit_x_j_eq_0: Nat.getBit x j = 0 := by
              have h_either_eq := Nat.getBit_eq_zero_or_one (k := x) (n := j)
              simp only [h, or_false] at h_either_eq
              exact h_either_eq
            rw [h_bit_x_j_eq_0, zero_mul]
        exact h_res
      )
    simp only [h_sum]
    have h_bit_repr_j := Nat.getBit_repr (ℓ := ℓ) (j := j) (by omega)
    rw [←h_bit_repr_j]

/-- The basis vectors `{Xⱼ(X), j ∈ Fin 2^ℓ}` forms a basis for `L⦃<2^ℓ⦄[X]` -/
noncomputable def basisVectors (ℓ : Nat) (h_ℓ : ℓ ≤ r) :
  Fin (2 ^ ℓ) → L⦃<2^ℓ⦄[X] :=
  fun j => ⟨Xⱼ 𝔽q β ℓ h_ℓ j, by
    -- proof of coercion of `Xⱼ(X)` to `L⦃<2^ℓ⦄[X]`, i.e. `degree < 2^ℓ`
    apply Polynomial.mem_degreeLT.mpr
    rw [degree_Xⱼ 𝔽q β ℓ h_ℓ j]
    change (j.val: WithBot ℕ) < ((2: WithBot ℕ) ^ ℓ)
    norm_cast -- somehow `change` helps `norm_cast` to work better here
    omega
  ⟩

/-- The vector space of coefficients for polynomials of degree < 2^ℓ. -/
abbrev CoeffVecSpace (L : Type u) (ℓ : Nat) := Fin (2^ℓ) → L

noncomputable instance (ℓ : Nat) : AddCommGroup (CoeffVecSpace L ℓ) := by
  unfold CoeffVecSpace
  infer_instance -- default additive group for `Fin (2^ℓ) → L`

noncomputable instance finiteDimensionalCoeffVecSpace (ℓ : ℕ) :
  FiniteDimensional (K := L) (V := CoeffVecSpace L ℓ) := by
  unfold CoeffVecSpace
  exact inferInstance

/-- The linear map from polynomials (in the subtype) to their coefficient vectors. -/
def toCoeffsVec (ℓ : Nat) : L⦃<2^ℓ⦄[X] →ₗ[L] CoeffVecSpace L ℓ where
  toFun := fun p => fun i => p.val.coeff i.val
  map_add' := fun p q => by ext i; simp [coeff_add]
  map_smul' := fun c p => by ext i; simp [coeff_smul, smul_eq_mul]

/-- The rows of a square lower-triangular matrix with
non-zero diagonal entries are linearly independent. -/
lemma linearIndependent_rows_of_lower_triangular_ne_zero_diag
  {n : ℕ} {R : Type*} [Field R] (A : Matrix (Fin n) (Fin n) R)
  (h_lower_triangular : A.BlockTriangular ⇑OrderDual.toDual) (h_diag : ∀ i, A i i ≠ 0) :
  LinearIndependent R A := by -- This follows from the fact that such a matrix is invertible
  -- because its determinant is non-zero.
  have h_det : A.det ≠ 0 := by
    rw [Matrix.det_of_lowerTriangular A h_lower_triangular]
    apply prod_ne_zero_iff.mpr
    intro i _; exact h_diag i
  exact Matrix.linearIndependent_rows_of_det_ne_zero (A := A) h_det

/-- The change-of-basis matrix from the novel basis to the monomial basis.
Aⱼᵢ = coeff of Xⁱ in novel basis vector 𝕏ⱼ. novel_coeffs * A = monomial_coeffs -/
noncomputable def changeOfBasisMatrix (ℓ : Nat) (h_ℓ : ℓ ≤ r) : Matrix (Fin (2^ℓ)) (Fin (2^ℓ)) L :=
    fun j i => (toCoeffsVec (L := L) (ℓ := ℓ) (
      basisVectors 𝔽q β ℓ h_ℓ j)) i

omit h_Fq_char_prime in
theorem changeOfBasisMatrix_lower_triangular
  (ℓ : Nat) (h_ℓ : ℓ ≤ r) :
  (changeOfBasisMatrix 𝔽q β ℓ h_ℓ).BlockTriangular ⇑OrderDual.toDual := by
  intro i j hij
  dsimp only [toCoeffsVec, basisVectors, LinearMap.coe_mk, AddHom.coe_mk, changeOfBasisMatrix]
  -- ⊢ (Xⱼ β ℓ ↑i).coeff ↑j = 0
  have deg_X : (Xⱼ 𝔽q β ℓ h_ℓ i).degree = i :=
    degree_Xⱼ 𝔽q β ℓ h_ℓ i
  have h_i_lt_j : i < j := by
    simp only [OrderDual.toDual_lt_toDual] at hij
    exact hij
  have h_res: (Xⱼ 𝔽q β ℓ h_ℓ i).coeff j = 0 := by
    apply coeff_eq_zero_of_natDegree_lt -- we don't use coeff_eq_zero_of_degree_lt
    -- because p.natDegree returns a value of type ℕ instead of WithBot ℕ as in p.degree
    rw [natDegree_eq_of_degree_eq_some (degree_Xⱼ 𝔽q β ℓ h_ℓ i)]
    norm_cast -- auto resolve via h_i_lt_j
  exact h_res

omit h_Fq_char_prime in
theorem changeOfBasisMatrix_diag_ne_zero
  (ℓ : Nat) (h_ℓ : ℓ ≤ r) :
  (∀ i, (changeOfBasisMatrix 𝔽q β ℓ h_ℓ) i i ≠ 0) := by
  intro i
  dsimp [changeOfBasisMatrix, toCoeffsVec, basisVectors]
  have h_deg : (Xⱼ 𝔽q β ℓ h_ℓ i).degree = i := degree_Xⱼ 𝔽q β ℓ h_ℓ i
  apply coeff_ne_zero_of_eq_degree
  norm_cast

omit h_Fq_char_prime in
/-- The determinant of the change-of-basis matrix is non-zero. -/
theorem changeOfBasisMatrix_det_ne_zero
  (ℓ : Nat) (h_ℓ : ℓ ≤ r) :
  (changeOfBasisMatrix 𝔽q β ℓ h_ℓ).det ≠ 0 := by
  let A := changeOfBasisMatrix 𝔽q β ℓ h_ℓ
  -- Use the fact that A is lower-triangular with non-zero diagonal
  rw [Matrix.det_of_lowerTriangular A]
  · -- The determinant of a lower-triangular matrix is
    -- the product of diagonal entries: ⊢ ∏ i, A i i ≠ 0
    let res := changeOfBasisMatrix_diag_ne_zero 𝔽q β ℓ h_ℓ
    exact prod_ne_zero_iff.mpr fun a a_1 ↦ res a
  · -- A is lower-triangular
    exact changeOfBasisMatrix_lower_triangular 𝔽q β ℓ h_ℓ

/-- The change-of-basis matrix is invertible, this is required by the proofs
 of inversion between monomial and novel polynomial basis coefficients. -/
noncomputable instance changeOfBasisMatrix_invertible
  (ℓ : Nat) (h_ℓ : ℓ ≤ r) :
  Invertible (changeOfBasisMatrix 𝔽q β ℓ h_ℓ) := by
  let h_A_invertible: Invertible (changeOfBasisMatrix 𝔽q β ℓ h_ℓ) := by
    refine (changeOfBasisMatrix 𝔽q β ℓ h_ℓ).invertibleOfIsUnitDet ?_
    (expose_names; exact Ne.isUnit (changeOfBasisMatrix_det_ne_zero 𝔽q β ℓ h_ℓ))
  exact h_A_invertible

omit h_Fq_char_prime in
/--
The coefficient vectors of the novel basis polynomials are linearly independent.
This is proven by showing that the change-of-basis matrix to the monomial basis
is lower-triangular with a non-zero diagonal.
-/
lemma coeff_vectors_linear_independent
  (ℓ : Nat) (h_ℓ : ℓ ≤ r) :
    LinearIndependent L (toCoeffsVec (ℓ := ℓ) ∘ (basisVectors 𝔽q β ℓ h_ℓ)) := by
  -- Let `A` be the `2^ℓ x 2^ℓ` change-of-basis matrix.
  set A := changeOfBasisMatrix 𝔽q β ℓ h_ℓ
  -- The `i`-th row of `A` is the coefficient vector of `Xᵢ` in the novel basis.
  -- Apply the lemma about triangular matrices.
  apply linearIndependent_rows_of_lower_triangular_ne_zero_diag A
  · -- ⊢ A.BlockTriangular ⇑OrderDual.toDual => Prove the matrix A is lower-triangular.
    exact changeOfBasisMatrix_lower_triangular 𝔽q β ℓ h_ℓ
  · -- ⊢ ∀ (i : Fin (2 ^ ℓ)), A i i ≠ 0 => All diagonal entries are non-zero.
    exact fun i ↦ changeOfBasisMatrix_diag_ne_zero 𝔽q β ℓ h_ℓ i

omit h_Fq_char_prime in
/-- The basis vectors are linearly independent over `L`. -/
theorem basisVectors_linear_independent (ℓ : Nat) (h_ℓ : ℓ ≤ r) :
    LinearIndependent L (basisVectors 𝔽q β ℓ h_ℓ) := by
  -- We have proved that the image of our basis vectors under the linear map
  -- `toCoeffsVec` is a linearly independent family.
  have h_comp_li := coeff_vectors_linear_independent 𝔽q β ℓ h_ℓ
  -- `LinearIndependent.of_comp` states that if the image of a family of vectors under
  -- a linear map is linearly independent, then so is the original family.
  exact LinearIndependent.of_comp (toCoeffsVec (L := L) (ℓ := ℓ)) h_comp_li

omit h_Fq_char_prime in
/-- The basis vectors span the space of polynomials with degree less than `2^ℓ`. -/
theorem basisVectors_span (ℓ : Nat) (h_ℓ : ℓ ≤ r) :
    Submodule.span L (Set.range (basisVectors 𝔽q β ℓ h_ℓ)) = ⊤ := by
  have h_li := basisVectors_linear_independent 𝔽q β ℓ h_ℓ
  let n := 2 ^ ℓ
  have h_n: n = 2 ^ ℓ := by omega
  have h_n_pos: 0 < n := by
    rw [h_n]
    exact Nat.two_pow_pos ℓ
  have h_finrank_eq_n : Module.finrank L (L⦃< n⦄[X]) = n := finrank_degreeLT_n n
  -- We have `n` linearly independent vectors in an `n`-dimensional space.
  -- The dimension of their span is `n`.
  have h_span_finrank : Module.finrank L (Submodule.span L (Set.range (
    basisVectors 𝔽q β ℓ h_ℓ))) = n := by
    rw [finrank_span_eq_card h_li, Fintype.card_fin]
  -- A subspace with the same dimension as the ambient space must be the whole space.
  rw [←h_finrank_eq_n] at h_span_finrank
  have inst_finite_dim : FiniteDimensional (K := L) (V := L⦃< n⦄[X]) :=
    finiteDimensional_degreeLT (h_n_pos := by omega)
  apply Submodule.eq_top_of_finrank_eq (K := L) (V := L⦃< n⦄[X])
  exact h_span_finrank

/-- The novel polynomial basis for `L⦃<2^ℓ⦄[X]` -/
noncomputable def novelPolynomialBasis (ℓ : Nat) (h_ℓ : ℓ ≤ r) :
  Basis (Fin (2^ℓ)) (R := L) (M := L⦃<2^ℓ⦄[X]) := by
  have hli := basisVectors_linear_independent 𝔽q β ℓ h_ℓ
  have hspan := basisVectors_span 𝔽q β ℓ h_ℓ
  exact Basis.mk hli (le_of_eq hspan.symm)

end NovelPolynomialBasisProof

/-- The polynomial `P(X)` derived from coefficients `a` in the novel polynomial basis `(Xⱼ)`,
`P(X) := ∑_{j=0}^{2^ℓ-1} aⱼ ⋅ Xⱼ(X)` -/
noncomputable def polynomialFromNovelCoeffs (ℓ : ℕ) (h_ℓ : ℓ ≤ r)
  (a : Fin (2 ^ ℓ) → L) : L[X] := ∑ j, C (a j) * (Xⱼ 𝔽q β ℓ h_ℓ j)

noncomputable def polynomialFromNovelCoeffsF₂
  (ℓ : ℕ) (h_ℓ : ℓ ≤ r) (a : Fin (2 ^ ℓ) → L) : L⦃<2^ℓ⦄[X] :=
  ⟨polynomialFromNovelCoeffs 𝔽q β ℓ h_ℓ a, by
    simp only [mem_degreeLT, Nat.cast_pow, Nat.cast_ofNat]
    apply (Polynomial.degree_sum_le Finset.univ (fun j => C (a j) * Xⱼ 𝔽q β ℓ h_ℓ j)).trans_lt
    apply (Finset.sup_lt_iff ?_).mpr ?_
    · -- ⊢ ⊥ < 2 ^ ℓ
      exact compareOfLessAndEq_eq_lt.mp rfl
    · -- ∀ b ∈ univ, (C (a b) * Xⱼ 𝔽q β ℓ h_ℓ b).degree < 2 ^ ℓ
      intro j _
      -- ⊢ (C (a j) * Xⱼ 𝔽q β ℓ h_ℓ j).degree < 2 ^ ℓ
      calc (C (a j) * Xⱼ 𝔽q β ℓ h_ℓ j).degree
        _ ≤ (C (a j)).degree + (Xⱼ 𝔽q β ℓ h_ℓ j).degree := by apply Polynomial.degree_mul_le
        _ ≤ 0 + (Xⱼ 𝔽q β ℓ h_ℓ j).degree := by gcongr; exact Polynomial.degree_C_le
        _ = ↑j.val := by
          simp only [degree_Xⱼ 𝔽q β ℓ h_ℓ j, zero_add]; norm_cast
        _ < ↑(2^ℓ) := by norm_cast; exact j.isLt
  ⟩

omit h_Fq_char_prime in
/-- Proof that the novel polynomial basis is indeed the indicated basis vectors -/
theorem novelPolynomialBasis_is_basisVectors (ℓ : Nat) (h_ℓ : ℓ ≤ r) :
    (novelPolynomialBasis 𝔽q β ℓ h_ℓ)
    = basisVectors 𝔽q β ℓ h_ℓ := by
  simp only [novelPolynomialBasis, Basis.coe_mk]

/-- Convert monomial coefficients to novel polynomial basis coefficients.
Using row vectors: n = m * A⁻¹.
-/
noncomputable def monomialToNovelCoeffs

  (ℓ : ℕ) (h_ℓ : ℓ ≤ r) (monomial_coeffs : Fin (2 ^ ℓ) → L) : Fin (2^ℓ) → L :=
  let A := changeOfBasisMatrix 𝔽q β ℓ h_ℓ
  -- We need A to be invertible to use A⁻¹. This is implicitly handled by Lean
  -- when A⁻¹ is used, but we will rely on the determinant proof later.
  Matrix.vecMul monomial_coeffs A⁻¹

/-- Convert novel polynomial basis coefficients to monomial coefficients.
Using row vectors: m = n * A.
-/
noncomputable def novelToMonomialCoeffs

  (ℓ : ℕ) (h_ℓ : ℓ ≤ r) (novel_coeffs : Fin (2 ^ ℓ) → L) : Fin (2^ℓ) → L :=
  let A := changeOfBasisMatrix 𝔽q β ℓ h_ℓ
  Matrix.vecMul novel_coeffs A

omit h_Fq_char_prime in
/-- The conversion functions are inverses of each other. (Monomial -> Novel -> Monomial) -/
theorem monomialToNovel_novelToMonomial_inverse
  (ℓ : ℕ) (h_ℓ : ℓ ≤ r) :
  ∀ coeffs : Fin (2^ℓ) → L,
    novelToMonomialCoeffs 𝔽q β ℓ h_ℓ
    (monomialToNovelCoeffs 𝔽q β ℓ h_ℓ coeffs) = coeffs := by
  intro coeffs
  -- Unfold the definitions and the let bindings.
  unfold monomialToNovelCoeffs novelToMonomialCoeffs
  dsimp only
  -- Let A be the change of basis matrix.
  let A := changeOfBasisMatrix 𝔽q β ℓ h_ℓ
  -- Goal: (coeffs * A⁻¹) * A = coeffs
  -- Use associativity of vecMul: (v * M) * N = v * (M * N).
  rw [Matrix.vecMul_vecMul]
  -- Goal: coeffs * (A⁻¹ * A) = coeffs, We need A⁻¹ * A = I. This requires det(A) ≠ 0.
  -- Use Matrix.nonsing_inv_mul (A⁻¹ * A = I).
  rw [Matrix.nonsing_inv_mul A (Matrix.isUnit_det_of_invertible A)]
  -- Goal: coeffs * 1 = coeffs
  rw [Matrix.vecMul_one]

omit h_Fq_char_prime in
/-- The conversion functions are inverses of each other. (Novel -> Monomial -> Novel) -/
theorem novelToMonomial_monomialToNovel_inverse
  (ℓ : ℕ) (h_ℓ : ℓ ≤ r) :
  ∀ coeffs : Fin (2^ℓ) → L,
    monomialToNovelCoeffs 𝔽q β ℓ h_ℓ
      (novelToMonomialCoeffs 𝔽q β ℓ h_ℓ coeffs) = coeffs := by
  intro coeffs
  -- Unfold the definitions and the let bindings.
  unfold novelToMonomialCoeffs monomialToNovelCoeffs
  dsimp only
  let A := changeOfBasisMatrix 𝔽q β ℓ h_ℓ
  -- Goal: (coeffs * A) * A⁻¹ = coeffs
  rw [Matrix.vecMul_vecMul]
  -- Goal: coeffs * (A * A⁻¹) = coeffs, we need A * A⁻¹ = I.
  rw [Matrix.mul_nonsing_inv A (Matrix.isUnit_det_of_invertible A)]
  -- Goal: coeffs * 1 = coeffs
  rw [Matrix.vecMul_one]

end AdditiveNTT
