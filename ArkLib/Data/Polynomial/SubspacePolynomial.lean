/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Subspace polynomials

For an additive subgroup `V` of a finite field `F`, the subspace polynomial of `V` is
`∏ x ∈ V, (X - x)`. In characteristic `2` it is a *linearized* polynomial: only the coefficients
of `X ^ (2 ^ i)` can be nonzero.

The file proves:
1. The subspace polynomial is monic of degree `|V|`, and its roots are exactly `V`.
2. In characteristic `2`, adjoining `b ∉ V` multiplies by the translate `P_V (X - b)`.
3. In characteristic `2`, a linearized polynomial is additive and subspace polynomials are
   linearized.

## Main definitions

* `Polynomial.subspacePolynomial`: the polynomial `∏ x ∈ V, (X - x)`.
* `Polynomial.IsTwoLinearized`: only coefficients at powers of two are nonzero.
* `Polynomial.subspaceTopCoeffs`, `Polynomial.subspaceTopPoly`: the coefficients of
  `X ^ (2 ^ a), …, X ^ (2 ^ (v - 1))`, and `X ^ (2 ^ v) + ∑ j, b j * X ^ (2 ^ (a + j))`.

## Main statements

* `Polynomial.isTwoLinearized_subspacePolynomial`, `Polynomial.isTwoLinearized_X`
* `Polynomial.subspacePolynomial_range_eq_prod`: for an injective `L`, the subspace polynomial of
  its range is `∏ g, (X - C (L g))`.
* `Polynomial.subspaceTopPoly_sub_mem_degreeLT`: for any monic `2`-linearized `P` of degree `2 ^ v`
  (not only a subspace polynomial), removing its top coefficients leaves degree `< 2 ^ a`.

`subspacePolynomial` is noncomputable because Mathlib's `Polynomial` arithmetic is noncomputable.
-/

@[expose] public section

namespace Polynomial

section SubspacePolynomial

variable {F : Type*} [Field F] [Fintype F]

open Classical in
/-- The subspace polynomial `∏ x ∈ V, (X - x)` of an additive subgroup `V ≤ F`. -/
noncomputable def subspacePolynomial (V : AddSubgroup F) : F[X] :=
  ∏ x ∈ Finset.univ.filter (· ∈ V), (X - C x)

/-- `P` is `2`-linearized: only the coefficients at powers of two can be nonzero. -/
def IsTwoLinearized (P : F[X]) : Prop :=
  ∀ j, P.coeff j ≠ 0 → ∃ i, j = 2 ^ i

/-- The subspace polynomial is monic. -/
theorem monic_subspacePolynomial (V : AddSubgroup F) : (subspacePolynomial V).Monic := by
  unfold subspacePolynomial
  exact monic_prod_of_monic _ _ (fun x _ => monic_X_sub_C x)

/-- The subspace polynomial of `V` has degree `Nat.card V`. -/
theorem natDegree_subspacePolynomial (V : AddSubgroup F) :
    (subspacePolynomial V).natDegree = Nat.card V := by
  classical
  unfold subspacePolynomial
  rw [natDegree_prod_of_monic _ _ (fun x _ => monic_X_sub_C x)]
  simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- The roots of the subspace polynomial of `V` are exactly the elements of `V`. -/
theorem eval_subspacePolynomial_eq_zero_iff (V : AddSubgroup F) (x : F) :
    (subspacePolynomial V).eval x = 0 ↔ x ∈ V := by
  classical
  unfold subspacePolynomial
  rw [eval_prod, Finset.prod_eq_zero_iff]
  simp [sub_eq_zero]

/-- The subspace polynomial of the trivial subgroup is `X`. -/
@[simp]
theorem subspacePolynomial_bot : subspacePolynomial (⊥ : AddSubgroup F) = X := by
  classical
  unfold subspacePolynomial
  have : (Finset.univ.filter (· ∈ (⊥ : AddSubgroup F))) = {0} := by
    ext x; simp
  rw [this]; simp

/-- The subspace polynomial of the range of an injective additive map is the product over its
domain. -/
theorem subspacePolynomial_range_eq_prod {G : Type*} [AddCommGroup G] [Fintype G] (L : G →+ F)
    (hL : Function.Injective L) : subspacePolynomial L.range = ∏ g, (X - C (L g)) := by
  classical
  unfold subspacePolynomial
  rw [← Finset.prod_image (f := fun x => X - C x) (s := Finset.univ) fun x _ y _ h => hL h]
  congr 1
  ext x
  simp [AddMonoidHom.mem_range]

/-- Adjoining `b ∉ V` in characteristic `2` multiplies the subspace polynomial by its translate:
`P_{V ⊔ ⟨b⟩} = P_V * P_V (X - b)`. -/
theorem subspacePolynomial_sup_zmultiples [CharP F 2] (V : AddSubgroup F) (b : F) (hb : b ∉ V) :
    subspacePolynomial (V ⊔ AddSubgroup.zmultiples b) =
      subspacePolynomial V * (subspacePolynomial V).comp (X - C b) := by
  classical
  have h2 : ∀ n : ℤ, ∀ z : F, (n • b = z) → z = 0 ∨ z = b := by
    intro n z hz
    subst hz
    rcases Int.even_or_odd' n with ⟨k, rfl | rfl⟩
    · left; rw [zsmul_eq_mul]; push_cast; rw [CharTwo.two_eq_zero]; simp
    · right; rw [zsmul_eq_mul]; push_cast; rw [CharTwo.two_eq_zero]; simp
  have hmem : ∀ x : F, x ∈ V ⊔ AddSubgroup.zmultiples b ↔ x ∈ V ∨ x + b ∈ V := by
    intro x
    rw [AddSubgroup.mem_sup]
    constructor
    · rintro ⟨y, hy, z, hz, rfl⟩
      obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hz
      rcases h2 n z hn with rfl | rfl
      · left; simpa using hy
      · right; rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]; exact hy
    · rintro (h | h)
      · exact ⟨x, h, 0, zero_mem _, by simp⟩
      · refine ⟨x + b, h, b, AddSubgroup.mem_zmultiples b, ?_⟩
        rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have hset : Finset.univ.filter (· ∈ V ⊔ AddSubgroup.zmultiples b) =
      Finset.univ.filter (· ∈ V) ∪ (Finset.univ.filter (· ∈ V)).image (· + b) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_image,
      hmem]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr ⟨x + b, h, by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]⟩
    · rintro (h | ⟨y, hy, rfl⟩)
      · exact Or.inl h
      · right; rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]; exact hy
  have hdisj : Disjoint (Finset.univ.filter (· ∈ V))
      ((Finset.univ.filter (· ∈ V)).image (· + b)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image] at hx hx'
    obtain ⟨y, hy, rfl⟩ := hx'
    exact hb (by simpa using V.sub_mem hx hy)
  unfold subspacePolynomial
  rw [hset, Finset.prod_union hdisj, Finset.prod_image (fun x _ y _ h => add_right_cancel h)]
  congr 1
  rw [prod_comp]
  refine Finset.prod_congr rfl fun y _ => ?_
  simp only [sub_comp, X_comp, C_comp]
  rw [map_add]; ring

end SubspacePolynomial

section Linearized

variable {F : Type*} [Field F]

/-- `X` is `2`-linearized. -/
theorem isTwoLinearized_X : IsTwoLinearized (X : F[X]) := by
  intro j hj
  rw [coeff_X] at hj
  split_ifs at hj with h
  · exact ⟨0, by rw [← h, pow_zero]⟩
  · exact absurd rfl hj

/-- A `2`-linearized polynomial is additive in characteristic `2`: `P (X - b) = P - P b`. -/
theorem IsTwoLinearized.comp_X_sub_C [CharP F 2] {P : F[X]} (hP : IsTwoLinearized P) (b : F) :
    P.comp (X - C b) = P - C (P.eval b) := by
  classical
  have key : ∀ n ∈ P.support,
      C (P.coeff n) * (X - C b) ^ n = C (P.coeff n) * X ^ n - C (P.coeff n * b ^ n) := by
    intro n hn
    obtain ⟨i, rfl⟩ := hP n (mem_support_iff.mp hn)
    rw [sub_pow_char_pow, ← C_pow, mul_sub, C_mul]
  rw [comp, eval₂_eq_sum, Polynomial.sum_def, Finset.sum_congr rfl key, Finset.sum_sub_distrib,
    ← map_sum C, ← as_sum_support_C_mul_X_pow, eval_eq_sum, Polynomial.sum_def]

/-- `P ^ 2 - C c * P` is `2`-linearized when `P` is, in characteristic `2`. -/
theorem IsTwoLinearized.sq_sub_C_mul [CharP F 2] {P : F[X]} (hP : IsTwoLinearized P) (c : F) :
    IsTwoLinearized (P ^ 2 - C c * P) := by
  intro j hj
  have hcoeff : (P ^ 2).coeff j ≠ 0 ∨ (C c * P).coeff j ≠ 0 := by
    by_contra h
    push Not at h
    exact hj (by rw [coeff_sub, h.1, h.2, sub_zero])
  rcases hcoeff with h | h
  · have hp : (map (frobenius F 2) (expand F 2 P)).coeff j ≠ 0 := by
      rw [map_frobenius_expand]; exact h
    rw [coeff_map] at hp
    have hp' : (expand F 2 P).coeff j ≠ 0 := fun h0 => hp (by rw [h0, map_zero])
    rw [coeff_expand (by norm_num)] at hp'
    split_ifs at hp' with hd
    · obtain ⟨k, rfl⟩ := hd
      have e : 2 * k / 2 = k := by omega
      rw [e] at hp'
      obtain ⟨i, hi⟩ := hP _ hp'
      exact ⟨i + 1, by rw [hi, pow_succ]; ring⟩
    · exact absurd rfl hp'
  · rw [coeff_C_mul] at h
    exact hP j (right_ne_zero_of_mul h)

end Linearized

section TopPolynomial

variable {F : Type*} [Field F]

/-- The coefficients of `X^(2^a), …, X^(2^(v-1))`. -/
noncomputable def subspaceTopCoeffs (a v : ℕ) (P : F[X]) : Fin (v - a) → F :=
  fun j => P.coeff (2 ^ (a + (j : ℕ)))

/-- `X^(2^v) + ∑_j b_j X^(2^(a+j))`. -/
noncomputable def subspaceTopPoly (a v : ℕ) (b : Fin (v - a) → F) : F[X] :=
  X ^ (2 ^ v) + ∑ j : Fin (v - a), C (b j) * X ^ (2 ^ (a + (j : ℕ)))

/-- For a monic `2`-linearized `P` of degree `2^v`, removing the top part leaves a polynomial of
degree `< 2^a`. -/
theorem subspaceTopPoly_sub_mem_degreeLT {P : F[X]} (hP : IsTwoLinearized P) (hmon : P.Monic)
    {a v : ℕ} (hdeg : P.natDegree = 2 ^ v) :
    subspaceTopPoly a v (subspaceTopCoeffs a v P) - P ∈ degreeLT F (2 ^ a) := by
  classical
  rw [mem_degreeLT, degree_lt_iff_coeff_zero]
  intro n hn
  rw [coeff_sub]
  have hmon' : P.coeff (2 ^ v) = 1 := by rw [← hdeg]; exact hmon
  have hle : ∀ m, 2 ^ v < m → P.coeff m = 0 := fun m hm =>
    coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; exact hm)
  have hpow : 2 ^ a ≤ n := hn
  have hsum : (∑ j : Fin (v - a), C (subspaceTopCoeffs a v P j) * X ^ (2 ^ (a + (j : ℕ)))).coeff n =
      ∑ j : Fin (v - a), if n = 2 ^ (a + (j : ℕ)) then subspaceTopCoeffs a v P j else 0 := by
    rw [finsetSum_coeff]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [coeff_C_mul, coeff_X_pow]; split_ifs <;> simp
  unfold subspaceTopPoly
  rw [coeff_add, coeff_X_pow, hsum]
  by_cases hP0 : P.coeff n = 0
  · rw [hP0, sub_zero]
    by_cases h1 : n = 2 ^ v
    · exfalso
      rw [h1] at hP0 hn
      rw [hP0] at hmon'; exact zero_ne_one hmon'
    · simp only [h1, ite_false, zero_add]
      refine Finset.sum_eq_zero fun j _ => ?_
      split_ifs with h3
      · subst h3; exact hP0
      · rfl
  · obtain ⟨i, rfl⟩ := hP n hP0
    have hiv : i ≤ v := by
      by_contra h
      push Not at h
      exact hP0 (hle _ (Nat.pow_lt_pow_right (by norm_num) h))
    have hai : a ≤ i := by
      by_contra h
      push Not at h
      exact absurd hn (not_le.mpr (Nat.pow_lt_pow_right (by norm_num) h))
    rcases hiv.eq_or_lt with rfl | hlt
    · rw [hmon']
      have : ∀ j : Fin (i - a), (2 ^ i = 2 ^ (a + (j : ℕ))) = False := fun j => by
        apply eq_false; intro h
        have := Nat.pow_right_injective (le_refl 2) h
        have := j.2; omega
      simp [this]
    · have hne : ¬ (2 ^ i = 2 ^ v) := (Nat.pow_right_injective (le_refl 2)).ne hlt.ne
      simp only [hne, ite_false]
      have : ∑ j : Fin (v - a),
          (if 2 ^ i = 2 ^ (a + (j : ℕ)) then subspaceTopCoeffs a v P j else 0) =
            P.coeff (2 ^ i) := by
        rw [Finset.sum_eq_single ⟨i - a, by omega⟩]
        · simp [subspaceTopCoeffs, Nat.add_sub_cancel' hai]
        · intro j _ hj
          rw [ite_eq_right_iff]
          intro h
          have := Nat.pow_right_injective (le_refl 2) h
          exact (hj (Fin.ext (by simp; omega))).elim
        · simp
      rw [this]; ring

end TopPolynomial

section Linearization

variable {F : Type*} [Field F] [Fintype F]

/-- In characteristic `2` the subspace polynomial of any additive subgroup is `2`-linearized. -/
theorem isTwoLinearized_subspacePolynomial [CharP F 2] (V : AddSubgroup F) :
    IsTwoLinearized (subspacePolynomial V) := by
  classical
  have key : ∀ S : Finset F,
      IsTwoLinearized (subspacePolynomial (AddSubgroup.closure (S : Set F))) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      simp only [Finset.coe_empty, AddSubgroup.closure_empty, subspacePolynomial_bot]
      exact isTwoLinearized_X
    | insert a S ha ih =>
      have hcl : AddSubgroup.closure ((insert a S : Finset F) : Set F)
          = AddSubgroup.closure (S : Set F) ⊔ AddSubgroup.zmultiples a := by
        rw [Finset.coe_insert, Set.insert_eq, AddSubgroup.closure_union,
          AddSubgroup.zmultiples_eq_closure, sup_comm]
      rw [hcl]
      by_cases hb : a ∈ AddSubgroup.closure (S : Set F)
      · have : AddSubgroup.closure (S : Set F) ⊔ AddSubgroup.zmultiples a
            = AddSubgroup.closure (S : Set F) :=
          sup_eq_left.mpr ((AddSubgroup.zmultiples_le).mpr hb)
        rw [this]; exact ih
      · rw [subspacePolynomial_sup_zmultiples _ a hb, ih.comp_X_sub_C a, mul_sub, ← sq,
          mul_comm _ (C _)]
        exact ih.sq_sub_C_mul _
  have h := key (Finset.univ.filter (· ∈ V))
  have hV : AddSubgroup.closure ((Finset.univ.filter (· ∈ V) : Finset F) : Set F) = V := by
    apply le_antisymm
    · rw [AddSubgroup.closure_le]; intro x hx; simpa using hx
    · intro x hx; exact AddSubgroup.subset_closure (by simpa using hx)
  rwa [hV] at h

end Linearization

end Polynomial
