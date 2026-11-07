/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

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
4. A finite field with `2 ^ m` elements has at least `2 ^ (v * (m - v))` additive subgroups of
   size `2 ^ v`, namely the graphs of `𝔽₂`-linear maps `𝔽₂ ^ v → 𝔽₂ ^ (m - v)`.

## Main definitions

* `Polynomial.subspacePolynomial`: the polynomial `∏ x ∈ V, (X - x)`.
* `Polynomial.IsTwoLinearized`: only coefficients at powers of two are nonzero.

## Main statements

* `Polynomial.isTwoLinearized_subspacePolynomial`
* `Polynomial.exists_finset_addSubgroup_card`

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
      intro j hj
      refine ⟨0, ?_⟩
      by_contra hne
      apply hj
      rw [coeff_X]
      split_ifs with h
      · exact absurd h.symm (by simpa using hne)
      · rfl
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

section Counting

/-- A field of characteristic `2` with `2 ^ m` elements is additively `(ZMod 2) ^ m`. -/
private theorem nonempty_addEquiv_pi_zmod_two {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {m : ℕ} (hF : Fintype.card F = 2 ^ m) : Nonempty (F ≃+ (Fin m → ZMod 2)) := by
  let : Module (ZMod 2) F := AddCommGroup.zmodModule (n := 2) (fun x => by
    rw [two_nsmul]; exact CharTwo.add_self_eq_zero x)
  have h1 : Fintype.card F = Fintype.card (ZMod 2) ^ Module.finrank (ZMod 2) F :=
    Module.card_eq_pow_finrank
  rw [ZMod.card, hF] at h1
  have h2 : Module.finrank (ZMod 2) F = m :=
    (Nat.pow_right_injective (le_refl 2) h1).symm
  have h3 : Module.finrank (ZMod 2) F = Module.finrank (ZMod 2) (Fin m → ZMod 2) := by
    rw [h2, Module.finrank_fin_fun]
  exact ⟨(LinearEquiv.ofFinrankEq F (Fin m → ZMod 2) h3).toAddEquiv⟩

/-- The graph of the `𝔽₂`-linear map with matrix `A`, as an additive map
`𝔽₂ ^ v → 𝔽₂ ^ m`. -/
private def graphHom {m v : ℕ} (hv : v ≤ m) (A : Fin (m - v) → Fin v → ZMod 2) :
    (Fin v → ZMod 2) →+ (Fin m → ZMod 2) where
  toFun y i := if h : i.val < v then y ⟨i, h⟩ else ∑ j, A ⟨i - v, by omega⟩ j * y j
  map_zero' := by ext i; simp
  map_add' := by
    intro x y; ext i
    by_cases h : i.val < v <;> simp [h, mul_add, Finset.sum_add_distrib]

private theorem graphHom_apply_lt {m v : ℕ} (hv : v ≤ m) (A : Fin (m - v) → Fin v → ZMod 2)
    (y : Fin v → ZMod 2) (j : Fin v) : graphHom hv A y ⟨j, by omega⟩ = y j := by
  simp [graphHom]

private theorem graphHom_injective {m v : ℕ} (hv : v ≤ m) (A : Fin (m - v) → Fin v → ZMod 2) :
    Function.Injective (graphHom hv A) := by
  intro x y h
  funext j
  rw [← graphHom_apply_lt hv A x j, ← graphHom_apply_lt hv A y j, h]

private theorem range_graphHom_injective {m v : ℕ} (hv : v ≤ m) :
    Function.Injective (fun A : Fin (m - v) → Fin v → ZMod 2 => (graphHom hv A).range) := by
  intro A B h
  funext r j
  have hmem : graphHom hv A (Pi.single j 1) ∈ (graphHom hv B).range := by
    have : graphHom hv A (Pi.single j 1) ∈ (graphHom hv A).range := ⟨_, rfl⟩
    simpa [h] using this
  obtain ⟨y, hy⟩ := hmem
  have hyj : y = Pi.single j 1 := by
    funext k
    have := congrFun hy ⟨k, by omega⟩
    rw [graphHom_apply_lt, graphHom_apply_lt] at this
    exact this
  subst hyj
  have := congrFun hy ⟨v + r, by omega⟩
  have hnl : ¬ (v + r.val < v) := by omega
  simp [graphHom, hnl, Pi.single_apply] at this
  exact this.symm

private theorem exists_finset_addSubgroup_pi_zmod_two {m v : ℕ} (hv : v ≤ m) :
    ∃ T : Finset (AddSubgroup (Fin m → ZMod 2)),
      2 ^ (v * (m - v)) ≤ T.card ∧ ∀ V ∈ T, Nat.card V = 2 ^ v := by
  classical
  refine ⟨Finset.univ.image (fun A => (graphHom hv A).range), ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ (range_graphHom_injective hv)]
    simp [ZMod.card, ← pow_mul]
  · intro V hV
    obtain ⟨A, -, rfl⟩ := Finset.mem_image.1 hV
    have : Nat.card (graphHom hv A).range = Nat.card (Fin v → ZMod 2) :=
      (Nat.card_congr (AddMonoidHom.ofInjective (graphHom_injective hv A)).toEquiv).symm
    rw [this]; simp [Nat.card_eq_fintype_card, ZMod.card]

variable {F : Type*} [Field F] [Fintype F]

/-- A finite field of characteristic `2` with `2 ^ m` elements has at least `2 ^ (v * (m - v))`
additive subgroups of size `2 ^ v`. -/
theorem exists_finset_addSubgroup_card [CharP F 2] {m v : ℕ} (hF : Fintype.card F = 2 ^ m)
    (hv : v ≤ m) :
    ∃ T : Finset (AddSubgroup F), 2 ^ (v * (m - v)) ≤ T.card ∧ ∀ V ∈ T, Nat.card V = 2 ^ v := by
  classical
  obtain ⟨e⟩ := nonempty_addEquiv_pi_zmod_two hF
  obtain ⟨T, hc, hV⟩ := exists_finset_addSubgroup_pi_zmod_two (m := m) hv
  refine ⟨T.image (AddSubgroup.map e.symm.toAddMonoidHom), ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ (AddSubgroup.map_injective e.symm.injective)]
    exact hc
  · intro W hW
    obtain ⟨V, hV', rfl⟩ := Finset.mem_image.1 hW
    rw [← hV V hV']
    exact (Nat.card_congr (AddSubgroup.equivMapOfInjective V e.symm.toAddMonoidHom
      e.symm.injective)).symm

end Counting

end Polynomial
