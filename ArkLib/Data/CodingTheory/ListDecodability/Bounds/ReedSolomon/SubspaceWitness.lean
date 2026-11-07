/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import ArkLib.Data.CodingTheory.ListDecodability.Bounds.Basic
public import ArkLib.Data.CodingTheory.ReedSolomon
public import ArkLib.Data.Polynomial.SubspacePolynomial

/-!
# Subspace-polynomial witnesses for large Reed-Solomon lists

Over a finite field `F` with `q = 2 ^ m` elements, let `a ≤ v ≤ m` and let `V` range over the
additive subgroups of `F` of size `2 ^ v`. The proof outline for superpolynomial lists is:
1. There are at least `2 ^ (v * (m - v))` such subgroups
   (`Polynomial.exists_finset_addSubgroup_card`).
2. The subspace polynomial `P_V` of `V` is monic, `2`-linearized and of degree `2 ^ v`. Its
   coefficients at `X ^ (2 ^ a), …, X ^ (2 ^ (v - 1))` take at most `q ^ (v - a)` values. By
   pigeonhole, some value `b` is shared by at least `2 ^ (v * (m - v)) / q ^ (v - a)` subgroups.
3. Fix such a `b` and let `g = subspaceTopPoly a v b`. Each `g - P_V` has degree `< 2 ^ a` and
   agrees with `g` exactly on `V`. So the `g - P_V` are distinct Reed-Solomon codewords at
   relative distance `1 - 2 ^ v / q` from `evalOnPoints domain g`
   (`card_le_ncard_closeCodewordsRel_of_topCoeffs`).

## Main definitions

* `CodingTheory.subspaceTopCoeffs`: the coefficients of `X ^ (2 ^ a), …, X ^ (2 ^ (v - 1))`.
* `CodingTheory.subspaceTopPoly`: the polynomial `X ^ (2 ^ v) + ∑ j, b j * X ^ (2 ^ (a + j))`.

## Main statements

* `CodingTheory.subspaceTopPoly_sub_mem_degreeLT`
* `CodingTheory.card_le_ncard_closeCodewordsRel_of_topCoeffs`

`subspaceTopCoeffs` and `subspaceTopPoly` are noncomputable because Mathlib's `Polynomial`
arithmetic is noncomputable.

The consumer is `rs_lambda_superpoly_extension` in
`ArkLib/Data/CodingTheory/ListDecodability/Bounds/ReedSolomon.lean`.
-/

@[expose] public section

namespace CodingTheory

open Polynomial Code ReedSolomon

section TopPolynomial

variable {F : Type*} [Field F]

/-- The coefficients of `X^(2^a), …, X^(2^(v-1))`. -/
noncomputable def subspaceTopCoeffs (a v : ℕ) (P : F[X]) : Fin (v - a) → F :=
  fun j => P.coeff (2 ^ (a + (j : ℕ)))

/-- `X^(2^v) + ∑_j b_j X^(2^(a+j))`. -/
noncomputable def subspaceTopPoly (a v : ℕ) (b : Fin (v - a) → F) : F[X] :=
  X ^ (2 ^ v) + ∑ j : Fin (v - a), C (b j) * X ^ (2 ^ (a + (j : ℕ)))

/-- For a monic linearized `P` of degree `2^v` and `a ≤ v`, removing the top part leaves a
polynomial of degree `< 2^a`. -/
theorem subspaceTopPoly_sub_mem_degreeLT {P : F[X]} (hP : IsTwoLinearized P) (hmon : P.Monic)
    {a v : ℕ} (hdeg : P.natDegree = 2 ^ v) (hav : a ≤ v) :
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

section Fiber

variable {F : Type*} [Field F] [Fintype F]

/-- Let `g = subspaceTopPoly a v b`. Each subgroup `V` of size `2 ^ v` whose subspace polynomial
`P_V` has top coefficients `b` gives the codeword `g - P_V`, which agrees with `g` exactly on `V`.
Distinct `V` give distinct codewords. -/
theorem card_le_ncard_closeCodewordsRel_of_topCoeffs [CharP F 2]
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (domain : ι ↪ F) (hdom : Fintype.card ι = Fintype.card F) {a v : ℕ} (hav : a ≤ v)
    (b : Fin (v - a) → F) (S : Finset (AddSubgroup F))
    (hS : ∀ V ∈ S, Nat.card V = 2 ^ v ∧ subspaceTopCoeffs a v (subspacePolynomial V) = b) :
    (S.card : ℝ) ≤
      ((closeCodewordsRel ((code domain (2 ^ a) : Submodule F (ι → F)) : Set (ι → F))
        (evalOnPoints domain (subspaceTopPoly a v b))
        (1 - (2 : ℝ) ^ v / (Fintype.card F : ℝ))).ncard : ℝ) := by
  classical
  set g := subspaceTopPoly a v b with hg
  have hbij : Function.Bijective domain :=
    (Fintype.bijective_iff_injective_and_card _).2 ⟨domain.injective, hdom⟩
  let f : AddSubgroup F → (ι → F) := fun V => evalOnPoints domain (g - subspacePolynomial V)
  have hdeg : ∀ V ∈ S, g - subspacePolynomial V ∈ degreeLT F (2 ^ a) := by
    intro V hV
    obtain ⟨h1, h2⟩ := hS V hV
    have := subspaceTopPoly_sub_mem_degreeLT (isTwoLinearized_subspacePolynomial V)
      (monic_subspacePolynomial V)
      (a := a) (v := v) (by rw [natDegree_subspacePolynomial, h1]) hav
    rw [h2] at this
    exact this
  have hagree : ∀ V : AddSubgroup F, ∀ i, (evalOnPoints domain g) i = f V i ↔ domain i ∈ V := by
    intro V i
    simp only [f, evalOnPoints, LinearMap.coe_mk, AddHom.coe_mk, map_sub, Pi.sub_apply,
      ← eval_subspacePolynomial_eq_zero_iff]
    constructor <;> intro h <;> linear_combination h
  have hcard : ∀ V : AddSubgroup F, Nat.card V = 2 ^ v →
      (Finset.univ.filter fun i => domain i ∈ V).card = 2 ^ v := by
    intro V hV
    rw [← hV, Nat.card_eq_fintype_card, Fintype.card_subtype]
    refine Finset.card_bij (fun i _ => domain i) (by simp) (fun i _ j _ h => domain.injective h) ?_
    intro y hy
    obtain ⟨i, rfl⟩ := hbij.2 y
    exact ⟨i, by simpa using hy, rfl⟩
  have hmaps : ∀ V ∈ S, f V ∈ closeCodewordsRel
      ((code domain (2 ^ a) : Submodule F (ι → F)) : Set (ι → F))
      (evalOnPoints domain g) (1 - (2 : ℝ) ^ v / (Fintype.card F : ℝ)) := by
    intro V hV
    rw [mem_closeCodewordsRel_iff]
    refine ⟨?_, ?_⟩
    · rw [SetLike.mem_coe, mem_code_iff_exists_polynomial]
      refine ⟨g - subspacePolynomial V, ?_, rfl⟩
      have := hdeg V hV
      rw [mem_degreeLT] at this
      simpa using this
    · rw [Code.relHammingDist_coe]
      have hd : hammingDist (evalOnPoints domain g) (f V) = Fintype.card ι - 2 ^ v := by
        have : hammingDist (evalOnPoints domain g) (f V) =
            (Finset.univ.filter fun i => ¬ domain i ∈ V).card := by
          rw [hammingDist]
          congr 1
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rw [← hagree V i]
        have h4 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset ι))
          (fun i => domain i ∈ V)
        rw [this]
        have h5 := hcard V (hS V hV).1
        rw [Finset.card_univ] at h4
        omega
      have hle : 2 ^ v ≤ Fintype.card ι := by
        rw [← hcard V (hS V hV).1]
        exact (Finset.card_filter_le (Finset.univ : Finset ι) _).trans (by rw [Finset.card_univ])
      have hpos : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
      rw [hd, Nat.cast_sub hle, hdom]
      apply le_of_eq
      push_cast
      field_simp
  have hinj : Set.InjOn f (S : Set (AddSubgroup F)) := by
    intro V hV V' hV' h
    ext x
    obtain ⟨i, rfl⟩ := hbij.2 x
    rw [← hagree V i, ← hagree V' i, h]
  have := Set.ncard_le_ncard_of_injOn f (fun V hV => hmaps V hV) hinj (Set.toFinite _)
  rw [Set.ncard_coe_finset] at this
  exact_mod_cast this

end Fiber

end CodingTheory
