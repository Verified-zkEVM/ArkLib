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
   (`FiniteField.two_pow_le_card_addSubgroup`).
2. The subspace polynomial `P_V` of `V` is monic, `2`-linearized and of degree `2 ^ v`. Its
   coefficients at `X ^ (2 ^ a), …, X ^ (2 ^ (v - 1))` take at most `q ^ (v - a)` values. By
   pigeonhole, some value `b` is shared by at least `2 ^ (v * (m - v)) / q ^ (v - a)` subgroups.
3. Fix such a `b` and let `g = subspaceTopPoly a v b`. Each `g - P_V` has degree `< 2 ^ a` and
   agrees with `g` exactly on `V`. So the `g - P_V` are distinct Reed-Solomon codewords at
   relative distance `1 - 2 ^ v / q` from `evalOnPoints domain g`
   (`card_le_ncard_closeCodewordsRel_of_topCoeffs`).

`Polynomial.subspaceTopCoeffs`, `Polynomial.subspaceTopPoly` and
`Polynomial.subspaceTopPoly_sub_mem_degreeLT` are in
`ArkLib/Data/Polynomial/SubspacePolynomial.lean`.

## Main statements

* `CodingTheory.card_le_ncard_closeCodewordsRel_of_topCoeffs`

The consumer is `rs_lambda_superpoly_extension` in
`ArkLib/Data/CodingTheory/ListDecodability/Bounds/ReedSolomon.lean`.
-/

@[expose] public section

namespace CodingTheory

open Polynomial Code ReedSolomon

section Fiber

variable {F : Type*} [Field F] [Fintype F]

/-- Let `g = subspaceTopPoly a v b`. Each subgroup `V` of size `2 ^ v` whose subspace polynomial
`P_V` has top coefficients `b` gives the codeword `g - P_V`, which agrees with `g` exactly on `V`.
Distinct `V` give distinct codewords. -/
theorem card_le_ncard_closeCodewordsRel_of_topCoeffs [CharP F 2]
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (domain : ι ↪ F) (hdom : Fintype.card ι = Fintype.card F) {a v : ℕ}
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
      (a := a) (v := v) (by rw [natDegree_subspacePolynomial, h1])
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
