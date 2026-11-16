/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.Basic
public import Mathlib.LinearAlgebra.Lagrange

/-!
# Lower bounds on the error of scalar and affine combiners

Explicit pairs of received words with many exceptional challenges, on a domain of size `n` in a
field of size `q`.

For the affine combiner without agreement loss, `f = 0` and `g` vanishes on `A - 1` coordinates
and is one elsewhere.
Every challenge `(-β z, β)` with `β ≠ 0` and `z` off those coordinates makes the zero candidate
exceptional, which gives `(n - A + 1)(q - 1)` challenges.

For the scalar combiner with agreement loss `s`, `g` is the vanishing polynomial of `A - s - 1`
coordinates, so no polynomial of degree at most `d` agrees with `g` on more than `A - s - 1`
coordinates.
The other coordinates are cut into blocks of `s + 1`, each with its own challenge `γ`, and
`f = -γ g` on the block of `γ`.
Each full block makes the zero candidate exceptional for its challenge.

## Main statements

* `ReedSolomon.affineMCAError_zero_loss_ge` and `ReedSolomon.affineMCAError_zero_loss_ge_half`:
  without agreement loss, the affine error is at least `(n - A + 1)(q - 1) / q²`, hence at least
  `(n - A + 1) / (2q)` (Proposition 6.2 of [CWYZ26]).
* `ReedSolomon.scalarMCAError_ge`: with agreement loss `s`, the scalar error is at least
  `(1 + ⌊(n - A) / (s + 1)⌋) / q` (Proposition 6.1 of [CWYZ26]).

## References

* [Chiesa, A., Weissenberg, G., Yogev, E., and Zheng, K. Z.,
    *Affine combiners for Reed–Solomon proximity gaps*][CWYZ26]
-/

@[expose] public section

namespace ReedSolomon

open Polynomial Finset

variable {F : Type*} [Field F] [DecidableEq F] {ι : Type*} [Fintype ι]

/-- The coordinates whose position in a fixed enumeration lies in `U` are as many as `U`, when
every element of `U` is a position. -/
private theorem card_filter_equivFin_mem (U : Finset ℕ) (hU : ∀ k ∈ U, k < Fintype.card ι) :
    #{i : ι | (Fintype.equivFin ι i : ℕ) ∈ U} = #U := by
  classical
  rw [← card_image_of_injective _
    (Fin.val_injective.comp (Fintype.equivFin ι).injective)]
  congr 1
  ext k
  simp only [mem_image, mem_filter, mem_univ, true_and, Function.comp_apply]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact hi
  · intro hk
    exact ⟨(Fintype.equivFin ι).symm ⟨k, hU k hk⟩, by simpa using hk, by simp⟩

/-- Without agreement loss, the affine combiner has error at least `(n - A + 1)(q - 1) / q²`. -/
theorem affineMCAError_zero_loss_ge [Fintype F] (domain : ι ↪ F) {d A : ℕ}
    (hdA : d + 1 < A) (hAn : A ≤ Fintype.card ι) :
    ((Fintype.card ι - A + 1 : ℕ) : ℝ) * ((Fintype.card F : ℝ) - 1) / (Fintype.card F : ℝ) ^ 2 ≤
      affineMCAError domain d A 0 := by
  classical
  set n := Fintype.card ι
  set pos : ι → ℕ := fun i ↦ (Fintype.equivFin ι i : ℕ)
  have hpos_inj : Function.Injective pos :=
    Fin.val_injective.comp (Fintype.equivFin ι).injective
  have hpos_lt : ∀ i, pos i < n := fun i ↦ (Fintype.equivFin ι i).isLt
  let g : ι → F := fun i ↦ if pos i < A - 1 then 0 else 1
  -- The agreement set of the zero candidate contains the first `A - 1` coordinates and `z`.
  have hS : ∀ z β i, pos i < A - 1 ∨ i = z →
      i ∈ polynomialAgreementSet domain (combinedWord domain 0 g
        (affineMultiplier (-(β * domain z)) β)) 0 := by
    rintro z β i (hi | rfl)
    · simp [g, hi]
    · simp
  have hexc : ∀ z β, A - 1 ≤ pos z → β ≠ 0 →
      IsAffineExceptional domain 0 g d A 0 (-(β * domain z)) β 0 := by
    intro z β hz hβ
    refine ⟨by simp, ?_, ?_⟩
    · have hU : ∀ k ∈ insert (pos z) (range (A - 1)), k < n := by
        intro k hk
        rcases mem_insert.mp hk with rfl | hk
        · exact hpos_lt z
        · have := mem_range.mp hk
          omega
      calc A = #(insert (pos z) (range (A - 1))) := by
              rw [card_insert_of_notMem (by simpa using hz), card_range]
              omega
        _ = #{i : ι | pos i ∈ insert (pos z) (range (A - 1))} :=
              (card_filter_equivFin_mem _ hU).symm
        _ ≤ _ := by
              refine card_le_card fun i hi ↦ hS z β i ?_
              simp only [mem_filter, mem_univ, true_and, mem_insert, mem_range] at hi
              rcases hi with hi | hi
              · exact Or.inr (hpos_inj hi)
              · exact Or.inl hi
    · intro F₀ G₀ _ hG ⟨_, hloss⟩
      -- Without loss, `G₀` agrees with `g` on the whole agreement set.
      have hagree : ∀ i, pos i < A - 1 ∨ i = z → G₀.eval (domain i) = g i := by
        intro i hi
        by_contra hne
        have hmem : i ∈ agreementLoss domain 0 g (affineMultiplier (-(β * domain z)) β) 0
            F₀ G₀ := mem_filter.mpr ⟨hS z β i hi, Or.inr hne⟩
        exact (card_pos.mpr ⟨i, hmem⟩).ne' (Nat.le_zero.mp hloss)
      -- So `G₀` vanishes on `A - 1 > d` points, hence is zero, but `g z = 1`.
      have hG0 : G₀ = 0 := by
        refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero' G₀
          ((univ.filter fun i : ι ↦ pos i ∈ range (A - 1)).map domain) ?_ ?_
        · intro x hx
          obtain ⟨i, hi, rfl⟩ := mem_map.mp hx
          have hi : pos i < A - 1 := by simpa using hi
          rw [hagree i (Or.inl hi)]
          simp [g, hi]
        · rw [card_map, card_filter_equivFin_mem _ fun k hk ↦ by
            have := mem_range.mp hk; omega, card_range]
          have := natDegree_le_of_degree_le hG.le
          omega
      have := hagree z (Or.inr rfl)
      simp [hG0, g, not_lt.mpr hz] at this
  set q := Fintype.card F
  have hq : 1 ≤ q := Fintype.card_pos
  -- The challenges `(-β x_z, β)` with `β ≠ 0` and `z` outside the first `A - 1` coordinates.
  let E : Finset (F × F) :=
    ((univ.filter fun z : ι ↦ pos z ∈ Ico (A - 1) n) ×ˢ (univ.erase (0 : F))).image
      fun p ↦ (-(p.2 * domain p.1), p.2)
  have hEcard : #E = (n - (A - 1)) * (q - 1) := by
    rw [card_image_of_injOn, card_product, card_erase_of_mem (mem_univ _), card_univ,
      card_filter_equivFin_mem _ fun k hk ↦ (mem_Ico.mp hk).2, Nat.card_Ico]
    rintro ⟨z, β⟩ hzβ ⟨z', β'⟩ hzβ' h
    simp only [Prod.mk.injEq, neg_inj] at h
    obtain ⟨h1, rfl⟩ := h
    have hβ : β ≠ 0 := (mem_erase.mp (mem_product.mp hzβ).2).1
    rw [mul_right_inj' hβ, domain.apply_eq_iff_eq] at h1
    rw [h1]
  have hEsub :
      E ⊆ univ.filter fun c : F × F ↦ ∃ P, IsAffineExceptional domain 0 g d A 0 c.1 c.2 P := by
    intro c hc
    obtain ⟨⟨z, β⟩, hzβ, rfl⟩ := mem_image.mp hc
    simp only [mem_product, mem_filter, mem_univ, true_and, mem_Ico, mem_erase] at hzβ
    exact mem_filter.mpr ⟨mem_univ _, 0, hexc z β hzβ.1.1 hzβ.2.1⟩
  refine le_trans ?_ (le_affineMCAError domain d A 0 0 g)
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc ((n - A + 1 : ℕ) : ℝ) * ((q : ℝ) - 1) = (#E : ℝ) := by
        rw [hEcard, show n - A + 1 = n - (A - 1) by omega]
        push_cast [hq]
        ring
    _ ≤ _ := by exact_mod_cast card_le_card hEsub

/-- Without agreement loss, the affine combiner has error at least `(n - A + 1) / (2q)`. -/
theorem affineMCAError_zero_loss_ge_half [Fintype F] (domain : ι ↪ F) {d A : ℕ}
    (hdA : d + 1 < A) (hAn : A ≤ Fintype.card ι) :
    ((Fintype.card ι - A + 1 : ℕ) : ℝ) / (2 * (Fintype.card F : ℝ)) ≤
      affineMCAError domain d A 0 := by
  refine le_trans ?_ (affineMCAError_zero_loss_ge domain hdA hAn)
  have hq : (2 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.one_lt_card
  have hN : (0 : ℝ) ≤ ((Fintype.card ι - A + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (mul_nonneg hN (by linarith : (0 : ℝ) ≤ Fintype.card F))
    (by linarith : (0 : ℝ) ≤ Fintype.card F - 2)]

/-- With agreement loss `s`, the scalar combiner has error at least
`(1 + ⌊(n - A) / (s + 1)⌋) / q`. -/
theorem scalarMCAError_ge [Fintype F] (domain : ι ↪ F) {d A s : ℕ}
    (hdA : d + s + 1 < A) (hAn : A ≤ Fintype.card ι) :
    ((1 + (Fintype.card ι - A) / (s + 1) : ℕ) : ℝ) / (Fintype.card F : ℝ) ≤
      scalarMCAError domain d A s := by
  classical
  set n := Fintype.card ι
  set pos : ι → ℕ := fun i ↦ (Fintype.equivFin ι i : ℕ)
  set m := A - s - 1
  set k := 1 + (n - A) / (s + 1) with hk
  have hkn : m + k * (s + 1) ≤ n := by
    have := Nat.div_mul_le_self (n - A) (s + 1)
    have : k * (s + 1) = (s + 1) + (n - A) / (s + 1) * (s + 1) := by rw [hk]; ring
    omega
  -- The vanishing polynomial `V` of the first `m` coordinates is the second received word.
  set C := univ.filter fun i : ι ↦ pos i ∈ range m
  have hCcard : #C = m := by
    rw [card_filter_equivFin_mem _ fun k hk ↦ by have := mem_range.mp hk; omega, card_range]
  set V : F[X] := Lagrange.nodal C domain
  have hVdeg : V.natDegree = m := by rw [Lagrange.natDegree_nodal, hCcard]
  set g : ι → F := fun i ↦ V.eval (domain i)
  -- Distinct challenges, one per block of `s + 1` coordinates after the first `m`.
  set γ : ℕ → F := fun j ↦ if h : j < n then domain ((Fintype.equivFin ι).symm ⟨j, h⟩) else 0
  have hγ : Set.InjOn γ (range n) := by
    intro j hj j' hj' h
    have hj : j < n := mem_range.mp hj
    have hj' : j' < n := mem_range.mp hj'
    simpa [γ, hj, hj'] using h
  set lab : ι → ℕ := fun i ↦ (pos i - m) / (s + 1)
  set f : ι → F := fun i ↦ -(γ (lab i) * g i)
  have hS : ∀ j i, pos i < m ∨ lab i = j →
      i ∈ polynomialAgreementSet domain (combinedWord domain f g (Polynomial.C (γ j))) 0 := by
    rintro j i (hi | rfl)
    · have hg : g i = 0 := Lagrange.eval_nodal_at_node (by simpa [C] using hi)
      simp [f, hg]
    · simp [f]
  have hcard : ∀ j < k, A ≤
      #(polynomialAgreementSet domain (combinedWord domain f g (Polynomial.C (γ j))) 0) := by
    intro j hj
    have hjk : (j + 1) * (s + 1) ≤ k * (s + 1) := Nat.mul_le_mul_right _ hj
    have hU : ∀ x ∈ range m ∪ Ico (m + j * (s + 1)) (m + (j + 1) * (s + 1)), x < n := by
      intro x hx
      rcases mem_union.mp hx with hx | hx
      · have := mem_range.mp hx; omega
      · have := mem_Ico.mp hx; omega
    calc A = #(range m ∪ Ico (m + j * (s + 1)) (m + (j + 1) * (s + 1))) := by
          rw [card_union_of_disjoint (disjoint_left.mpr fun x hx hx' ↦ by
            have := mem_range.mp hx; have := mem_Ico.mp hx'; omega), card_range, Nat.card_Ico]
          rw [add_mul]
          omega
      _ = #{i : ι | pos i ∈ range m ∪ Ico (m + j * (s + 1)) (m + (j + 1) * (s + 1))} :=
          (card_filter_equivFin_mem _ hU).symm
      _ ≤ _ := by
          refine card_le_card fun i hi ↦ hS j i ?_
          simp only [mem_filter, mem_univ, true_and, mem_union, mem_range, mem_Ico] at hi
          rcases hi with hi | hi
          · exact Or.inl hi
          · exact Or.inr (Nat.div_eq_of_lt_le (by omega) (by omega))
  have hexc : ∀ j < k, IsScalarExceptional domain f g d A s (γ j) 0 := by
    intro j hj
    refine ⟨by simp, hcard j hj, ?_⟩
    intro F₀ G₀ _ hG ⟨_, hloss⟩
    -- The witness `G₀` agrees with `g` off the lost points, so on more than `m` points.
    have hsplit := card_filter_add_card_filter_not
      (s := polynomialAgreementSet domain (combinedWord domain f g (Polynomial.C (γ j))) 0)
      fun i ↦ F₀.eval (domain i) ≠ f i ∨ G₀.eval (domain i) ≠ g i
    have hA := hcard j hj
    have hloss' := hloss
    unfold agreementLoss at hloss'
    have hzero : V - G₀ = 0 := by
      refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _
        (((polynomialAgreementSet domain (combinedWord domain f g (Polynomial.C (γ j))) 0).filter
          fun i ↦ ¬(F₀.eval (domain i) ≠ f i ∨ G₀.eval (domain i) ≠ g i)).map domain) ?_ ?_
      · intro x hx
        obtain ⟨i, hi, rfl⟩ := mem_map.mp hx
        have hi := (mem_filter.mp hi).2
        simp only [ne_eq, not_or, not_not] at hi
        simp [g, hi.2]
      · rw [card_map]
        have := natDegree_sub_le V G₀
        have := natDegree_le_of_degree_le hG
        omega
    have := natDegree_le_of_degree_le hG
    rw [← sub_eq_zero.mp hzero, hVdeg] at this
    omega
  refine le_trans ?_ (le_scalarMCAError domain d A s f g)
  apply div_le_div_of_nonneg_right _ (by positivity)
  have : k ≤ #(univ.filter fun c : F ↦ ∃ P, IsScalarExceptional domain f g d A s c P) := by
    rw [← card_range k]
    refine card_le_card_of_injOn γ (fun j hj ↦ ?_) (hγ.mono ?_)
    · exact mem_filter.mpr ⟨mem_univ _, 0, hexc j (mem_range.mp hj)⟩
    · intro j hj
      simp only [coe_range, Set.mem_Iio] at hj ⊢
      have : k ≤ k * (s + 1) := Nat.le_mul_of_pos_right _ (by omega)
      omega
  exact_mod_cast this

end ReedSolomon
