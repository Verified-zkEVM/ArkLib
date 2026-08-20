/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks, Aleph
-/

import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.ProximityGap.Errors

/-!
# GCXK25 list-decoding-to-MCA bound

This file proves the general linear-code conversion from a list-size bound below minimum distance
to an affine-line MCA bound. The proof combines interpolation of two affine challenges with a
finite-family incidence estimate.

## Main result

- `linear_mcaError_le_of_Lambda_le` is the conversion theorem.

## References

- [GCXK25] Theorem 3.
-/

namespace CodingTheory

open scoped NNReal
open Code CoreDefinitions ProximityGap

section ListImpliesMCA

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

private noncomputable def large_family_low {κ ι π : Type} [Fintype κ] [Fintype ι]
    [Fintype π] [DecidableEq ι] (A : κ → Finset ι) (D : π → Finset ι) : Finset κ := by
  classical
  exact Finset.univ.filter fun x => ∃ p, D p ⊆ A x

private noncomputable def large_family_high {κ ι π : Type} [Fintype κ] [Fintype ι]
    [Fintype π] [DecidableEq ι] (A : κ → Finset ι) (D : π → Finset ι) : Finset κ := by
  classical
  exact Finset.univ \ large_family_low A D

open scoped BigOperators in
private def large_family_sum_card_eq_sum_incidence
    {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι]
    (A : κ → Finset ι) :
    (∑ x : κ, ((A x).card : ℝ)) =
      ∑ i : ι, (((Finset.univ : Finset κ).filter fun x => i ∈ A x).card : ℝ) := by
  classical
  calc
    (∑ x : κ, ((A x).card : ℝ)) =
        ∑ x : κ, ∑ i : ι, if i ∈ A x then (1 : ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro x hx
          symm
          simp
    _ = ∑ i : ι, ∑ x : κ, if i ∈ A x then (1 : ℝ) else 0 := Finset.sum_comm
    _ = ∑ i : ι,
        (((Finset.univ : Finset κ).filter fun x => i ∈ A x).card : ℝ) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact Finset.sum_boole (R := ℝ) (fun x : κ => i ∈ A x) Finset.univ

open scoped BigOperators in
private def large_family_sum_sq_incidence_eq_sum_inter
    {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι]
    (A : κ → Finset ι) :
    (∑ i : ι,
      (((Finset.univ : Finset κ).filter fun x => i ∈ A x).card : ℝ) ^ 2) =
      ∑ x : κ, ∑ y : κ, (((A x) ∩ (A y)).card : ℝ) := by
  classical
  symm
  calc
    (∑ x : κ, ∑ y : κ, (((A x) ∩ (A y)).card : ℝ)) =
        ∑ x : κ, ∑ y : κ, ∑ i : ι,
          if i ∈ A x ∩ A y then (1 : ℝ) else 0 := by
            apply Finset.sum_congr rfl
            intro x hx
            apply Finset.sum_congr rfl
            intro y hy
            have hsum :=
              Finset.sum_boole (R := ℝ) (fun i : ι => i ∈ A x ∩ A y) Finset.univ
            have hf : (Finset.univ.filter fun i : ι => i ∈ A x ∩ A y) = A x ∩ A y := by
              ext i
              simp
            rw [hf] at hsum
            exact hsum.symm
    _ = ∑ x : κ, ∑ i : ι, ∑ y : κ,
          if i ∈ A x ∩ A y then (1 : ℝ) else 0 := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [Finset.sum_comm]
    _ = ∑ i : ι, ∑ x : κ, ∑ y : κ,
          if i ∈ A x ∩ A y then (1 : ℝ) else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ i : ι, ∑ x : κ, ∑ y : κ,
          (if i ∈ A x then (1 : ℝ) else 0) *
            (if i ∈ A y then (1 : ℝ) else 0) := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro x hx
            apply Finset.sum_congr rfl
            intro y hy
            simp only [Finset.mem_inter]
            by_cases hix : i ∈ A x <;> by_cases hiy : i ∈ A y <;> simp [hix, hiy]
    _ = ∑ i : ι,
        (∑ x : κ, if i ∈ A x then (1 : ℝ) else 0) ^ 2 := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [sq, Finset.sum_mul_sum]
    _ = ∑ i : ι,
        (((Finset.univ : Finset κ).filter fun x => i ∈ A x).card : ℝ) ^ 2 := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_boole (R := ℝ) (fun x : κ => i ∈ A x) Finset.univ]

private def linear_mca_affine_agreement (u : Fin 2 → ι → F) (x : F) (c : ι → F) : Finset ι :=
  Finset.univ.filter fun i => u 0 i + x * u 1 i = c i

private def linear_mca_affine_two_agreements (C : LinearCode ι F)
    (u : Fin 2 → ι → F) (x y : F) (hxy : x ≠ y)
    (cx cy : ι → F) (hcx : cx ∈ C) (hcy : cy ∈ C) (S : Finset ι)
    (hx : ∀ i ∈ S, u 0 i + x * u 1 i = cx i)
    (hy : ∀ i ∈ S, u 0 i + y * u 1 i = cy i) :
    ∃ d : Fin 2 → ι → F, (∀ j, d j ∈ C) ∧
      ∀ j i, i ∈ S → u j i = d j i := by
  let d1 : ι → F := (y - x)⁻¹ • (cy - cx)
  have hd1 : d1 ∈ C := by
    exact C.smul_mem (y - x)⁻¹ (C.sub_mem hcy hcx)
  let d0 : ι → F := cx - x • d1
  have hd0 : d0 ∈ C := by
    exact C.sub_mem hcx (C.smul_mem x hd1)
  let d : Fin 2 → ι → F := ![d0, d1]
  refine ⟨d, ?_, ?_⟩
  · intro j
    fin_cases j
    · exact hd0
    · exact hd1
  · intro j i hi
    have hne : y - x ≠ 0 := sub_ne_zero.mpr hxy.symm
    have h1 : u 1 i = d1 i := by
      dsimp [d1]
      field_simp [hne]
      linear_combination hy i hi - hx i hi
    fin_cases j
    · dsimp [d, d0]
      rw [← h1]
      linear_combination hx i hi
    · simpa [d] using h1

private noncomputable def linear_mca_bad_scalars
    (C : LinearCode ι F) (u : Fin 2 → ι → F) (p η : ℝ) : Finset F := by
  classical
  exact Finset.univ.filter fun x : F =>
    IsMCA (AffineLineGenerator F) C x u
      (1 - (1 - p + η) ^ ((1 : ℝ) / 2))

private def linear_mca_high_algebra (m p η s : ℝ)
    (hp_lt : p < 1) (hη_pos : 0 < η)
    (hs_sq : s ^ 2 = 1 - p + η)
    (hineq : m * s ^ 2 ≤ 1 + (m - 1) * (1 - p)) :
    m < 1 / η := by
  rw [lt_div_iff₀ hη_pos]
  nlinarith

open scoped BigOperators in
private def large_family_sparse_card_lt
    {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι]
    (A : κ → Finset ι) (p η s : ℝ)
    (hn : 0 < (Fintype.card ι : ℝ)) (hp_lt : p < 1)
    (hη_pos : 0 < η) (hs_nonneg : 0 ≤ s)
    (hs_sq : s ^ 2 = 1 - p + η)
    (hA : ∀ x, (Fintype.card ι : ℝ) * s ≤ ((A x).card : ℝ))
    (hinter : ∀ x y, x ≠ y →
      (((A x) ∩ (A y)).card : ℝ) ≤ (Fintype.card ι : ℝ) * (1 - p)) :
    (Fintype.card κ : ℝ) < 1 / η := by
  classical
  let m : ℝ := Fintype.card κ
  let n : ℝ := Fintype.card ι
  by_cases hm0 : Fintype.card κ = 0
  · have hm0R : (Fintype.card κ : ℝ) = 0 := by exact_mod_cast hm0
    rw [hm0R]
    positivity
  have hmNat : 0 < Fintype.card κ := Nat.pos_of_ne_zero hm0
  have hm : 0 < m := by
    simpa [m] using (Nat.cast_pos.mpr hmNat : (0 : ℝ) < (Fintype.card κ : ℝ))
  have hn0 : 0 < n := by simpa [n] using hn
  let Z : ℝ := ∑ x : κ, ((A x).card : ℝ)
  let Q : ℝ := ∑ x : κ, ∑ y : κ, (((A x) ∩ (A y)).card : ℝ)
  have hZnonneg : 0 ≤ Z := by
    dsimp [Z]
    positivity
  have hZlower : m * n * s ≤ Z := by
    have hsum := Finset.sum_le_sum (fun x (_hx : x ∈ (Finset.univ : Finset κ)) => hA x)
    simpa [m, n, Z, mul_assoc] using hsum
  have hZupper : Z ≤ m * n := by
    have hsum : (∑ x : κ, ((A x).card : ℝ)) ≤
        ∑ _x : κ, (Fintype.card ι : ℝ) := by
      exact Finset.sum_le_sum fun x _ => by exact_mod_cast Finset.card_le_univ (A x)
    simpa [m, n, Z] using hsum
  have hCauchy : Z ^ 2 ≤ n * Q := by
    have hc := sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset ι))
      (f := fun i =>
        (((Finset.univ : Finset κ).filter fun x => i ∈ A x).card : ℝ))
    rw [← large_family_sum_card_eq_sum_incidence A,
      large_family_sum_sq_incidence_eq_sum_inter A] at hc
    simpa [Z, Q, n] using hc
  let f : κ × κ → ℝ := fun z => (((A z.1) ∩ (A z.2)).card : ℝ)
  have hQsplit : Q = Z + ∑ z ∈ (Finset.univ : Finset κ).offDiag, f z := by
    calc
      Q = ∑ z ∈ (Finset.univ : Finset κ) ×ˢ (Finset.univ : Finset κ), f z := by
        dsimp [Q, f]
        symm
        exact Finset.sum_product _ _ _
      _ = ∑ z ∈ (Finset.univ : Finset κ).diag ∪
            (Finset.univ : Finset κ).offDiag, f z := by
        rw [Finset.diag_union_offDiag]
      _ = (∑ z ∈ (Finset.univ : Finset κ).diag, f z) +
            ∑ z ∈ (Finset.univ : Finset κ).offDiag, f z :=
        Finset.sum_union (Finset.disjoint_diag_offDiag (s := (Finset.univ : Finset κ)))
      _ = Z + ∑ z ∈ (Finset.univ : Finset κ).offDiag, f z := by
        rw [Finset.sum_diag]
        simp [f, Z]
  have hoffCard : (((Finset.univ : Finset κ).offDiag.card : ℕ) : ℝ) = m * (m - 1) := by
    rw [Finset.offDiag_card]
    simp only [Finset.card_univ]
    have hle : Fintype.card κ ≤ Fintype.card κ * Fintype.card κ := by
      nlinarith
    rw [Nat.cast_sub hle]
    push_cast
    simp [m]
    ring
  have hoff : (∑ z ∈ (Finset.univ : Finset κ).offDiag, f z) ≤
      m * (m - 1) * n * (1 - p) := by
    calc
      (∑ z ∈ (Finset.univ : Finset κ).offDiag, f z) ≤
          ∑ _z ∈ (Finset.univ : Finset κ).offDiag, n * (1 - p) := by
            apply Finset.sum_le_sum
            intro z hz
            exact hinter z.1 z.2 (Finset.mem_offDiag.mp hz).2.2
      _ = (((Finset.univ : Finset κ).offDiag.card : ℕ) : ℝ) *
          (n * (1 - p)) := by simp
      _ = m * (m - 1) * n * (1 - p) := by rw [hoffCard]; ring
  have hQupper : Q ≤ Z + m * (m - 1) * n * (1 - p) := by
    rw [hQsplit]
    gcongr
  have hsqLower : (m * n * s) ^ 2 ≤ Z ^ 2 := by
    nlinarith [mul_nonneg (mul_nonneg hm.le hn0.le) hs_nonneg]
  have hmain : (m * n * s) ^ 2 ≤
      n * (m * n + m * (m - 1) * n * (1 - p)) := by
    calc
      (m * n * s) ^ 2 ≤ Z ^ 2 := hsqLower
      _ ≤ n * Q := hCauchy
      _ ≤ n * (Z + m * (m - 1) * n * (1 - p)) := by gcongr
      _ ≤ n * (m * n + m * (m - 1) * n * (1 - p)) := by gcongr
  have hineq : m * s ^ 2 ≤ 1 + (m - 1) * (1 - p) := by
    have hpos : 0 < m * n ^ 2 := mul_pos hm (sq_pos_of_pos hn0)
    nlinarith
  exact linear_mca_high_algebra m p η s hp_lt hη_pos hs_sq hineq

private def large_family_high_card_le_of_domains
    {κ ι π : Type} [Fintype κ] [Fintype ι] [Fintype π] [DecidableEq ι]
    (A : κ → Finset ι) (D : π → Finset ι) (δ η s : ℝ)
    (hn : 0 < (Fintype.card ι : ℝ)) (hδ_lt : δ < 1)
    (hη_pos : 0 < η) (hs_nonneg : 0 ≤ s)
    (hs_sq : s ^ 2 = 1 - δ + η)
    (hA : ∀ x, (Fintype.card ι : ℝ) * s ≤ ((A x).card : ℝ))
    (hpair : ∀ x y, x ≠ y →
      (Fintype.card ι : ℝ) * (1 - δ) ≤ (((A x) ∩ (A y)).card : ℝ) →
      ∃ p, A x ∩ A y ⊆ D p ∧ D p ⊆ A x ∧ D p ⊆ A y) :
    ((large_family_high A D).card : ℝ) ≤ 1 / η := by
  classical
  let H := large_family_high A D
  let AH (x : H) : Finset ι := A x.1
  have hAH (x : H) : (Fintype.card ι : ℝ) * s ≤ ((AH x).card : ℝ) :=
    hA x.1
  have hinter (x y : H) (hxy : x ≠ y) :
      (((AH x) ∩ (AH y)).card : ℝ) ≤
        (Fintype.card ι : ℝ) * (1 - δ) := by
    by_contra hnot
    push Not at hnot
    have hxyval : x.1 ≠ y.1 := by
      intro h
      apply hxy
      exact Subtype.ext h
    obtain ⟨p, hIp, hpX, -⟩ := hpair x.1 y.1 hxyval hnot.le
    have hxlow : x.1 ∈ large_family_low A D := by
      unfold large_family_low
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, ⟨p, hpX⟩⟩
    have hxhigh : x.1 ∈ large_family_high A D := x.2
    unfold large_family_high at hxhigh
    exact (Finset.mem_sdiff.mp hxhigh).2 hxlow
  have hsparse := large_family_sparse_card_lt
    (A := AH) δ η s hn hδ_lt hη_pos hs_nonneg hs_sq hAH hinter
  have hcard : ((large_family_high A D).card : ℝ) < 1 / η := by
    simpa [H] using hsparse
  exact hcard.le

private def linear_mca_low_family_card_le {α S : Type} [Fintype S] [Nonempty S]
    [DecidableEq S] [DecidableEq α]
    (B : Finset α) (A : α → Finset S) (D : Finset S) (p : ℝ)
    (hproper : ∀ a ∈ B, D ⊂ A a)
    (hinter : ∀ a ∈ B, ∀ b ∈ B, a ≠ b → A a ∩ A b = D)
    (hD : (Fintype.card S : ℝ) * (1 - p) ≤ D.card) :
    (B.card : ℝ) ≤ p * Fintype.card S := by
  classical
  have hex (a : B) : ∃ i ∈ A a.1, i ∉ D :=
    Finset.exists_of_ssubset (hproper a.1 a.2)
  let f (a : B) : S := Classical.choose (hex a)
  have hfA (a : B) : f a ∈ A a.1 := (Classical.choose_spec (hex a)).1
  have hfD (a : B) : f a ∉ D := (Classical.choose_spec (hex a)).2
  let g (a : B) : ↥Dᶜ := ⟨f a, Finset.mem_compl.mpr (hfD a)⟩
  have hginj : Function.Injective g := by
    intro a b hab
    by_contra hne
    have hval : f a = f b := congrArg Subtype.val hab
    have hi : f a ∈ A a.1 ∩ A b.1 := by
      rw [Finset.mem_inter]
      exact ⟨hfA a, hval ▸ hfA b⟩
    have habval : a.1 ≠ b.1 := by
      intro heq
      apply hne
      exact Subtype.ext heq
    rw [hinter a.1 a.2 b.1 b.2 habval] at hi
    exact hfD a hi
  have hcardNat : B.card ≤ Dᶜ.card := by
    have hle : B.card ≤ Fintype.card S - D.card := by
      simpa using Fintype.card_le_of_injective g hginj
    rwa [← Finset.card_compl D] at hle
  have hDn : D.card ≤ Fintype.card S := by
    simpa using Finset.card_le_univ D
  have hcompR : (Dᶜ.card : ℝ) ≤ p * (Fintype.card S : ℝ) := by
    rw [Finset.card_compl, Nat.cast_sub hDn]
    nlinarith
  exact (by exact_mod_cast hcardNat : (B.card : ℝ) ≤ (Dᶜ.card : ℝ)).trans hcompR

private def linear_mca_low_family_card_le_of_disjoint {α S : Type} [Fintype S] [Nonempty S]
    [DecidableEq S] [DecidableEq α]
    (B : Finset α) (A : α → Finset S) (D : Finset S) (p : ℝ)
    (hproper : ∀ a ∈ B, D ⊂ A a)
    (hdisj : ∀ a ∈ B, ∀ b ∈ B, a ≠ b →
      (A a \ D) ∩ (A b \ D) = ∅)
    (hD : (Fintype.card S : ℝ) * (1 - p) ≤ D.card) :
    (B.card : ℝ) ≤ p * Fintype.card S := by
  classical
  have hex (a : B) : ∃ i ∈ A a.1, i ∉ D :=
    Finset.exists_of_ssubset (hproper a.1 a.2)
  let f (a : B) : S := Classical.choose (hex a)
  have hfA (a : B) : f a ∈ A a.1 := (Classical.choose_spec (hex a)).1
  have hfD (a : B) : f a ∉ D := (Classical.choose_spec (hex a)).2
  let g (a : B) : ↥Dᶜ := ⟨f a, Finset.mem_compl.mpr (hfD a)⟩
  have hginj : Function.Injective g := by
    intro a b hab
    by_contra hne
    have hval : f a = f b := congrArg Subtype.val hab
    have hi : f a ∈ (A a.1 \ D) ∩ (A b.1 \ D) := by
      rw [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_sdiff]
      exact ⟨⟨hfA a, hfD a⟩, ⟨hval ▸ hfA b, hfD a⟩⟩
    have habval : a.1 ≠ b.1 := by
      intro heq
      apply hne
      exact Subtype.ext heq
    rw [hdisj a.1 a.2 b.1 b.2 habval] at hi
    simp at hi
  have hcardNat : B.card ≤ Dᶜ.card := by
    have hle : B.card ≤ Fintype.card S - D.card := by
      simpa using Fintype.card_le_of_injective g hginj
    rwa [← Finset.card_compl D] at hle
  have hDn : D.card ≤ Fintype.card S := by
    simpa using Finset.card_le_univ D
  have hcompR : (Dᶜ.card : ℝ) ≤ p * (Fintype.card S : ℝ) := by
    rw [Finset.card_compl, Nat.cast_sub hDn]
    nlinarith
  exact (by exact_mod_cast hcardNat : (B.card : ℝ) ≤ (Dᶜ.card : ℝ)).trans hcompR

open scoped BigOperators in
private def large_family_low_card_le_of_domains
    {κ ι π : Type} [Fintype κ] [Fintype ι] [Fintype π] [DecidableEq ι]
    (A : κ → Finset ι) (D : π → Finset ι) (δ : ℝ)
    (hn : 0 < (Fintype.card ι : ℝ))
    (hD : ∀ p, (Fintype.card ι : ℝ) * (1 - δ) ≤ ((D p).card : ℝ))
    (hstrict : ∀ x p, D p ⊆ A x → D p ≠ A x)
    (hpair : ∀ x y, x ≠ y →
      (Fintype.card ι : ℝ) * (1 - δ) ≤ (((A x) ∩ (A y)).card : ℝ) →
      ∃ p, A x ∩ A y ⊆ D p ∧ D p ⊆ A x ∧ D p ⊆ A y) :
    ((large_family_low A D).card : ℝ) ≤
      (Fintype.card π : ℝ) * δ * (Fintype.card ι : ℝ) := by
  classical
  have hnNat : 0 < Fintype.card ι := by exact_mod_cast hn
  letI : Nonempty ι := Fintype.card_pos_iff.mp hnNat
  rcases isEmpty_or_nonempty π with hπ | hπ
  · have hlow : large_family_low A D = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      unfold large_family_low at hx
      obtain ⟨p, -⟩ := (Finset.mem_filter.mp hx).2
      exact isEmptyElim p
    simp [hlow]
  · letI : Nonempty π := hπ
    let L := large_family_low A D
    let cand (x : L) : Finset π := Finset.univ.filter fun p => D p ⊆ A x.1
    have hcand (x : L) : (cand x).Nonempty := by
      have hxmem : x.1 ∈ large_family_low A D := x.2
      unfold large_family_low at hxmem
      obtain ⟨p, hp⟩ := (Finset.mem_filter.mp hxmem).2
      exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hp⟩⟩
    have hmax (x : L) : ∃ p ∈ cand x, ∀ q ∈ cand x, (D q).card ≤ (D p).card :=
      Finset.exists_max_image (cand x) (fun p => (D p).card) (hcand x)
    let best (x : L) : π := Classical.choose (hmax x)
    have hbestmem (x : L) : best x ∈ cand x := (Classical.choose_spec (hmax x)).1
    have hbestmax (x : L) (q : π) (hq : q ∈ cand x) :
        (D q).card ≤ (D (best x)).card :=
      (Classical.choose_spec (hmax x)).2 q hq
    have hbestsub (x : L) : D (best x) ⊆ A x.1 :=
      (Finset.mem_filter.mp (hbestmem x)).2
    let fiber (p : π) : Finset L := Finset.univ.filter fun x => best x = p
    have hfiber (p : π) : ((fiber p).card : ℝ) ≤
        δ * (Fintype.card ι : ℝ) := by
      apply linear_mca_low_family_card_le_of_disjoint
        (B := fiber p) (A := fun x : L => A x.1) (D := D p) (p := δ)
      · intro x hx
        have hbp : best x = p := (Finset.mem_filter.mp hx).2
        have hsub : D p ⊆ A x.1 := hbp ▸ hbestsub x
        exact Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hstrict x.1 p hsub⟩
      · intro x hx y hy hxy
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro i hi
        have hbpX : best x = p := (Finset.mem_filter.mp hx).2
        have hiX := Finset.mem_sdiff.mp (Finset.mem_inter.mp hi).1
        have hiY := Finset.mem_sdiff.mp (Finset.mem_inter.mp hi).2
        have hsubX : D p ⊆ A x.1 := hbpX ▸ hbestsub x
        have hbpY : best y = p := (Finset.mem_filter.mp hy).2
        have hsubY : D p ⊆ A y.1 := hbpY ▸ hbestsub y
        have hDinter : D p ⊂ A x.1 ∩ A y.1 := by
          apply Finset.ssubset_iff_subset_ne.mpr
          refine ⟨fun z hz => Finset.mem_inter.mpr ⟨hsubX hz, hsubY hz⟩, ?_⟩
          intro heq
          have hiD : i ∈ D p := by
            rw [heq]
            exact Finset.mem_inter.mpr ⟨hiX.1, hiY.1⟩
          exact hiX.2 hiD
        have hDsub : D p ⊆ A x.1 ∩ A y.1 :=
          (Finset.ssubset_iff_subset_ne.mp hDinter).1
        have hlarge : (Fintype.card ι : ℝ) * (1 - δ) ≤
            (((A x.1) ∩ (A y.1)).card : ℝ) :=
          (hD p).trans (by exact_mod_cast Finset.card_le_card hDsub)
        have hxyval : x.1 ≠ y.1 := by
          intro h
          apply hxy
          exact Subtype.ext h
        obtain ⟨q, hIq, hqX, -⟩ := hpair x.1 y.1 hxyval hlarge
        have hqCand : q ∈ cand x :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ q, hqX⟩
        have hle := hbestmax x q hqCand
        have hlt : (D p).card < (D q).card :=
          lt_of_lt_of_le (Finset.card_lt_card hDinter) (Finset.card_le_card hIq)
        rw [hbpX] at hle
        omega
      · exact hD p
    have hmaps : ((Finset.univ : Finset L) : Set L).MapsTo best (Finset.univ : Finset π) := by
      intro x hx
      exact Finset.mem_univ _
    have hcardEq : (large_family_low A D).card = ∑ p : π, (fiber p).card := by
      have h := Finset.card_eq_sum_card_fiberwise hmaps
      simpa [L, fiber] using h
    calc
      ((large_family_low A D).card : ℝ) = ∑ p : π, ((fiber p).card : ℝ) := by
        exact_mod_cast hcardEq
      _ ≤ ∑ _p : π, δ * (Fintype.card ι : ℝ) :=
        Finset.sum_le_sum fun p _ => hfiber p
      _ = (Fintype.card π : ℝ) * δ * (Fintype.card ι : ℝ) := by
        simp
        ring

open scoped BigOperators in
private def large_family_card_le_of_domains
    {κ ι π : Type} [Fintype κ] [Fintype ι] [Fintype π] [DecidableEq ι]
    (A : κ → Finset ι) (D : π → Finset ι) (δ η s : ℝ)
    (hn : 0 < (Fintype.card ι : ℝ))
    (_hδ_pos : 0 < δ) (hδ_lt : δ < 1)
    (hη_pos : 0 < η) (_hη_lt : η < 1)
    (hs_nonneg : 0 ≤ s) (hs_sq : s ^ 2 = 1 - δ + η)
    (hA : ∀ x, (Fintype.card ι : ℝ) * s ≤ ((A x).card : ℝ))
    (hD : ∀ p, (Fintype.card ι : ℝ) * (1 - δ) ≤ ((D p).card : ℝ))
    (hstrict : ∀ x p, D p ⊆ A x → D p ≠ A x)
    (hpair : ∀ x y, x ≠ y →
      (Fintype.card ι : ℝ) * (1 - δ) ≤ (((A x) ∩ (A y)).card : ℝ) →
      ∃ p, A x ∩ A y ⊆ D p ∧ D p ⊆ A x ∧ D p ⊆ A y) :
    (Fintype.card κ : ℝ) ≤
      (Fintype.card π : ℝ) * δ * (Fintype.card ι : ℝ) + 1 / η := by
  classical
  have hlow := large_family_low_card_le_of_domains
    A D δ hn hD hstrict hpair
  have hhigh := large_family_high_card_le_of_domains
    A D δ η s hn hδ_lt hη_pos hs_nonneg hs_sq hA hpair
  have hlowNat : (large_family_low A D).card ≤ Fintype.card κ := by
    simpa using Finset.card_le_univ (large_family_low A D)
  have hhighEq : (large_family_high A D).card =
      Fintype.card κ - (large_family_low A D).card := by
    unfold large_family_high
    rw [Finset.card_sdiff]
    simp
  have hsumNat : Fintype.card κ =
      (large_family_low A D).card + (large_family_high A D).card := by
    rw [hhighEq]
    omega
  have hsumR : (Fintype.card κ : ℝ) =
      ((large_family_low A D).card : ℝ) +
        ((large_family_high A D).card : ℝ) := by
    exact_mod_cast hsumNat
  rw [hsumR]
  exact add_le_add hlow hhigh

private def linear_mca_pair_agreement (u c : Fin 2 → ι → F) : Finset ι :=
  Finset.univ.filter fun i => ∀ j : Fin 2, u j i = c j i

private noncomputable def linear_mca_row_list (C : LinearCode ι F) (u : Fin 2 → ι → F)
    (p : ℝ) (j : Fin 2) : Finset (ι → F) :=
  (Set.toFinite (closeCodewordsRel (C : Set (ι → F)) (u j) p)).toFinset

private noncomputable def linear_mca_relevant_pairs (C : LinearCode ι F)
    (u : Fin 2 → ι → F) (p : ℝ) : Finset ((ι → F) × (ι → F)) := by
  classical
  exact ((linear_mca_row_list C u p 0).product (linear_mca_row_list C u p 1)).filter fun d =>
    (Fintype.card ι : ℝ) * (1 - p) ≤
      (linear_mca_pair_agreement u ![d.1, d.2]).card

private def linear_mca_relevant_pairs_card_le (C : LinearCode ι F) (L : ℕ) (p : ℝ)
    (hΛ : Lambda ((C : Set (ι → F))) p ≤ (L : ℕ∞))
    (u : Fin 2 → ι → F) :
    (linear_mca_relevant_pairs C u p).card ≤ L ^ 2 := by
  classical
  have hlist0 := (Code.Lambda_le_iff_forall_ncard_le.mp hΛ) (u 0)
  have hlist1 := (Code.Lambda_le_iff_forall_ncard_le.mp hΛ) (u 1)
  have hrow0 : (linear_mca_row_list C u p 0).card ≤ L := by
    simpa [linear_mca_row_list, Set.ncard_eq_toFinset_card _ hlist0.1] using hlist0.2
  have hrow1 : (linear_mca_row_list C u p 1).card ≤ L := by
    simpa [linear_mca_row_list, Set.ncard_eq_toFinset_card _ hlist1.1] using hlist1.2
  unfold linear_mca_relevant_pairs
  calc
    (((linear_mca_row_list C u p 0).product
      (linear_mca_row_list C u p 1)).filter fun d =>
        (Fintype.card ι : ℝ) * (1 - p) ≤
          (linear_mca_pair_agreement u ![d.1, d.2]).card).card
        ≤ ((linear_mca_row_list C u p 0).product
          (linear_mca_row_list C u p 1)).card := Finset.card_filter_le _ _
    _ = (linear_mca_row_list C u p 0).card *
        (linear_mca_row_list C u p 1).card := Finset.card_product _ _
    _ ≤ L * L := Nat.mul_le_mul hrow0 hrow1
    _ = L ^ 2 := by ring

private def linear_codeword_eq_of_large_agreement (C : LinearCode ι F) (p : ℝ)
    (hp_dist : p < (Code.minDist ((C : Set (ι → F))) : ℝ) / Fintype.card ι)
    (c d : ι → F) (hc : c ∈ C) (hd : d ∈ C) (S : Finset ι)
    (hS : (Fintype.card ι : ℝ) * (1 - p) ≤ S.card)
    (hagree : ∀ i ∈ S, c i = d i) : c = d := by
  have hnR : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast Fintype.card_pos (α := ι)
  have hpn : p * (Fintype.card ι : ℝ) <
      (Code.minDist (C : Set (ι → F)) : ℝ) :=
    (lt_div_iff₀ hnR).mp hp_dist
  apply Code.eq_of_disagreementCols_subset_of_card_lt_minDist hc hd
    ((Finset.univ : Finset ι) \ S)
  · intro i hi
    rw [Finset.mem_sdiff]
    refine ⟨Finset.mem_univ i, ?_⟩
    intro hiS
    exact (Code.mem_disagreementCols.mp hi) (hagree i hiS)
  · have hSn : S.card ≤ Fintype.card ι := by
      simpa using Finset.card_le_univ S
    have hcomp : ((((Finset.univ : Finset ι) \ S).card : ℕ) : ℝ) ≤
        p * (Fintype.card ι : ℝ) := by
      simp only [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
      rw [Nat.cast_sub hSn]
      nlinarith
    exact_mod_cast lt_of_le_of_lt hcomp hpn

open scoped BigOperators in
private def linear_mca_error_le_of_lambda_le_aux
    (C : LinearCode ι F) (L : ℕ) (δ η : ℝ)
    (_hδ_pos : 0 < δ) (_hδ_lt : δ < 1)
    (_hδ_lt_dist :
        δ < (Code.minDist ((C : Set (ι → F))) : ℝ) / Fintype.card ι)
    (_hη_pos : 0 < η) (_hη_lt : η < 1)
    (_hΛ : Lambda ((C : Set (ι → F))) δ ≤ (L : ℕ∞)) :
    mcaError (AffineLineGenerator F) C
        (1 - (1 - δ + η) ^ ((1 : ℝ) / 2)) ≤
      ENNReal.ofReal
        (((L : ℝ) ^ 2 * δ * Fintype.card ι + 1 / η) / Fintype.card F) := by
  classical
  let R : ℝ := ((L : ℝ) ^ 2 * δ * Fintype.card ι + 1 / η)
  have hR_nonneg : 0 ≤ R := by dsimp [R]; positivity
  have hq_pos : (0 : ℝ) < Fintype.card F := by
    exact_mod_cast Fintype.card_pos (α := F)
  unfold mcaError
  refine iSup_le fun U => ?_
  rw [Probability.prob_uniform_eq_card_filter_div_card]
  let r : ℝ := 1 - (1 - δ + η) ^ ((1 : ℝ) / 2)
  let B := Finset.univ.filter fun γ : F =>
    IsMCA (AffineLineGenerator F) C γ U r
  let w (γ : F) : ι → F := fun i => U 0 i + γ * U 1 i
  have hMCA (γ : B) : IsMCA (AffineLineGenerator F) C γ.1 U r :=
    (Finset.mem_filter.mp γ.2).2
  have hex (γ : B) : ∃ T : Finset ι,
      (T.card : ℝ) ≥ (Fintype.card ι : ℝ) * (1 - r) ∧
      LinearCode.projectedWord (w γ.1) T ∈ LinearCode.projectedCodeSubmod C T ∧
      ∃ j : Fin 2, LinearCode.projectedWord (U j) T ∉
        LinearCode.projectedCodeSubmod C T := by
    simpa [IsMCA, AffineLineGenerator, w, Fin.sum_univ_two] using hMCA γ
  let T (γ : B) : Finset ι := Classical.choose (hex γ)
  have hT (γ : B) :
      ((T γ).card : ℝ) ≥ (Fintype.card ι : ℝ) * (1 - r) ∧
      LinearCode.projectedWord (w γ.1) (T γ) ∈
        LinearCode.projectedCodeSubmod C (T γ) ∧
      ∃ j : Fin 2, LinearCode.projectedWord (U j) (T γ) ∉
        LinearCode.projectedCodeSubmod C (T γ) :=
    Classical.choose_spec (hex γ)
  have hcode_ex (γ : B) : ∃ c : ι → F, c ∈ C ∧
      LinearCode.projectedWord (w γ.1) (T γ) =
        LinearCode.projectedWord c (T γ) := by
    exact (LinearCode.mem_projectedCodeSubmod_iff C (T γ) _).mp (hT γ).2.1
  let c (γ : B) : C :=
    ⟨Classical.choose (hcode_ex γ), (Classical.choose_spec (hcode_ex γ)).1⟩
  have hcproj (γ : B) : LinearCode.projectedWord (w γ.1) (T γ) =
      LinearCode.projectedWord (c γ : ι → F) (T γ) :=
    (Classical.choose_spec (hcode_ex γ)).2
  let A (γ : B) : Finset ι :=
    Finset.univ.filter fun i => w γ.1 i = (c γ : ι → F) i
  have hTsubA (γ : B) : T γ ⊆ A γ := by
    intro i hi
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ i, congrFun (hcproj γ) ⟨i, hi⟩⟩
  have hAcard (γ : B) : ((A γ).card : ℝ) ≥
      (Fintype.card ι : ℝ) * (1 - r) := by
    exact le_trans (hT γ).1 (by exact_mod_cast Finset.card_le_card (hTsubA γ))
  have hnR : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast Fintype.card_pos (α := ι)
  have hrel_le {u v : ι → F} {D : Finset ι}
      (hD : (Fintype.card ι : ℝ) * (1 - δ) ≤ (D.card : ℝ))
      (hag : ∀ i ∈ D, u i = v i) : (Code.relHammingDist u v : ℝ) ≤ δ := by
    rw [Code.relHammingDist_coe, div_le_iff₀ hnR]
    have hsub : Code.disagreementCols u v ⊆ (Finset.univ : Finset ι) \ D := by
      intro i hi
      rw [Finset.mem_sdiff]
      refine ⟨Finset.mem_univ i, ?_⟩
      intro hiD
      exact (Code.mem_disagreementCols.mp hi) (hag i hiD)
    have hnat : Δ₀(u, v) ≤ ((Finset.univ : Finset ι) \ D).card := by
      rw [Code.hammingDist_eq_disagreementCols_card]
      exact Finset.card_le_card hsub
    have hDn : D.card ≤ Fintype.card ι := by
      simpa using Finset.card_le_univ D
    have hcomp : ((((Finset.univ : Finset ι) \ D).card : ℕ) : ℝ) ≤
        δ * (Fintype.card ι : ℝ) := by
      simp only [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
      rw [Nat.cast_sub hDn]
      nlinarith
    exact le_trans (by exact_mod_cast hnat) hcomp
  have hcard : (B.card : ℝ) ≤ R := by
    by_cases hr : 0 ≤ r
    · let s : ℝ := Real.sqrt (1 - δ + η)
      have hbase : 0 ≤ 1 - δ + η := by linarith
      have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg _
      have hs_sq : s ^ 2 = 1 - δ + η := by
        simpa [s] using Real.sq_sqrt hbase
      have hrs : 1 - r = s := by
        dsimp [r, s]
        rw [Real.sqrt_eq_rpow]
        ring
      let D (p : C × C) : Finset ι :=
        Finset.univ.filter fun i =>
          U 0 i = (p.1 : ι → F) i ∧ U 1 i = (p.2 : ι → F) i
      let P := Finset.univ.filter fun p : C × C =>
        (Fintype.card ι : ℝ) * (1 - δ) ≤ ((D p).card : ℝ)
      have hPcard : P.card ≤ L ^ 2 := by
        have hlist0 := (Code.Lambda_le_iff_forall_ncard_le.mp _hΛ) (w 0)
        have hlist1 := (Code.Lambda_le_iff_forall_ncard_le.mp _hΛ) (w 1)
        let S0 : Finset (ι → F) := hlist0.1.toFinset
        let S1 : Finset (ι → F) := hlist1.1.toFinset
        have hS0card : S0.card ≤ L := by
          simpa [S0, Set.ncard_eq_toFinset_card _ hlist0.1] using hlist0.2
        have hS1card : S1.card ≤ L := by
          simpa [S1, Set.ncard_eq_toFinset_card _ hlist1.1] using hlist1.2
        have hp0close (p : P) : (p.1.1 : ι → F) ∈
            Code.closeCodewordsRel (C : Set (ι → F)) (w 0) δ := by
          rw [Code.mem_closeCodewordsRel_iff]
          refine ⟨p.1.1.property, hrel_le (Finset.mem_filter.mp p.2).2 ?_⟩
          intro i hi
          have hi' := (Finset.mem_filter.mp hi).2
          simpa [w] using hi'.1
        have hp1close (p : P) : ((p.1.1 + p.1.2 : C) : ι → F) ∈
            Code.closeCodewordsRel (C : Set (ι → F)) (w 1) δ := by
          rw [Code.mem_closeCodewordsRel_iff]
          refine ⟨(p.1.1 + p.1.2 : C).property,
            hrel_le (Finset.mem_filter.mp p.2).2 ?_⟩
          intro i hi
          have hi' := (Finset.mem_filter.mp hi).2
          simp only [w, one_mul]
          rw [hi'.1, hi'.2]
          rfl
        have hp0S (p : P) : (p.1.1 : ι → F) ∈ S0 := by
          simpa [S0] using hp0close p
        have hp1S (p : P) : ((p.1.1 + p.1.2 : C) : ι → F) ∈ S1 := by
          simpa [S1] using hp1close p
        let φ (p : P) : S0 × S1 :=
          (⟨(p.1.1 : ι → F), hp0S p⟩,
            ⟨((p.1.1 + p.1.2 : C) : ι → F), hp1S p⟩)
        have hφinj : Function.Injective φ := by
          intro p q hpq
          have h0 : (p.1.1 : ι → F) = (q.1.1 : ι → F) :=
            congrArg (fun z : S0 × S1 => (z.1 : ι → F)) hpq
          have hsum : (((p.1.1 + p.1.2 : C) : ι → F)) =
              (((q.1.1 + q.1.2 : C) : ι → F)) :=
            congrArg (fun z : S0 × S1 => (z.2 : ι → F)) hpq
          have h0C : p.1.1 = q.1.1 := Subtype.ext h0
          have hsumC : p.1.1 + p.1.2 = q.1.1 + q.1.2 := Subtype.ext hsum
          apply Subtype.ext
          apply Prod.ext
          · exact h0C
          · rw [h0C] at hsumC
            exact add_left_cancel hsumC
        have hinjcard : Fintype.card P ≤ Fintype.card (S0 × S1) :=
          Fintype.card_le_of_injective φ hφinj
        have hprod : P.card ≤ S0.card * S1.card := by simpa using hinjcard
        calc
          P.card ≤ S0.card * S1.card := hprod
          _ ≤ L * L := Nat.mul_le_mul hS0card hS1card
          _ = L ^ 2 := by ring
      have hpair (x y : B) (hxy : x.1 ≠ y.1) :
          ∃ p : C × C, A x ∩ A y ⊆ D p ∧ D p ⊆ A x ∧ D p ⊆ A y := by
        let q1 : C := (y.1 - x.1)⁻¹ • (c y - c x)
        let q0 : C := c x - x.1 • q1
        have hden : y.1 - x.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
        have hqx : q0 + x.1 • q1 = c x := by simp [q0]
        have hqy : q0 + y.1 • q1 = c y := by
          apply Subtype.ext
          ext i
          simp only [q0, q1, Submodule.coe_add, Submodule.coe_sub,
            Submodule.coe_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          field_simp [hden]
          ring
        refine ⟨(q0, q1), ?_, ?_, ?_⟩
        · intro i hi
          have hix := (Finset.mem_filter.mp (Finset.mem_inter.mp hi).1).2
          have hiy := (Finset.mem_filter.mp (Finset.mem_inter.mp hi).2).2
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ i, ?_⟩
          have hq1i : U 1 i = (q1 : ι → F) i := by
            dsimp [q1]
            field_simp [hden]
            linear_combination hiy - hix
          have hq0i : U 0 i = (q0 : ι → F) i := by
            dsimp [q0]
            change U 0 i = (c x : ι → F) i - x.1 * (q1 : ι → F) i
            rw [← hq1i]
            linear_combination hix
          exact ⟨hq0i, hq1i⟩
        · intro i hi
          have hi' := (Finset.mem_filter.mp hi).2
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ i, ?_⟩
          simpa [w, hi'.1, hi'.2] using congrFun (congrArg Subtype.val hqx) i
        · intro i hi
          have hi' := (Finset.mem_filter.mp hi).2
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ i, ?_⟩
          simpa [w, hi'.1, hi'.2] using congrFun (congrArg Subtype.val hqy) i
      have hDlarge (p : P) : (Fintype.card ι : ℝ) * (1 - δ) ≤
          ((D p.1).card : ℝ) := (Finset.mem_filter.mp p.2).2
      have hstrict (x : B) (p : P) (hsub : D p.1 ⊆ A x) : D p.1 ≠ A x := by
        intro heq
        obtain ⟨j, hj⟩ := (hT x).2.2
        apply hj
        rw [LinearCode.mem_projectedCodeSubmod_iff]
        fin_cases j
        · refine ⟨(p.1.1 : ι → F), p.1.1.property, ?_⟩
          funext z
          have hzA : z.1 ∈ A x := hTsubA x z.2
          have hzD : z.1 ∈ D p.1 := by simpa [heq] using hzA
          change U 0 z.1 = (p.1.1 : ι → F) z.1
          exact (Finset.mem_filter.mp hzD).2.1
        · refine ⟨(p.1.2 : ι → F), p.1.2.property, ?_⟩
          funext z
          have hzA : z.1 ∈ A x := hTsubA x z.2
          have hzD : z.1 ∈ D p.1 := by simpa [heq] using hzA
          change U 1 z.1 = (p.1.2 : ι → F) z.1
          exact (Finset.mem_filter.mp hzD).2.2
      have hpairP (x y : B) (hxy : x ≠ y)
          (hlarge : (Fintype.card ι : ℝ) * (1 - δ) ≤
            (((A x) ∩ (A y)).card : ℝ)) :
          ∃ p : P, A x ∩ A y ⊆ D p.1 ∧ D p.1 ⊆ A x ∧ D p.1 ⊆ A y := by
        have hval : x.1 ≠ y.1 := by
          intro h
          exact hxy (Subtype.ext h)
        obtain ⟨p, hpI, hpx, hpy⟩ := hpair x y hval
        have hpD : (Fintype.card ι : ℝ) * (1 - δ) ≤ ((D p).card : ℝ) :=
          le_trans hlarge (by exact_mod_cast Finset.card_le_card hpI)
        let pp : P := ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hpD⟩⟩
        exact ⟨pp, hpI, hpx, hpy⟩
      have hfamily := large_family_card_le_of_domains
        (A := A) (D := fun p : P => D p.1) δ η s hnR
        _hδ_pos _hδ_lt _hη_pos _hη_lt hs_nonneg hs_sq
        (fun x => by simpa [hrs] using hAcard x)
        hDlarge hstrict hpairP
      calc
        (B.card : ℝ) ≤ (P.card : ℝ) * δ * (Fintype.card ι : ℝ) + 1 / η := by
          simpa using hfamily
        _ ≤ ((L ^ 2 : ℕ) : ℝ) * δ * (Fintype.card ι : ℝ) + 1 / η := by
          gcongr
        _ = R := by simp [R, Nat.cast_pow]
    · have hBempty : B = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro γ hγ
        let γB : B := ⟨γ, hγ⟩
        have hAle : ((A γB).card : ℝ) ≤ Fintype.card ι := by
          exact_mod_cast Finset.card_le_univ (A γB)
        have hlarge := hAcard γB
        nlinarith
      rw [hBempty]
      simpa using hR_nonneg
  rw [ENNReal.ofReal_div_of_pos hq_pos]
  have hden : ENNReal.ofReal (Fintype.card F : ℝ) =
      (Fintype.card F : ENNReal) := by
    rw [ENNReal.ofReal_natCast]
  rw [hden]
  apply ENNReal.div_le_div_right
  have hcard' : (B.card : ENNReal) ≤ ENNReal.ofReal R := by
    exact_mod_cast (ENNReal.ofReal_le_ofReal hcard)
  simpa [B, R, r] using hcard'
omit [DecidableEq ι] in
/-- Converts a list-size bound at `δ` below the relative minimum distance into an
affine-line MCA bound at radius `1 - √(1 - δ + η)`. -/
theorem linear_mcaError_le_of_Lambda_le (C : LinearCode ι F) (L : ℕ) (δ η : ℝ)
    (_hδ_pos : 0 < δ) (_hδ_lt : δ < 1)
    (_hδ_lt_dist :
        δ < (Code.minDist ((C : Set (ι → F))) : ℝ) / Fintype.card ι)
    (_hη_pos : 0 < η) (_hη_lt : η < 1)
    (_hΛ : Lambda ((C : Set (ι → F))) δ ≤ (L : ℕ∞)) :
    mcaError (AffineLineGenerator F) C
        (1 - (1 - δ + η) ^ ((1 : ℝ) / 2)) ≤
      ENNReal.ofReal
        (((L : ℝ) ^ 2 * δ * Fintype.card ι + 1 / η) / Fintype.card F) := by
  classical
  exact linear_mca_error_le_of_lambda_le_aux C L δ η _hδ_pos _hδ_lt
    _hδ_lt_dist _hη_pos _hη_lt _hΛ

end ListImpliesMCA

end CodingTheory
