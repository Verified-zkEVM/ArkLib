/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: František Silváši, Ilia Vlasov
-/

import ArkLib.Data.Domain.CosetFftDomain.Subdomain

/-! Claim 4.23 from [ACFY24] and lemma 4.9 from [ACFY24stir] share
  a similar combinatorial proof technique which we call "pullback argument".

  This file introduces the definition of a pullback set for two subdomains and
  various lemmas establishing relations between cardinalities
  of the pullback set and its projections on either of the components.

  ## Main results

  The main results establish structural and cardinality properties of this
  construction:

  * the first projection of the pullback is in bijection with the pullback
    itself (`card_pullback_eq_card_pullback₁`);
  * the second projection is exactly the given subset whenever the subset lies
    in the smaller subdomain (`card_pullback₂_eq`);
  * the first projection decomposes as a disjoint union of blocks indexed by
    the second projection (`pullback₁_eq_biUnion_pullback₂`);
  * consequently, the pullback has cardinality
    `2 ^ (r - l) * #(pullback₂ ω l r s)`
    (`card_pullback_eq_mul_card_pullback₂`).

  ## References

  * [Arnon, G., Chiesa, A., Fenzi, G., Yogev, E.,
    *STIR: Reed–Solomon Proximity Testing with Fewer Queries*][ACFY24stir]
  * [Arnon, G., Chiesa, A., Fenzi, G., and Yogev, E., *WHIR: Reed–Solomon Proximity Testing
        with Super-Fast Verification*][ACFY24]
-/

namespace Domain

variable {F : Type} [Field F] [DecidableEq F]

namespace CosetFftDomainClass

variable {n : ℕ}
variable {D : Type} [FunLike D (Fin (2 ^ n)) F] [CosetFftDomainClass D (Fin (2 ^ n)) F]
variable {ω : D}

namespace Pullback

open Finset

variable {l r : ℕ} {s : Finset F}

/-- The pullback set is the pullback of the following maps:
   pullback ω l r s ·······································> (subdomain ω r)⁻¹ s
         ·__|                                                         |
         ·                                                            |
         ·                                                            |
         ·
         ·                                                       subdomain ω r
         ·
         ·                                                            |
         ·                                                            |
         ·                                                            |
         V                                                            v
  Fin (2 ^ (n - l)) --- subdomain ω l --→ F --- (-) ^ 2 ^ (r - l) --→ F
-/
def pullback (ω : D) (l r : ℕ) (s : Finset F) : Finset (Fin (2 ^ (n - l)) × Fin (2 ^ (n - r))) :=
  { i | subdomain ω l i.1 ^ 2 ^ (r - l) = subdomain ω r i.2 ∧ subdomain ω r i.2 ∈ s }

/-- The pullback set is empty when `s` is empty. -/
@[simp]
lemma pullback_empty : pullback ω l r ∅ = ∅ := by simp [pullback]

@[simp]
lemma mem_pullback {i : Fin (2 ^ (n - l)) × Fin (2 ^ (n - r))} :
  i ∈ pullback ω l r s ↔
    subdomain ω l i.1 ^ 2 ^ (r - l) = subdomain ω r i.2 ∧
          subdomain ω r i.2 ∈ s := by simp [pullback]

/-- `Prod.fst` is injective on the pullback set. -/
@[simp]
lemma proj₁_injOn :
  Set.InjOn Prod.fst
    (pullback ω l r s : Set (Fin (2 ^ (n - l)) × Fin (2 ^ (n - r)))) := fun x hx y hy hxy ↦ by
  have := injective (subdomain ω r) (a₁ := x.2) (a₂ := y.2)
  aesop

/-- The projection of the pullback set onto the first component. -/
def pullback₁ (ω : D) (l r : ℕ) (s : Finset F) : Finset (Fin (2 ^ (n - l))) :=
  image Prod.fst (pullback ω l r s)

lemma mem_s_of_mem_pullback₁ {i : Fin (2 ^ (n - l))} (h : i ∈ pullback₁ ω l r s) :
  subdomain ω l i ^ 2 ^ (r - l) ∈ s := by aesop (add simp pullback₁)

lemma mem_pullback₁ {i : Fin (2 ^ (n - l))} (hl : l ≤ r) (hr : r ≤ n) :
  i ∈ pullback₁ ω l r s ↔ subdomain ω l i ^ 2 ^ (r - l) ∈ s := by
  simp only [pullback₁, mem_image, mem_pullback, Prod.exists, exists_and_right, exists_eq_right]
  constructor
  · aesop
  · intro h
    have : (subdomain ω l) i ^ 2 ^ (r - l) ∈ subdomain ω (l + (r - l)) :=
      pow_mem_of_mem (by omega) (by simp)
    rw [show l + (r - l) = r by omega] at this
    have ⟨x, hx⟩ := this
    exact ⟨x, by aesop⟩

@[simp]
lemma proj₁_mapsTo :
  Set.MapsTo Prod.fst
    (pullback ω l r s : Set ((Fin (2 ^ (n - l))) × Fin (2 ^ (n - r))))
    (pullback₁ ω l r s : Set (Fin (2 ^ (n - l)))) := by
  aesop (add simp pullback₁) (add safe Set.mapsTo_image)

@[simp]
lemma proj₁_surjOn :
  Set.SurjOn Prod.fst
    (pullback ω l r s : Set (Fin (2 ^ (n - l)) × Fin (2 ^ (n - r))))
    (pullback₁ ω l r s : Set (Fin (2 ^ (n - l)))) := by
  aesop (add simp pullback₁) (add safe Set.surjOn_image)

/-- The cardinality of the pullback set is equal to
  the cardinality of its first projection. -/
lemma card_pullback_eq_card_pullback₁ :
  #(pullback ω l r s) = #(pullback₁ ω l r s) := by
  apply Finset.card_nbij Prod.fst <;> simp

/-- The projection of the pullback set onto the second component. -/
def pullback₂ (ω : D) (l r : ℕ) (s : Finset F) : Finset (Fin (2 ^ (n - r))) :=
  image Prod.snd (pullback ω l r s)

lemma mem_pullback₂ {i : Fin (2 ^ (n - r))} (hl : l ≤ r) (hr : r ≤ n) :
  i ∈ pullback₂ ω l r s ↔ subdomain ω r i ∈ s := by
  simp only [pullback₂, mem_image, mem_pullback, Prod.exists, exists_eq_right, exists_and_right,
    and_iff_right_iff_imp]
  intro h
  have : subdomain ω r i ∈ subdomain ω (l + (r - l)) := by
    rw [show l + (r - l) = r by omega]
    simp
  obtain ⟨y, hy⟩ := root_exists (by omega) this
  aesop (add simp mem_def)

/-- The connection between components of the pullback set. -/
lemma mem_pullback₁_iff_mem_pullback₂ {i : Fin (2 ^ n)} (hl : l ≤ r) (hr : r ≤ n) :
  ω i ^ 2 ^ l ∈ subdomain ω l '' pullback₁ ω l r s ↔
    ω i ^ 2 ^ r ∈ subdomain ω r '' pullback₂ ω l r s := by
  simp only [Set.mem_image, SetLike.mem_coe]
  constructor <;> intro ⟨x, hx₁, hx₂⟩
  · simp only [mem_pullback₁ hl hr] at hx₁
    rw [hx₂, ←pow_mul, ←pow_add, show l + (r - l) = r by omega] at hx₁
    obtain ⟨j, hj⟩ : ω i ^ 2 ^ r ∈ subdomain ω r :=
      pow_mem_subdomain_of_mem_subdomain_0 (by omega) (by rw [mem_subdomain_0_iff_mem]; simp)
    aesop (add safe (by rw [mem_pullback₂]))
  · simp [mem_pullback₂ hl hr] at hx₁
    obtain ⟨j, hj⟩ : ω i ^ 2 ^ l ∈ subdomain ω l :=
      pow_mem_subdomain_of_mem_subdomain_0 (by omega) (by rw [mem_subdomain_0_iff_mem]; simp)
    exists j
    rw [mem_pullback₁ hl hr]
    simp only [hj, and_true]
    rw [←pow_mul, ←pow_add, show l + (r - l) = r by omega]
    simp_all

/-- The connection between components of the pullback set when `l = 0`. -/
lemma mem_pullback₁_iff_mem_pullback₂_l_0 {i : Fin (2 ^ n)} (hr : r ≤ n) :
  ω i ∈ ω '' pullback₁ ω 0 r s ↔ ω i ^ 2 ^ r ∈ subdomain ω r '' pullback₂ ω 0 r s := by
  rw [←mem_pullback₁_iff_mem_pullback₂ (by simp) hr]
  constructor
  · rintro ⟨x, hx, hxi⟩
    exact ⟨x, hx, by simpa only [subdomain_0_apply, pow_zero, pow_one] using hxi⟩
  · rintro ⟨x, hx, hxi⟩
    exact ⟨x, hx, by simpa only [subdomain_0_apply, pow_zero, pow_one] using hxi⟩

/-- The connection between components of the pullback set when `l = 1`. -/
lemma mem_pullback₁_iff_mem_pullback₂_l_1 {i : Fin (2 ^ n)} (h1r : 1 ≤ r) (hr : r ≤ n) :
  ω i ^ 2 ∈ subdomain ω 1 '' pullback₁ ω 1 r s ↔
    ω i ^ 2 ^ r ∈ subdomain ω r '' pullback₂ ω 1 r s := by
  simp [←mem_pullback₁_iff_mem_pullback₂ h1r hr]

/-- If `s` is a subset of the subdomain `subdomain ω r` then
  the cardinality of `pullback₂ ω l r s` is exactly the cardinality
  of `s`. -/
lemma card_pullback₂_eq (hl : l ≤ r) (hr : r ≤ n) (hs : s ⊆ (subdomain ω r).toFinset) :
  #(pullback₂ ω l r s) = #s := by
  apply Finset.card_bij (fun i _ ↦ subdomain ω r i)
  · aesop (add simp mem_pullback₂)
  · intro x _ y _ hxy
    exact CosetFftDomainClass.injective _ hxy
  · intro b hb
    obtain ⟨a, ha⟩ : b ∈ subdomain ω r := by
      specialize hs hb
      aesop
    exists a
    aesop (add simp mem_pullback₂)

/-- `pullback₁ ω l r s` is a union of blocks indexed by
  `pullback₂ ω l r s`. -/
lemma pullback₁_eq_biUnion_pullback₂ (hl : l ≤ r) (hr : r ≤ n) :
  pullback₁ ω l r s =
    Finset.biUnion (pullback₂ ω l r s)
      (blockIdx (subdomain ω l) (r - l) ∘ (subdomain ω r)) := by
  ext i
  simp only [mem_pullback₁ hl hr, mem_biUnion, mem_pullback₂ hl hr, Function.comp_apply,
    mem_blockIdx_iff_mem_block, mem_block, mem_self, true_and]
  constructor
  · intro h
    obtain ⟨a, ha⟩ : (subdomain ω l) i ^ 2 ^ (r - l) ∈ subdomain ω r := by
      rw [mem_subdomain_of_eq_vals (j := l + (r - l)) (by omega)]
      exact pow_mem_of_mem (by omega) (by simp)
    exact ⟨a, by aesop⟩
  · aesop

/-- The expression of the cardinality of `pullback ω l r s`
  in terms of `pullback₂ ω l r s`. -/
lemma card_pullback_eq_mul_card_pullback₂ (hl : l ≤ r) (hr : r ≤ n) :
  #(pullback ω l r s) = 2 ^ (r - l) * #(pullback₂ ω l r s) := by
  rw [card_pullback_eq_card_pullback₁,
      pullback₁_eq_biUnion_pullback₂ hl hr,
      Finset.card_biUnion (by aesop (add safe (by rw [←Set.InjOn.pairwiseDisjoint_image])))]
  calc
    _ = ∑ u ∈ pullback₂ ω l r s, 2 ^ (r - l) :=
      Finset.sum_equiv (Equiv.refl _) (by simp) (fun i hi ↦ by
        simp only [Function.comp_apply, card_blockIdx]
        rw [card_block_of_mem_subdomain (by omega)]
        rw [show l + (r - l) = r by omega]
        simp)
    _ = _ := by aesop (add safe (by ac_nf))

end Pullback

end CosetFftDomainClass

end Domain
