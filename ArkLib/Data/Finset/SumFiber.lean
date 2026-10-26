/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Weighted sums over finite fibers

`Finset.sumFiber` sums the weights of occurrences carrying one key. Occurrences are enumerated by
a finite set; the key type need not be finite. The computation needs only executable equality on
keys and an additive commutative monoid of weights.

The regrouping theorem collects all fibers over any finite set containing the occurring keys.
The isolation theorem preserves a selected fiber under an encoding that separates its key from
every other occurring key, without requiring global injectivity of that encoding.
-/

@[expose] public section

namespace Finset

variable {ι κ ν R S : Type*} [DecidableEq κ] [AddCommMonoid R]

/-- Sum the weights of occurrences whose key equals the selected key. -/
def sumFiber (s : Finset ι) (key : ι → κ) (weight : ι → R) (k : κ) : R :=
  ∑ i ∈ s.filter (fun i ↦ key i = k), weight i

@[simp]
theorem sumFiber_empty (key : ι → κ) (weight : ι → R) (k : κ) :
    (∅ : Finset ι).sumFiber key weight k = 0 := by
  simp [sumFiber]

/-- The fiber sum is the sum of the weights selected by its key predicate. -/
theorem sumFiber_eq_sum_ite (s : Finset ι) (key : ι → κ) (weight : ι → R) (k : κ) :
    s.sumFiber key weight k = ∑ i ∈ s, if key i = k then weight i else 0 := by
  exact sum_filter _ _

/-- A fiber containing no occurrence has weight zero. -/
theorem sumFiber_eq_zero_of_forall_ne (s : Finset ι) (key : ι → κ) (weight : ι → R)
    (k : κ) (h : ∀ i ∈ s, key i ≠ k) : s.sumFiber key weight k = 0 := by
  unfold sumFiber
  apply sum_eq_zero
  intro i hi
  exact False.elim (h i (mem_filter.mp hi).1 (mem_filter.mp hi).2)

/-- Adding occurrence weights adds their fiber sums. -/
theorem sumFiber_add (s : Finset ι) (key : ι → κ) (weight weight' : ι → R) (k : κ) :
    s.sumFiber key (fun i ↦ weight i + weight' i) k =
      s.sumFiber key weight k + s.sumFiber key weight' k := by
  simp [sumFiber, sum_add_distrib]

variable [AddCommMonoid S]

/-- An additive map transports the total weight of each fiber. -/
theorem sumFiber_map (f : R →+ S) (s : Finset ι) (key : ι → κ) (weight : ι → R) (k : κ) :
    s.sumFiber key (fun i ↦ f (weight i)) k = f (s.sumFiber key weight k) := by
  simp [sumFiber]

/-- Summing over a finite set containing every occurring key recovers the original sum. -/
theorem sum_sumFiber (s : Finset ι) (keys : Finset κ) (key : ι → κ) (weight : ι → R)
    (h : ∀ i ∈ s, key i ∈ keys) :
    ∑ k ∈ keys, s.sumFiber key weight k = ∑ i ∈ s, weight i := by
  exact sum_fiberwise_of_maps_to h weight

variable [DecidableEq ν]

/-- Encoding preserves one fiber when no other occurring key encodes to its value. -/
theorem sumFiber_comp_eq_of_isolated (s : Finset ι) (key : ι → κ) (weight : ι → R)
    (encode : κ → ν) (k : κ)
    (h : ∀ i ∈ s, encode (key i) = encode k → key i = k) :
    s.sumFiber (encode ∘ key) weight (encode k) = s.sumFiber key weight k := by
  unfold sumFiber
  apply sum_congr
  · ext i
    simp only [mem_filter, Function.comp_apply]
    exact and_congr_right fun hi ↦ ⟨h i hi, congrArg encode⟩
  · intro i _
    rfl

/-- An encoded fiber is the sum of the original fibers mapping to its encoded key.
Only occurring keys are enumerated; the key carriers may both be infinite. -/
theorem sumFiber_comp (s : Finset ι) (key : ι → κ) (weight : ι → R)
    (encode : κ → ν) (encoded : ν) :
    s.sumFiber (encode ∘ key) weight encoded =
      ∑ k ∈ (s.image key).filter (fun k ↦ encode k = encoded), s.sumFiber key weight k := by
  let selected := s.filter (fun i ↦ encode (key i) = encoded)
  have hmap : ∀ i ∈ selected, key i ∈ (s.image key).filter (fun k ↦ encode k = encoded) := by
    intro i hi
    exact mem_filter.mpr ⟨mem_image.mpr ⟨i, (mem_filter.mp hi).1, rfl⟩,
      (mem_filter.mp hi).2⟩
  symm
  calc
    _ = ∑ k ∈ (s.image key).filter (fun k ↦ encode k = encoded),
        selected.sumFiber key weight k := by
      apply sum_congr rfl
      intro k hk
      unfold sumFiber
      congr 1
      ext i
      simp only [mem_filter, selected]
      constructor
      · rintro ⟨hi, hkey⟩
        exact ⟨⟨hi, hkey ▸ (mem_filter.mp hk).2⟩, hkey⟩
      · exact fun h ↦ ⟨h.1.1, h.2⟩
    _ = ∑ i ∈ selected, weight i := sum_sumFiber selected _ key weight hmap
    _ = _ := rfl

/-- Zero weight in every original fiber remains zero after any encoding, even with collisions. -/
theorem sumFiber_comp_eq_zero (s : Finset ι) (key : ι → κ) (weight : ι → R)
    (encode : κ → ν) (hzero : ∀ k, s.sumFiber key weight k = 0) (encoded : ν) :
    s.sumFiber (encode ∘ key) weight encoded = 0 := by
  rw [sumFiber_comp]
  exact sum_eq_zero fun k _ ↦ hzero k

end Finset
