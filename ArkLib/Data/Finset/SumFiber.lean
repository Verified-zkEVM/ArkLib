/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
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

end Finset
