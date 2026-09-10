/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks, Quang Dao
-/
module

public import Mathlib.Algebra.Polynomial.Roots

/-!
# Additional polynomial root-multiplicity lemmas

## Main statements

* `Polynomial.sum_rootMultiplicity_le_natDegree` — root multiplicities summed over a finite
  set are bounded by the degree.
* `Polynomial.eq_zero_of_degree_lt_mul_of_pow_X_sub_C_dvd_at_injOn` — a polynomial with
  sufficiently many distinct roots of uniform multiplicity and strictly smaller degree is zero.
* `Polynomial.eq_zero_of_natDegree_lt_mul_of_pow_X_sub_C_dvd_at_injOn` — the corresponding
  natural-degree formulation.

Generic facts intended as candidates for upstreaming to Mathlib.
-/

@[expose] public section

namespace Polynomial

/-- The sum of the root multiplicities of a polynomial over a finite set of points is at most
its natural degree. -/
lemma sum_rootMultiplicity_le_natDegree {F : Type*} [Field F]
    {W : Polynomial F} (S : Finset F) :
    ∑ a ∈ S, W.rootMultiplicity a ≤ W.natDegree := by
  classical
  have hle : (∑ a ∈ S, Multiset.replicate (W.rootMultiplicity a) a) ≤ W.roots := by
    rw [Multiset.le_iff_count]
    intro b
    rw [Multiset.count_sum', Polynomial.count_roots]
    calc ∑ a ∈ S, Multiset.count b (Multiset.replicate (W.rootMultiplicity a) a)
        = ∑ a ∈ S, (if a = b then W.rootMultiplicity a else 0) :=
          Finset.sum_congr rfl fun a _ => by rw [Multiset.count_replicate]
      _ ≤ W.rootMultiplicity b := by
          rw [Finset.sum_ite_eq' S b]
          split <;> simp
  have hcard := Multiset.card_le_card hle
  rw [Multiset.card_sum] at hcard
  simp only [Multiset.card_replicate] at hcard
  exact hcard.trans (Polynomial.card_roots' W)

/-- A polynomial is zero when it has at least `requiredPoints` distinct prescribed roots, each
with multiplicity at least `multiplicity`, and its degree is strictly below the resulting total
multiplicity. The evaluation map only needs to be injective on the supplied indices.

This degree formulation deliberately permits `multiplicity = 0`, `requiredPoints = 0`, and an
empty index set. In those cases the strict degree hypothesis forces `W = 0`, because the zero
polynomial is the only polynomial whose `WithBot`-valued degree is below zero. -/
theorem eq_zero_of_degree_lt_mul_of_pow_X_sub_C_dvd_at_injOn
    {ι F : Type*} [Field F] {W : F[X]} (points : ι → F) (indices : Finset ι)
    (multiplicity requiredPoints : ℕ) (hpoints : Set.InjOn points (indices : Set ι))
    (hcard : requiredPoints ≤ indices.card)
    (hdiv : ∀ i ∈ indices, (X - C (points i)) ^ multiplicity ∣ W)
    (hdegree : W.degree < (multiplicity * requiredPoints : ℕ)) :
    W = 0 := by
  classical
  by_contra hW
  have hroot : ∀ a ∈ indices.image points, multiplicity ≤ W.rootMultiplicity a := by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    exact (le_rootMultiplicity_iff hW).2 (hdiv i hi)
  have hsum :
      multiplicity * (indices.image points).card ≤
        ∑ a ∈ indices.image points, W.rootMultiplicity a := by
    calc
      multiplicity * (indices.image points).card =
          ∑ _a ∈ indices.image points, multiplicity := by simp [Nat.mul_comm]
      _ ≤ ∑ a ∈ indices.image points, W.rootMultiplicity a :=
        Finset.sum_le_sum fun a ha ↦ hroot a ha
  have htotal : multiplicity * requiredPoints ≤ W.natDegree := by
    calc
      multiplicity * requiredPoints ≤ multiplicity * indices.card :=
        Nat.mul_le_mul_left multiplicity hcard
      _ = multiplicity * (indices.image points).card := by
        rw [Finset.card_image_of_injOn hpoints]
      _ ≤ ∑ a ∈ indices.image points, W.rootMultiplicity a := hsum
      _ ≤ W.natDegree := sum_rootMultiplicity_le_natDegree (indices.image points)
  have hdegree' : W.natDegree < multiplicity * requiredPoints := by
    rw [degree_eq_natDegree hW] at hdegree
    exact_mod_cast hdegree
  exact (not_lt_of_ge htotal) hdegree'

/-- Natural-degree version of
`Polynomial.eq_zero_of_degree_lt_mul_of_pow_X_sub_C_dvd_at_injOn`.

Unlike the `degree` formulation, this theorem's strict hypothesis is impossible when either
`multiplicity = 0` or `requiredPoints = 0`, even for `W = 0`, because `natDegree 0 = 0`. -/
theorem eq_zero_of_natDegree_lt_mul_of_pow_X_sub_C_dvd_at_injOn
    {ι F : Type*} [Field F] {W : F[X]} (points : ι → F) (indices : Finset ι)
    (multiplicity requiredPoints : ℕ) (hpoints : Set.InjOn points (indices : Set ι))
    (hcard : requiredPoints ≤ indices.card)
    (hdiv : ∀ i ∈ indices, (X - C (points i)) ^ multiplicity ∣ W)
    (hdegree : W.natDegree < multiplicity * requiredPoints) :
    W = 0 := by
  apply eq_zero_of_degree_lt_mul_of_pow_X_sub_C_dvd_at_injOn
      points indices multiplicity requiredPoints hpoints hcard hdiv
  exact degree_le_natDegree.trans_lt (by exact_mod_cast hdegree)

end Polynomial
