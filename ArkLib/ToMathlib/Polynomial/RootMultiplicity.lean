/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
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

All three hold over any integral domain. The domain hypothesis is needed: over `ZMod 4` the
nonzero polynomial `2 * X` of degree one is divisible by both `X` and `X - 2`.

Generic facts intended as candidates for upstreaming to Mathlib.

## References

The two vanishing theorems are ported from `ArkLib/ToMathlib/Polynomial/RootMultiplicity.lean` at
ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d, where they and
`sum_rootMultiplicity_le_natDegree` are stated over a field; here `[Field F]` becomes
`[CommRing R] [IsDomain R]`.
-/

@[expose] public section

namespace Polynomial

/-- The sum of the root multiplicities of a polynomial over a finite set of points is at most
its natural degree. For `W = 0` both sides are `0`, since Mathlib sets the root multiplicity of
every point in the zero polynomial to `0`. -/
lemma sum_rootMultiplicity_le_natDegree {R : Type*} [CommRing R] [IsDomain R]
    {W : Polynomial R} (S : Finset R) :
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

/-- A polynomial over an integral domain is zero when it is divisible by
`(X - C (points i)) ^ multiplicity` for every `i` in `indices`, the points are distinct on
`indices`, `requiredPoints ≤ #indices`, and its degree is below `multiplicity * requiredPoints`.

The distinct roots contribute total root multiplicity at least `multiplicity * requiredPoints`,
while a nonzero polynomial has total root multiplicity at most its degree. The points only need
to be distinct on `indices`, and `indices` may be larger than `requiredPoints`. The statement allows
`multiplicity = 0`, `requiredPoints = 0` and empty `indices`: then the degree hypothesis says
`W.degree < 0`, which already forces `W = 0`. -/
theorem eq_zero_of_degree_lt_mul_of_pow_X_sub_C_dvd_at_injOn
    {ι R : Type*} [CommRing R] [IsDomain R] {W : R[X]} (points : ι → R) (indices : Finset ι)
    (multiplicity requiredPoints : ℕ) (hpoints : Set.InjOn points (indices : Set ι))
    (hcard : requiredPoints ≤ indices.card)
    (hdiv : ∀ i ∈ indices, (X - C (points i)) ^ multiplicity ∣ W)
    (hdegree : W.degree < (multiplicity * requiredPoints : ℕ)) :
    W = 0 := by
  classical
  by_contra hW
  have htotal : multiplicity * requiredPoints ≤ W.natDegree :=
    calc multiplicity * requiredPoints ≤ multiplicity * indices.card :=
          Nat.mul_le_mul_left multiplicity hcard
      _ = ∑ _a ∈ indices.image points, multiplicity := by
          rw [Finset.sum_const, Finset.card_image_of_injOn hpoints, smul_eq_mul, mul_comm]
      _ ≤ ∑ a ∈ indices.image points, W.rootMultiplicity a := by
          refine Finset.sum_le_sum fun a ha ↦ ?_
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
          exact (le_rootMultiplicity_iff hW).2 (hdiv i hi)
      _ ≤ W.natDegree := sum_rootMultiplicity_le_natDegree _
  rw [degree_eq_natDegree hW, Nat.cast_lt] at hdegree
  omega

/-- Natural-degree form of `eq_zero_of_degree_lt_mul_of_pow_X_sub_C_dvd_at_injOn`. Unlike the
`degree` form, its degree hypothesis cannot hold when `multiplicity = 0` or `requiredPoints = 0`,
since `natDegree 0 = 0`. -/
theorem eq_zero_of_natDegree_lt_mul_of_pow_X_sub_C_dvd_at_injOn
    {ι R : Type*} [CommRing R] [IsDomain R] {W : R[X]} (points : ι → R) (indices : Finset ι)
    (multiplicity requiredPoints : ℕ) (hpoints : Set.InjOn points (indices : Set ι))
    (hcard : requiredPoints ≤ indices.card)
    (hdiv : ∀ i ∈ indices, (X - C (points i)) ^ multiplicity ∣ W)
    (hdegree : W.natDegree < multiplicity * requiredPoints) :
    W = 0 :=
  eq_zero_of_degree_lt_mul_of_pow_X_sub_C_dvd_at_injOn points indices multiplicity
    requiredPoints hpoints hcard hdiv (degree_le_natDegree.trans_lt (by exact_mod_cast hdegree))

end Polynomial
