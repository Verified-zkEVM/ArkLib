/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.Coordinates
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.Basic

/-!
# The local rank on the weighted support

Members of `weightedSupportSpace F D d W L` have higher-jet weight at most `W` and, for `0 < D`,
total jet degree below `L / D`, hence below the natural cutoff `⌈L / D⌉₊`. The local constraint
map of order `m` restricted to this space therefore has the support bounds of
`localConstraintAt_support_of_weight_bounds`, and its rank over a field is at most
`localResidualCoordinateBudget d m W ⌈L / D⌉₊` by
`finrank_range_localConstraintAt_domRestrict_le`. This is an upper bound on the rank, valid in
every characteristic, and not a claim that the counted coordinates are attained.

## Main statements

* `weightedSupport_localConstraint_support` and `weightedSupport_localConstraint_mem_exponents`:
  every monomial of a local constraint of a member of the weighted support space satisfies the
  four bounds, and so lies in `localResidualExponents hd m W ⌈L / D⌉₊`.
* `weightedSupportLocalConstraint` and `finrank_weightedSupportLocalConstraint_le`: the local
  constraint map on the weighted support space and its rank bound.

## References

Ported from
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/WeightedSupport/LocalRank.lean`
at ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d.

* `weightedSupport_localConstraint_support` keeps its statement, with the source's
  `reachableLocalJetDegree e` written `e.weight (localJetDegreeWeight d)`.
* `weightedSupport_localConstraint_mem_exponents` and `finrank_weightedSupportLocalConstraint_le`
  use the natural cutoff `⌈L / D⌉₊` where the source's `localResidualExponents` and
  `localResidualCoordinateBudget` took the real cutoff `L / D`; the two agree because
  `n < x ↔ n < ⌈x⌉₊` for natural `n`. The rank bound is the specialization of the existing
  `finrank_range_localConstraintAt_domRestrict_le` to the weighted support space.
* `weightedSupportLocalConstraint` is unchanged, except that `weightedSupportSpace` no longer
  takes `hD`; the rank bound takes `hD` instead.

* Brakensiek, Chen, Putterman, Zhang, and Zheng, *Algorithmic List Decoding of Reed--Solomon
  Codes up to Capacity in the Low-Rate Regime*, ECCC TR26-164, Section 3.
-/

@[expose] public section

open PolynomialDifferential

noncomputable section

namespace ReedSolomon.HiddenDerivative

variable {R : Type*} [CommRing R] {d D m W : ℕ} {L : ℝ}

/-- For `0 < D`, every monomial `T^t E^h ⋯` of a local constraint of order `m` of a member of the
weighted support space has `h ≤ t`, higher-jet weight at most `W + (t - h)`, contact order below
`m`, and jet degree below `L / D`. The hypothesis `0 < D` is what turns the coarse cutoff into a
jet-degree cutoff. -/
theorem weightedSupport_localConstraint_support (hD : 0 < D) (center received : R)
    {Q : DifferentialPolynomial R d} (hQ : Q ∈ weightedSupportSpace R D d W L)
    {e : LocalVariable d →₀ ℕ} (he : e ∈ (localConstraintAt m center received Q).support) :
    e (localE d) ≤ e (localT d) ∧
      e.weight (localHigherJetWeight d) ≤ W + (e (localT d) - e (localE d)) ∧
      localContactOrder d e < m ∧ (e.weight (localJetDegreeWeight d) : ℝ) < L / D := by
  have hs := mem_weightedSupportSpace_iff.mp hQ
  obtain ⟨hb, hw, hc, ht⟩ := localConstraintAt_support_of_weight_bounds (B := ⌈L / D⌉₊)
    center received (fun u hu => (hs u hu).1)
    (fun u hu => Nat.lt_ceil.mpr (totalJetDegree_lt_of_weightedSupportEligible hD (hs u hu))) he
  exact ⟨hb, hw, hc, Nat.lt_ceil.mp ht⟩

/-- For `0 < d` and `0 < D`, every monomial of a local constraint of a member of the weighted
support space lies in the finite set `localResidualExponents hd m W ⌈L / D⌉₊`. The hypothesis
`0 < d` is needed for the coordinates of `localResidualExponents`. -/
theorem weightedSupport_localConstraint_mem_exponents (hd : 0 < d) (hD : 0 < D)
    (center received : R) {Q : DifferentialPolynomial R d}
    (hQ : Q ∈ weightedSupportSpace R D d W L)
    {e : LocalVariable d →₀ ℕ} (he : e ∈ (localConstraintAt m center received Q).support) :
    e ∈ localResidualExponents hd m W ⌈L / D⌉₊ := by
  obtain ⟨hb, hw, hc, ht⟩ := weightedSupport_localConstraint_support hD center received hQ he
  exact mem_localResidualExponents_of_bounds hd hb hw hc (Nat.lt_ceil.mpr ht)

/-- The local constraint map of order `m` at `(center, received)`, restricted to the weighted
support space. -/
def weightedSupportLocalConstraint (m : ℕ) (center received : R) :
    weightedSupportSpace R D d W L →ₗ[R] LocalPolynomial R d :=
  (localConstraintAt m center received).domRestrict _

/-- For `0 < d` and `0 < D`, the local constraint map on the weighted support space has rank at
most `localResidualCoordinateBudget d m W ⌈L / D⌉₊` over every field. -/
theorem finrank_weightedSupportLocalConstraint_le {F : Type*} [Field F] (hd : 0 < d)
    (hD : 0 < D) (center received : F) :
    Module.finrank F (LinearMap.range
      (weightedSupportLocalConstraint (D := D) (d := d) (W := W) (L := L) m center received)) ≤
      localResidualCoordinateBudget d m W ⌈L / D⌉₊ :=
  finrank_range_localConstraintAt_domRestrict_le hd m W _ center received _ fun _ hQ u hu =>
    have h := mem_weightedSupportSpace_iff.mp hQ u hu
    ⟨h.1, Nat.lt_ceil.mpr (totalJetDegree_lt_of_weightedSupportEligible hD h)⟩

end ReedSolomon.HiddenDerivative
