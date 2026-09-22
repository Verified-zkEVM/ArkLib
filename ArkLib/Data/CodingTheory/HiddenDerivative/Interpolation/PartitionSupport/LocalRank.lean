/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.Coordinates
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.PartitionSupport.Basic

/-!
# The local rank on the partition support

After the unscaled local substitution, a monomial `T^t E^h Y^c` of a local constraint of order
`m` of a polynomial of derivative-order weight at most `W` satisfies `h ≤ t`,
`∑_j (j + 1) c_j ≤ W + (t - h)` and `t + d h < m`
(`localConstraintAt_support_of_derivative_weight`). Grouping by the residual `r = t - h` counts at
most `∑_{r < m} ⌈(m - r)/(d + 1)⌉ · p_d(W + r)` such monomials, where `p_d(n)` is the number of
exponents of `Y₁, ..., Y_d` of derivative-order weight at most `n`; this is
`localDerivativeCoordinateBudget d m W`. So the local constraint map on the partition support
space has rank at most that budget over every field. This is an upper bound on the rank, not an
independence claim. Unlike the weighted support, no jet-degree cutoff and no positivity of `d` is
needed; `0 < D` enters only as the index of the space.

## Main statements

* `partitionSupport_localConstraint_support`: the three support bounds on the partition support.
* `partitionSupportLocalConstraint` and `finrank_partitionSupportLocalConstraint_le`: the local
  constraint map on the partition support space and its rank bound.
-/

@[expose] public section

open PolynomialDifferential

noncomputable section

namespace ReedSolomon.HiddenDerivative

variable {R : Type*} [CommRing R] {d D m W : ℕ} {L : ℝ}

/-- Every monomial `T^t E^h Y^c` of a local constraint of order `m` of a member of the partition
support space has `h ≤ t`, derivative-order weight at most `W + (t - h)`, and contact order below
`m`. -/
theorem partitionSupport_localConstraint_support (hD : 0 < D) (center received : R)
    {Q : DifferentialPolynomial R d} (hQ : Q ∈ partitionSupportSpace R D d W L hD)
    {e : LocalVariable d →₀ ℕ} (he : e ∈ (localConstraintAt m center received Q).support) :
    e (localE d) ≤ e (localT d) ∧
      e.weight (localDerivativeJetWeight d) ≤ W + (e (localT d) - e (localE d)) ∧
      localContactOrder d e < m :=
  localConstraintAt_support_of_derivative_weight center received
    (fun u hu => (mem_partitionSupportSpace_iff.mp hQ u hu).1) he

/-- The local constraint map of order `m` at `(center, received)`, restricted to the partition
support space. -/
def partitionSupportLocalConstraint (m : ℕ) (hD : 0 < D) (center received : R) :
    partitionSupportSpace R D d W L hD →ₗ[R] LocalPolynomial R d :=
  (localConstraintAt m center received).domRestrict _

/-- The local constraint map on the partition support space has rank at most
`localDerivativeCoordinateBudget d m W` over every field, for all `d` and `L`. -/
theorem finrank_partitionSupportLocalConstraint_le {F : Type*} [Field F] (hD : 0 < D)
    (center received : F) :
    Module.finrank F (LinearMap.range
      (partitionSupportLocalConstraint (d := d) (W := W) (L := L) m hD center received)) ≤
      localDerivativeCoordinateBudget d m W :=
  finrank_range_localConstraintAt_domRestrict_le_of_derivative_weight m W center received _
    fun _ hQ u hu => (mem_partitionSupportSpace_iff.mp hQ u hu).1

end ReedSolomon.HiddenDerivative
