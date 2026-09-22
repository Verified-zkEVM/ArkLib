/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.Coordinates
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.PartitionSupport.Basic
public import ArkLib.ToMathlib.LinearAlgebra.FiniteDimensional

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

If the dimension of a space `S` of derivative-order weight at most `W` exceeds the number of
points times the budget, the joint kernel of the local constraint maps at those points is nonzero
(`LinearMap.exists_ne_zero_of_sum_finrank_range_lt`), so `S` contains a nonzero polynomial
satisfying all local constraints. The rank bound is an upper bound, so the surplus condition is
sufficient but not necessary; for `m = 0` the budget is zero and every nonzero member of `S` is an
interpolant. The partition support space is such a space.

## Main statements

* `partitionSupport_localConstraint_support`: the three support bounds on the partition support.
* `partitionSupportLocalConstraint` and `finrank_partitionSupportLocalConstraint_le`: the local
  constraint map on the partition support space and its rank bound.
* `exists_ne_zero_satisfiesLocalConstraints_of_derivative_weight`: the interpolant in any space
  of derivative-order weight at most `W`.
* `exists_nonzero_partitionSupport_interpolant`: the interpolant in the partition support space.

## References

* [Dao, Q., Kominers, S. D., and Thaler, J., *Reed–Solomon Codes Beyond Johnson: Efficient Decoding
  and Smaller Cryptographic Proofs*][DKT26], Section 3.5, Definition 3.7 and Lemma 3.8, and Section
  6.1, (70)–(72)
-/

@[expose] public section

open PolynomialDifferential Finset

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

/-! ### Interpolation from a surplus -/

/-- Let `S` be a space of differential polynomials whose exponents all have derivative-order
weight at most `W`. If `card ι * localDerivativeCoordinateBudget d m W < dim S`, then `S` contains
a nonzero polynomial satisfying the local constraints of order `m` at every point
`(centers i, received i)`. The surplus must be strict: for `m = 0` the budget is zero, and the
zero space has no nonzero member. `S` need not be assumed finite-dimensional. -/
theorem exists_ne_zero_satisfiesLocalConstraints_of_derivative_weight {F ι : Type*} [Field F]
    [Fintype ι] {m : ℕ} (centers received : ι → F) (S : Submodule F (DifferentialPolynomial F d))
    (hS : ∀ Q ∈ S, ∀ u ∈ Q.support, fullDerivativeJetWeight u ≤ W)
    (hdim : Fintype.card ι * localDerivativeCoordinateBudget d m W < Module.finrank F S) :
    ∃ Q : DifferentialPolynomial F d, Q ≠ 0 ∧ Q ∈ S ∧
      ∀ i, SatisfiesLocalConstraints m (centers i) (received i) Q := by
  let φ := fun i => (localConstraintAt m (centers i) (received i)).domRestrict S
  have hsum : ∑ i, Module.finrank F (LinearMap.range (φ i)) < Module.finrank F S :=
    calc ∑ i, Module.finrank F (LinearMap.range (φ i))
        ≤ ∑ _i : ι, localDerivativeCoordinateBudget d m W := sum_le_sum fun i _ =>
          finrank_range_localConstraintAt_domRestrict_le_of_derivative_weight m W _ _ S hS
      _ = Fintype.card ι * localDerivativeCoordinateBudget d m W := by simp
      _ < Module.finrank F S := hdim
  obtain ⟨Q, hQ, hlocal⟩ := LinearMap.exists_ne_zero_of_sum_finrank_range_lt φ hsum
  exact ⟨Q.1, fun h => hQ (Subtype.ext h), Q.2, hlocal⟩

/-- If the number of partition-support eligible exponents exceeds `card ι` times the local
coordinate budget `localDerivativeCoordinateBudget d m W`, the partition support space contains a
nonzero polynomial satisfying the local constraints of order `m` at every point
`(centers i, received i)`. The statement holds over every field and for every real cutoff `L`. -/
theorem exists_nonzero_partitionSupport_interpolant {F ι : Type*} [Field F] [Fintype ι] {m : ℕ}
    (hD : 0 < D) (centers received : ι → F)
    (hdim : Fintype.card ι * localDerivativeCoordinateBudget d m W <
      #(partitionSupportExponents D d W L hD)) :
    ∃ Q : DifferentialPolynomial F d, Q ≠ 0 ∧ Q ∈ partitionSupportSpace F D d W L hD ∧
      ∀ i, SatisfiesLocalConstraints m (centers i) (received i) Q :=
  exists_ne_zero_satisfiesLocalConstraints_of_derivative_weight centers received _
    (fun _ hQ u hu => (mem_partitionSupportSpace_iff.mp hQ u hu).1)
    (by rwa [finrank_partitionSupportSpace_eq_card])

end ReedSolomon.HiddenDerivative
