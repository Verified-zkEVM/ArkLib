/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.DimensionBridge


/-!
# The finite support for first-order interpolation

To tune a code of length `n` and message dimension `k`, choose an integer agreement
threshold `A` and interpolation parameters `m`, `M`, and `μ`. Instead of fixing them from
an asymptotic capacity gap, count the monomials available at these actual parameters:

```text
X^x Y₀^a Y₁^b,  b ≤ M,  a + b ≤ μ,
                    x + D a + (D - 1) b < m A.
```

Here `D` bounds the degree of a message polynomial. Substituting `P` for `Y₀` and its
first Hasse derivative for `Y₁` gives degree at most `x + D*a + (D-1)*b`. The strict
cutoff therefore ensures degree below `m*A`. The separate cap `M` controls how often
`Y₁` can occur; the total cap `μ` bounds the degree in both jet variables together.
These are the support restrictions used by the finite first-order certificate in [DKTZ26].

## Reading the definitions

* `JetVariable 1` has three coordinates: the ordinary variable `X` and the two jet
  variables `Y₀`, `Y₁`. A finitely supported function `u` records their exponents.
* `firstOrderExponents D A m M μ` is precisely the finite set displayed above.
  The coordinate characterization states both directions, so it is an exact support.
* `firstOrderSpace F ...` consists of polynomials over `F` supported on that set.
  Its dimension is the cardinality of the support, independently of the field.
* Natural subtraction is truncated. In particular, `D - 1` is zero when `D ≤ 1`.
  Finiteness holds even then because the total jet degree is separately capped.

## Proof route and use

Bound the ordinary exponent by `m*A` and the sum of jet exponents by `μ` to prove
finiteness. The monomial basis then identifies dimension with support cardinality.
For `1 < D`, this space embeds into the existing exact first-order interpolation
space, allowing `FirstOrder.Interpolation` to reuse its local rank theorem. The
weighted-degree result here is the other ingredient: sufficiently many roots, each
of multiplicity `m`, force the specialized interpolant to vanish identically.

The cutoff-sensitive rank and geometric transfer are separate claims; a large support
alone does not bound a decoding list or an exceptional challenge set.

## References

* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding and Mutual Correlated
  Agreement up to Capacity*][DKTZ26], Section 6.1.3, Proposition 6.3 (finite first-order
  certificate).
-/

@[expose] public section

open PolynomialDifferential


namespace ReedSolomon.HiddenDerivative

noncomputable section

variable {F : Type*} {D A m M μ : ℕ}

/-- Eligibility for the finite derivative-weighted first-order support. -/
def FirstOrderEligibleExponent (D A m M μ : ℕ) (u : JetVariable 1 →₀ ℕ) : Prop :=
  firstJetExponent u ≤ M ∧
    totalJetDegree u ≤ μ ∧
    exactInterpolationMonomialWeight D u < m * A

/-- The set underlying `firstOrderExponents`. -/
def firstOrderExponentSet (D A m M μ : ℕ) : Set (JetVariable 1 →₀ ℕ) :=
  {u | FirstOrderEligibleExponent D A m M μ u}

/-- The total-jet cap makes the first-order support finite for every `D`, including the boundary
case `D = 1`. -/
theorem firstOrderExponentSet_finite (D A m M μ : ℕ) :
    (firstOrderExponentSet D A m M μ).Finite := by
  apply (Finsupp.finite_of_degree_le (m * A + μ)).subset
  intro u hu
  change Finsupp.degree u ≤ m * A + μ
  rw [exponentDegree_eq_x_add_totalJetDegree]
  apply Nat.add_le_add
  · apply Nat.le_of_lt
    exact lt_of_le_of_lt (by
      rw [exactInterpolationMonomialWeight_eq]
      exact Nat.le_add_right _ _) hu.2.2
  · exact hu.2.1

/-- The finite derivative-weighted first-order support, with a cap on total jet degree. -/
def firstOrderExponents (D A m M μ : ℕ) : Finset (JetVariable 1 →₀ ℕ) :=
  (firstOrderExponentSet_finite D A m M μ).toFinset

@[simp]
theorem mem_firstOrderExponents {u : JetVariable 1 →₀ ℕ} :
    u ∈ firstOrderExponents D A m M μ ↔ FirstOrderEligibleExponent D A m M μ u := by
  simp [firstOrderExponents, firstOrderExponentSet]

/-- First-order support membership in the paper's three monomial coordinates. -/
theorem mem_firstOrderExponents_iff_coordinates {u : JetVariable 1 →₀ ℕ} :
    u ∈ firstOrderExponents D A m M μ ↔
      (exactExponentCoordinatesEquiv (by omega : 0 < 1) u).2.1.2 ≤ M ∧
      (exactExponentCoordinatesEquiv (by omega : 0 < 1) u).2.1.1 +
          (exactExponentCoordinatesEquiv (by omega : 0 < 1) u).2.1.2 ≤ μ ∧
      (exactExponentCoordinatesEquiv (by omega : 0 < 1) u).1 +
          D * (exactExponentCoordinatesEquiv (by omega : 0 < 1) u).2.1.1 +
          (D - 1) * (exactExponentCoordinatesEquiv (by omega : 0 < 1) u).2.1.2 < m * A := by
  let hd : 0 < 1 := by omega
  change u ∈ firstOrderExponents D A m M μ ↔
    (exactExponentCoordinatesEquiv hd u).2.1.2 ≤ M ∧
    (exactExponentCoordinatesEquiv hd u).2.1.1 +
        (exactExponentCoordinatesEquiv hd u).2.1.2 ≤ μ ∧
    (exactExponentCoordinatesEquiv hd u).1 +
        D * (exactExponentCoordinatesEquiv hd u).2.1.1 +
        (D - 1) * (exactExponentCoordinatesEquiv hd u).2.1.2 < m * A
  rw [mem_firstOrderExponents, FirstOrderEligibleExponent,
    firstJetExponent_eq_coordinate hd, exactInterpolationMonomialWeight_eq_coordinates hd]
  have hhigher : higherJetTupleSpecializationCost D
      (exactExponentCoordinatesEquiv hd u).2.2 = 0 := by
    simp [higherJetTupleSpecializationCost]
  rw [hhigher, Nat.add_zero]
  simp only [totalJetDegree, Finsupp.degree_eq_sum,
    sum_jet_eq_y₀_add_y₁_add_higher (by omega : 0 < 1)]
  simp [exactExponentCoordinatesEquiv_y₀, exactExponentCoordinatesEquiv_y₁]

/-- Differential polynomials supported on the capped first-order monomials. -/
def firstOrderSpace (F : Type*) [CommSemiring F]
    (D A m M μ : ℕ) :
    Submodule F (DifferentialPolynomial F 1) :=
  MvPolynomial.restrictSupport F
    (↑(firstOrderExponents D A m M μ) : Set (JetVariable 1 →₀ ℕ))

/-- Membership is pointwise membership of every monomial in the finite first-order support. -/
theorem mem_firstOrderSpace_iff [CommSemiring F]
    {Q : DifferentialPolynomial F 1} :
    Q ∈ firstOrderSpace F D A m M μ ↔
      ∀ u ∈ Q.support, u ∈ firstOrderExponents D A m M μ := by
  rw [firstOrderSpace, MvPolynomial.mem_restrictSupport_iff]
  simp only [Set.subset_def, Finset.mem_coe]

/-- The capped support is a genuine subspace of the exact interpolation space used by the local
constraint machinery. -/
theorem firstOrderSpace_le_exactInterpolationSpace [CommSemiring F] (hD : 1 < D) :
    firstOrderSpace F D A m M μ ≤
      exactInterpolationSpace F D A 1 m M 0 hD := by
  intro Q hQ
  rw [mem_exactInterpolationSpace_iff]
  intro u hu
  have h := mem_firstOrderExponents.mp (mem_firstOrderSpace_iff.mp hQ u hu)
  refine ⟨h.1, ?_, h.2.2⟩
  simp [fullHigherJetWeight, Finsupp.weight_apply, Finsupp.sum_fintype]

/-- Canonical monomial basis of the capped first-order space. -/
def firstOrderSpaceBasis (F : Type*) [CommSemiring F]
    (D A m M μ : ℕ) :=
  MvPolynomial.basisRestrictSupport (R := F)
    (↑(firstOrderExponents D A m M μ) : Set (JetVariable 1 →₀ ℕ))

/-- The dimension of the first-order space is exactly its finite support cardinality. -/
theorem finrank_firstOrderSpace_eq_card [Field F] :
    Module.finrank F (firstOrderSpace F D A m M μ) =
      (firstOrderExponents D A m M μ).card := by
  let b := firstOrderSpaceBasis F D A m M μ
  change Module.finrank F
    (MvPolynomial.restrictSupport F
      (↑(firstOrderExponents D A m M μ) : Set (JetVariable 1 →₀ ℕ))) = _
  rw [Module.finrank_eq_card_basis b]
  exact Fintype.card_coe _

/-- Every first-order interpolant has the required strict specialization-weight bound. -/
theorem differentialWeightedDegree_lt_of_mem_firstOrderSpace [CommSemiring F]
    (hbudget : 0 < m * A) {Q : DifferentialPolynomial F 1}
    (hQ : Q ∈ firstOrderSpace F D A m M μ) :
    differentialWeightedDegree D Q < m * A := by
  rw [differentialWeightedDegree, MvPolynomial.weightedTotalDegree,
    Finset.sup_lt_iff hbudget]
  intro u hu
  exact (mem_firstOrderExponents.mp (mem_firstOrderSpace_iff.mp hQ u hu)).2.2

end

end ReedSolomon.HiddenDerivative
