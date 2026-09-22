/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Dimension

/-!
# The first-order interpolation space

For a degree bound `D`, agreement threshold `A`, multiplicity `m`, first-jet cap `M`, and total
jet cap `μ`, the first-order interpolation space consists of the differential polynomials
`Q(X, Y₀, Y₁)` whose monomials `X^x Y₀^a Y₁^b` satisfy

```text
b ≤ M,   a + b ≤ μ,   x + D a + (D - 1) b < m A.
```

The last expression is the `differentialWeight D` weight of the exponent, which bounds the degree
of the specialization `Q(X, P, P')` when `deg P ≤ D`. Natural subtraction is truncated, so
`D - 1 = 0` when `D ≤ 1`. The cap `μ` on the total jet degree makes the support finite for every
`D`, so no hypothesis on `D` is needed; by contrast the exact interpolation space of
`Interpolation/Index.lean` needs `d < D`.

When `1 < D` the first-order space lies in the exact interpolation space with `d = 1`, so the
local rank bound of `Interpolation/Local/CertifiedRankBound.lean` applies to it. For `D ≤ 1` it
still lies in an exact interpolation space with a larger degree bound and agreement threshold;
the local constraint maps do not depend on these two parameters.

## Main statements

* `firstOrderExponentSet_finite`: the eligible exponents form a finite set, for every `D`.
* `mem_firstOrderExponents_iff_coordinates`: eligibility in the exponents `x`, `a`, `b` of `X`,
  `Y₀`, `Y₁`.
* `firstOrderSpace` with its monomial basis, and `finrank_firstOrderSpace_eq_card`: its dimension
  is the number of eligible exponents.
* `differentialWeightedDegree_lt_of_mem_firstOrderSpace` and
  `jetTotalDegree_le_of_mem_firstOrderSpace`: degree bounds for members of the space.
* `firstOrderSpace_le_exactInterpolationSpace_of_le` and
  `firstOrderSpace_le_exactInterpolationSpace`: embeddings into exact interpolation spaces.

## References

* [Dao, Q., Kominers, S. D., and Thaler, J., *Reed–Solomon Codes Beyond Johnson: Efficient
  Decoding and Smaller Cryptographic Proofs*][DKT26], Section 6.1.
-/

@[expose] public section

open PolynomialDifferential

namespace ReedSolomon.HiddenDerivative

noncomputable section

variable {F : Type*} {D A m M μ : ℕ}

/-! ### Eligible exponents -/

/-- Eligibility of an exponent on `X, Y₀, Y₁`: at most `M` copies of `Y₁`, total jet degree at
most `μ`, and specialization weight strictly below `m * A`. -/
def FirstOrderEligibleExponent (D A m M μ : ℕ) (u : JetVariable 1 →₀ ℕ) : Prop :=
  firstJetExponent u ≤ M ∧ totalJetDegree u ≤ μ ∧
    Finsupp.weight (differentialWeight D) u < m * A

/-- The set of first-order eligible exponents. -/
def firstOrderExponentSet (D A m M μ : ℕ) : Set (JetVariable 1 →₀ ℕ) :=
  {u | FirstOrderEligibleExponent D A m M μ u}

/-- There are finitely many first-order eligible exponents, for every `D`: the `X` exponent is
below `m * A` and the total jet degree is at most `μ`. -/
theorem firstOrderExponentSet_finite (D A m M μ : ℕ) :
    (firstOrderExponentSet D A m M μ).Finite := by
  refine (Finsupp.finite_of_degree_le (m * A + μ)).subset fun u hu => ?_
  change u.degree ≤ _
  have hw := hu.2.2
  rw [weight_differentialWeight_eq] at hw
  rw [degree_eq_add_totalJetDegree]
  have := hu.2.1
  omega

/-- The finite set of first-order eligible exponents. It is specified through
`Set.Finite.toFinset`, so it is not an executable enumeration. -/
def firstOrderExponents (D A m M μ : ℕ) : Finset (JetVariable 1 →₀ ℕ) :=
  (firstOrderExponentSet_finite D A m M μ).toFinset

/-- Membership in `firstOrderExponents` is `FirstOrderEligibleExponent`. -/
@[simp]
theorem mem_firstOrderExponents {u : JetVariable 1 →₀ ℕ} :
    u ∈ firstOrderExponents D A m M μ ↔ FirstOrderEligibleExponent D A m M μ u := by
  simp [firstOrderExponents, firstOrderExponentSet]

/-- First-order eligibility in the exponents `x = u X`, `a = u Y₀`, and `b = u Y₁`:
`b ≤ M`, `a + b ≤ μ`, and `x + D a + (D - 1) b < m A`. -/
theorem mem_firstOrderExponents_iff_coordinates {u : JetVariable 1 →₀ ℕ} :
    u ∈ firstOrderExponents D A m M μ ↔
      u (some 1) ≤ M ∧ u (some 0) + u (some 1) ≤ μ ∧
        u none + D * u (some 0) + (D - 1) * u (some 1) < m * A := by
  rw [mem_firstOrderExponents, FirstOrderEligibleExponent,
    firstJetExponent_eq_coordinates Nat.one_pos, totalJetDegree_eq_coordinates Nat.one_pos,
    weight_differentialWeight_eq_coordinates Nat.one_pos]
  simp [higherJetTupleSpecializationCost]
  rfl

/-! ### The space and its basis -/

/-- Differential polynomials in `X, Y₀, Y₁` supported on first-order eligible exponents. -/
def firstOrderSpace (F : Type*) [CommSemiring F] (D A m M μ : ℕ) :
    Submodule F (DifferentialPolynomial F 1) :=
  MvPolynomial.restrictSupport F
    (↑(firstOrderExponents D A m M μ) : Set (JetVariable 1 →₀ ℕ))

/-- Membership in the first-order space is eligibility of every support exponent. -/
theorem mem_firstOrderSpace_iff [CommSemiring F] {Q : DifferentialPolynomial F 1} :
    Q ∈ firstOrderSpace F D A m M μ ↔
      ∀ u ∈ Q.support, FirstOrderEligibleExponent D A m M μ u := by
  rw [firstOrderSpace, MvPolynomial.mem_restrictSupport_iff]
  simp only [Set.subset_def, Finset.mem_coe, mem_firstOrderExponents]

/-- A monomial lies in the first-order space exactly when its exponent is eligible, unless its
coefficient is zero. -/
@[simp]
theorem monomial_mem_firstOrderSpace [CommSemiring F] {u : JetVariable 1 →₀ ℕ} {a : F} :
    MvPolynomial.monomial u a ∈ firstOrderSpace F D A m M μ ↔
      FirstOrderEligibleExponent D A m M μ u ∨ a = 0 := by
  simp [firstOrderSpace]

/-- The monomial basis of the first-order space, indexed by the eligible exponents. -/
def firstOrderSpaceBasis (F : Type*) [CommSemiring F] (D A m M μ : ℕ) :
    Module.Basis ↥(firstOrderExponents D A m M μ) F (firstOrderSpace F D A m M μ) :=
  MvPolynomial.basisRestrictSupport (R := F)
    (↑(firstOrderExponents D A m M μ) : Set (JetVariable 1 →₀ ℕ))

/-- The first-order space is a finite module, since its monomial basis is finite. -/
instance firstOrderSpace.finite [CommSemiring F] :
    Module.Finite F (firstOrderSpace F D A m M μ) :=
  Module.Finite.of_basis (firstOrderSpaceBasis F D A m M μ)

/-- The dimension of the first-order space over a field is the number of eligible exponents. -/
theorem finrank_firstOrderSpace_eq_card [Field F] :
    Module.finrank F (firstOrderSpace F D A m M μ) = (firstOrderExponents D A m M μ).card := by
  rw [Module.finrank_eq_card_basis (firstOrderSpaceBasis F D A m M μ)]
  exact Fintype.card_coe _

/-! ### Degree bounds -/

/-- Every member of the first-order space has specialization-weighted degree below `m * A`. The
hypothesis `0 < m * A` is needed for the zero polynomial, whose weighted degree is `0`. -/
theorem differentialWeightedDegree_lt_of_mem_firstOrderSpace [CommSemiring F]
    (hbudget : 0 < m * A) {Q : DifferentialPolynomial F 1}
    (hQ : Q ∈ firstOrderSpace F D A m M μ) :
    differentialWeightedDegree D Q < m * A := by
  rw [differentialWeightedDegree, MvPolynomial.weightedTotalDegree, Finset.sup_lt_iff hbudget]
  exact fun u hu => (mem_firstOrderSpace_iff.mp hQ u hu).2.2

/-- Every member of the first-order space has total jet degree at most `μ`. -/
theorem jetTotalDegree_le_of_mem_firstOrderSpace [CommSemiring F]
    {Q : DifferentialPolynomial F 1} (hQ : Q ∈ firstOrderSpace F D A m M μ) :
    jetTotalDegree Q ≤ μ :=
  (jetTotalDegree_le_iff Q _).mpr fun u hu => (mem_firstOrderSpace_iff.mp hQ u hu).2.1

/-! ### Embeddings into exact interpolation spaces -/

/-- Raising the degree bound from `D` to `D' ≥ D` raises the specialization weight of an exponent
by at most `(D' - D)` times its total jet degree, since each jet variable gains at most
`D' - D` and `X` gains nothing. -/
theorem weight_differentialWeight_le_add_mul_totalJetDegree {d D' : ℕ} (hDD' : D ≤ D')
    (u : JetVariable d →₀ ℕ) :
    Finsupp.weight (differentialWeight D') u ≤
      Finsupp.weight (differentialWeight D) u + (D' - D) * totalJetDegree u := by
  rw [weight_differentialWeight_eq, weight_differentialWeight_eq, totalJetDegree_eq_sum,
    Finset.mul_sum, add_assoc, ← Finset.sum_add_distrib]
  gcongr with j
  rw [← Nat.add_mul]
  exact Nat.mul_le_mul_right _ (by omega)

/-- The first-order space lies in the exact interpolation space with `d = 1`, degree bound
`D' ≥ D`, and agreement threshold `A'` whenever `m A + (D' - D) μ ≤ m A'`, for every higher-jet
budget `W`. With `d = 1` there are no higher jets, so `W` plays no role. -/
theorem firstOrderSpace_le_exactInterpolationSpace_of_le [CommSemiring F] {D' A' W : ℕ}
    (hD' : 1 < D') (hDD' : D ≤ D') (hA : m * A + (D' - D) * μ ≤ m * A') :
    firstOrderSpace F D A m M μ ≤ exactInterpolationSpace F D' A' 1 m M W hD' := by
  intro Q hQ
  rw [mem_exactInterpolationSpace_iff]
  intro u hu
  obtain ⟨hM, hμ, hw⟩ := mem_firstOrderSpace_iff.mp hQ u hu
  refine ⟨hM, ?_, ?_⟩
  · simp [fullHigherJetWeight, jetHigherWeight, Finsupp.weight_apply, Finsupp.sum_fintype]
  · have hle := weight_differentialWeight_le_add_mul_totalJetDegree hDD' u
    have := Nat.mul_le_mul_left (D' - D) hμ
    omega

/-- For `1 < D` the first-order space lies in the exact interpolation space with the same
parameters and `d = 1`, for every higher-jet budget `W`. -/
theorem firstOrderSpace_le_exactInterpolationSpace [CommSemiring F] {W : ℕ} (hD : 1 < D) :
    firstOrderSpace F D A m M μ ≤ exactInterpolationSpace F D A 1 m M W hD :=
  firstOrderSpace_le_exactInterpolationSpace_of_le hD le_rfl (by simp)

end

end ReedSolomon.HiddenDerivative
