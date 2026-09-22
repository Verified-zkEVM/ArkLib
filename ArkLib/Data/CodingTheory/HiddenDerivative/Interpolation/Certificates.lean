/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.WeightedSupport.Capacity
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Global.Multiplicity
public import ArkLib.Data.CodingTheory.ReedSolomon.Agreement
public import ArkLib.Data.CodingTheory.ReedSolomon.ListSpecification
public import ArkLib.Data.Polynomial.Differential.DerivativeDescent
public import Mathlib.Algebra.Field.ZMod

/-!
# Hidden-derivative interpolation certificates

An interpolation certificate of order `d` and multiplicity `m` for a received word is a nonzero
differential polynomial `Q(X, Y₀, ..., Y_d)` over a commutative ring `R`, together with an ambient
dimension `K ≥ k`, such that the weighted degree of `Q` at degree `K - 1` is below `m A` and `Q`
satisfies the local constraints of order `m` at every evaluation point. The order `d` is part of the
type of `Q` and of its constraints, not only a numerical exponent in a list bound.

Over a domain, every message polynomial of degree below `k` with at least `A` agreements is then a
root of `Q`: `Q(X, P, D¹P, ..., DᵈP) = 0`. This is
`differentialSpecialization_eq_zero_of_differentialWeightedDegree_lt` in
`Interpolation/Global/Multiplicity.lean` applied to the agreement set of `P`.

For prime fields `ZMod q`, `ReedSolomon.HiddenDerivativeInterpolationCertificate` adds the two
side conditions that the finite-field root count uses: the cast hypothesis
`JetDegreeCastsNeZero` at every jet, and the contact budget `m A ≤ q ^ 2`. The uniform capacity
targets `UniformHiddenDerivativeInterpolation` and `WeightedSupportConstruction` quantify over these
certificates. They are existence statements, not algorithms.

## Main definitions

* `HiddenDerivative.InterpolationCertificate k A d m domain received`: the certificate over any
  commutative ring and any finite index type.
* `HiddenDerivativeInterpolationCertificate d m domain received`: the prime-field certificate.
* `UniformHiddenDerivativeInterpolation`, `WeightedSupportConstruction`: the uniform targets.

## Main statements

* `HiddenDerivative.InterpolationCertificate.specializes_to_zero_of_natDegree_le` and
  `HiddenDerivative.InterpolationCertificate.specializes_to_zero`: agreeing polynomials are roots.
* `HiddenDerivativeInterpolationCertificate.below_characteristic`: over `ZMod q`, the degree
  `K - 1` and every jet degree are below `q`.

## References

Ports `Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/Certificates.lean` at ArkLib
revision a5aa2677fee4e3a79d6bb05136631cce4a08587d.

* The source's `HiddenDerivativeInterpolationCertificate` is split. Its fields that describe the
  interpolation (`ambientDim`, `messageDim_le`, `ambientDim_le`, `order_lt_degree`, `interpolant`,
  `nonzero`, `weighted_degree_lt`, `local_constraints`) form `InterpolationCertificate`, stated over
  a commutative ring `R` with an embedding `domain : ι ↪ R` of a finite index type instead of
  `Fin n ↪ ZMod q`; `ambientDim_le` reads `ambientDim ≤ Fintype.card ι`. The prime-field structure
  extends it with the other two fields.
* The source field `below_characteristic : IsBelowCharacteristic (ambientDim - 1) interpolant`
  becomes `castsNeZero : ∀ j, JetDegreeCastsNeZero interpolant j`, since the port replaced
  `IsBelowCharacteristic` by `JetDegreeCastsNeZero` (see
  `ArkLib.Data.Polynomial.Differential.SingularRecursion`). Over `ZMod q` both halves of the source
  predicate follow: `HiddenDerivativeInterpolationCertificate.below_characteristic` proves
  `ambientDim - 1 < q ∧ ∀ j, jetDegree interpolant j < q`, where `ambientDim - 1 < q` comes from
  `ambientDim ≤ n ≤ q`. The source field `contact_budget_le` is unchanged.
* The source's `specializes_to_zero` is `InterpolationCertificate.specializes_to_zero`, over a
  domain; `specializes_to_zero_of_natDegree_le` is new and applies to every polynomial of degree at
  most `ambientDim - 1`.
* `UniformHiddenDerivativeInterpolation` and `WeightedSupportConstruction` keep their statements,
  with the source's `agreementThreshold δ n k` written as `k + ⌈δ * n⌉₊` and the source's
  `weightedSupportMultiplicity δ` written as
  `weightedSupportMultiplicity (capacityDerivativeOrder δ)`.

* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding and Mutual Correlated Agreement
  up to Capacity*][DKTZ26], weighted-support interpolation and uniform capacity decoding.
* [Brakensiek, Chen, Putterman, Zhang, and Zheng, *Algorithmic List Decoding of Reed-Solomon
  Codes up to Capacity in the Low-Rate Regime*][BCPZZ26], hidden-derivative interpolation.
-/

@[expose] public section

open PolynomialDifferential Polynomial

namespace ReedSolomon

namespace HiddenDerivative

/-- An order-`d`, multiplicity-`m` interpolation certificate for the received word `received` on
the evaluation points `domain`, at message dimension `k` and agreement threshold `A`.

The ambient dimension `ambientDim` may exceed `k`; interpolation and root counting use the ambient
degree `ambientDim - 1`. The bound `d < ambientDim - 1` keeps the order below the ambient degree,
and `ambientDim ≤ #ι` keeps the ambient dimension at most the block length. -/
structure InterpolationCertificate {ι R : Type*} [Fintype ι] [CommRing R] (k A d m : ℕ)
    (domain : ι ↪ R) (received : ι → R) where
  /-- The ambient dimension; the ambient degree is `ambientDim - 1`. -/
  ambientDim : ℕ
  /-- Every message polynomial lies in the ambient space. -/
  messageDim_le : k ≤ ambientDim
  /-- The ambient dimension is at most the block length. -/
  ambientDim_le : ambientDim ≤ Fintype.card ι
  /-- The order is below the ambient degree. -/
  order_lt_degree : d < ambientDim - 1
  /-- The differential polynomial, with jet variables indexed by `Fin (d + 1)`. -/
  interpolant : DifferentialPolynomial R d
  /-- The interpolant is nonzero. -/
  nonzero : interpolant ≠ 0
  /-- The weighted degree at the ambient degree is below `m * A`. -/
  weighted_degree_lt : differentialWeightedDegree (ambientDim - 1) interpolant < m * A
  /-- The local constraints of order `m` hold at every evaluation point. -/
  local_constraints : ∀ i, SatisfiesLocalConstraints m (domain i) (received i) interpolant

namespace InterpolationCertificate

variable {ι R : Type*} [Fintype ι] [CommRing R] {k A d m : ℕ} {domain : ι ↪ R}
  {received : ι → R}

/-- The ambient dimension is positive, since the order `d ≥ 0` is below `ambientDim - 1`. -/
theorem one_le_ambientDim (c : InterpolationCertificate k A d m domain received) :
    1 ≤ c.ambientDim := by
  have := c.order_lt_degree
  omega

/-- A message polynomial of degree below `k` has degree at most the ambient degree
`ambientDim - 1`. -/
theorem natDegree_le (c : InterpolationCertificate k A d m domain received)
    (P : ListDecoding.MessagePolynomial R k) : (P : R[X]).natDegree ≤ c.ambientDim - 1 := by
  by_cases hP : (P : R[X]) = 0
  · simp [hP]
  have hdeg := (Polynomial.natDegree_lt_iff_degree_lt hP).mpr
    (Polynomial.mem_degreeLT.mp P.property)
  have := c.messageDim_le
  omega

/-- If `P` has degree at most the ambient degree and agrees with `received` in at least `A`
coordinates, then `Q(X, P, D¹P, ..., DᵈP) = 0` for the certificate's interpolant `Q`.

The agreement coordinates have distinct evaluation points because `domain` is injective. The
domain hypothesis on `R` is needed for the root count: over `ZMod 4`, `2 X` has degree `1` and
vanishes at the two points `0` and `2`. -/
theorem specializes_to_zero_of_natDegree_le [IsDomain R] [DecidableEq R]
    (c : InterpolationCertificate k A d m domain received) (P : R[X])
    (hP : P.natDegree ≤ c.ambientDim - 1)
    (hAgreement : A ≤ Code.agree (ReedSolomon.evalOnPoints domain P) received) :
    differentialSpecialization c.interpolant P = 0 :=
  differentialSpecialization_eq_zero_of_differentialWeightedDegree_lt domain received
    (polynomialAgreementSet domain received P) c.weighted_degree_lt
    (fun i _ ↦ c.local_constraints i) P hP domain.injective.injOn hAgreement
    (fun _ hi ↦ (Finset.mem_filter.mp hi).2)

/-- Every message polynomial of degree below `k` with at least `A` agreements is a root of the
certificate's interpolant: `Q(X, P, D¹P, ..., DᵈP) = 0`. -/
theorem specializes_to_zero [IsDomain R] [DecidableEq R]
    (c : InterpolationCertificate k A d m domain received)
    (P : ListDecoding.MessagePolynomial R k)
    (hAgreement : A ≤ Code.agree (ReedSolomon.evalOnPoints domain P) received) :
    differentialSpecialization c.interpolant (P : R[X]) = 0 :=
  c.specializes_to_zero_of_natDegree_le P (c.natDegree_le P) hAgreement

end InterpolationCertificate

end HiddenDerivative

open HiddenDerivative ListDecoding

/-- A prime-field hidden-derivative interpolation certificate of order `d` and multiplicity `m`,
at message dimension `k` and agreement threshold `A`.

It extends `HiddenDerivative.InterpolationCertificate` with the two conditions used by the
finite-field root count: every positive integer up to a jet degree of the interpolant is nonzero in
`ZMod q`, and the contact budget `m * A` is at most `q ^ 2`. -/
structure HiddenDerivativeInterpolationCertificate {n q k A : ℕ} (d m : ℕ)
    (domain : Fin n ↪ ZMod q) (received : Fin n → ZMod q) extends
    InterpolationCertificate k A d m domain received where
  /-- The cast hypothesis at every jet. -/
  castsNeZero : ∀ j, JetDegreeCastsNeZero interpolant j
  /-- The contact budget is at most `q ^ 2`. -/
  contact_budget_le : m * A ≤ q ^ 2

namespace HiddenDerivativeInterpolationCertificate

variable {n q k A d m : ℕ} {domain : Fin n ↪ ZMod q} {received : Fin n → ZMod q}

/-- Over `ZMod q` with `q` prime, the ambient degree and every jet degree of the interpolant are
below `q`, which is `ringChar (ZMod q)`. This is the source's `IsBelowCharacteristic` guard. The
first half uses `ambientDim ≤ n ≤ q`, where `n ≤ q` holds because `domain` is injective; the second
half applies the cast hypothesis at `q`, which is `0` in `ZMod q`. -/
theorem below_characteristic [Fact q.Prime]
    (c : HiddenDerivativeInterpolationCertificate (k := k) (A := A) d m domain received) :
    c.ambientDim - 1 < q ∧ ∀ j, jetDegree c.interpolant j < q := by
  have hq := (Fact.out : q.Prime).pos
  refine ⟨?_, fun j ↦ ?_⟩
  · have hnq : n ≤ q := by
      simpa using Fintype.card_le_of_embedding domain
    have := c.ambientDim_le
    have := c.one_le_ambientDim
    simp only [Fintype.card_fin] at *
    omega
  · by_contra h
    exact c.castsNeZero j q hq (not_lt.mp h) (ZMod.natCast_self q)

end HiddenDerivativeInterpolationCertificate

/-- The uniform construction target: for every gap `0 < δ < 1`, an order `d`, a positive
multiplicity `m` and a block-length threshold `N` are chosen before the code parameters, and for
every block length `n ≥ N`, message dimension `0 < k ≤ n`, prime `q ≥ n` with agreement threshold
`k + ⌈δ n⌉₊ ≤ n`, every received word has a certificate. Thresholds above `n` are excluded because
their agreement lists are empty. -/
def UniformHiddenDerivativeInterpolation : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ d m N : ℕ, 0 < m ∧ ∀ n k q : ℕ,
      N ≤ n → 0 < k → k ≤ n → q.Prime → n ≤ q →
      k + ⌈δ * n⌉₊ ≤ n →
      ∀ (domain : Fin n ↪ ZMod q) (received : Fin n → ZMod q),
        Nonempty (HiddenDerivativeInterpolationCertificate (k := k)
          (A := k + ⌈δ * n⌉₊) d m domain received)

/-- The weighted-support construction target: for `0 < δ < 1 / 4`, at the prescribed order
`d = capacityDerivativeOrder δ` and multiplicity `m = weightedSupportMultiplicity d`, whenever
`8 m ≤ n`, `0 < k ≤ n`, `q ≥ n` is prime and `k + ⌈δ n⌉₊ ≤ n`, every received word has a
certificate with ambient dimension `weightedSupportAmbientDimension δ n k`. -/
def WeightedSupportConstruction : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < (1 / 4 : ℝ) →
    ∀ n k q : ℕ, 8 * weightedSupportMultiplicity (capacityDerivativeOrder δ) ≤ n →
      0 < k → k ≤ n → q.Prime → n ≤ q → k + ⌈δ * n⌉₊ ≤ n →
      ∀ (domain : Fin n ↪ ZMod q) (received : Fin n → ZMod q),
        ∃ construction : HiddenDerivativeInterpolationCertificate (k := k)
            (A := k + ⌈δ * n⌉₊) (capacityDerivativeOrder δ)
            (weightedSupportMultiplicity (capacityDerivativeOrder δ)) domain received,
          construction.ambientDim = weightedSupportAmbientDimension δ n k

end ReedSolomon
