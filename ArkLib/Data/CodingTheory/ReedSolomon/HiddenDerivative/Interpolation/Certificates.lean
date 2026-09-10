/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.WeightedSupport.Capacity
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Global.Multiplicity
public import Mathlib.Algebra.Field.ZMod
public import ArkLib.Data.CodingTheory.ReedSolomon.ListSpecification
/-!
# Hidden-derivative interpolation witnesses

The propositions in `ListDecodability/Capacity/Basic.lean` do not certify a proof method. This file
ties the order parameter to a nonzero differential polynomial, local interpolation constraints,
weighted specialization degree, and the characteristic conditions for differential root finding.
Order `d` means that the construction uses derivatives of order at most `d`; it need not depend
nontrivially on the last variable. Changing `d` changes the type of the interpolant and its local
constraints, not merely a numerical exponent in a list bound.

These are existence statements, not executable algorithms. The uniform capacity decoding theorem
additionally requires a decoder with proved output refinement and bit complexity.

## References

* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding and Mutual Correlated Agreement
  up to Capacity*][DKTZ26], weighted-support interpolation and uniform capacity decoding.
* [Brakensiek, Chen, Putterman, Zhang, and Zheng, *Algorithmic List Decoding of Reed-Solomon
  Codes up to Capacity in the Low-Rate Regime*][BCPZZ26], hidden-derivative interpolation.
-/

@[expose] public section

open PolynomialDifferential


namespace ReedSolomon

open HiddenDerivative ListDecoding Polynomial

noncomputable section

/-- A genuine order-at-most-`d` hidden-derivative interpolant for one received word.
The polynomial and constraints depend on the same `d` and `m`. The message dimension is distinct
from the ambient dimension used for interpolation and root counting. -/
structure HiddenDerivativeInterpolationCertificate {n q k A : ℕ} (d m : ℕ)
    (domain : Fin n ↪ ZMod q) (received : Fin n → ZMod q) where
  /-- Ambient message dimension, so the ambient degree is `ambientDim - 1`. -/
  ambientDim : ℕ
  messageDim_le : k ≤ ambientDim
  ambientDim_le : ambientDim ≤ n
  order_lt_degree : d < ambientDim - 1
  /-- Actual differential polynomial with jet variables indexed by `Fin (d + 1)`. -/
  interpolant : DifferentialPolynomial (ZMod q) d
  nonzero : interpolant ≠ 0
  weighted_degree_lt : differentialWeightedDegree (ambientDim - 1) interpolant < m * A
  below_characteristic : IsBelowCharacteristic (ambientDim - 1) interpolant
  contact_budget_le : m * A ≤ q ^ 2
  local_constraints : ∀ i, SatisfiesLocalConstraints m (domain i) (received i) interpolant

/-- The required differential identity follows from the construction's local constraints and
degree bound. It is not a second independent witness field. -/
theorem HiddenDerivativeInterpolationCertificate.specializes_to_zero
    {n q k A d m : ℕ} [Fact q.Prime] {domain : Fin n ↪ ZMod q}
    {received : Fin n → ZMod q}
    (construction : HiddenDerivativeInterpolationCertificate (k := k) (A := A) d m domain received)
    (P : MessagePolynomial (ZMod q) k)
    (hAgreement : A ≤ Code.agree (ReedSolomon.evalOnPoints domain P) received) :
    differentialSpecialization construction.interpolant (P : (ZMod q)[X]) = 0 := by
  classical
  let indices := Finset.univ.filter fun i ↦ (P : (ZMod q)[X]).eval (domain i) = received i
  have hP : (P : (ZMod q)[X]).natDegree ≤ construction.ambientDim - 1 := by
    by_cases hp : (P : (ZMod q)[X]) = 0
    · simp [hp]
    · have hdeg := (Polynomial.natDegree_lt_iff_degree_lt hp).mpr
        (Polynomial.mem_degreeLT.mp
          (Polynomial.degreeLT_mono construction.messageDim_le P.property))
      omega
  apply differentialSpecialization_eq_zero_of_global_multiplicity
    domain indices m A construction.interpolant (P : (ZMod q)[X])
    domain.injective.injOn
  · exact hAgreement
  · intro i hi
    exact X_sub_C_pow_dvd_differentialSpecialization_of_contact
      construction.interpolant (P : (ZMod q)[X]) (domain i) (received i)
      (Finset.mem_filter.mp hi).2 (construction.local_constraints i)
  · exact (natDegree_differentialSpecialization_le _ _ hP).trans_lt
      construction.weighted_degree_lt

/-- Uniform construction target, separate from the polynomial-list target. Both the derivative
order and multiplicity are selected before every code parameter and received word. Only feasible
agreement thresholds require an interpolant; oversized thresholds are handled by empty lists. -/
def UniformHiddenDerivativeInterpolation : Prop :=
  ∀ delta : ℝ, 0 < delta → delta < 1 →
    ∃ d m N : ℕ, 0 < m ∧ ∀ n k q : ℕ,
      N ≤ n → 0 < k → k ≤ n → q.Prime → n ≤ q →
      agreementThreshold delta n k ≤ n →
      ∀ (domain : Fin n ↪ ZMod q) (received : Fin n → ZMod q),
        Nonempty (HiddenDerivativeInterpolationCertificate (k := k)
          (A := agreementThreshold delta n k) d m domain received)

/-- Weighted-support interpolants at the prescribed order, multiplicity, ambient dimension, and
block threshold. The order indexes an actual differential polynomial and its local constraints. -/
def WeightedSupportConstruction : Prop :=
  ∀ delta : ℝ, 0 < delta → delta < (1 / 4 : ℝ) →
    ∀ n k q : ℕ, 8 * weightedSupportMultiplicity delta ≤ n →
      0 < k → k ≤ n → q.Prime → n ≤ q → agreementThreshold delta n k ≤ n →
      ∀ (domain : Fin n ↪ ZMod q) (received : Fin n → ZMod q),
        ∃ construction : HiddenDerivativeInterpolationCertificate (k := k)
            (A := agreementThreshold delta n k)
            (capacityDerivativeOrder delta) (weightedSupportMultiplicity delta) domain received,
          construction.ambientDim = weightedSupportAmbientDimension delta n k

end
end ReedSolomon
