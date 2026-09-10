/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.Interpolation.Solution.Basis
public import
ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.WeightedSupportInterpolant
/-!
# Weighted-support witnesses in the executable interpolation search

The mathematical weighted-support constructor returns the two strict bounds that define the
finite support enumerated by the decoder. This module converts those bounds into the executable
`Eligible` predicate and places the prescribed ambient degree inside the descending search range.
-/

@[expose] public section

open PolynomialDifferential

namespace ReedSolomon.HiddenDerivative

noncomputable section

open ReedSolomon ListDecoding

variable {F : Type*} [Field F]

/-- Strict total-jet and differential-weight bounds imply membership in the executable support
with strict jet cutoff `J`. -/
theorem weightedSupport_witness_eligibleWithBudget {D d m J A : ℕ}
    (Q : DifferentialPolynomial F d) (htotal : jetTotalDegree Q < J)
    (hweight : differentialWeightedDegree D Q < m * A) :
    NonzeroInterpolationMachine.EligibleWithBudget D m J A Q := by
  apply (NonzeroInterpolationMachine.eligibleWithBudget_iff D m J A Q).mpr
  intro u hu
  constructor
  · exact ((jetTotalDegree_le_iff Q _).mp le_rfl u hu).trans_lt htotal
  · have huweight :=
      (MvPolynomial.le_weightedTotalDegree (differentialWeight D) hu).trans_lt hweight
    change exactInterpolationMonomialWeight D u < m * A at huweight
    simpa [exactInterpolationMonomialWeight_eq, Finsupp.weight_apply,
      Finsupp.sum_fintype, mul_comm] using huweight

/-- A weak paper degree cap `≤ ν` is contained by the strict executable cutoff `ν + 1`. -/
theorem weightedSupport_witness_eligible_succ {D d m A ν : ℕ}
    (Q : DifferentialPolynomial F d) (htotal : jetTotalDegree Q ≤ ν)
    (hweight : differentialWeightedDegree D Q < m * A) :
    NonzeroInterpolationMachine.EligibleWithBudget D m (ν + 1) A Q := by
  exact weightedSupport_witness_eligibleWithBudget Q (by omega) hweight

/-- Legacy executable eligibility specializes the strict cutoff to `2 * m`. -/
theorem weightedSupport_witness_eligible {D d m A : ℕ}
    (Q : DifferentialPolynomial F d) (htotal : jetTotalDegree Q < 2 * m)
    (hweight : differentialWeightedDegree D Q < m * A) :
    NonzeroInterpolationMachine.Eligible D m A Q := by
  have h := weightedSupport_witness_eligibleWithBudget Q htotal hweight
  simpa [NonzeroInterpolationMachine.Eligible,
    NonzeroInterpolationMachine.EligibleWithBudget,
    ReceivedInterpolationMatrixMachine.support] using h

/-- The prescribed no-band interpolant is a successful candidate in the decoder's finite
descending ambient search. The actual agreement input may exceed the canonical threshold. -/
theorem prescribed_weightedSupport_eligible_candidate
    {q : ℕ} [Fact q.Prime] (delta : ℝ) (hdelta : 0 < delta)
    (hquarter : delta < (1 / 4 : ℝ)) (n k A : ℕ)
    (hblock : 8 * weightedSupportMultiplicity delta ≤ n) (hk : 0 < k)
    (_hkn : k ≤ n) (hA : ReedSolomon.agreementThreshold delta n k ≤ A) (hAn : A ≤ n)
    (domain : Fin n ↪ ZMod q) (received : Fin n → ZMod q) (hnq : n ≤ q) :
    let d := capacityDerivativeOrder delta
    let m := weightedSupportMultiplicity delta
    let D := weightedSupportAmbientDimension delta n k - 1
    max (k - 1) (d + 1) ≤ D ∧ D < n ∧
      ∃ Q : DifferentialPolynomial (ZMod q) d,
        Q ≠ 0 ∧ NonzeroInterpolationMachine.Eligible D m A Q ∧
          ∀ p ∈ List.ofFn (fun i => (domain i, received i)),
            localConstraintAt m p.1 p.2 Q = 0 := by
  let d := capacityDerivativeOrder delta
  let m := weightedSupportMultiplicity delta
  let K := weightedSupportAmbientDimension delta n k
  let D := K - 1
  obtain ⟨construction, hK, htotal⟩ :=
    exists_prescribed_weightedSupport_construction domain received hdelta hquarter hk hblock hnq
      (hA.trans hAn)
  have hkK : k ≤ K := by simpa only [K, hK] using construction.messageDim_le
  have hKn : K ≤ n := by simpa only [K, hK] using construction.ambientDim_le
  have hdD : d < D := by simpa only [d, D, K, hK] using construction.order_lt_degree
  have hweight : differentialWeightedDegree D construction.interpolant < m * A := by
    have hcanonical := construction.weighted_degree_lt
    have hcanonical' : differentialWeightedDegree D construction.interpolant <
        m * ReedSolomon.agreementThreshold delta n k := by
      simpa only [D, K, hK, m] using hcanonical
    have hmono : m * ReedSolomon.agreementThreshold delta n k ≤ m * A :=
      Nat.mul_le_mul_left m hA
    exact hcanonical'.trans_le hmono
  refine ⟨by omega, by omega, construction.interpolant, construction.nonzero,
    weightedSupport_witness_eligible construction.interpolant
      (by simpa only [d, m] using htotal) hweight, ?_⟩
  intro p hp
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
  exact construction.local_constraints i

end

end ReedSolomon.HiddenDerivative
