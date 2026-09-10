/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.Basic
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Global.Multiplicity
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FiniteField.ExtensionRootCount
/-!
# Pointwise list bounds from a hidden-derivative interpolant

This file connects the canonical set of agreeing Reed--Solomon message polynomials to differential
root counting.  A target polynomial retains its original strict degree bound while the generic
embedding places it in an ambient degree bound `D`.  The final theorem instantiates `D = K - 1`
from `messageDim ≤ K`.

The first theorem packages each agreeing polynomial as a bounded solution of the exact interpolant.
The cardinality adapters then compare the canonical point list directly with the bounded-solution
type.  The final theorem applies the unconditional differential root count.  It makes no claim
about computing the list or the running time of a decoder.
-/

@[expose] public section

open PolynomialDifferential


namespace ReedSolomon

noncomputable section

open ListDecoding HiddenDerivative Polynomial

variable {F index : Type*}

set_option maxHeartbeats 800000 in
-- Checking the dependent exact-interpolation proof crosses the full local-contact and I6 layers.
/-- Each target-degree polynomial with at least `A` agreements has a bounded-solution
representative with the same underlying polynomial. -/
theorem exists_boundedSolution_polynomial_eq [Field F] [DecidableEq F] [Fintype index]
    {messageDim D A d m M W : ℕ}
    (hmessageDim : messageDim ≤ D + 1)
    (hbudget : 0 < m * A) (hdD : d < D)
    (domain : index ↪ F) (received : index → F)
    {Q : DifferentialPolynomial F d}
    (hQspace : Q ∈ exactInterpolationSpace F D A d m M W hdD)
    (hconstraints : ∀ i, SatisfiesLocalConstraints m (domain i) (received i) Q)
    (p : agreeingPolynomials domain messageDim A received) :
    ∃ solution : BoundedSolution Q D, solution.polynomial = p.1 := by
  let agreementIndices : Finset index :=
    Finset.univ.filter fun i => (p.1 : F[X]).eval (domain i) = received i
  have hAmbient : (p.1 : F[X]) ∈ Polynomial.degreeLT F (D + 1) :=
    Polynomial.degreeLT_mono hmessageDim p.1.2
  let _ : NeZero (D + 1) := ⟨Nat.succ_ne_zero D⟩
  have hDegree : (p.1 : F[X]).natDegree ≤ D :=
    Nat.lt_succ_iff.mp (ReedSolomon.natDegree_lt_of_mem_degreeLT hAmbient)
  have hAgreementCard : A ≤ agreementIndices.card := by
    have hp := p.property
    change A ≤ Code.agree (ReedSolomon.evalOnPoints domain p.1) received at hp
    unfold Code.agree at hp
    change A ≤ agreementIndices.card at hp
    exact hp
  have hAgreements : ∀ i ∈ agreementIndices,
      (p.1 : F[X]).eval (domain i) = received i := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  refine ⟨⟨⟨p.1, hAmbient⟩, ?_⟩, rfl⟩
  exact differentialSpecialization_eq_zero_of_mem_exactInterpolationSpace_of_agreements
    hbudget hdD domain received agreementIndices hQspace hconstraints p.1 hDegree
    domain.injective.injOn hAgreementCard hAgreements

/-- Choose the canonical bounded-solution representative whose polynomial is the given agreeing
polynomial. -/
def agreeingPolynomialToBoundedSolution [Field F] [DecidableEq F] [Fintype index]
    {messageDim D A d m M W : ℕ}
    (hmessageDim : messageDim ≤ D + 1)
    (hbudget : 0 < m * A) (hdD : d < D)
    (domain : index ↪ F) (received : index → F)
    {Q : DifferentialPolynomial F d}
    (hQspace : Q ∈ exactInterpolationSpace F D A d m M W hdD)
    (hconstraints : ∀ i, SatisfiesLocalConstraints m (domain i) (received i) Q)
    (p : agreeingPolynomials domain messageDim A received) : BoundedSolution Q D :=
  Classical.choose (exists_boundedSolution_polynomial_eq hmessageDim hbudget hdD domain received
    hQspace hconstraints p)

@[simp]
theorem agreeingPolynomialToBoundedSolution_polynomial [Field F] [DecidableEq F]
    [Fintype index] {messageDim D A d m M W : ℕ}
    (hmessageDim : messageDim ≤ D + 1)
    (hbudget : 0 < m * A) (hdD : d < D)
    (domain : index ↪ F) (received : index → F)
    {Q : DifferentialPolynomial F d}
    (hQspace : Q ∈ exactInterpolationSpace F D A d m M W hdD)
    (hconstraints : ∀ i, SatisfiesLocalConstraints m (domain i) (received i) Q)
    (p : agreeingPolynomials domain messageDim A received) :
    (agreeingPolynomialToBoundedSolution hmessageDim hbudget hdD domain received
      hQspace hconstraints p).polynomial = p.1 :=
  Classical.choose_spec (exists_boundedSolution_polynomial_eq hmessageDim hbudget hdD
    domain received hQspace hconstraints p)

/-- Every target-degree polynomial with at least `A` agreements embeds into the bounded solutions
of the exact interpolant.  The embedding preserves the underlying polynomial. -/
def agreeingPolynomialsToBoundedSolution [Field F] [DecidableEq F] [Fintype index]
    {messageDim D A d m M W : ℕ}
    (hmessageDim : messageDim ≤ D + 1)
    (hbudget : 0 < m * A) (hdD : d < D)
    (domain : index ↪ F) (received : index → F)
    {Q : DifferentialPolynomial F d}
    (hQspace : Q ∈ exactInterpolationSpace F D A d m M W hdD)
    (hconstraints : ∀ i, SatisfiesLocalConstraints m (domain i) (received i) Q) :
    agreeingPolynomials domain messageDim A received ↪ BoundedSolution Q D where
  toFun := agreeingPolynomialToBoundedSolution hmessageDim hbudget hdD domain received
    hQspace hconstraints
  inj' p q hpq := by
    apply Subtype.ext
    apply Subtype.ext
    have h := congrArg (fun r : BoundedSolution Q D ↦ r.polynomial) hpq
    simpa only [agreeingPolynomialToBoundedSolution_polynomial] using h

/-- The canonical point list injects into the bounded differential solutions.  This statement is
kept separate from any root-count estimate so stronger future root bounds compose without changing
the Reed--Solomon frontend. -/
theorem agreeingPolynomials_encard_le_boundedSolution_natCard [Field F] [Finite F]
    [DecidableEq F] [Fintype index]
    {messageDim D A d m M W : ℕ}
    (hmessageDim : messageDim ≤ D + 1)
    (hbudget : 0 < m * A) (hdD : d < D)
    (domain : index ↪ F) (received : index → F)
    {Q : DifferentialPolynomial F d}
    (hQspace : Q ∈ exactInterpolationSpace F D A d m M W hdD)
    (hconstraints : ∀ i, SatisfiesLocalConstraints m (domain i) (received i) Q) :
    (agreeingPolynomials domain messageDim A received).encard ≤
      (Nat.card (BoundedSolution Q D) : ℕ∞) := by
  calc
    (agreeingPolynomials domain messageDim A received).encard
        ≤ ENat.card (BoundedSolution Q D) :=
      ENat.card_le_card_of_injective
        (agreeingPolynomialsToBoundedSolution hmessageDim hbudget hdD domain received
          hQspace hconstraints).injective
    _ = (Nat.card (BoundedSolution Q D) : ℕ∞) :=
      ENat.card_eq_coe_natCard _

/-- A conditional adapter from any natural-number bound on the bounded solutions to the canonical
point-list bound. -/
theorem agreeingPolynomials_encard_le_of_boundedSolution_natCard_le [Field F] [Finite F]
    [DecidableEq F] [Fintype index]
    {messageDim D A d m M W listBound : ℕ}
    (hmessageDim : messageDim ≤ D + 1)
    (hbudget : 0 < m * A) (hdD : d < D)
    (domain : index ↪ F) (received : index → F)
    {Q : DifferentialPolynomial F d}
    (hQspace : Q ∈ exactInterpolationSpace F D A d m M W hdD)
    (hconstraints : ∀ i, SatisfiesLocalConstraints m (domain i) (received i) Q)
    (hroot : Nat.card (BoundedSolution Q D) ≤ listBound) :
    (agreeingPolynomials domain messageDim A received).encard ≤ (listBound : ℕ∞) :=
  (agreeingPolynomials_encard_le_boundedSolution_natCard hmessageDim hbudget hdD
    domain received hQspace hconstraints).trans (ENat.natCast_le_natCast.mpr hroot)

/-- A nonzero exact interpolant gives the canonical pointwise Reed--Solomon list bound after the
characteristic and field-size budgets needed by differential root counting are discharged. -/
theorem agreeingPolynomials_encard_le_two_mul_pow_of_exactInterpolant [Field F] [Finite F]
    [DecidableEq F] [Fintype index]
    {messageDim K A d m M W : ℕ}
    (hK : 0 < K) (hmessageDim : messageDim ≤ K)
    (hbudget : 0 < m * A) (hdK : d < K - 1)
    (domain : index ↪ F) (received : index → F)
    {Q : DifferentialPolynomial F d}
    (hQ : Q ≠ 0)
    (hQspace : Q ∈ exactInterpolationSpace F (K - 1) A d m M W hdK)
    (hconstraints : ∀ i, SatisfiesLocalConstraints m (domain i) (received i) Q)
    (hchar : IsBelowCharacteristic (K - 1) Q)
    (hfield : m * A ≤ Nat.card F ^ 2) :
    (agreeingPolynomials domain messageDim A received).encard ≤
      (2 * (d + 1) * Nat.card F ^ (3 * d + 2) : ℕ) := by
  have hmessageAmbient : messageDim ≤ (K - 1) + 1 := by
    simpa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hK))]
      using hmessageDim
  apply agreeingPolynomials_encard_le_of_boundedSolution_natCard_le
      hmessageAmbient hbudget hdK domain received hQspace hconstraints
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have hlarge : 2 * Nat.card F ^ 2 ≤ Nat.card F ^ 3 := by
    calc
      2 * Nat.card F ^ 2 ≤ Nat.card F * Nat.card F ^ 2 :=
        Nat.mul_le_mul_right (Nat.card F ^ 2) hq
      _ = Nat.card F ^ 3 := by ring
  have hroot := natCard_boundedSolution_le_extension_pow_of_weightedDegree
    Q 3 (Nat.card F ^ 2) (by decide) hQ hchar
    ((differentialWeightedDegree_lt_of_mem_exactInterpolationSpace
      hbudget hdK hQspace).le.trans hfield) hlarge
  convert hroot using 1
  ring

end

end ReedSolomon
