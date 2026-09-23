/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Global.Multiplicity
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Index
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.SolutionEmbedding
public import ArkLib.Data.Polynomial.Differential.TotalJetDegreeCount
public import ArkLib.Data.CodingTheory.ReedSolomon.AgreementList

/-!
# List bounds from exact differential interpolants

An exact differential interpolant vanishes after specialization at every message polynomial
with enough agreements. The resulting embedding places the agreement list inside the bounded
solutions of the interpolant. A root count over a degree-three field extension then bounds the
list size in terms of the field size and differential order.

## Main statements

* `differentialSpecialization_eq_zero_of_agreeingPolynomial`: every agreeing message polynomial
  solves an exact interpolant satisfying the local constraints.
* `agreeingPolynomialToBoundedSolution` and `exists_boundedSolution_polynomial_eq`: a canonical
  bounded-solution representative for each agreeing message polynomial.
* `agreeingPolynomialsToBoundedSolution`: the agreement list embeds into the bounded solutions.
* `agreeingPolynomials_encard_le_boundedSolution_natCard` and
  `agreeingPolynomials_encard_le_of_boundedSolution_natCard_le`: cardinality adapters.
* `agreeingPolynomials_encard_le_two_mul_pow_of_exactInterpolant`: the pointwise list bound.

## References

* [DKT26]
-/

@[expose] public section

open PolynomialDifferential

namespace ReedSolomon

noncomputable section

open ListDecoding HiddenDerivative Polynomial

variable {F index : Type*} [Field F] [DecidableEq F] [Fintype index]

/-- Every message polynomial with at least `A` agreements solves an exact interpolant satisfying
the local constraints. -/
theorem differentialSpecialization_eq_zero_of_agreeingPolynomial
    {messageDim D A d m M W : ℕ} (hmessageDim : messageDim ≤ D + 1) (hdD : d < D)
    (domain : index ↪ F) (received : index → F) {Q : DifferentialPolynomial F d}
    (hQspace : Q ∈ exactInterpolationSpace F D A d m M W hdD)
    (hconstraints : ∀ i, SatisfiesLocalConstraints m (domain i) (received i) Q)
    (p : agreeingPolynomials domain messageDim A received) :
    differentialSpecialization Q (p.1 : F[X]) = 0 := by
  classical
  let agreementIndices : Finset index :=
    Finset.univ.filter fun i => (p.1 : F[X]).eval (domain i) = received i
  have hAmbient : (p.1 : F[X]) ∈ Polynomial.degreeLT F (D + 1) :=
    Polynomial.degreeLT_mono hmessageDim p.1.property
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
  exact differentialSpecialization_eq_zero_of_mem_exactInterpolationSpace_of_agreements
    hdD domain received agreementIndices hQspace hconstraints (p.1 : F[X]) hDegree
    domain.injective.injOn hAgreementCard hAgreements

/-- Embed every message polynomial with enough agreements into the bounded solutions of an exact
interpolant satisfying the local constraints. -/
def agreeingPolynomialsToBoundedSolution
    {messageDim D A d m M W : ℕ} (hmessageDim : messageDim ≤ D + 1) (hdD : d < D)
    (domain : index ↪ F) (received : index → F) {Q : DifferentialPolynomial F d}
    (hQspace : Q ∈ exactInterpolationSpace F D A d m M W hdD)
    (hconstraints : ∀ i, SatisfiesLocalConstraints m (domain i) (received i) Q) :
    agreeingPolynomials domain messageDim A received ↪ BoundedSolution Q D :=
  solutionEmbeddingOf Q hmessageDim
    (fun p => differentialSpecialization_eq_zero_of_agreeingPolynomial hmessageDim hdD
      domain received hQspace hconstraints p)

/-- The embedding into bounded solutions retains each agreeing polynomial. -/
@[simp]
theorem agreeingPolynomialsToBoundedSolution_polynomial
    {messageDim D A d m M W : ℕ} (hmessageDim : messageDim ≤ D + 1) (hdD : d < D)
    (domain : index ↪ F) (received : index → F) {Q : DifferentialPolynomial F d}
    (hQspace : Q ∈ exactInterpolationSpace F D A d m M W hdD)
    (hconstraints : ∀ i, SatisfiesLocalConstraints m (domain i) (received i) Q)
    (p : agreeingPolynomials domain messageDim A received) :
    ((agreeingPolynomialsToBoundedSolution hmessageDim hdD domain received hQspace
      hconstraints p).polynomial : F[X]) = (p.1 : F[X]) := by
  exact solutionEmbeddingOf_polynomial Q hmessageDim
    (fun p => differentialSpecialization_eq_zero_of_agreeingPolynomial hmessageDim hdD
      domain received hQspace hconstraints p) p

/-- The canonical bounded-solution representative of an agreeing message polynomial. -/
def agreeingPolynomialToBoundedSolution
    {messageDim D A d m M W : ℕ} (hmessageDim : messageDim ≤ D + 1) (hdD : d < D)
    (domain : index ↪ F) (received : index → F) {Q : DifferentialPolynomial F d}
    (hQspace : Q ∈ exactInterpolationSpace F D A d m M W hdD)
    (hconstraints : ∀ i, SatisfiesLocalConstraints m (domain i) (received i) Q)
    (p : agreeingPolynomials domain messageDim A received) : BoundedSolution Q D :=
  agreeingPolynomialsToBoundedSolution hmessageDim hdD domain received hQspace hconstraints p

/-- The canonical representative has the same underlying message polynomial. -/
@[simp]
theorem agreeingPolynomialToBoundedSolution_polynomial
    {messageDim D A d m M W : ℕ} (hmessageDim : messageDim ≤ D + 1) (hdD : d < D)
    (domain : index ↪ F) (received : index → F) {Q : DifferentialPolynomial F d}
    (hQspace : Q ∈ exactInterpolationSpace F D A d m M W hdD)
    (hconstraints : ∀ i, SatisfiesLocalConstraints m (domain i) (received i) Q)
    (p : agreeingPolynomials domain messageDim A received) :
    (agreeingPolynomialToBoundedSolution hmessageDim hdD domain received hQspace
      hconstraints p).polynomial = (p.1 : F[X]) :=
  agreeingPolynomialsToBoundedSolution_polynomial hmessageDim hdD domain received hQspace
    hconstraints p

/-- Every agreeing message polynomial is the polynomial of a bounded solution. -/
theorem exists_boundedSolution_polynomial_eq
    {messageDim D A d m M W : ℕ} (hmessageDim : messageDim ≤ D + 1) (hdD : d < D)
    (domain : index ↪ F) (received : index → F) {Q : DifferentialPolynomial F d}
    (hQspace : Q ∈ exactInterpolationSpace F D A d m M W hdD)
    (hconstraints : ∀ i, SatisfiesLocalConstraints m (domain i) (received i) Q)
    (p : agreeingPolynomials domain messageDim A received) :
    ∃ solution : BoundedSolution Q D, solution.polynomial = (p.1 : F[X]) :=
  ⟨agreeingPolynomialToBoundedSolution hmessageDim hdD domain received hQspace hconstraints p,
    agreeingPolynomialToBoundedSolution_polynomial hmessageDim hdD domain received hQspace
      hconstraints p⟩

/-- The agreement-list cardinality is bounded by the natural cardinality of the bounded
solutions. -/
theorem agreeingPolynomials_encard_le_boundedSolution_natCard [Finite F]
    {messageDim D A d m M W : ℕ} (hmessageDim : messageDim ≤ D + 1) (hdD : d < D)
    (domain : index ↪ F) (received : index → F) {Q : DifferentialPolynomial F d}
    (hQspace : Q ∈ exactInterpolationSpace F D A d m M W hdD)
    (hconstraints : ∀ i, SatisfiesLocalConstraints m (domain i) (received i) Q) :
    (agreeingPolynomials domain messageDim A received).encard ≤
      (Nat.card (BoundedSolution Q D) : ℕ∞) := by
  calc
    (agreeingPolynomials domain messageDim A received).encard
        ≤ ENat.card (BoundedSolution Q D) :=
      ENat.card_le_card_of_injective
        (agreeingPolynomialsToBoundedSolution hmessageDim hdD domain received hQspace
          hconstraints).injective
    _ = (Nat.card (BoundedSolution Q D) : ℕ∞) := ENat.card_eq_coe_natCard _

/-- Any natural-number bound on the bounded solutions also bounds the agreement list. -/
theorem agreeingPolynomials_encard_le_of_boundedSolution_natCard_le [Finite F]
    {messageDim D A d m M W listBound : ℕ}
    (hmessageDim : messageDim ≤ D + 1) (hdD : d < D)
    (domain : index ↪ F) (received : index → F) {Q : DifferentialPolynomial F d}
    (hQspace : Q ∈ exactInterpolationSpace F D A d m M W hdD)
    (hconstraints : ∀ i, SatisfiesLocalConstraints m (domain i) (received i) Q)
    (hroot : Nat.card (BoundedSolution Q D) ≤ listBound) :
    (agreeingPolynomials domain messageDim A received).encard ≤ (listBound : ℕ∞) :=
  (agreeingPolynomials_encard_le_boundedSolution_natCard hmessageDim hdD domain received
    hQspace hconstraints).trans (ENat.natCast_le_natCast.mpr hroot)

/-- Let `Q` be a nonzero member of the exact interpolation space at degree `K - 1` and order `d`.
If `d < K - 1`, `Q` satisfies the local constraints, its jet degrees satisfy the cast hypotheses,
the binomial coefficients required by the root count are nonzero, and `m * A ≤ |F|²`, then
the agreement list has extended cardinality at most `2 * (d + 1) * |F|^(3 * d + 2)`. -/
theorem agreeingPolynomials_encard_le_two_mul_pow_of_exactInterpolant [Finite F]
    {messageDim K A d m M W : ℕ} (hK : 0 < K) (hmessageDim : messageDim ≤ K)
    (hdK : d < K - 1)
    (domain : index ↪ F) (received : index → F) {Q : DifferentialPolynomial F d}
    (hQ : Q ≠ 0)
    (hQspace : Q ∈ exactInterpolationSpace F (K - 1) A d m M W hdK)
    (hconstraints : ∀ i, SatisfiesLocalConstraints m (domain i) (received i) Q)
    (hcast : ∀ j, JetDegreeCastsNeZero Q j)
    (hbinom : ∀ k s, 0 < k → k + s ≤ K - 1 → ((k + s).choose s : F) ≠ 0)
    (hfield : m * A ≤ Nat.card F ^ 2) :
    (agreeingPolynomials domain messageDim A received).encard ≤
      (2 * (d + 1) * Nat.card F ^ (3 * d + 2) : ℕ∞) := by
  have hbudget : 0 < m * A := by
    by_contra h
    have hzero : m * A = 0 := Nat.eq_zero_of_not_pos h
    exact hQ (eq_zero_of_mem_exactInterpolationSpace_of_mul_eq_zero hzero hdK hQspace)
  have hmessageAmbient : messageDim ≤ (K - 1) + 1 := by
    simpa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hK))]
      using hmessageDim
  have hweighted : differentialWeightedDegree (K - 1) Q < m * A :=
    differentialWeightedDegree_lt_of_mem_exactInterpolationSpace hbudget hdK hQspace
  have hweight : differentialWeightedDegree (K - 1) Q - ((K - 1) - d) ≤ m * A :=
    (Nat.sub_le _ _).trans (Nat.le_of_lt hweighted)
  have hjet : jetTotalDegree Q ≤ Nat.card F ^ 2 := by
    apply (jetTotalDegree_le_floor_of_mem_exactInterpolationSpace hdK hQspace).trans
    apply (Nat.div_le_self _ _).trans
    exact (Nat.sub_le _ _).trans hfield
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have hlarge : 2 * (m * A) ≤ Nat.card F ^ 3 := by
    calc
      2 * (m * A) ≤ 2 * Nat.card F ^ 2 := Nat.mul_le_mul_left 2 hfield
      _ ≤ Nat.card F * Nat.card F ^ 2 := Nat.mul_le_mul_right _ hq
      _ = Nat.card F ^ 3 := by ring
  have hroot := BoundedSolution.natCard_le_two_mul_jetTotalDegree_mul_extension
    hQ hcast hbinom hweight (e := 3) (by decide) hlarge
  have hbound : Nat.card (BoundedSolution Q (K - 1)) ≤
      2 * (d + 1) * Nat.card F ^ (3 * d + 2) := by
    calc
      Nat.card (BoundedSolution Q (K - 1)) ≤
          2 * jetTotalDegree Q * Nat.card F ^ (3 * d) := hroot
      _ ≤ 2 * Nat.card F ^ 2 * Nat.card F ^ (3 * d) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hjet)
      _ = 2 * Nat.card F ^ (3 * d + 2) := by
        rw [pow_add]
        ring
      _ ≤ 2 * (d + 1) * Nat.card F ^ (3 * d + 2) := by
        apply Nat.mul_le_mul_right _
        calc
          2 = 2 * 1 := by ring
          _ ≤ 2 * (d + 1) := Nat.mul_le_mul_left 2 (by omega)
  exact agreeingPolynomials_encard_le_of_boundedSolution_natCard_le hmessageAmbient hdK
    domain received hQspace hconstraints hbound

end

end ReedSolomon
