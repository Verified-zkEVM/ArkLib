/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.PowerAgreement
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerTupleCounting
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerBatchedPointRecognition
/-!
# Finite families of admissible Frobenius power tuples

The retained family consists of common-sample interpolants satisfying the Frobenius chart
identities. Its size is bounded by the initial equation's graph-coordinate degree, and one
exceptional challenge set controls exact power agreement for every retained tuple.

## Main statements

* `ReedSolomon.frobeniusRetainedPowerTupleFamily` and
  `ReedSolomon.mem_frobeniusRetainedPowerTupleFamily_iff`: the finite family of admissible
  interpolants and its membership characterization.
* `ReedSolomon.frobeniusRetainedPowerTupleFamily_card_le`: a bound by the initial equation's
  degree in the graph coordinate.
* `ReedSolomon.exists_exceptional_frobeniusRetainedPowerTupleFamily`: one exceptional set gives
  exact power agreement for every retained tuple.

## References

* [DKT26]
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial PolynomialDifferential

variable {F E α : Type*} [Field F] [Field E] [Fintype α] {k K ℓ : ℕ}

/-- The sample interpolants that satisfy the Frobenius graph identities. -/
def frobeniusRetainedPowerTupleFamily
    (domain : α ↪ F) (values : Fin (ℓ + 1) → α → F)
    (ι : F →+* E) (roots : α → E) (center : E)
    (Q : DifferentialPolynomial E[X] 0) (K k τ s : ℕ) :
    Finset (Fin (ℓ + 1) → F[X]) := by
  classical
  exact (polynomialTupleFamily domain values k).filter
    (IsAdmissibleFrobeniusPowerTuple domain values ι roots center Q K k τ s)

/-- Membership in the retained family is equivalent to Frobenius admissibility. -/
theorem mem_frobeniusRetainedPowerTupleFamily_iff
    (domain : α ↪ F) (values : Fin (ℓ + 1) → α → F)
    (ι : F →+* E) (roots : α → E) (center : E)
    (Q : DifferentialPolynomial E[X] 0) (K k τ s : ℕ)
    (P : Fin (ℓ + 1) → F[X]) :
    P ∈ frobeniusRetainedPowerTupleFamily
      domain values ι roots center Q K k τ s ↔
      IsAdmissibleFrobeniusPowerTuple domain values ι roots center Q K k τ s P := by
  classical
  constructor
  · exact fun h ↦ (Finset.mem_filter.mp h).2
  · intro hP
    obtain ⟨sample, hcard, hagree, _⟩ := hP.sample
    have hcommon : k ≤ (commonCurveAgreementSet domain values P).card := by
      rw [← hcard]
      apply Finset.card_le_card
      intro i hi
      simpa only [commonCurveAgreementSet, Finset.mem_filter, Finset.mem_univ,
        true_and] using hagree i hi
    exact Finset.mem_filter.mpr
      ⟨(mem_polynomialTupleFamily_iff domain values P k).mpr ⟨hP.degree, hcommon⟩, hP⟩

/-- If the initial equation is nonzero and the root, degree, and Taylor-exponent hypotheses hold,
the retained family with `s = p ^ e` has cardinality at most the initial equation's degree in the
graph coordinate. -/
theorem frobeniusRetainedPowerTupleFamily_card_le [Infinite E]
    (domain : α ↪ F) (values : Fin (ℓ + 1) → α → F) (ι : F →+* E)
    (roots : α → E) (center : E) (Q : DifferentialPolynomial E[X] 0)
    (p e τ : ℕ) [ExpChar E p]
    (hroots : ∀ i, roots i ^ (p ^ e) = ι (domain i))
    (hK : 0 < K) (hKk : K ≤ p ^ e * k) (hτ : TaylorExponentSufficient 0 K τ)
    (hinit : jointInitialJetEquation center Q ≠ 0) :
    (frobeniusRetainedPowerTupleFamily
      domain values ι roots center Q K k τ (p ^ e)).card ≤
      (jointInitialJetEquation center Q).degreeOf (some 0) := by
  apply admissibleFrobeniusPowerTuples_card_le_degreeOf
    domain values ι roots center Q p e τ hroots hK hKk hτ hinit
  intro P hP
  exact (mem_frobeniusRetainedPowerTupleFamily_iff
    domain values ι roots center Q K k τ (p ^ e) P).mp hP

open Classical in
/-- One exceptional set controls exact power agreement for every retained tuple, with at most
`ℓ * (|α| - k)` challenges per tuple. -/
theorem exists_exceptional_frobeniusRetainedPowerTupleFamily
    (domain : α ↪ F) (values : Fin (ℓ + 1) → α → F)
    (ι : F →+* E) (roots : α → E) (center : E)
    (Q : DifferentialPolynomial E[X] 0) (K k τ s : ℕ) :
    ∃ exceptional : Finset E,
      exceptional.card ≤ ℓ * (Fintype.card α - k) *
        (frobeniusRetainedPowerTupleFamily
          domain values ι roots center Q K k τ s).card ∧
      ∀ P ∈ frobeniusRetainedPowerTupleFamily
        domain values ι roots center Q K k τ s,
        ∀ z ∉ exceptional,
          HasExactPowerAgreement domain values ι k z
            (powerBatchedPolynomial (fun t ↦ (P t).map ι) z) := by
  classical
  let tuples := frobeniusRetainedPowerTupleFamily
    domain values ι roots center Q K k τ s
  have hdegree : ∀ P ∈ tuples, ∀ t, (P t).degree < k := by
    intro P hP
    exact ((mem_frobeniusRetainedPowerTupleFamily_iff
      domain values ι roots center Q K k τ s P).mp hP).degree
  have hcommon : ∀ P ∈ tuples, k ≤ (commonCurveAgreementSet domain values P).card := by
    intro P hP
    have hP' := (mem_frobeniusRetainedPowerTupleFamily_iff
      domain values ι roots center Q K k τ s P).mp hP
    obtain ⟨sample, hcard, hagree, _⟩ := hP'.sample
    rw [← hcard]
    apply Finset.card_le_card
    intro i hi
    simpa only [commonCurveAgreementSet, Finset.mem_filter, Finset.mem_univ,
      true_and] using hagree i hi
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_exceptional_exactPowerAgreement_family
      (k := k) (L := k) domain values ι tuples hdegree hcommon
  refine ⟨exceptional, ?_, ?_⟩
  · simpa [tuples, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hcard
  · intro P hP z hz
    exact hgood P hP z hz

end ReedSolomon
