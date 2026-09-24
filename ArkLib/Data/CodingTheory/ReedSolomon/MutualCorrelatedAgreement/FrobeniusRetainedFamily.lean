/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FrobeniusAdmissibility
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Pairs.ExceptionalSet
/-!
# Finite families of admissible Frobenius pairs

The retained family filters the sample interpolants to pairs satisfying the Frobenius graph
identities. Its size is bounded by the initial equation's graph-coordinate degree, and one
exceptional challenge set controls the agreement behavior of every retained pair.

## Main statements

* `ReedSolomon.frobeniusRetainedPairFamily`: interpolant pairs satisfying Frobenius admissibility.
* `ReedSolomon.mem_frobeniusRetainedPairFamily_iff`: membership is equivalent to admissibility.
* `ReedSolomon.frobeniusRetainedPairFamily_card_le`: a bound by the initial equation's degree in
  the graph coordinate.
* `ReedSolomon.exists_exceptional_frobeniusRetainedPairFamily`: one exceptional set for the
  agreement behavior of all retained pairs.

## References

* [DKT26]
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial PolynomialDifferential

variable {F E ι : Type*} [Field F] [Field E] [Fintype ι] {k K : ℕ}

/-- The sample interpolants that satisfy the Frobenius graph identities. -/
def frobeniusRetainedPairFamily
    (domain : ι ↪ F) (f g : ι → F) (φ : F →+* E) (roots : ι → E)
    (center : E) (Q : DifferentialPolynomial E[X] 0) (K k τ s : ℕ) :
    Finset (F[X] × F[X]) := by
  classical
  exact (correlatedPairFamily domain f g k).filter fun P ↦
    IsAdmissibleFrobeniusPair domain f g φ roots center Q K k τ s P.1 P.2

/-- Membership in the retained family is equivalent to Frobenius admissibility. -/
theorem mem_frobeniusRetainedPairFamily_iff
    (domain : ι ↪ F) (f g : ι → F) (φ : F →+* E) (roots : ι → E)
    (center : E) (Q : DifferentialPolynomial E[X] 0) (K k τ s : ℕ)
    (P : F[X] × F[X]) :
    P ∈ frobeniusRetainedPairFamily domain f g φ roots center Q K k τ s ↔
      IsAdmissibleFrobeniusPair domain f g φ roots center Q K k τ s P.1 P.2 := by
  classical
  constructor
  · exact fun hP ↦ (Finset.mem_filter.mp hP).2
  · intro hP
    change P ∈ (correlatedPairFamily domain f g k).filter
      (fun P ↦ IsAdmissibleFrobeniusPair domain f g φ roots center Q K k τ s P.1 P.2)
    apply Finset.mem_filter.mpr
    refine ⟨(mem_correlatedPairFamily_iff domain f g P).mpr ?_, hP⟩
    obtain ⟨sample, hcard, hagree⟩ := hP.sample
    refine ⟨hP.degree_left, hP.degree_right, ?_⟩
    rw [← hcard]
    apply Finset.card_le_card
    intro i hi
    exact (mem_commonPolynomialAgreementSet domain f g P.1 P.2 i).mpr
      ⟨(hagree i hi).2.1, (hagree i hi).2.2.1⟩

/-- If `E` is infinite, `ExpChar E p` holds, `0 < K`, `K ≤ p ^ e * k`,
`TaylorExponentSufficient 0 K τ` holds, and the initial equation is nonzero, then the retained
family with `s = p ^ e` has cardinality at most its degree in the graph coordinate. -/
theorem frobeniusRetainedPairFamily_card_le
    [Infinite E] (domain : ι ↪ F) (f g : ι → F) (φ : F →+* E) (roots : ι → E)
    (center : E) (Q : DifferentialPolynomial E[X] 0) (p e τ : ℕ) [ExpChar E p]
    (hK : 0 < K) (hKk : K ≤ p ^ e * k) (hτ : TaylorExponentSufficient 0 K τ)
    (hinit : jointInitialJetEquation center Q ≠ 0) :
    (frobeniusRetainedPairFamily domain f g φ roots center Q K k τ (p ^ e)).card ≤
      (jointInitialJetEquation center Q).degreeOf (some 0) := by
  apply admissibleFrobeniusPairs_card_le_degreeOf domain f g φ roots center Q p e τ
    hK hKk hτ hinit
  intro P hP
  exact (mem_frobeniusRetainedPairFamily_iff domain f g φ roots center Q K k τ (p ^ e) P).mp
    hP

/-- There is an exceptional set of at most `(Fintype.card ι - k)` times the family size
challenges, outside which each retained pair's affine agreement set equals its common agreement
set. -/
theorem exists_exceptional_frobeniusRetainedPairFamily
    [DecidableEq F] [DecidableEq E]
    (domain : ι ↪ F) (f g : ι → F) (φ : F →+* E) (roots : ι → E)
    (center : E) (Q : DifferentialPolynomial E[X] 0) (K k τ s : ℕ) :
    ∃ exceptional : Finset E,
      exceptional.card ≤ (Fintype.card ι - k) *
        (frobeniusRetainedPairFamily domain f g φ roots center Q K k τ s).card ∧
      ∀ P ∈ frobeniusRetainedPairFamily domain f g φ roots center Q K k τ s,
        ∀ z ∉ exceptional,
          polynomialAgreementSet (domain.trans ⟨φ, φ.injective⟩)
              (fun i ↦ φ (f i) + z * φ (g i))
              (P.1.map φ + Polynomial.C z * P.2.map φ) =
            commonPolynomialAgreementSet domain f g P.1 P.2 := by
  classical
  let pairs := frobeniusRetainedPairFamily domain f g φ roots center Q K k τ s
  have hcommon : ∀ P ∈ pairs,
      k ≤ (commonPolynomialAgreementSet domain f g P.1 P.2).card := by
    intro P hP
    have hadmissible :=
      (mem_frobeniusRetainedPairFamily_iff domain f g φ roots center Q K k τ s P).mp hP
    obtain ⟨sample, hcard, hagree⟩ := hadmissible.sample
    rw [← hcard]
    apply Finset.card_le_card
    intro i hi
    exact (mem_commonPolynomialAgreementSet domain f g P.1 P.2 i).mpr
      ⟨(hagree i hi).2.1, (hagree i hi).2.2.1⟩
  obtain ⟨exceptional, hcard, hagree⟩ :=
    exists_exceptional_correlatedPairFamily (L := k) domain f g φ pairs hcommon
  refine ⟨exceptional, ?_, ?_⟩
  · simpa [pairs, Nat.mul_comm] using hcard
  · intro P hP z hz
    have hP' : P ∈ pairs := hP
    simpa [pairs, correlatedPairSpecialization] using hagree P hP' z hz

end ReedSolomon
