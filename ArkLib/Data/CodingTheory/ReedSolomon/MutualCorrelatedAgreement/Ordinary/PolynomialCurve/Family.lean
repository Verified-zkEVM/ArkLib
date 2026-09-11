/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.PolynomialCurve.Counting
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.GraphCounting
/-!
# Retained Frobenius power-tuple family

The retained family filters the explicit common-sample interpolation family by the actual sparse
chart identities.  Its exact-agreement exceptions are counted in the original challenge
coordinate and cost `ℓ * (n-k)` per retained tuple.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial MvPolynomial PolynomialDifferential HiddenDerivative AffineHilbert

variable {F E : Type*} [Field F] [Field E] {n k K ℓ : ℕ}

/-- The finite common-sample family filtered by intrinsic Frobenius admissibility. -/
def frobeniusRetainedPowerTupleFamily
    (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F)
    (ι : F →+* E) (roots : Fin n → E) (center : E)
    (Q : DifferentialPolynomial E[X] 0) (K k τ s : ℕ) :
    Finset (Fin (ℓ + 1) → F[X]) := by
  classical
  exact (polynomialTupleFamily domain values k).filter
    (IsAdmissibleFrobeniusPowerTuple domain values ι roots center Q K k τ s)

/-- The retained family contains exactly the intrinsically admissible tuples. -/
theorem mem_frobeniusRetainedPowerTupleFamily_iff
    (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F)
    (ι : F →+* E) (roots : Fin n → E) (center : E)
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

/-- The complete retained tuple family is bounded by the source root degree. -/
theorem frobeniusRetainedPowerTupleFamily_card_le [Infinite E]
    (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F) (ι : F →+* E)
    (roots : Fin n → E) (center : E) (Q : DifferentialPolynomial E[X] 0)
    (p e τ : ℕ) [ExpChar E p]
    (hroots : ∀ i, roots i ^ (p ^ e) = ι (domain i))
    (hK : 0 < K) (hKk : K ≤ p ^ e * k) (hτ : TaylorExponentSufficient 0 K τ)
    (hinit : symbolicSourceInitialEquation center Q ≠ 0) :
    (frobeniusRetainedPowerTupleFamily
      domain values ι roots center Q K k τ (p ^ e)).card ≤
      (symbolicSourceInitialEquation center Q).degreeOf (some 0) := by
  apply admissibleFrobeniusPowerTuples_card_le_degreeOf
    domain values ι roots center Q p e τ hroots hK hKk hτ hinit
  intro P hP
  exact (mem_frobeniusRetainedPowerTupleFamily_iff
    domain values ι roots center Q K k τ (p ^ e) P).mp hP

open Classical in
/-- One exceptional set controls exact full agreement for every retained tuple. -/
theorem exists_exceptional_frobeniusRetainedPowerTupleFamily
    (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F)
    (ι : F →+* E) (roots : Fin n → E) (center : E)
    (Q : DifferentialPolynomial E[X] 0) (K k τ s : ℕ) :
    ∃ exceptional : Finset E,
      exceptional.card ≤ ℓ * (n - k) *
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
  have hex (P : Fin (ℓ + 1) → F[X]) (hP : P ∈ tuples) :
      ∃ exceptional : Finset E, exceptional.card ≤ ℓ * (n - k) ∧
        ∀ z ∉ exceptional,
          HasExactPowerAgreement domain values ι k z
            (powerBatchedPolynomial (fun t ↦ (P t).map ι) z) := by
    have hp := (mem_frobeniusRetainedPowerTupleFamily_iff
      domain values ι roots center Q K k τ s P).mp hP
    obtain ⟨sample, hcard, hagree, _⟩ := hp.sample
    exact exists_exceptional_frobeniusPower_challenges_of_sample
      domain values sample hcard P hp.degree hagree ι
  let ex (P : Fin (ℓ + 1) → F[X]) : Finset E :=
    if hP : P ∈ tuples then (hex P hP).choose else ∅
  refine ⟨tuples.biUnion ex, ?_, ?_⟩
  · calc
      (tuples.biUnion ex).card ≤ ∑ P ∈ tuples, (ex P).card := Finset.card_biUnion_le
      _ ≤ ∑ _P ∈ tuples, ℓ * (n - k) := by
        apply Finset.sum_le_sum
        intro P hP
        simpa only [ex, dif_pos hP] using (hex P hP).choose_spec.1
      _ = ℓ * (n - k) * tuples.card := by simp [Nat.mul_comm]
  · intro P hP z hz
    change P ∈ tuples at hP
    have hz' : z ∉ ex P := by
      intro hze
      exact hz (Finset.mem_biUnion.mpr ⟨P, hP, hze⟩)
    apply (hex P hP).choose_spec.2 z
    simpa only [ex, dif_pos hP] using hz'

end ReedSolomon
