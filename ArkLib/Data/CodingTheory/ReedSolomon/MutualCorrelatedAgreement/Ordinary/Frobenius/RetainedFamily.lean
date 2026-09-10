/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.Frobenius.GraphCounting
/-!
# The finite family of retained Frobenius pairs

The retained family consists of actual sample interpolants satisfying the chart identities.
Its accidental-agreement set is counted in the original challenge coordinate.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial MvPolynomial PolynomialDifferential HiddenDerivative AffineHilbert

variable {F E : Type*} [Field F] [Field E] {n k K : ℕ}

/-- The finite sample family filtered by actual Frobenius-chart admissibility. -/
def frobeniusRetainedPairFamily (domain : Fin n ↪ F) (f g : Fin n → F)
    (ι : F →+* E) (roots : Fin n → E) (center : E)
    (Q : DifferentialPolynomial E[X] 0) (K k τ s : ℕ) : Finset (F[X] × F[X]) := by
  classical
  exact ((Finset.univ.powersetCard k).image (fun sample ↦
    (Lagrange.interpolate sample domain f, Lagrange.interpolate sample domain g))).filter
      (fun P ↦ IsAdmissibleFrobeniusPair domain f g ι roots center Q K k τ s P.1 P.2)

/-- Every intrinsically admissible pair occurs in the explicit finite sample family. -/
theorem mem_frobeniusRetainedPairFamily_iff
    (domain : Fin n ↪ F) (f g : Fin n → F) (ι : F →+* E)
    (roots : Fin n → E) (center : E) (Q : DifferentialPolynomial E[X] 0)
    (K k τ s : ℕ) (P : F[X] × F[X]) :
    P ∈ frobeniusRetainedPairFamily domain f g ι roots center Q K k τ s ↔
      IsAdmissibleFrobeniusPair domain f g ι roots center Q K k τ s P.1 P.2 := by
  classical
  constructor
  · exact fun h ↦ (Finset.mem_filter.mp h).2
  · intro hP
    obtain ⟨sample, hcard, hagree, _⟩ := hP.sample
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨sample,
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩, ?_⟩, hP⟩
    apply Prod.ext
    · apply Polynomial.eq_of_degrees_lt_of_eval_index_eq sample domain.injective.injOn
      · exact Lagrange.degree_interpolate_lt f domain.injective.injOn
      · simpa only [hcard] using hP.degree_left
      · intro i hi
        rw [Lagrange.eval_interpolate_at_node f domain.injective.injOn hi]
        exact (hagree i hi).1.symm
    · apply Polynomial.eq_of_degrees_lt_of_eval_index_eq sample domain.injective.injOn
      · exact Lagrange.degree_interpolate_lt g domain.injective.injOn
      · simpa only [hcard] using hP.degree_right
      · intro i hi
        rw [Lagrange.eval_interpolate_at_node g domain.injective.injOn hi]
        exact (hagree i hi).2.symm

/-- The complete retained family is bounded by the source root degree. -/
theorem frobeniusRetainedPairFamily_card_le [Infinite E]
    (domain : Fin n ↪ F) (f g : Fin n → F) (ι : F →+* E)
    (roots : Fin n → E) (center : E) (Q : DifferentialPolynomial E[X] 0)
    (p e τ : ℕ) [ExpChar E p]
    (hroots : ∀ i, roots i ^ (p ^ e) = ι (domain i))
    (hK : 0 < K) (hKk : K ≤ p ^ e * k) (hτ : TaylorExponentSufficient 0 K τ)
    (hinit : symbolicSourceInitialEquation center Q ≠ 0) :
    (frobeniusRetainedPairFamily domain f g ι roots center Q K k τ (p ^ e)).card ≤
      (symbolicSourceInitialEquation center Q).degreeOf (some 0) := by
  apply admissibleFrobeniusPairs_card_le_degreeOf domain f g ι roots center Q p e τ
    hroots hK hKk hτ hinit
  intro P hP
  exact (mem_frobeniusRetainedPairFamily_iff domain f g ι roots center Q K k τ (p ^ e) P).mp hP

open Classical in
/-- A common exceptional set of original challenges controls accidental agreements for
all retained pairs, with a charge of at most `n-k` for each pair. -/
theorem exists_exceptional_frobeniusRetainedPairFamily
    (domain : Fin n ↪ F) (f g : Fin n → F) (ι : F →+* E)
    (roots : Fin n → E) (center : E) (Q : DifferentialPolynomial E[X] 0)
    (K k τ s : ℕ) :
    ∃ exceptional : Finset E,
      exceptional.card ≤ (n - k) *
        (frobeniusRetainedPairFamily domain f g ι roots center Q K k τ s).card ∧
      ∀ P ∈ frobeniusRetainedPairFamily domain f g ι roots center Q K k τ s,
        ∀ z ∉ exceptional,
          polynomialAgreementSet (mappedDomain domain ι)
              (fun i ↦ ι (f i) + z * ι (g i))
              (P.1.map ι + Polynomial.C z * P.2.map ι) =
            commonPolynomialAgreementSet domain f g P.1 P.2 := by
  classical
  let pairs := frobeniusRetainedPairFamily domain f g ι roots center Q K k τ s
  have hex (P : F[X] × F[X]) (hP : P ∈ pairs) :
      ∃ exceptional : Finset E, exceptional.card ≤ n - k ∧
        ∀ z ∉ exceptional,
          polynomialAgreementSet (mappedDomain domain ι)
              (fun i ↦ ι (f i) + z * ι (g i))
              (P.1.map ι + Polynomial.C z * P.2.map ι) =
            commonPolynomialAgreementSet domain f g P.1 P.2 := by
    have hp := (mem_frobeniusRetainedPairFamily_iff domain f g ι roots center Q
      K k τ s P).mp hP
    obtain ⟨sample, hcard, hagree, _⟩ := hp.sample
    exact exists_exceptional_graphLine_challenges_of_sample domain f g sample hcard
      P.1 P.2 hagree ι
  let ex (P : F[X] × F[X]) : Finset E :=
    if hP : P ∈ pairs then (hex P hP).choose else ∅
  refine ⟨pairs.biUnion ex, ?_, ?_⟩
  · calc
      (pairs.biUnion ex).card ≤ ∑ P ∈ pairs, (ex P).card := Finset.card_biUnion_le
      _ ≤ ∑ _P ∈ pairs, (n - k) := by
        apply Finset.sum_le_sum
        intro P hP
        simpa only [ex, dif_pos hP] using (hex P hP).choose_spec.1
      _ = (n - k) * pairs.card := by simp [Nat.mul_comm]
  · intro P hP z hz
    change P ∈ pairs at hP
    have hz' : z ∉ ex P := by
      intro hze
      exact hz (Finset.mem_biUnion.mpr ⟨P, hP, hze⟩)
    apply (hex P hP).choose_spec.2 z
    simpa only [ex, dif_pos hP] using hz'

end ReedSolomon
