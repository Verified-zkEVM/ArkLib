/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerTupleRegularBound
public import ArkLib.Data.Polynomial.Differential.RootPresentation

/-!
# Exceptional challenges for separable Frobenius power solutions

An irreducible differential equation with nonzero root derivative controls every sufficiently
agreeing polynomial-curve solution outside one finite exceptional set. This set combines regular
incidence exceptions with challenges admitting a solution whose separant vanishes.

## Main statements

* `ReedSolomon.exists_exceptional_frobeniusPowerSeparableSolutions_at` gives a bounded exceptional
  set at any retained-agreement threshold `L` between `k` and `A`.

## References

* [DKT26]
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial MvPolynomial PolynomialDifferential

variable {F E : Type*} [Field F] [Field E] {n k K ℓ : ℕ}

open Classical in
/-- Given roots with `roots i ^ (p ^ e) = ι (domain i)`, suppose `Q` has coefficient height at
most `h`, jet degree at most `b`, root degree `b`, is irreducible, and has nonzero root
derivative. If `K ≤ p ^ e * k`, `TaylorExponentSufficient 0 K τ`, `0 < τ, ℓ, b`, and
`k ≤ L ≤ A`, then outside one set of size at most
`(h * (1 + τ * (b - 1)) + b * (p ^ e * ℓ + τ * h)) * ((n - L + 1) / (A - L + 1)) +
  ℓ * (n - L) * b + (2 * b - 1) * h`, every expanded degree-`< K` solution of the challenge
specialization with at least `A` agreements has exact power agreement. -/
theorem exists_exceptional_frobeniusPowerSeparableSolutions_at [IsAlgClosed E]
    {L : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F) (ι : F →+* E)
    (roots : Fin n → E) (Q : DifferentialPolynomial E[X] 0)
    (p e τ h b A : ℕ) [ExpChar E p]
    (hroots : ∀ i, roots i ^ (p ^ e) = ι (domain i))
    (hK : 0 < K) (hKk : K ≤ p ^ e * k) (hτ : TaylorExponentSufficient 0 K τ)
    (hτpos : 0 < τ) (hℓ : 0 < ℓ) (hb : 0 < b)
    (hkL : k ≤ L) (hLA : L ≤ A)
    (hheight : CoeffNatDegreeLE Q h) (hjet : jetTotalDegree Q ≤ b)
    (hirr : Irreducible Q) (hder : pderiv (some 0) Q ≠ 0)
    (hdegree : Q.degreeOf (some 0) = b) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤
        (h * (1 + τ * (b - 1)) + b * (p ^ e * ℓ + τ * h) : ℕ) *
          (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) +
        (ℓ * (n - L) * b : ℕ) + ((2 * b - 1) * h : ℕ) ∧
      ∀ z ∉ exceptional, ∀ P : E[X],
        (expand E (p ^ e) P).degree < K →
        differentialSpecialization (challengeSpecialization Q z) (expand E (p ^ e) P) = 0 →
        A ≤ (polynomialAgreementSet (domain.trans ⟨ι, ι.injective⟩)
          (powerBatchedWord (fun t i ↦ ι (values t i)) (z ^ (p ^ e))) P).card →
        HasExactPowerAgreement domain values ι k (z ^ (p ^ e)) P := by
  classical
  obtain ⟨regularEx, hregularCard, hregular⟩ :=
    exists_exceptional_frobeniusPowerRegularSolutions_at
      domain values ι roots Q p e τ h b A hroots hK hKk hτ hτpos hℓ hb
        hkL hLA hheight hjet
  obtain ⟨singularEx, hsingularCard, hsingular⟩ :=
    exists_exceptional_ordinary_separant hirr
      (by simpa only [hdegree] using hb) hder hheight
  refine ⟨regularEx ∪ singularEx, ?_, ?_⟩
  · have hcard : ((regularEx ∪ singularEx).card : ℚ) ≤
        regularEx.card + singularEx.card := by
      exact_mod_cast Finset.card_union_le regularEx singularEx
    have hsingularQ : (singularEx.card : ℚ) ≤ ((2 * b - 1) * h : ℕ) := by
      rw [hdegree] at hsingularCard
      exact_mod_cast hsingularCard
    linarith
  · intro z hz P hdeg hsol hagree
    have hz' := Finset.notMem_union.mp hz
    exact hregular z hz'.1 P hdeg hsol
      (hsingular z hz'.2 (expand E (p ^ e) P) hsol) hagree

end ReedSolomon

end
