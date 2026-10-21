/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerTupleRegularBound
public import ArkLib.Data.Polynomial.Differential.RootPresentation
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.FactorBudget

/-!
# Exceptional challenges for separable Frobenius power solutions

An irreducible differential equation with nonzero root derivative controls every sufficiently
agreeing polynomial-curve solution outside one finite exceptional set. This set combines regular
incidence exceptions with challenges admitting a solution whose separant vanishes.

## Main statements

* `ReedSolomon.exists_exceptional_frobeniusPowerSeparableSolutions_at` gives a bounded exceptional
  set at any retained-agreement threshold `L` between `k` and `A`.
* `ReedSolomon.exists_exceptional_frobeniusPowerFactorSolutions_unifiedAt` expresses the bound
  using the free-retention ordinary factor charge at any retention threshold `L` with `D < L`.
* `ReedSolomon.exists_exceptional_frobeniusPowerFactorSolutions` expresses the bound using the
  polynomial-curve ordinary factor charge.

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

open Classical in
/-- Suppose `Q` has coefficient height at most `h`, jet degree at most `b` and root degree `b`, is
irreducible, and has nonzero root derivative. For `0 < D, ell, b` and `D < L ≤ A`, every
degree-`< D + 1` polynomial `P` whose Frobenius expansion solves the specialization of `Q` at `w`
and which has at least `A` agreements with the power-batched word at `w ^ p ^ e` has exact power
agreement, unless `w ^ p ^ e` lies in one set of size at most
`ordinaryUnifiedPowerFactorAt n D ell (p ^ e * b) h A L`. -/
theorem exists_exceptional_frobeniusPowerFactorSolutions_unifiedAt [IsAlgClosed E]
    (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F) (ι : F →+* E)
    (Q : DifferentialPolynomial E[X] 0) (p e D h b L A : ℕ) [ExpChar E p]
    (hD : 0 < D) (hℓ : 0 < ℓ) (hb : 0 < b) (hDL : D < L) (hLA : L ≤ A)
    (hheight : CoeffNatDegreeLE Q h) (hjet : jetTotalDegree Q ≤ b)
    (hirr : Irreducible Q) (hder : pderiv (some 0) Q ≠ 0)
    (hdegree : Q.degreeOf (some 0) = b) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤ ordinaryUnifiedPowerFactorAt n D ℓ (p ^ e * b) h A L ∧
      ∀ w : E, w ^ (p ^ e) ∉ exceptional → ∀ P : E[X],
        P.degree < D + 1 →
        differentialSpecialization (challengeSpecialization Q w) (expand E (p ^ e) P) = 0 →
        A ≤ (polynomialAgreementSet (domain.trans ⟨ι, ι.injective⟩)
          (powerBatchedWord (fun t i ↦ ι (values t i)) (w ^ (p ^ e))) P).card →
        HasExactPowerAgreement domain values ι (D + 1) (w ^ (p ^ e)) P := by
  classical
  let s := p ^ e
  let K := D * s + 1
  let theta : ℚ := ((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)
  let roots : Fin n → E := fun i ↦ (iterateFrobeniusEquiv E p e).symm (ι (domain i))
  have hs : 0 < s := pow_pos (expChar_pos E p) e
  have hK : 0 < K := by positivity
  have hKk : K ≤ s * (D + 1) := by
    calc
      D * s + 1 ≤ D * s + s := by omega
      _ = s * (D + 1) := by ring
  have hDs : 0 < D * s := Nat.mul_pos hD hs
  have hτpos : 0 < 2 * D * s - 1 := by
    have hbound : 2 ≤ 2 * D * s := by nlinarith [hDs]
    omega
  have hτ : TaylorExponentSufficient 0 K (2 * D * s - 1) := by
    intro l
    have hl := l.isLt
    have hl' : l.val ≤ D * s := by simpa [K] using Nat.lt_succ_iff.mp hl
    change 2 * l.val - 1 ≤ 2 * D * s - 1
    calc
      2 * l.val - 1 ≤ 2 * (D * s) - 1 :=
        Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 hl') 1
      _ = 2 * D * s - 1 := by rw [← Nat.mul_assoc]
  have htheta : 0 ≤ theta := by
    dsimp [theta]
    positivity
  obtain ⟨ex, hcard, hex⟩ :=
    exists_exceptional_frobeniusPowerSeparableSolutions_at
      (k := D + 1) (K := K) (L := L) domain values ι roots Q p e
      (2 * D * s - 1) h b A
      (by intro i; exact (iterateFrobeniusEquiv E p e).apply_symm_apply (ι (domain i)))
      hK hKk hτ hτpos hℓ hb (by omega) hLA hheight hjet hirr hder hdegree
  have hcharge := ordinaryFrobeniusCurve_charge_le_unifiedAt theta n D ℓ h s b L htheta
    (by omega : 1 ≤ s)
  have hcard' : (ex.card : ℚ) ≤
      (ordinaryFrobeniusCurveMixedDegree D ℓ h s b : ℚ) * theta +
        ((ℓ * ((n - L) * b) : ℕ) : ℚ) + (((2 * b - 1) * h : ℕ) : ℚ) := by
    simpa [ordinaryFrobeniusCurveMixedDegree, s, theta, Nat.mul_assoc,
      Nat.mul_left_comm, Nat.mul_comm] using hcard
  refine ⟨ex.image (fun w ↦ w ^ (p ^ e)), ?_, ?_⟩
  · calc
      ((ex.image (fun w ↦ w ^ (p ^ e))).card : ℚ) ≤ ex.card := by
          exact_mod_cast Finset.card_image_le
      _ ≤
          (ordinaryFrobeniusCurveMixedDegree D ℓ h s b : ℚ) * theta +
            ((ℓ * ((n - L) * b) : ℕ) : ℚ) + (((2 * b - 1) * h : ℕ) : ℚ) := hcard'
      _ = (((2 * b - 1) * h : ℕ) : ℚ) +
          theta * ordinaryFrobeniusCurveMixedDegree D ℓ h s b +
            ((ℓ * ((n - L) * b) : ℕ) : ℚ) := by ring
      _ ≤ ordinaryUnifiedPowerFactorAt n D ℓ (p ^ e * b) h A L := hcharge
  · intro w hw P hdeg hsol hagree
    have hw' : w ∉ ex := fun hmem ↦ hw (Finset.mem_image.mpr ⟨w, hmem, rfl⟩)
    apply hex w hw' P ?_ hsol hagree
    apply lt_of_le_of_lt (Polynomial.degree_le_natDegree
      (p := expand E (p ^ e) P))
    apply WithBot.coe_lt_coe.mpr
    rw [Polynomial.natDegree_expand]
    have hnat : P.natDegree ≤ D := by
      by_cases hP : P = 0
      · simp [hP]
      · have hdeg' : P.degree < ((D + 1 : ℕ) : WithBot ℕ) := by exact_mod_cast hdeg
        have := (Polynomial.natDegree_lt_iff_degree_lt hP).mpr hdeg'
        omega
    have hnat' : P.natDegree * (p ^ e) ≤ D * (p ^ e) :=
      Nat.mul_le_mul_right (p ^ e) hnat
    simpa [K, s, Nat.mul_comm] using Nat.lt_succ_of_le hnat'

open Classical in
/-- If `Q` has coefficient height at most `h`, jet degree and root degree `b`, is irreducible,
and has nonzero root derivative. For `0 < D, ell, b` and `D + 1 ≤ A ≤ n`, every degree-`< D+1`
solution with at least `A` agreements has exact power agreement outside a set of size at most
`ordinaryCurveFactorRaw ((n - D) / (A - D)) n D ell (p ^ e * b) h`. -/
theorem exists_exceptional_frobeniusPowerFactorSolutions [IsAlgClosed E]
    (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F) (ι : F →+* E)
    (Q : DifferentialPolynomial E[X] 0) (p e D h b A : ℕ) [ExpChar E p]
    (hD : 0 < D) (hℓ : 0 < ℓ) (hb : 0 < b) (hDA : D + 1 ≤ A) (hAn : A ≤ n)
    (hheight : CoeffNatDegreeLE Q h) (hjet : jetTotalDegree Q ≤ b)
    (hirr : Irreducible Q) (hder : pderiv (some 0) Q ≠ 0)
    (hdegree : Q.degreeOf (some 0) = b) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤ ordinaryCurveFactorRaw
        (((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ)) n D ℓ (p ^ e * b) h ∧
      ∀ w : E, w ^ (p ^ e) ∉ exceptional → ∀ P : E[X],
        P.degree < D + 1 →
        differentialSpecialization (challengeSpecialization Q w) (expand E (p ^ e) P) = 0 →
        A ≤ (polynomialAgreementSet (domain.trans ⟨ι, ι.injective⟩)
          (powerBatchedWord (fun t i ↦ ι (values t i)) (w ^ (p ^ e))) P).card →
        HasExactPowerAgreement domain values ι (D + 1) (w ^ (p ^ e)) P := by
  obtain ⟨ex, hcard, hex⟩ := exists_exceptional_frobeniusPowerFactorSolutions_unifiedAt
    domain values ι Q p e D h b (D + 1) A hD hℓ hb (by omega) hDA hheight hjet hirr hder hdegree
  rw [ordinaryUnifiedPowerFactorAt_succ_eq n D ℓ _ h A hDA hAn] at hcard
  exact ⟨ex, hcard.trans (ordinaryUnifiedPowerFactorRaw_le_ordinaryCurveFactorRaw n ℓ _ h
    (by positivity) hD), hex⟩

end ReedSolomon

end
