/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity.FirstOrderRateParameters
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrderCurve
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.PowerToLine
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.RateCertificate
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.FirstOrder.RateLimits
/-!
# First-order rate-dependent correlated agreement

A finite rate certificate constructs one symbolic equation for an entire received line.  The
curve consumer chooses one exceptional set before the challenge and candidate polynomial, and
outside it recovers equality of the complete agreement set.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

universe u

open Polynomial HiddenDerivative PolynomialDifferential
open SymbolicReceivedInterpolation SymbolicWeightedSupportInterpolation

/-- A checked finite rate choice gives an exact line correlated-agreement theorem over every
field satisfying the stated characteristic condition. -/
theorem finite_firstOrderRate_lineMCA
    {F : Type u} [Field F] [DecidableEq F] {R a : ℝ}
    (p : FirstOrderFiniteRateParameters R a)
    (hR : 0 < R) (hRa : R < a)
    {n k A : ℕ} (hn : 2 ≤ n) (hk : 0 < k)
    (hkR : (k : ℝ) ≤ R * n) (haA : a * n ≤ A) (hAn : A ≤ n)
    (domain : Fin n ↪ F) (f g : Fin n → F)
    (hchar : ringChar F = 0 ∨ max (k - 1) p.jetDegree < ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤
        firstOrderRateExceptionalConstant (a - R) p.jetDegree p.challengeDegree * n ^ 2 ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  classical
  let K := max k 2
  let D := K - 1
  let L := correlatedMidpoint (a - R) n k
  let values : Fin 2 → Fin n → F := ![f, g]
  let E := AlgebraicClosure F
  let iota : F →+* E := algebraMap F E
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have ha : 0 < a := hR.trans hRa
  have hkA : k ≤ A := by
    have h : (k : ℝ) ≤ A :=
      hkR.trans ((mul_le_mul_of_nonneg_right hRa.le hnR.le).trans haA)
    exact_mod_cast h
  have hKn : K ≤ n := max_le (hkA.trans hAn) hn
  have hD : 0 < D := by dsimp [D, K]; omega
  have hDk : D ≤ k := by dsimp [D, K]; omega
  have hkD : k ≤ D + 1 := by dsimp [D, K]; omega
  have hDrate : (D : ℝ) ≤ R * n := (Nat.cast_le.mpr hDk).trans hkR
  have hbudget : 0 < p.multiplicity * A :=
    mul_pos p.multiplicity_pos (hk.trans_le hkA)
  have hμ : 0 < p.jetDegree := by
    apply Nat.lt_ceil.mpr
    have hm : (0 : ℝ) < p.multiplicity := by exact_mod_cast p.multiplicity_pos
    simpa only [FirstOrderFiniteRateParameters.jetDegree, firstOrderRateJetDegree,
      Nat.cast_zero] using (show (0 : ℝ) < p.multiplicity * a / R by positivity)
  have hgap : (k : ℝ) + (a - R) * n ≤ A := by nlinarith
  have hmid := correlatedMidpoint_bounds (a - R) n k A
    (sub_nonneg.mpr hRa.le) hgap hAn
  have hcharK : ringChar F = 0 ∨ max (K - 1) p.jetDegree < ringChar F := by
    apply hchar.imp_right
    intro hc
    have h : K - 1 ≤ max (k - 1) p.jetDegree := by dsimp [K]; omega
    exact (max_le h (le_max_right _ _)).trans_lt hc
  obtain ⟨cert⟩ := exists_firstOrderRate_symbolicCertificate.{u, u} p
    hnpos hD hbudget hkD hDrate haA domain f g
  let curveCert : FirstOrderCurveCertificate.{u, u} (F := F)
      D A p.multiplicity p.derivativeCap p.jetDegree k p.challengeDegree domain
      (fun i ↦ powerBatchedCoordinate fun t ↦ values t i)
      (firstOrderColumns (D := D) (A := A) (m := p.multiplicity)
        (M := p.derivativeCap) (μ := p.jetDegree)) := by
    simpa [values, powerBatchedCoordinate, Fin.sum_univ_two, receivedLine,
      ← Polynomial.C_mul_X_eq_monomial] using cert.toCurve
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_baseExceptional_firstOrderCurve_of_certificate_of_exponent
      (D := D) (A := A) (m := p.multiplicity) (M := p.derivativeCap)
      (mu := p.jetDegree) (k := k) (h := p.challengeDegree) (n := n)
      (K := K) (L := L) (ell := 1)
      domain values iota _ curveCert (by dsimp [K]; omega) (le_max_left _ _) hk
        hmid.1 hmid.2.1 hAn (by omega)
        (2 * K - 3) (taylorExponentSufficient_two_mul_sub_three 0 (by dsimp [K]; omega))
          (taylorExponentSufficient_two_mul_sub_three 1 (by dsimp [K]; omega))
            (by dsimp [K]; omega) hcharK
  refine ⟨exceptional, ?_, ?_⟩
  · have hcardR : (exceptional.card : ℝ) ≤
        ((firstOrderCurveBound n K k L A p.jetDegree p.derivativeCap 1 p.challengeDegree
          (2 * K - 3) (firstOrderCurveDirectRatio n k A) : ℚ) : ℝ) := by
      exact_mod_cast hcard
    exact hcardR.trans (firstOrderCurveBound_le_rateExceptionalConstant
      (a - R) n K k A p.jetDegree p.derivativeCap p.challengeDegree
      (sub_pos.mpr hRa) hnpos (by dsimp [K]; omega) hKn hk hgap hAn
        (by simp [FirstOrderFiniteRateParameters.challengeDegree,
          firstOrderRateChallengeDegree]))
  · intro z hz P hdegree hagree
    have hword : powerBatchedWord values z = fun i ↦ f i + z * g i := by
      funext i
      simp [values, powerBatchedWord, Fin.sum_univ_two]
    have hpower := hgood z hz P hdegree (by rwa [hword])
    simpa [values] using
      (exactCorrelatedPair_of_powerAgreement_one domain values (RingHom.id F) z P hpower)

/-- Above the first-order threshold, one finite choice works uniformly for every later field,
block length, code dimension, agreement threshold, domain, and received line. -/
theorem exists_firstOrderRate_lineMCA
    {R a : ℝ} (hR : 0 < R) (hRa : R < a) (haone : a < 1)
    (hthreshold : firstOrderRateThreshold R < a) :
    ∃ p : FirstOrderFiniteRateParameters R a,
      ∀ {F : Type u} [Field F] [DecidableEq F]
        {n k A : ℕ}, 2 ≤ n → 0 < k →
        (k : ℝ) ≤ R * n → a * n ≤ A → A ≤ n →
        ∀ (domain : Fin n ↪ F) (f g : Fin n → F),
          (ringChar F = 0 ∨ max (k - 1) p.jetDegree < ringChar F) →
          ∃ exceptional : Finset F,
            (exceptional.card : ℝ) ≤
              firstOrderRateExceptionalConstant (a - R) p.jetDegree
                p.challengeDegree * n ^ 2 ∧
            ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
              A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
              HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  obtain ⟨p⟩ := exists_firstOrderFiniteRateParameters hR hRa haone hthreshold
  refine ⟨p, ?_⟩
  intro F _ _ n k A hn hk hkR haA hAn domain f g hchar
  exact finite_firstOrderRate_lineMCA p hR hRa hn hk hkR haA hAn domain f g hchar

end ReedSolomon
