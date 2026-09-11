/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.PolynomialCurve.Separable
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.Factors.AggregationBounds
/-! # Original-coordinate charge of one polynomial-curve Frobenius factor -/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial MvPolynomial PolynomialDifferential HiddenDerivative

variable {F E : Type*} [Field F] [Field E] {n ℓ : ℕ}

/-- The ordinary factor charge for a degree-`ℓ` challenge curve. -/
def ordinaryPowerFactorRaw (theta : ℚ) (n D ℓ a h : ℕ) : ℚ :=
  ((2 * a - 1) * h : ℕ) + theta * (h + ℓ * a + 4 * D * a * h : ℕ) +
    (ℓ * ((n - D - 1) * a) : ℕ)

/-- The polynomial-curve charge is at most `ℓ` copies of the line charge whenever its
coefficient height is at most `ℓ` times the line height. -/
theorem ordinaryPowerFactorRaw_le_mul (theta : ℚ) (n D ℓ a h H : ℕ)
    (htheta : 0 ≤ theta) (hh : h ≤ ℓ * H) :
    ordinaryPowerFactorRaw theta n D ℓ a h ≤ ℓ * ordinaryFactorRaw theta n D a H := by
  have hfirst : (2 * a - 1) * h ≤ (2 * a - 1) * (ℓ * H) :=
    Nat.mul_le_mul_left _ hh
  have hmixed : h + ℓ * a + 4 * D * a * h ≤ ℓ * (H + a + 4 * D * a * H) := by
    calc
      h + ℓ * a + 4 * D * a * h ≤
          ℓ * H + ℓ * a + 4 * D * a * (ℓ * H) := by
        gcongr
      _ = ℓ * (H + a + 4 * D * a * H) := by ring
  have hrhs : ℓ * ordinaryFactorRaw theta n D a H =
      (((2 * a - 1) * (ℓ * H) : ℕ) : ℚ) +
        theta * ((ℓ * (H + a + 4 * D * a * H) : ℕ) : ℚ) +
        ((ℓ * ((n - D - 1) * a) : ℕ) : ℚ) := by
    unfold ordinaryFactorRaw
    push_cast
    ring
  rw [hrhs]
  unfold ordinaryPowerFactorRaw
  exact add_le_add
    (add_le_add (by exact_mod_cast hfirst)
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hmixed) htheta)) le_rfl

/-- The mixed Taylor-chart degree for a degree-`ℓ` received curve. -/
def ordinaryFrobeniusPowerMixedDegree (D ℓ h s b : ℕ) : ℕ :=
  h * (1 + (2 * D * s - 1) * (b - 1)) + b * (s * ℓ + (2 * D * s - 1) * h)

/-- The polynomial-curve mixed degree is linear in the challenge degree. -/
theorem ordinaryFrobeniusPowerMixedDegree_eq (D ℓ h s b : ℕ) (hb : 1 ≤ b) :
    ordinaryFrobeniusPowerMixedDegree D ℓ h s b =
      h + ℓ * (s * b) + (2 * D * s - 1) * h * (2 * b - 1) := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hb
  simp only [ordinaryFrobeniusPowerMixedDegree, Nat.add_sub_cancel_left,
    Nat.mul_add, Nat.mul_one]
  have ht : 2 + 2 * b - 1 = 1 + 2 * b := by omega
  rw [ht]
  ring

/-- The polynomial-curve mixed degree is linear in the challenge degree. -/
theorem ordinaryFrobeniusPowerMixedDegree_le (D ℓ h s b : ℕ) (hb : 1 ≤ b) :
    ordinaryFrobeniusPowerMixedDegree D ℓ h s b ≤
      h + ℓ * (s * b) + 4 * D * h * (s * b) := by
  rw [ordinaryFrobeniusPowerMixedDegree_eq D ℓ h s b hb]
  have hprod : (2 * D * s - 1) * h * (2 * b - 1) ≤
      (2 * D * s) * h * (2 * b) := by
    gcongr <;> omega
  exact (Nat.add_le_add_left hprod _).trans_eq (by ring)

/-- A pulled factor spends the polynomial-curve charge at its original root degree `s*b`. -/
theorem ordinaryFrobeniusPower_charge_le (theta : ℚ) (n D ℓ h s b : ℕ)
    (htheta : 0 ≤ theta) (hs : 1 ≤ s) (hb : 1 ≤ b) :
    ((2 * b - 1) * h : ℕ) + theta * ordinaryFrobeniusPowerMixedDegree D ℓ h s b +
        (ℓ * ((n - D - 1) * b) : ℕ) ≤
      ordinaryPowerFactorRaw theta n D ℓ (s * b) h := by
  have hbs : b ≤ s * b := by nlinarith
  unfold ordinaryPowerFactorRaw
  apply add_le_add
  · apply add_le_add
    · exact_mod_cast Nat.mul_le_mul_right h (Nat.sub_le_sub_right
        (Nat.mul_le_mul_left 2 hbs) 1)
    · apply mul_le_mul_of_nonneg_left _ htheta
      exact_mod_cast (show ordinaryFrobeniusPowerMixedDegree D ℓ h s b ≤
        h + ℓ * (s * b) + 4 * D * (s * b) * h by
          simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
            ordinaryFrobeniusPowerMixedDegree_le D ℓ h s b hb)
  · exact_mod_cast Nat.mul_le_mul_left ℓ (Nat.mul_le_mul_left (n - D - 1) hbs)

open Classical in
/-- One separable pulled factor has a polynomial-curve ordinary charge linear in the curve
degree. The constituent polynomials retain their original degree bound. -/
theorem exists_exceptional_frobeniusPowerFactorSolutions [IsAlgClosed E]
    (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F) (ι : F →+* E)
    (Q : DifferentialPolynomial E[X] 0) (p e D h b A : ℕ) [ExpChar E p]
    (hD : 0 < D) (hℓ : 0 < ℓ) (hb : 0 < b) (hDA : D + 1 ≤ A) (hAn : A ≤ n)
    (hheight : ChallengeHeightLE Q h)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ b)
    (hirr : Irreducible Q) (hder : pderiv (some 0) Q ≠ 0)
    (hdegree : Q.degreeOf (some 0) = b) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤ ordinaryPowerFactorRaw
        (((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ)) n D ℓ (p ^ e * b) h ∧
      ∀ w : E, w ^ (p ^ e) ∉ exceptional → ∀ P : E[X],
        P.degree < D + 1 →
        differentialSpecialization (challengeSpecialization Q w) (expand E (p ^ e) P) = 0 →
        A ≤ (polynomialAgreementSet (mappedDomain domain ι)
          (powerBatchedWord (fun t i ↦ ι (values t i)) (w ^ (p ^ e))) P).card →
        HasExactPowerAgreement domain values ι (D + 1) (w ^ (p ^ e)) P := by
  classical
  let roots : Fin n → E := fun i ↦ (iterateFrobeniusEquiv E p e).symm (ι (domain i))
  have hroots : ∀ i, roots i ^ (p ^ e) = ι (domain i) := by
    intro i
    exact (iterateFrobeniusEquiv E p e).apply_symm_apply (ι (domain i))
  have hs : 0 < p ^ e := pow_pos (expChar_pos E p) e
  have hK : D * p ^ e + 1 ≤ p ^ e * (D + 1) := by nlinarith
  have hτpos : 0 < 2 * D * p ^ e - 1 := by
    have hDs := Nat.mul_pos hD hs
    have : 2 ≤ 2 * D * p ^ e := by nlinarith
    omega
  obtain ⟨ex, hexCard, hex⟩ := exists_exceptional_frobeniusPowerSeparableSolutions
    (K := D * p ^ e + 1) domain values ι roots Q p e (2 * D * p ^ e - 1) h b A
    hroots (by omega) hK (by intro l; simp only [Nat.mul_assoc]; omega)
    hτpos hℓ hb hDA hAn hheight hjet hirr hder hdegree
  refine ⟨ex.image (fun w ↦ w ^ (p ^ e)), ?_, ?_⟩
  · have hcard : ((ex.image (fun w ↦ w ^ (p ^ e))).card : ℚ) ≤ ex.card := by
      exact_mod_cast Finset.card_image_le
    have hn : n - (D + 1) + 1 = n - D := by omega
    have hA : A - (D + 1) + 1 = A - D := by omega
    have hn' : n - (D + 1) = n - D - 1 := by omega
    rw [hn, hA, hn'] at hexCard
    apply hcard.trans (hexCard.trans ?_)
    let theta : ℚ := ((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ)
    have htheta : 0 ≤ theta := by positivity
    have hcharge := ordinaryFrobeniusPower_charge_le theta n D ℓ h (p ^ e) b
      htheta hs hb
    unfold ordinaryFrobeniusPowerMixedDegree at hcharge
    calc
      ((h * (1 + (2 * D * p ^ e - 1) * (b - 1)) +
              b * (p ^ e * ℓ + (2 * D * p ^ e - 1) * h) : ℕ) : ℚ) * theta +
            ((ℓ * (n - D - 1) * b : ℕ) : ℚ) + (((2 * b - 1) * h : ℕ) : ℚ) =
          (((2 * b - 1) * h : ℕ) : ℚ) + theta *
              ((h * (1 + (2 * D * p ^ e - 1) * (b - 1)) +
                b * (p ^ e * ℓ + (2 * D * p ^ e - 1) * h) : ℕ) : ℚ) +
            ((ℓ * ((n - D - 1) * b) : ℕ) : ℚ) := by
        push_cast
        ring
      _ ≤ ordinaryPowerFactorRaw theta n D ℓ (p ^ e * b) h := hcharge
  · intro w hw P hdeg hsol hagree
    have hw' : w ∉ ex := fun hmem ↦ hw (Finset.mem_image.mpr ⟨w, hmem, rfl⟩)
    apply hex w hw' P _ hsol hagree
    apply lt_of_le_of_lt (Polynomial.degree_le_natDegree (p := expand E (p ^ e) P))
    apply WithBot.coe_lt_coe.mpr
    rw [Polynomial.natDegree_expand]
    have hnat : P.natDegree ≤ D := by
      by_cases hP : P = 0
      · simp [hP]
      · have hdeg' : P.degree < ((D + 1 : ℕ) : WithBot ℕ) := by exact_mod_cast hdeg
        have := (Polynomial.natDegree_lt_iff_degree_lt hP).mpr hdeg'
        omega
    nlinarith

end ReedSolomon
