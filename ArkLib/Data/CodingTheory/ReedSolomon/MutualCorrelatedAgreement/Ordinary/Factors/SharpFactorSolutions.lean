/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.Frobenius.FactorSolutions
/-!
# Sharper ordinary factor charges

When each separable factor degree is at most `D`, the exact mixed-degree comparison gives
an improved finite charge. The aggregate estimate applies in particular when the original
root-degree cap is at most `D`.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open scoped BigOperators
/-- The sharper positive-degree ordinary charge. -/
def ordinaryFactorSharpRaw (theta : ℚ) (n D a h : ℕ) : ℚ :=
  ((2 * a - 1) * h : ℕ) + theta *
    (h + a + (2 * D - 1) * h * (2 * a - 1) : ℕ) + ((n - D - 1) * a : ℕ)
/-- The sharper pulled-factor charge uses its original root degree when `b ≤ D`. -/
theorem ordinaryFrobenius_charge_le_sharp (theta : ℚ) (n D h s b : ℕ)
    (htheta : 0 ≤ theta) (hs : 1 ≤ s) (hb : 1 ≤ b) (hbD : b ≤ D) :
    ((2 * b - 1) * h : ℕ) + theta * ordinaryFrobeniusMixedDegree D h s b +
        ((n - D - 1) * b : ℕ) ≤ ordinaryFactorSharpRaw theta n D (s * b) h := by
  have hbs : b ≤ s * b := by nlinarith
  unfold ordinaryFactorSharpRaw
  apply add_le_add
  · apply add_le_add
    · exact_mod_cast Nat.mul_le_mul_right h (Nat.sub_le_sub_right
        (Nat.mul_le_mul_left 2 hbs) 1)
    · apply mul_le_mul_of_nonneg_left _ htheta
      exact_mod_cast ordinaryFrobeniusMixedDegree_le_sharp h hbD hs hb
  · exact_mod_cast Nat.mul_le_mul_left (n - D - 1) hbs

/-- Content plus every distinct positive-degree factor fits in the original ordinary budget. -/
theorem ordinaryFactorSharpRaw_sum_le {I : Type*} (S : Finset I) (a height : I → ℕ)
    (theta : ℚ) (n D mu H contentHeight : ℕ)
    (htheta : 0 ≤ theta) (hmu : 1 ≤ mu)
    (ha : ∑ i ∈ S, a i ≤ mu)
    (hh : contentHeight + ∑ i ∈ S, height i ≤ H) :
    (contentHeight : ℚ) + ∑ i ∈ S, ordinaryFactorSharpRaw theta n D (a i) (height i) ≤
      ordinaryFactorSharpRaw theta n D mu H := by
  let c : ℚ := (2 * mu - 1 : ℕ) + theta * (1 + (2 * D - 1 : ℕ) * (2 * mu - 1 : ℕ))
  let d : ℚ := theta + (n - D - 1 : ℕ)
  have hc : 1 ≤ c := by
    have hnat : 1 ≤ 2 * mu - 1 := by omega
    have hcast : (1 : ℚ) ≤ (2 * mu - 1 : ℕ) := by exact_mod_cast hnat
    exact hcast.trans (le_add_of_nonneg_right (mul_nonneg htheta (by positivity)))
  have hc0 : 0 ≤ c := le_trans zero_le_one hc
  have hd0 : 0 ≤ d := by dsimp [d]; positivity
  have hterm (i : I) (hi : i ∈ S) :
      ordinaryFactorSharpRaw theta n D (a i) (height i) ≤ c * height i + d * a i := by
    have hai : a i ≤ mu := (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hi).trans ha
    have hsub : 2 * a i - 1 ≤ 2 * mu - 1 := by omega
    have hfirst : (((2 * a i - 1) * height i : ℕ) : ℚ) ≤
        (2 * mu - 1 : ℕ) * (height i : ℚ) := by exact_mod_cast Nat.mul_le_mul_right (height i) hsub
    have hsecond : (((2 * D - 1) * height i * (2 * a i - 1) : ℕ) : ℚ) ≤
        ((2 * D - 1 : ℕ) : ℚ) * height i * (2 * mu - 1 : ℕ) := by
      exact_mod_cast Nat.mul_le_mul_left ((2 * D - 1) * height i) hsub
    unfold ordinaryFactorSharpRaw
    dsimp [c, d]
    push_cast at hfirst hsecond ⊢
    nlinarith [mul_nonneg htheta (sub_nonneg.mpr hsecond)]
  have hsum := Finset.sum_le_sum hterm
  have hcontent : (contentHeight : ℚ) ≤ c * contentHeight := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg contentHeight)
  have hhQ : (contentHeight : ℚ) + ∑ i ∈ S, (height i : ℚ) ≤ H := by exact_mod_cast hh
  have haQ : (∑ i ∈ S, (a i : ℚ)) ≤ mu := by exact_mod_cast ha
  calc
    (contentHeight : ℚ) + ∑ i ∈ S, ordinaryFactorSharpRaw theta n D (a i) (height i) ≤
        c * contentHeight + ∑ i ∈ S, (c * height i + d * a i) := add_le_add hcontent hsum
    _ = c * ((contentHeight : ℚ) + ∑ i ∈ S, (height i : ℚ)) +
        d * ∑ i ∈ S, (a i : ℚ) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      ring
    _ ≤ c * H + d * mu := add_le_add (mul_le_mul_of_nonneg_left hhQ hc0)
      (mul_le_mul_of_nonneg_left haQ hd0)
    _ = ordinaryFactorSharpRaw theta n D mu H := by
      dsimp [c, d, ordinaryFactorSharpRaw]
      push_cast
      ring

open Polynomial MvPolynomial PolynomialDifferential HiddenDerivative
variable {F E : Type*} [Field F] [Field E] {n : ℕ}
open Classical in
/-- The original-coordinate charge improves when the separable factor degree is at most `D`. -/
theorem exists_exceptional_frobeniusFactorSolutions_sharp [IsAlgClosed E]
    (domain : Fin n ↪ F) (f g : Fin n → F) (ι : F →+* E)
    (Q : DifferentialPolynomial E[X] 0) (p e D h b A : ℕ) [ExpChar E p]
    (hD : 0 < D) (hb : 0 < b) (hDA : D + 1 ≤ A) (hAn : A ≤ n)
    (hheight : ChallengeHeightLE Q h)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ b)
    (hirr : Irreducible Q) (hder : pderiv (some 0) Q ≠ 0)
    (hdegree : Q.degreeOf (some 0) = b) (hbD : b ≤ D) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤ ordinaryFactorSharpRaw
        (((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ)) n D (p ^ e * b) h ∧
      ∀ w : E, w ^ (p ^ e) ∉ exceptional → ∀ P : E[X],
        P.degree < D + 1 →
        differentialSpecialization (challengeSpecialization Q w) (expand E (p ^ e) P) = 0 →
        A ≤ (polynomialAgreementSet (mappedDomain domain ι)
          (fun i ↦ ι (f i) + w ^ (p ^ e) * ι (g i)) P).card →
        HasExactCorrelatedPair domain f g ι (D + 1) (w ^ (p ^ e)) P := by
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
  obtain ⟨ex, hexCard, hex⟩ := exists_exceptional_frobeniusSeparableSolutions
    (K := D * p ^ e + 1) domain f g ι roots Q p e (2 * D * p ^ e - 1) h b A
    hroots (by omega) hK (frobeniusTaylorExponentSufficient D (p ^ e))
    hτpos hb hDA hAn hheight hjet hirr hder hdegree
  refine ⟨ex.image (fun w ↦ w ^ (p ^ e)), ?_, ?_⟩
  · have hcard : ((ex.image (fun w ↦ w ^ (p ^ e))).card : ℚ) ≤ ex.card := by
      exact_mod_cast Finset.card_image_le
    have hn : n - (D + 1) + 1 = n - D := by omega
    have hA : A - (D + 1) + 1 = A - D := by omega
    have hn' : n - (D + 1) = n - D - 1 := by omega
    rw [hn, hA, hn'] at hexCard
    apply hcard.trans (hexCard.trans ?_)
    have hcharge := ordinaryFrobenius_charge_le_sharp
      (((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ)) n D h (p ^ e) b
      (by positivity) hs hb hbD
    unfold ordinaryFrobeniusMixedDegree at hcharge
    linarith
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
