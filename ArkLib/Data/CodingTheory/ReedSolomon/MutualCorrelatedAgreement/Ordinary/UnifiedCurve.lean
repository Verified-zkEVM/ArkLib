/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.PolynomialCurve.Solutions
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.Factors.UnifiedBudget
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.PolynomialCurve.Equation
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.EquationDescent
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.ExtensionDescent
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.GeometricTransfer
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Unified ordinary recovery on polynomial challenge curves

The positive-part coefficient `ordinaryPsi` removes the former split between a sharp bounded
separable-degree theorem and a coarse unconditional theorem. This module first connects that
arithmetic to the existing all-characteristic Frobenius recovery of one irreducible factor.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial MvPolynomial PolynomialDifferential HiddenDerivative

variable {F E : Type*} [Field F] [Field E] {n ell : ℕ}

open Classical in
/-- Free-retention semantic ordinary transfer from explicit geometric certificates.

This is the common boundary needed by the all-characteristic ordinary construction. `offGraph`
is the actual finite projection of high-agreement points outside persistent graphs, while
`retained` is the actual family of base-field graph tuples surviving the reduced generic fiber.
The hypotheses keep those two counts separate. No characteristic restriction involving `ell` is
introduced, and the conclusion identifies the full agreement set through
`HasExactPowerAgreement`.

The Frobenius incidence layer now constructs the free-`L` off-graph certificate; an unconditional
free-`L` ordinary theorem additionally requires routing that certificate through the regular,
separable, and factor-assembly layers. -/
theorem exists_exceptional_ordinaryPowerEquation_freeRetention_of_certificates [IsAlgClosed E]
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] 0) (D H B L A : ℕ)
    (hD : 0 < D) (hell : 0 < ell) (_hB : 0 < B)
    (hDL : D < L) (hLA : L ≤ A) (hAn : A ≤ n)
    (preliminary offGraph : Finset E)
    (retained : Finset (Fin (ell + 1) → F[X]))
    (hpreliminary : (preliminary.card : ℚ) ≤ ((2 * B - 1) * H : ℕ))
    (hoffGraph : (offGraph.card : ℚ) ≤
      (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) *
        (ell * B + H * ordinaryPsi D B : ℕ))
    (hretained : (retained.card : ℚ) ≤ B)
    (hdegree : ∀ P ∈ retained, ∀ t, (P t).degree < D + 1)
    (hcommon : ∀ P ∈ retained, L ≤ (commonCurveAgreementSet domain values P).card)
    (hcoverage : ∀ (z : E) (P : E[X]), P.degree < D + 1 →
      differentialSpecialization (challengeSpecialization Q z) P = 0 →
      A ≤ (polynomialAgreementSet (mappedDomain domain iota)
        (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
      z ∉ preliminary →
      z ∈ offGraph ∨ ∃ tuple ∈ retained,
        P = powerBatchedPolynomial (fun t ↦ (tuple t).map iota) z) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤ ordinaryUnifiedPowerFactorAt n D ell B H A L ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < D + 1 →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        A ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
        HasExactPowerAgreement domain values iota (D + 1) z P := by
  classical
  let Candidate : E → E[X] → Prop := fun z P ↦
    differentialSpecialization (challengeSpecialization Q z) P = 0
  let r : Unit → ℕ := fun _ ↦ 0
  let J : Unit → ℕ := fun _ ↦ ell * B + H * ordinaryPsi D B
  let fiberDegree : Unit → ℕ := fun _ ↦ B
  obtain ⟨exceptional, hcard, hgood⟩ := exists_geometricTransfer_exceptional
    (n := n) (k := D + 1) (ℓ := ell) (L := L) (A := A) (ν := Unit)
    (domain := domain) (w := values) (iota := iota) Candidate preliminary
    r J fiberDegree (fun _ ↦ offGraph) (fun _ ↦ retained)
    (by omega) (by omega) hLA hAn hell
    (fun s ↦ by simpa [r, J, geometricTransferIncidenceProduct] using hoffGraph)
    (fun s ↦ by simpa [r, fiberDegree, geometricTransferIncidenceProduct] using hretained)
    (fun _ P hP ↦ hdegree P hP) (fun _ P hP ↦ hcommon P hP)
    (fun z P _hCandidate hP hA hz ↦ by
      rcases hcoverage z P hP _hCandidate hA hz with hoff | ⟨tuple, ht, heq⟩
      · exact Or.inl ⟨(), hoff⟩
      · exact Or.inr ⟨(), tuple, ht, heq⟩)
  refine ⟨exceptional, ?_, ?_⟩
  · apply hcard.trans
    have htransferBudget :
        geometricTransferBound preliminary.card n (D + 1) ell L A r J fiberDegree =
          (preliminary.card : ℚ) +
            (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) *
              (ell * B + H * ordinaryPsi D B : ℕ) +
            ((ell * (n - L) : ℕ) : ℚ) * B := by
      unfold geometricTransferBound
      simp only [r, J, fiberDegree, geometricTransferIncidenceProduct_zero,
        Fintype.sum_unique, one_mul]
    rw [htransferBudget]
    unfold ordinaryUnifiedPowerFactorAt ordinaryUnifiedPowerFactorRawAt
    calc
      (preliminary.card : ℚ) +
            (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) *
              (ell * B + H * ordinaryPsi D B : ℕ) +
            ((ell * (n - L) : ℕ) : ℚ) * B ≤
          (((2 * B - 1) * H : ℕ) : ℚ) +
            (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) *
              (ell * B + H * ordinaryPsi D B : ℕ) +
            ((ell * (n - L) : ℕ) : ℚ) * B :=
        add_le_add (add_le_add hpreliminary le_rfl) le_rfl
      _ = _ := by push_cast; ring
  · intro z hz P hP hroot hA
    exact hgood z hz P hroot hP hA

/-- The polynomial-curve mixed degree satisfies the unified bound for every separable factor
degree, with no comparison between `b` and `D`. -/
theorem ordinaryFrobeniusPowerMixedDegree_le_unified {D s b : ℕ} (ell h : ℕ)
    (hD : 1 ≤ D) (hs : 1 ≤ s) (hb : 1 ≤ b) :
    ordinaryFrobeniusPowerMixedDegree D ell h s b ≤
      ell * (s * b) + h * ordinaryPsi D (s * b) := by
  rw [ordinaryFrobeniusPowerMixedDegree_eq D ell h s b hb]
  have hcoefficient := ordinaryFrobenius_unified_factor hD hs hb
  nlinarith

/-- One pulled factor spends the unified budget at a free retention threshold `L`. -/
theorem ordinaryFrobeniusPower_charge_le_unifiedAt (theta : ℚ)
    (n D ell h s b L : ℕ)
    (htheta : 0 ≤ theta) (hD : 1 ≤ D) (hs : 1 ≤ s) (hb : 1 ≤ b) :
    ((2 * b - 1) * h : ℕ) + theta * ordinaryFrobeniusPowerMixedDegree D ell h s b +
        (ell * ((n - L) * b) : ℕ) ≤
      ordinaryUnifiedPowerFactorRawAt theta n D ell (s * b) h L := by
  have hbs : b ≤ s * b := by nlinarith
  have hmixed := ordinaryFrobeniusPowerMixedDegree_le_unified ell h hD hs hb
  unfold ordinaryUnifiedPowerFactorRawAt
  apply add_le_add
  · apply add_le_add
    · exact_mod_cast Nat.mul_le_mul_right h
        (Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 hbs) 1)
    · exact mul_le_mul_of_nonneg_left (by exact_mod_cast hmixed) htheta
  · exact_mod_cast Nat.mul_le_mul_left ell (Nat.mul_le_mul_left (n - L) hbs)

/-- One pulled polynomial-curve factor spends the unified budget at its original root degree. -/
theorem ordinaryFrobeniusPower_charge_le_unified (theta : ℚ) (n D ell h s b : ℕ)
    (htheta : 0 ≤ theta) (hD : 1 ≤ D) (hs : 1 ≤ s) (hb : 1 ≤ b) :
    ((2 * b - 1) * h : ℕ) + theta * ordinaryFrobeniusPowerMixedDegree D ell h s b +
        (ell * ((n - D - 1) * b) : ℕ) ≤
      ordinaryUnifiedPowerFactorRaw theta n D ell (s * b) h := by
  have hbs : b ≤ s * b := by nlinarith
  have hmixed := ordinaryFrobeniusPowerMixedDegree_le_unified ell h hD hs hb
  unfold ordinaryUnifiedPowerFactorRaw
  apply add_le_add
  · apply add_le_add
    · exact_mod_cast Nat.mul_le_mul_right h
        (Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 hbs) 1)
    · exact mul_le_mul_of_nonneg_left (by exact_mod_cast hmixed) htheta
  · exact_mod_cast Nat.mul_le_mul_left ell (Nat.mul_le_mul_left (n - D - 1) hbs)

open Classical in
/-- One irreducible Frobenius factor has the unified polynomial-curve charge at a free retention
threshold. -/
theorem exists_exceptional_frobeniusPowerFactorSolutions_unifiedAt [IsAlgClosed E]
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] 0) (p e D h b L A : ℕ) [ExpChar E p]
    (hD : 0 < D) (hell : 0 < ell) (hb : 0 < b)
    (hDL : D < L) (hLA : L ≤ A) (hAn : A ≤ n)
    (hheight : ChallengeHeightLE Q h)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ b)
    (hirr : Irreducible Q) (hder : pderiv (some 0) Q ≠ 0)
    (hdegree : Q.degreeOf (some 0) = b) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤ ordinaryUnifiedPowerFactorAt
        n D ell (p ^ e * b) h A L ∧
      ∀ w : E, w ^ (p ^ e) ∉ exceptional → ∀ P : E[X],
        P.degree < D + 1 →
        differentialSpecialization (challengeSpecialization Q w) (expand E (p ^ e) P) = 0 →
        A ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (powerBatchedWord (fun t i ↦ iota (values t i)) (w ^ (p ^ e))) P).card →
        HasExactPowerAgreement domain values iota (D + 1) (w ^ (p ^ e)) P := by
  classical
  let roots : Fin n → E := fun i ↦ (iterateFrobeniusEquiv E p e).symm (iota (domain i))
  have hroots : ∀ i, roots i ^ (p ^ e) = iota (domain i) := by
    intro i
    exact (iterateFrobeniusEquiv E p e).apply_symm_apply (iota (domain i))
  have hs : 0 < p ^ e := pow_pos (expChar_pos E p) e
  have hK : D * p ^ e + 1 ≤ p ^ e * (D + 1) := by nlinarith
  have htau : 0 < 2 * D * p ^ e - 1 := by
    have hDs := Nat.mul_pos hD hs
    have : 2 ≤ 2 * D * p ^ e := by nlinarith
    omega
  obtain ⟨ex, hexCard, hex⟩ := exists_exceptional_frobeniusPowerSeparableSolutions_at
    (K := D * p ^ e + 1) domain values iota roots Q p e (2 * D * p ^ e - 1) h b A
    hroots (by omega) hK (by intro l; simp only [Nat.mul_assoc]; omega)
    htau hell hb (by omega) hLA hAn hheight hjet hirr hder hdegree
  refine ⟨ex.image (fun w ↦ w ^ (p ^ e)), ?_, ?_⟩
  · have hcard : ((ex.image (fun w ↦ w ^ (p ^ e))).card : ℚ) ≤ ex.card := by
      exact_mod_cast Finset.card_image_le
    apply hcard.trans (hexCard.trans ?_)
    let theta : ℚ := ((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)
    have htheta : 0 ≤ theta := by positivity
    have hcharge := ordinaryFrobeniusPower_charge_le_unifiedAt
      theta n D ell h (p ^ e) b L htheta hD hs hb
    unfold ordinaryFrobeniusPowerMixedDegree at hcharge
    unfold ordinaryUnifiedPowerFactorAt
    calc
      ((h * (1 + (2 * D * p ^ e - 1) * (b - 1)) +
              b * (p ^ e * ell + (2 * D * p ^ e - 1) * h) : ℕ) : ℚ) * theta +
            ((ell * (n - L) * b : ℕ) : ℚ) + (((2 * b - 1) * h : ℕ) : ℚ) =
          (((2 * b - 1) * h : ℕ) : ℚ) + theta *
              ((h * (1 + (2 * D * p ^ e - 1) * (b - 1)) +
                b * (p ^ e * ell + (2 * D * p ^ e - 1) * h) : ℕ) : ℚ) +
            ((ell * ((n - L) * b) : ℕ) : ℚ) := by
        push_cast
        ring
      _ ≤ ordinaryUnifiedPowerFactorRawAt theta n D ell (p ^ e * b) h L := hcharge
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

open Classical in
/-- One irreducible Frobenius factor has the unified polynomial-curve charge. The constituent
message keeps its original degree bound; inseparability creates no extra challenge loss. -/
theorem exists_exceptional_frobeniusPowerFactorSolutions_unified [IsAlgClosed E]
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] 0) (p e D h b A : ℕ) [ExpChar E p]
    (hD : 0 < D) (hell : 0 < ell) (hb : 0 < b) (hDA : D + 1 ≤ A) (hAn : A ≤ n)
    (hheight : ChallengeHeightLE Q h)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ b)
    (hirr : Irreducible Q) (hder : pderiv (some 0) Q ≠ 0)
    (hdegree : Q.degreeOf (some 0) = b) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤ ordinaryUnifiedPowerFactorRaw
        (((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ)) n D ell (p ^ e * b) h ∧
      ∀ w : E, w ^ (p ^ e) ∉ exceptional → ∀ P : E[X],
        P.degree < D + 1 →
        differentialSpecialization (challengeSpecialization Q w) (expand E (p ^ e) P) = 0 →
        A ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (powerBatchedWord (fun t i ↦ iota (values t i)) (w ^ (p ^ e))) P).card →
        HasExactPowerAgreement domain values iota (D + 1) (w ^ (p ^ e)) P := by
  classical
  let roots : Fin n → E := fun i ↦ (iterateFrobeniusEquiv E p e).symm (iota (domain i))
  have hroots : ∀ i, roots i ^ (p ^ e) = iota (domain i) := by
    intro i
    exact (iterateFrobeniusEquiv E p e).apply_symm_apply (iota (domain i))
  have hs : 0 < p ^ e := pow_pos (expChar_pos E p) e
  have hK : D * p ^ e + 1 ≤ p ^ e * (D + 1) := by nlinarith
  have htau : 0 < 2 * D * p ^ e - 1 := by
    have hDs := Nat.mul_pos hD hs
    have : 2 ≤ 2 * D * p ^ e := by nlinarith
    omega
  obtain ⟨ex, hexCard, hex⟩ := exists_exceptional_frobeniusPowerSeparableSolutions
    (K := D * p ^ e + 1) domain values iota roots Q p e (2 * D * p ^ e - 1) h b A
    hroots (by omega) hK (by intro l; simp only [Nat.mul_assoc]; omega)
    htau hell hb hDA hAn hheight hjet hirr hder hdegree
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
    have hcharge := ordinaryFrobeniusPower_charge_le_unified theta n D ell h (p ^ e) b
      htheta hD hs hb
    unfold ordinaryFrobeniusPowerMixedDegree at hcharge
    calc
      ((h * (1 + (2 * D * p ^ e - 1) * (b - 1)) +
              b * (p ^ e * ell + (2 * D * p ^ e - 1) * h) : ℕ) : ℚ) * theta +
            ((ell * (n - D - 1) * b : ℕ) : ℚ) + (((2 * b - 1) * h : ℕ) : ℚ) =
          (((2 * b - 1) * h : ℕ) : ℚ) + theta *
              ((h * (1 + (2 * D * p ^ e - 1) * (b - 1)) +
                b * (p ^ e * ell + (2 * D * p ^ e - 1) * h) : ℕ) : ℚ) +
            ((ell * ((n - D - 1) * b) : ℕ) : ℚ) := by
        push_cast
        ring
      _ ≤ ordinaryUnifiedPowerFactorRaw theta n D ell (p ^ e * b) h := hcharge
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

open Classical in
/-- An irreducible ordinary equation has the free-retention unified charge in every
characteristic. -/
theorem exists_exceptional_irreducibleOrdinaryPowerEquation_unifiedAt [IsAlgClosed E]
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] 0) (D h L A : ℕ)
    (hD : 0 < D) (hell : 0 < ell) (hDL : D < L) (hLA : L ≤ A) (hAn : A ≤ n)
    (hheight : ChallengeHeightLE Q h) (hirr : Irreducible Q)
    (hpos : 0 < Q.degreeOf (some 0)) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤ ordinaryUnifiedPowerFactorAt
        n D ell (Q.degreeOf (some 0)) h A L ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < D + 1 →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        A ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
        HasExactPowerAgreement domain values iota (D + 1) z P := by
  classical
  let p := ringExpChar E
  obtain ⟨e, R, hRirr, hRder, hRdegree, _, hRheight, htransport⟩ :=
    exists_frobeniusEquation p hpos hirr hheight
  have hRpos : 0 < R.degreeOf (some 0) := by
    by_contra! hz
    have hz' := Nat.eq_zero_of_le_zero hz
    rw [hz', zero_mul] at hRdegree
    omega
  obtain ⟨ex, hcard, hgood⟩ := exists_exceptional_frobeniusPowerFactorSolutions_unifiedAt
    domain values iota R p e D h (R.degreeOf (some 0)) L A
      hD hell hRpos hDL hLA hAn hRheight
      (by rw [ordinary_jetWeight_eq_degreeOf]) hRirr hRder rfl
  have heq : p ^ e * R.degreeOf (some 0) = Q.degreeOf (some 0) := by
    simpa only [Nat.mul_comm] using hRdegree
  refine ⟨ex, ?_, ?_⟩
  · simpa only [heq] using hcard
  · intro z hz P hdegree hroot hagree
    let w := (iterateFrobeniusEquiv E p e).symm z
    have hw : w ^ (p ^ e) = z := (iterateFrobeniusEquiv E p e).apply_symm_apply z
    have hEval (x : E) : (Polynomial.aeval x).toRingHom = Polynomial.evalRingHom x := by
      apply Polynomial.ringHom_ext
      · intro a
        simp
      · simp
    have hRroot : differentialSpecialization (challengeSpecialization R w)
        (expand E (p ^ e) P) = 0 := by
      rw [challengeSpecialization, hEval]
      apply htransport P w
      rw [hw]
      simpa only [challengeSpecialization, hEval] using hroot
    have hout := hgood w (by simpa only [hw] using hz) P hdegree hRroot
      (by simpa only [hw] using hagree)
    simpa only [hw] using hout

open Classical in
/-- An irreducible ordinary equation has the unified polynomial-curve charge in every
characteristic. Frobenius extraction is internal, and the charge is measured at the original
root degree. -/
theorem exists_exceptional_irreducibleOrdinaryPowerEquation_unified [IsAlgClosed E]
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] 0) (D h A : ℕ)
    (hD : 0 < D) (hell : 0 < ell) (hDA : D + 1 ≤ A) (hAn : A ≤ n)
    (hheight : ChallengeHeightLE Q h) (hirr : Irreducible Q)
    (hpos : 0 < Q.degreeOf (some 0)) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤ ordinaryUnifiedPowerFactorRaw
        (((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ)) n D ell
          (Q.degreeOf (some 0)) h ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < D + 1 →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        A ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
        HasExactPowerAgreement domain values iota (D + 1) z P := by
  classical
  let p := ringExpChar E
  obtain ⟨e, R, hRirr, hRder, hRdegree, _, hRheight, htransport⟩ :=
    exists_frobeniusEquation p hpos hirr hheight
  have hRpos : 0 < R.degreeOf (some 0) := by
    by_contra! hz
    have hz' := Nat.eq_zero_of_le_zero hz
    rw [hz', zero_mul] at hRdegree
    omega
  obtain ⟨ex, hcard, hgood⟩ := exists_exceptional_frobeniusPowerFactorSolutions_unified
    domain values iota R p e D h (R.degreeOf (some 0)) A hD hell hRpos hDA hAn
      hRheight (by rw [ordinary_jetWeight_eq_degreeOf]) hRirr hRder rfl
  have heq : p ^ e * R.degreeOf (some 0) = Q.degreeOf (some 0) := by
    simpa only [Nat.mul_comm] using hRdegree
  refine ⟨ex, ?_, ?_⟩
  · simpa only [heq] using hcard
  · intro z hz P hdegree hroot hagree
    let w := (iterateFrobeniusEquiv E p e).symm z
    have hw : w ^ (p ^ e) = z := (iterateFrobeniusEquiv E p e).apply_symm_apply z
    have hEval (x : E) : (Polynomial.aeval x).toRingHom = Polynomial.evalRingHom x := by
      apply Polynomial.ringHom_ext
      · intro a
        simp
      · simp
    have hRroot : differentialSpecialization (challengeSpecialization R w)
        (expand E (p ^ e) P) = 0 := by
      rw [challengeSpecialization, hEval]
      apply htransport P w
      rw [hw]
      simpa only [challengeSpecialization, hEval] using hroot
    have hout := hgood w (by simpa only [hw] using hz) P hdegree hRroot
      (by simpa only [hw] using hagree)
    simpa only [hw] using hout

open Classical in
/-- Content and all distinct positive-root factors assemble into the free-retention budget. -/
theorem exists_exceptional_ordinaryPowerFactorAssembly_unifiedAt
    {W V R sigma : Type*} [CommRing R] [IsDomain R]
    (Q : MvPolynomial (Option sigma) F) (hQ : Q ≠ 0)
    (ev : W → V → MvPolynomial (Option sigma) F →+* R)
    (Good : W → V → Prop) (height : MvPolynomial (Option sigma) F → ℕ)
    (theta : ℚ) (n D ell B H L : ℕ) (htheta : 0 ≤ theta) (hB : 1 ≤ B)
    (hroot : Q.degreeOf none ≤ B)
    (hheight : height (ordinaryContent Q) +
      ∑ a ∈ ordinaryRootFactorClasses Q, height (ordinaryFactorRepresentative a) ≤ H)
    (hcontent : ∃ ex : Finset W, ex.card ≤ height (ordinaryContent Q) ∧
      ∀ w ∉ ex, ∀ v, ev w v (ordinaryContent Q) ≠ 0)
    (hfactors : ∀ a ∈ ordinaryRootFactorClasses Q, ∃ ex : Finset W,
      (ex.card : ℚ) ≤ ordinaryUnifiedPowerFactorRawAt theta n D ell
        (degreeOf none (ordinaryFactorRepresentative a))
        (height (ordinaryFactorRepresentative a)) L ∧
      ∀ w ∉ ex, ∀ v, ev w v (ordinaryFactorRepresentative a) = 0 → Good w v) :
    ∃ ex : Finset W,
      (ex.card : ℚ) ≤ ordinaryUnifiedPowerFactorRawAt theta n D ell B H L ∧
      ∀ w ∉ ex, ∀ v, ev w v Q = 0 → Good w v := by
  classical
  obtain ⟨contentEx, hcCard, hc⟩ := hcontent
  let S := ordinaryRootFactorClasses Q
  choose factorEx hfCard hf using hfactors
  let allEx := contentEx ∪ S.biUnion fun a =>
    if ha : a ∈ S then factorEx a ha else ∅
  refine ⟨allEx, ?_, ?_⟩
  · have hUnion : allEx.card ≤ contentEx.card +
        ∑ a ∈ S, (if ha : a ∈ S then factorEx a ha else ∅).card :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_biUnion_le _)
    have hsum :
        (∑ a ∈ S, ((if ha : a ∈ S then factorEx a ha else ∅).card : ℚ)) ≤
          ∑ a ∈ S, ordinaryUnifiedPowerFactorRawAt theta n D ell
            (degreeOf none (ordinaryFactorRepresentative a))
            (height (ordinaryFactorRepresentative a)) L := by
      apply Finset.sum_le_sum
      intro a ha
      simpa only [dif_pos ha] using hfCard a ha
    have hUnionQ : (allEx.card : ℚ) ≤ contentEx.card +
        ∑ a ∈ S, ((if ha : a ∈ S then factorEx a ha else ∅).card : ℚ) := by
      exact_mod_cast hUnion
    apply hUnionQ.trans
    apply (add_le_add (show (contentEx.card : ℚ) ≤ height (ordinaryContent Q) by
      exact_mod_cast hcCard) hsum).trans
    exact ordinaryUnifiedPowerFactorRawAt_sum_le S
      (fun a => degreeOf none (ordinaryFactorRepresentative a))
      (fun a => height (ordinaryFactorRepresentative a)) theta n D ell B H L
      (height (ordinaryContent Q)) htheta hB
      ((ordinary_root_degree_sum_le Q hQ).trans hroot) hheight
  · intro w hw v hzero
    have hwc : w ∉ contentEx := fun hm => hw (Finset.mem_union_left _ hm)
    have hsplit := (ordinary_split_zero_iff Q hQ (ev w v)).mpr hzero
    rw [map_mul] at hsplit
    have hr := (mul_eq_zero.mp hsplit).resolve_left (hc w hwc v)
    rw [ordinaryRootProduct, map_prod, Finset.prod_eq_zero_iff] at hr
    obtain ⟨a, ha, hazero⟩ := hr
    apply hf a ha w _ v hazero
    intro hmem
    apply hw
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    exact ⟨a, ha, by simpa only [dif_pos (show a ∈ S from ha)] using hmem⟩

open Classical in
/-- Content and all distinct positive-root factors assemble into the unified budget. -/
theorem exists_exceptional_ordinaryPowerFactorAssembly_unified
    {W V R sigma : Type*} [CommRing R] [IsDomain R]
    (Q : MvPolynomial (Option sigma) F) (hQ : Q ≠ 0)
    (ev : W → V → MvPolynomial (Option sigma) F →+* R)
    (Good : W → V → Prop) (height : MvPolynomial (Option sigma) F → ℕ)
    (theta : ℚ) (n D ell B H : ℕ) (htheta : 0 ≤ theta) (hB : 1 ≤ B)
    (hroot : Q.degreeOf none ≤ B)
    (hheight : height (ordinaryContent Q) +
      ∑ a ∈ ordinaryRootFactorClasses Q, height (ordinaryFactorRepresentative a) ≤ H)
    (hcontent : ∃ ex : Finset W, ex.card ≤ height (ordinaryContent Q) ∧
      ∀ w ∉ ex, ∀ v, ev w v (ordinaryContent Q) ≠ 0)
    (hfactors : ∀ a ∈ ordinaryRootFactorClasses Q, ∃ ex : Finset W,
      (ex.card : ℚ) ≤ ordinaryUnifiedPowerFactorRaw theta n D ell
        (degreeOf none (ordinaryFactorRepresentative a))
        (height (ordinaryFactorRepresentative a)) ∧
      ∀ w ∉ ex, ∀ v, ev w v (ordinaryFactorRepresentative a) = 0 → Good w v) :
    ∃ ex : Finset W, (ex.card : ℚ) ≤ ordinaryUnifiedPowerFactorRaw theta n D ell B H ∧
      ∀ w ∉ ex, ∀ v, ev w v Q = 0 → Good w v := by
  classical
  obtain ⟨contentEx, hcCard, hc⟩ := hcontent
  let S := ordinaryRootFactorClasses Q
  choose factorEx hfCard hf using hfactors
  let allEx := contentEx ∪ S.biUnion fun a =>
    if ha : a ∈ S then factorEx a ha else ∅
  refine ⟨allEx, ?_, ?_⟩
  · have hUnion : allEx.card ≤ contentEx.card +
        ∑ a ∈ S, (if ha : a ∈ S then factorEx a ha else ∅).card :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_biUnion_le _)
    have hsum :
        (∑ a ∈ S, ((if ha : a ∈ S then factorEx a ha else ∅).card : ℚ)) ≤
          ∑ a ∈ S, ordinaryUnifiedPowerFactorRaw theta n D ell
            (degreeOf none (ordinaryFactorRepresentative a))
            (height (ordinaryFactorRepresentative a)) := by
      apply Finset.sum_le_sum
      intro a ha
      simpa only [dif_pos ha] using hfCard a ha
    have hUnionQ : (allEx.card : ℚ) ≤ contentEx.card +
        ∑ a ∈ S, ((if ha : a ∈ S then factorEx a ha else ∅).card : ℚ) := by
      exact_mod_cast hUnion
    apply hUnionQ.trans
    apply (add_le_add (show (contentEx.card : ℚ) ≤ height (ordinaryContent Q) by
      exact_mod_cast hcCard) hsum).trans
    exact ordinaryUnifiedPowerFactorRaw_sum_le S
      (fun a => degreeOf none (ordinaryFactorRepresentative a))
      (fun a => height (ordinaryFactorRepresentative a)) theta n D ell B H
      (height (ordinaryContent Q)) htheta hB
      ((ordinary_root_degree_sum_le Q hQ).trans hroot) hheight
  · intro w hw v hzero
    have hwc : w ∉ contentEx := fun hm => hw (Finset.mem_union_left _ hm)
    have hsplit := (ordinary_split_zero_iff Q hQ (ev w v)).mpr hzero
    rw [map_mul] at hsplit
    have hr := (mul_eq_zero.mp hsplit).resolve_left (hc w hwc v)
    rw [ordinaryRootProduct, map_prod, Finset.prod_eq_zero_iff] at hr
    obtain ⟨a, ha, hazero⟩ := hr
    apply hf a ha w _ v hazero
    intro hmem
    apply hw
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    exact ⟨a, ha, by simpa only [dif_pos (show a ∈ S from ha)] using hmem⟩

open Classical in
/-- Every nonzero positive-root-degree ordinary equation has the manuscript's unconditional
free-retention polynomial-curve transfer over an algebraically closed field. -/
theorem exists_exceptional_ordinaryPowerEquation_freeRetention [IsAlgClosed E]
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] 0) (D h B L A : ℕ)
    (hQ : Q ≠ 0) (hD : 0 < D) (hell : 0 < ell) (hB : 1 ≤ B)
    (_hDn : D + 2 ≤ n) (hDL : D < L) (hLA : L ≤ A) (hAn : A ≤ n)
    (hheight : ChallengeHeightLE Q h) (hdegree : Q.degreeOf (some 0) ≤ B) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤ ordinaryUnifiedPowerFactorAt n D ell B h A L ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < D + 1 →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        A ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
        HasExactPowerAgreement domain values iota (D + 1) z P := by
  classical
  let flat := ordinaryFlatten E Q
  let height (R : MvPolynomial (Option (Fin 2)) E) := R.degreeOf (some 1)
  let ev (z : E) (P : E[X]) :=
    ((differentialSpecializationHom P).toRingHom.comp
      (MvPolynomial.map (σ := JetVariable 0) (Polynomial.aeval z).toRingHom)).comp
        (ordinaryUnflatten E).toRingHom
  let Good (z : E) (P : E[X]) := P.degree < D + 1 →
    A ≤ (polynomialAgreementSet (mappedDomain domain iota)
      (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
    HasExactPowerAgreement domain values iota (D + 1) z P
  have hflat : flat ≠ 0 := (ordinaryFlatten E).map_ne_zero_iff.mpr hQ
  have hdegUnflat (R : MvPolynomial (Option (Fin 2)) E) :
      (ordinaryUnflatten E R).degreeOf (some 0) = R.degreeOf none := by
    rw [← degreeOf_none_ordinaryFlatten]
    simp [ordinaryUnflatten]
  have hev (z : E) (P : E[X]) (R : MvPolynomial (Option (Fin 2)) E) :
      ev z P R = differentialSpecialization
        (challengeSpecialization (ordinaryUnflatten E R) z) P := rfl
  have hc : ∃ ex : Finset E, ex.card ≤ height (ordinaryContent flat) ∧
      ∀ z ∉ ex, ∀ P, ev z P (ordinaryContent flat) ≠ 0 := by
    obtain ⟨ex, hcard, hgood⟩ := exists_exceptional_ordinaryContent
      (ordinaryUnflatten E (ordinaryContent flat))
      ((ordinaryUnflatten E).map_ne_zero_iff.mpr (ordinaryContent_ne_zero flat))
      (by rw [hdegUnflat, degreeOf_ordinaryContent_none])
      (challengeHeightLE_ordinaryUnflatten_of_degreeOf_le _ le_rfl)
    exact ⟨ex, hcard, hgood⟩
  have hf : ∀ a ∈ ordinaryRootFactorClasses flat, ∃ ex : Finset E,
      (ex.card : ℚ) ≤ ordinaryUnifiedPowerFactorRawAt
        (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) n D ell
        (degreeOf none (ordinaryFactorRepresentative a))
        (height (ordinaryFactorRepresentative a)) L ∧
      ∀ z ∉ ex, ∀ P, ev z P (ordinaryFactorRepresentative a) = 0 → Good z P := by
    intro a ha
    obtain ⟨hirr, hpos⟩ := ordinaryRootFactorClasses_spec flat ha
    obtain ⟨ex, hcard, hgood⟩ :=
      exists_exceptional_irreducibleOrdinaryPowerEquation_unifiedAt
        domain values iota (ordinaryUnflatten E (ordinaryFactorRepresentative a)) D
        (height (ordinaryFactorRepresentative a)) L A hD hell hDL hLA hAn
        (challengeHeightLE_ordinaryUnflatten_of_degreeOf_le _ le_rfl)
        (hirr.map (ordinaryUnflatten E)) (by simpa only [hdegUnflat] using hpos)
    refine ⟨ex, ?_, ?_⟩
    · unfold ordinaryUnifiedPowerFactorAt at hcard
      simpa only [hdegUnflat] using hcard
    · intro z hz P hroot hP hagree
      exact hgood z hz P hP hroot hagree
  obtain ⟨ex, hcard, hgood⟩ := exists_exceptional_ordinaryPowerFactorAssembly_unifiedAt
    flat hflat ev Good height (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ))
    n D ell B h L (by positivity) hB
    (by simpa only [flat, degreeOf_none_ordinaryFlatten] using hdegree)
    ((ordinary_degree_sum_le flat hflat (some 1)).trans
      (degreeOf_challenge_ordinaryFlatten_le Q hheight)) hc hf
  refine ⟨ex, ?_, ?_⟩
  · simpa only [ordinaryUnifiedPowerFactorAt] using hcard
  · intro z hz P hP hroot hagree
    apply hgood z hz P _ hP hagree
    rw [hev]
    simpa only [flat, ordinaryUnflatten, AlgEquiv.symm_apply_apply] using hroot

open Classical in
/-- Every nonzero ordinary equation has the manuscript's single unified polynomial-curve
transfer over an algebraically closed field. No comparison between its root degree and `D` is
required. -/
theorem exists_exceptional_ordinaryPowerEquation_unified [IsAlgClosed E]
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] 0) (D h B A : ℕ)
    (hQ : Q ≠ 0) (hD : 0 < D) (hell : 0 < ell) (hB : 1 ≤ B)
    (hDA : D + 1 ≤ A) (hAn : A ≤ n)
    (hheight : ChallengeHeightLE Q h) (hdegree : Q.degreeOf (some 0) ≤ B) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤ ordinaryUnifiedPowerFactorRaw
        (((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ)) n D ell B h ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < D + 1 →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        A ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
        HasExactPowerAgreement domain values iota (D + 1) z P := by
  classical
  let flat := ordinaryFlatten E Q
  let height (R : MvPolynomial (Option (Fin 2)) E) := R.degreeOf (some 1)
  let ev (z : E) (P : E[X]) :=
    ((differentialSpecializationHom P).toRingHom.comp
      (MvPolynomial.map (σ := JetVariable 0) (Polynomial.aeval z).toRingHom)).comp
        (ordinaryUnflatten E).toRingHom
  let Good (z : E) (P : E[X]) := P.degree < D + 1 →
    A ≤ (polynomialAgreementSet (mappedDomain domain iota)
      (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
    HasExactPowerAgreement domain values iota (D + 1) z P
  have hflat : flat ≠ 0 := (ordinaryFlatten E).map_ne_zero_iff.mpr hQ
  have hdegUnflat (R : MvPolynomial (Option (Fin 2)) E) :
      (ordinaryUnflatten E R).degreeOf (some 0) = R.degreeOf none := by
    rw [← degreeOf_none_ordinaryFlatten]
    simp [ordinaryUnflatten]
  have hev (z : E) (P : E[X]) (R : MvPolynomial (Option (Fin 2)) E) :
      ev z P R = differentialSpecialization
        (challengeSpecialization (ordinaryUnflatten E R) z) P := rfl
  have hc : ∃ ex : Finset E, ex.card ≤ height (ordinaryContent flat) ∧
      ∀ z ∉ ex, ∀ P, ev z P (ordinaryContent flat) ≠ 0 := by
    obtain ⟨ex, hcard, hgood⟩ := exists_exceptional_ordinaryContent
      (ordinaryUnflatten E (ordinaryContent flat))
      ((ordinaryUnflatten E).map_ne_zero_iff.mpr (ordinaryContent_ne_zero flat))
      (by rw [hdegUnflat, degreeOf_ordinaryContent_none])
      (challengeHeightLE_ordinaryUnflatten_of_degreeOf_le _ le_rfl)
    exact ⟨ex, hcard, hgood⟩
  have hf : ∀ a ∈ ordinaryRootFactorClasses flat, ∃ ex : Finset E,
      (ex.card : ℚ) ≤ ordinaryUnifiedPowerFactorRaw
        (((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ)) n D ell
        (degreeOf none (ordinaryFactorRepresentative a))
        (height (ordinaryFactorRepresentative a)) ∧
      ∀ z ∉ ex, ∀ P, ev z P (ordinaryFactorRepresentative a) = 0 → Good z P := by
    intro a ha
    obtain ⟨hirr, hpos⟩ := ordinaryRootFactorClasses_spec flat ha
    obtain ⟨ex, hcard, hgood⟩ := exists_exceptional_irreducibleOrdinaryPowerEquation_unified
      domain values iota (ordinaryUnflatten E (ordinaryFactorRepresentative a)) D
      (height (ordinaryFactorRepresentative a)) A hD hell hDA hAn
      (challengeHeightLE_ordinaryUnflatten_of_degreeOf_le _ le_rfl)
      (hirr.map (ordinaryUnflatten E)) (by simpa only [hdegUnflat] using hpos)
    refine ⟨ex, ?_, ?_⟩
    · simpa only [hdegUnflat] using hcard
    · intro z hz P hroot hP hagree
      exact hgood z hz P hP hroot hagree
  obtain ⟨ex, hcard, hgood⟩ := exists_exceptional_ordinaryPowerFactorAssembly_unified
    flat hflat ev Good height (((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ))
    n D ell B h (by positivity) hB
    (by simpa only [flat, degreeOf_none_ordinaryFlatten] using hdegree)
    ((ordinary_degree_sum_le flat hflat (some 1)).trans
      (degreeOf_challenge_ordinaryFlatten_le Q hheight)) hc hf
  refine ⟨ex, hcard, ?_⟩
  intro z hz P hP hroot hagree
  apply hgood z hz P _ hP hagree
  rw [hev]
  simpa only [flat, ordinaryUnflatten, AlgEquiv.symm_apply_apply] using hroot

open Classical in
/-- Compatibility presentation of the existing all-characteristic ordinary transfer at the
historical retention threshold `L = D + 1`.  This is the route used by the base-field consumer,
so existing certificates keep their literal budget while the public arithmetic now exposes the
free threshold. -/
theorem exists_exceptional_ordinaryPowerEquation_unifiedAt_succ [IsAlgClosed E]
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] 0) (D h B A : ℕ)
    (hQ : Q ≠ 0) (hD : 0 < D) (hell : 0 < ell) (hB : 1 ≤ B)
    (hDA : D + 1 ≤ A) (hAn : A ≤ n)
    (hheight : ChallengeHeightLE Q h) (hdegree : Q.degreeOf (some 0) ≤ B) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤ ordinaryUnifiedPowerFactorAt n D ell B h A (D + 1) ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < D + 1 →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        A ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
        HasExactPowerAgreement domain values iota (D + 1) z P := by
  obtain ⟨exceptional, hcard, hgood⟩ := exists_exceptional_ordinaryPowerEquation_unified
    domain values iota Q D h B A hQ hD hell hB hDA hAn hheight hdegree
  refine ⟨exceptional, ?_, hgood⟩
  rw [ordinaryUnifiedPowerFactorAt_succ_eq n D ell B h A hDA hAn]
  exact hcard

open Classical in
/-- Arbitrary-field semantic free-retention recovery with the exact manuscript bound. -/
theorem exists_exceptional_ordinaryPowerEquation_base_freeRetention
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F)
    (Q : DifferentialPolynomial F[X] 0) (D h B L A : ℕ)
    (hQ : Q ≠ 0) (hD : 0 < D) (hell : 0 < ell) (hB : 1 ≤ B)
    (hDn : D + 2 ≤ n) (hDL : D < L) (hLA : L ≤ A) (hAn : A ≤ n)
    (hheight : ChallengeHeightLE Q h) (hdegree : Q.degreeOf (some 0) ≤ B) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℚ) ≤ ordinaryUnifiedPowerFactorAt n D ell B h A L ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < D + 1 →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        A ≤ (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F) (D + 1) z P := by
  classical
  let E := AlgebraicClosure F
  let iota := algebraMap F E
  let QE := MvPolynomial.map (Polynomial.mapRingHom iota) Q
  have hQE : QE ≠ 0 := by
    intro hz
    apply hQ
    apply MvPolynomial.map_injective (Polynomial.mapRingHom iota)
      (Polynomial.map_injective iota iota.injective)
    simpa only [map_zero] using hz
  have hQheight : ChallengeHeightLE QE h := hheight.map_coefficients iota
  have hQdegree : QE.degreeOf (some 0) ≤ B := by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro u hu
    exact (MvPolynomial.monomial_le_degreeOf (some 0)
      (MvPolynomial.support_map_subset _ _ hu)).trans hdegree
  obtain ⟨ex, hexCard, hex⟩ := exists_exceptional_ordinaryPowerEquation_freeRetention
    domain values iota QE D h B L A hQE hD hell hB hDn hDL hLA hAn hQheight hQdegree
  let baseEx := ex.preimage iota iota.injective.injOn
  refine ⟨baseEx, ?_, ?_⟩
  · apply (show (baseEx.card : ℚ) ≤ ex.card by
      exact_mod_cast Finset.card_le_card_of_injOn iota
        (fun _ hz ↦ Finset.mem_preimage.mp hz) iota.injective.injOn).trans
    exact hexCard
  · intro z hz P hP hroot hagree
    apply HasExactPowerAgreement.descend domain values iota (D + 1) z P
    apply hex (iota z)
    · exact fun hmem ↦ hz (Finset.mem_preimage.mpr hmem)
    · exact Polynomial.degree_map_le.trans_lt hP
    · rw [← map_symbolicDifferentialSpecialization, hroot, Polynomial.map_zero]
    · have hword :
          powerBatchedWord (fun t i ↦ iota (values t i)) (iota z) =
            fun i ↦ iota (powerBatchedWord values z i) := by
          funext i
          simp only [powerBatchedWord, map_sum, map_mul, map_pow]
      rw [hword, polynomialAgreementSet_map]
      exact hagree

open Classical in
/-- Root-degree-zero equations contribute only their challenge height. Outside these exceptions
there are no candidate roots, so the semantic recovery conclusion holds uniformly. -/
theorem exists_exceptional_ordinaryPowerEquation_base_zeroDegree
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F)
    (Q : DifferentialPolynomial F[X] 0) (D h A : ℕ)
    (hQ : Q ≠ 0) (hdegree : Q.degreeOf (some 0) = 0)
    (hheight : ChallengeHeightLE Q h) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℚ) ≤ h ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < D + 1 →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        A ≤ (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F) (D + 1) z P := by
  obtain ⟨exceptional, hcard, hnonzero⟩ :=
    exists_exceptional_ordinaryContent Q hQ hdegree hheight
  refine ⟨exceptional, by exact_mod_cast hcard, ?_⟩
  intro z hz P _hP hroot _hagree
  exact False.elim ((hnonzero z hz P) hroot)

open Classical in
/-- Arbitrary-field free-retention recovery with an explicit positive-degree/formula branch and
the separate root-degree-zero height branch. -/
theorem exists_exceptional_ordinaryPowerEquation_base_freeRetention_allDegrees
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F)
    (Q : DifferentialPolynomial F[X] 0) (D h B L A : ℕ)
    (hQ : Q ≠ 0) (hD : 0 < D) (hell : 0 < ell)
    (hDn : D + 2 ≤ n) (hDL : D < L) (hLA : L ≤ A) (hAn : A ≤ n)
    (hheight : ChallengeHeightLE Q h) (hdegree : Q.degreeOf (some 0) ≤ B) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℚ) ≤
        ordinaryUnifiedPowerFactorAtOrHeight n D ell B h A L ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < D + 1 →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        A ≤ (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F) (D + 1) z P := by
  by_cases hB : B = 0
  · subst B
    obtain ⟨exceptional, hcard, hgood⟩ :=
      exists_exceptional_ordinaryPowerEquation_base_zeroDegree
        domain values Q D h A hQ (Nat.eq_zero_of_le_zero hdegree) hheight
    exact ⟨exceptional, by simpa using hcard, hgood⟩
  · obtain ⟨exceptional, hcard, hgood⟩ :=
      exists_exceptional_ordinaryPowerEquation_base_freeRetention
        domain values Q D h B L A hQ hD hell (Nat.one_le_iff_ne_zero.mpr hB)
          hDn hDL hLA hAn hheight hdegree
    exact ⟨exceptional,
      by simpa only [ordinaryUnifiedPowerFactorAtOrHeight, if_neg hB] using hcard, hgood⟩

open Classical in
/-- Base-field form of the unified ordinary polynomial-curve transfer. Algebraic closure and
Frobenius choices are internal; recovered constituents and the full agreement set descend to the
original field. -/
theorem exists_exceptional_ordinaryPowerEquation_base_unified
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F)
    (Q : DifferentialPolynomial F[X] 0) (D h B A : ℕ)
    (hQ : Q ≠ 0) (hD : 0 < D) (hell : 0 < ell) (hB : 1 ≤ B)
    (hDA : D + 1 ≤ A) (hAn : A ≤ n)
    (hheight : ChallengeHeightLE Q h) (hdegree : Q.degreeOf (some 0) ≤ B) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℚ) ≤ ordinaryUnifiedPowerFactorRaw
        (((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ)) n D ell B h ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < D + 1 →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        A ≤ (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F) (D + 1) z P := by
  classical
  let E := AlgebraicClosure F
  let iota := algebraMap F E
  let QE := MvPolynomial.map (Polynomial.mapRingHom iota) Q
  have hQE : QE ≠ 0 := by
    intro hz
    apply hQ
    apply MvPolynomial.map_injective (Polynomial.mapRingHom iota)
      (Polynomial.map_injective iota iota.injective)
    simpa only [map_zero] using hz
  have hQheight : ChallengeHeightLE QE h := hheight.map_coefficients iota
  have hQdegree : QE.degreeOf (some 0) ≤ B := by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro u hu
    exact (MvPolynomial.monomial_le_degreeOf (some 0)
      (MvPolynomial.support_map_subset _ _ hu)).trans hdegree
  obtain ⟨ex, hexCardAt, hex⟩ := exists_exceptional_ordinaryPowerEquation_unifiedAt_succ
    domain values iota QE D h B A hQE hD hell hB hDA hAn hQheight hQdegree
  have hexCard : (ex.card : ℚ) ≤ ordinaryUnifiedPowerFactorRaw
      (((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ)) n D ell B h := by
    rw [← ordinaryUnifiedPowerFactorAt_succ_eq n D ell B h A hDA hAn]
    exact hexCardAt
  let baseEx := ex.preimage iota iota.injective.injOn
  refine ⟨baseEx, ?_, ?_⟩
  · apply (show (baseEx.card : ℚ) ≤ ex.card by
      exact_mod_cast Finset.card_le_card_of_injOn iota
        (fun _ hz ↦ Finset.mem_preimage.mp hz) iota.injective.injOn).trans
    exact hexCard
  · intro z hz P hP hroot hagree
    apply HasExactPowerAgreement.descend domain values iota (D + 1) z P
    apply hex (iota z)
    · exact fun hmem ↦ hz (Finset.mem_preimage.mpr hmem)
    · exact Polynomial.degree_map_le.trans_lt hP
    · rw [← map_symbolicDifferentialSpecialization, hroot, Polynomial.map_zero]
    · have hword :
          powerBatchedWord (fun t i ↦ iota (values t i)) (iota z) =
            fun i ↦ iota (powerBatchedWord values z i) := by
          funext i
          simp only [powerBatchedWord, map_sum, map_mul, map_pow]
      rw [hword, polynomialAgreementSet_map]
      exact hagree

end ReedSolomon
