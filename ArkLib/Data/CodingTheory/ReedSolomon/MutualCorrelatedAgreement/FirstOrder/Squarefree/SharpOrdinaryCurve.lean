/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.PolynomialCurve.Equation
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.Factors.FactorBounds
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.EquationDescent
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.ExtensionDescent
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Sharp ordinary polynomial-curve transfer below the message degree

The ordinary factor transfer already works in arbitrary characteristic and for polynomial
received curves.  When the equation's root degree is at most the message degree, the exact
Frobenius-degree comparison gives the smaller unified joint budget used by the squarefree
first-order singular tail.  This module changes only that quantitative aggregation; recovery,
Frobenius transport, and full-agreement descent are reused unchanged.
-/

@[expose] public section

namespace ReedSolomon.FirstOrder.Squarefree

open Polynomial MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators

noncomputable section

universe u

/-- Sharp all-characteristic charge for one ordinary degree-`ell` received curve. -/
def sharpOrdinaryPowerRaw (theta : ℚ) (n D ell a h : ℕ) : ℚ :=
  ((2 * a - 1) * h : ℕ) +
    theta * (h + ell * a + (2 * D - 1) * h * (2 * a - 1) : ℕ) +
      (ell * ((n - D - 1) * a) : ℕ)

/-- The pulled Frobenius factor is charged at its original root degree whenever its separable
degree is at most the message degree. -/
theorem ordinaryFrobeniusPower_charge_le_sharp
    (theta : ℚ) (n D ell h s b : ℕ)
    (htheta : 0 ≤ theta) (hs : 1 ≤ s) (hb : 1 ≤ b) (hbD : b ≤ D) :
    ((2 * b - 1) * h : ℕ) + theta * ordinaryFrobeniusPowerMixedDegree D ell h s b +
        (ell * ((n - D - 1) * b) : ℕ) ≤
      sharpOrdinaryPowerRaw theta n D ell (s * b) h := by
  have hbs : b ≤ s * b := by nlinarith
  have hmixed : ordinaryFrobeniusPowerMixedDegree D ell h s b ≤
      h + ell * (s * b) + (2 * D - 1) * h * (2 * (s * b) - 1) := by
    rw [ordinaryFrobeniusPowerMixedDegree_eq D ell h s b hb]
    apply Nat.add_le_add_left
    simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      Nat.mul_le_mul_right h (ordinaryFrobenius_sharp_factor hbD hs hb)
  unfold sharpOrdinaryPowerRaw
  apply add_le_add
  · apply add_le_add
    · exact_mod_cast Nat.mul_le_mul_right h
        (Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 hbs) 1)
    · exact mul_le_mul_of_nonneg_left (by exact_mod_cast hmixed) htheta
  · exact_mod_cast Nat.mul_le_mul_left ell (Nat.mul_le_mul_left (n - D - 1) hbs)

/-- Content and distinct positive-degree factors aggregate into the sharp curve charge. -/
theorem sharpOrdinaryPowerRaw_sum_le {I : Type*} (S : Finset I)
    (a height : I → ℕ) (theta : ℚ) (n D ell mu H contentHeight : ℕ)
    (htheta : 0 ≤ theta) (hmu : 1 ≤ mu)
    (ha : ∑ i ∈ S, a i ≤ mu)
    (hh : contentHeight + ∑ i ∈ S, height i ≤ H) :
    (contentHeight : ℚ) +
        ∑ i ∈ S, sharpOrdinaryPowerRaw theta n D ell (a i) (height i) ≤
      sharpOrdinaryPowerRaw theta n D ell mu H := by
  let c : ℚ :=
    (2 * mu - 1 : ℕ) + theta * (1 + (2 * D - 1 : ℕ) * (2 * mu - 1 : ℕ))
  let d : ℚ := theta * ell + (ell * (n - D - 1) : ℕ)
  have hc : 1 ≤ c := by
    have hnat : 1 ≤ 2 * mu - 1 := by omega
    have hcast : (1 : ℚ) ≤ (2 * mu - 1 : ℕ) := by exact_mod_cast hnat
    exact hcast.trans (le_add_of_nonneg_right (mul_nonneg htheta (by positivity)))
  have hc0 : 0 ≤ c := le_trans zero_le_one hc
  have hd0 : 0 ≤ d := by dsimp [d]; positivity
  have hterm (i : I) (hi : i ∈ S) :
      sharpOrdinaryPowerRaw theta n D ell (a i) (height i) ≤
        c * height i + d * a i := by
    have hai : a i ≤ mu :=
      (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hi).trans ha
    have hsub : 2 * a i - 1 ≤ 2 * mu - 1 := by omega
    have hfirst : (((2 * a i - 1) * height i : ℕ) : ℚ) ≤
        (2 * mu - 1 : ℕ) * (height i : ℚ) := by
      exact_mod_cast Nat.mul_le_mul_right (height i) hsub
    have hsecond :
        (((2 * D - 1) * height i * (2 * a i - 1) : ℕ) : ℚ) ≤
          ((2 * D - 1 : ℕ) : ℚ) * height i * (2 * mu - 1 : ℕ) := by
      exact_mod_cast Nat.mul_le_mul_left ((2 * D - 1) * height i) hsub
    unfold sharpOrdinaryPowerRaw
    dsimp [c, d]
    push_cast at hfirst hsecond ⊢
    nlinarith [mul_nonneg htheta (sub_nonneg.mpr hsecond)]
  have hsum := Finset.sum_le_sum hterm
  have hcontent : (contentHeight : ℚ) ≤ c * contentHeight := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg contentHeight)
  have hhQ : (contentHeight : ℚ) + ∑ i ∈ S, (height i : ℚ) ≤ H := by
    exact_mod_cast hh
  have haQ : (∑ i ∈ S, (a i : ℚ)) ≤ mu := by exact_mod_cast ha
  calc
    (contentHeight : ℚ) +
          ∑ i ∈ S, sharpOrdinaryPowerRaw theta n D ell (a i) (height i) ≤
        c * contentHeight + ∑ i ∈ S, (c * height i + d * a i) :=
      add_le_add hcontent hsum
    _ = c * ((contentHeight : ℚ) + ∑ i ∈ S, (height i : ℚ)) +
        d * ∑ i ∈ S, (a i : ℚ) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      ring
    _ ≤ c * H + d * mu :=
      add_le_add (mul_le_mul_of_nonneg_left hhQ hc0)
        (mul_le_mul_of_nonneg_left haQ hd0)
    _ = sharpOrdinaryPowerRaw theta n D ell mu H := by
      dsimp [c, d, sharpOrdinaryPowerRaw]
      push_cast
      ring

open Classical in
/-- A separable pulled factor inherits the sharp polynomial-curve charge. -/
theorem exists_exceptional_frobeniusPowerFactorSolutions_sharp
    {F E : Type*} [Field F] [Field E] [IsAlgClosed E] {n ell : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] 0) (p e D h b A : ℕ) [ExpChar E p]
    (hD : 0 < D) (hell : 0 < ell) (hb : 0 < b) (hbD : b ≤ D)
    (hDA : D + 1 ≤ A) (hAn : A ≤ n)
    (hheight : ChallengeHeightLE Q h)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ b)
    (hirr : Irreducible Q) (hder : pderiv (some 0) Q ≠ 0)
    (hdegree : Q.degreeOf (some 0) = b) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤ sharpOrdinaryPowerRaw
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
    have hcharge := ordinaryFrobeniusPower_charge_le_sharp theta n D ell h
      (p ^ e) b htheta hs hb hbD
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
      _ ≤ sharpOrdinaryPowerRaw theta n D ell (p ^ e * b) h := hcharge
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
/-- An irreducible ordinary equation whose root degree is below `D` gets the sharp curve
charge, while retaining the existing all-characteristic Frobenius recovery. -/
theorem exists_exceptional_irreducibleOrdinaryPowerEquation_sharp
    {F E : Type*} [Field F] [Field E] [IsAlgClosed E] {n ell : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] 0) (D h A : ℕ)
    (hD : 0 < D) (hell : 0 < ell) (hDA : D + 1 ≤ A) (hAn : A ≤ n)
    (hheight : ChallengeHeightLE Q h) (hirr : Irreducible Q)
    (hpos : 0 < Q.degreeOf (some 0)) (hdegreeD : Q.degreeOf (some 0) ≤ D) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤ sharpOrdinaryPowerRaw
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
  have hRD : R.degreeOf (some 0) ≤ D := by
    have hle : R.degreeOf (some 0) ≤ R.degreeOf (some 0) * p ^ e :=
      Nat.le_mul_of_pos_right _ (pow_pos (expChar_pos E p) e)
    have hproduct : R.degreeOf (some 0) * p ^ e = Q.degreeOf (some 0) := by
      simpa only [Nat.mul_comm] using hRdegree
    exact hle.trans (hproduct.trans_le hdegreeD)
  obtain ⟨ex, hexCard, hex⟩ := exists_exceptional_frobeniusPowerFactorSolutions_sharp
    domain values iota R p e D h (R.degreeOf (some 0)) A hD hell hRpos hRD
      hDA hAn hRheight (by rw [ordinary_jetWeight_eq_degreeOf]) hRirr hRder rfl
  have heq : p ^ e * R.degreeOf (some 0) = Q.degreeOf (some 0) := by
    simpa only [Nat.mul_comm] using hRdegree
  refine ⟨ex, ?_, ?_⟩
  · simpa only [heq] using hexCard
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
    have hout := hex w (by simpa only [hw] using hz) P hdegree hRroot
      (by simpa only [hw] using hagree)
    simpa only [hw] using hout

/-- Assemble content and factor exceptions without changing the sharp polynomial-curve
budget. -/
theorem exists_exceptional_sharpOrdinaryPowerFactorAssembly
    {F W V R sigma : Type*} [Field F] [CommRing R] [IsDomain R]
    (Q : MvPolynomial (Option sigma) F) (hQ : Q ≠ 0)
    (ev : W → V → MvPolynomial (Option sigma) F →+* R)
    (Good : W → V → Prop) (height : MvPolynomial (Option sigma) F → ℕ)
    (theta : ℚ) (n D ell mu H : ℕ) (htheta : 0 ≤ theta)
    (_hell : 0 < ell) (hmu : 1 ≤ mu)
    (hroot : Q.degreeOf none ≤ mu)
    (hheight : height (ordinaryContent Q) +
      ∑ a ∈ ordinaryRootFactorClasses Q, height (ordinaryFactorRepresentative a) ≤ H)
    (hcontent : ∃ ex : Finset W, ex.card ≤ height (ordinaryContent Q) ∧
      ∀ w ∉ ex, ∀ v, ev w v (ordinaryContent Q) ≠ 0)
    (hfactors : ∀ a ∈ ordinaryRootFactorClasses Q, ∃ ex : Finset W,
      (ex.card : ℚ) ≤ sharpOrdinaryPowerRaw theta n D ell
        (degreeOf none (ordinaryFactorRepresentative a))
        (height (ordinaryFactorRepresentative a)) ∧
      ∀ w ∉ ex, ∀ v, ev w v (ordinaryFactorRepresentative a) = 0 → Good w v) :
    ∃ ex : Finset W, (ex.card : ℚ) ≤ sharpOrdinaryPowerRaw theta n D ell mu H ∧
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
          ∑ a ∈ S, sharpOrdinaryPowerRaw theta n D ell
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
    exact sharpOrdinaryPowerRaw_sum_le S
      (fun a => degreeOf none (ordinaryFactorRepresentative a))
      (fun a => height (ordinaryFactorRepresentative a)) theta n D ell mu H
      (height (ordinaryContent Q)) htheta hmu
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
/-- Every nonzero ordinary equation of root degree at most the message degree has the sharp
all-characteristic polynomial-curve transfer. -/
theorem exists_exceptional_ordinaryPowerEquation_sharp
    {F E : Type*} [Field F] [Field E] [IsAlgClosed E] {n ell : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] 0) (D h mu A : ℕ)
    (hQ : Q ≠ 0) (hD : 0 < D) (hell : 0 < ell) (hmu : 1 ≤ mu) (hmuD : mu ≤ D)
    (hDA : D + 1 ≤ A) (hAn : A ≤ n)
    (hheight : ChallengeHeightLE Q h) (hdegree : Q.degreeOf (some 0) ≤ mu) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤ sharpOrdinaryPowerRaw
        (((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ)) n D ell mu h ∧
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
      (ex.card : ℚ) ≤ sharpOrdinaryPowerRaw
        (((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ)) n D ell
        (degreeOf none (ordinaryFactorRepresentative a))
        (height (ordinaryFactorRepresentative a)) ∧
      ∀ z ∉ ex, ∀ P, ev z P (ordinaryFactorRepresentative a) = 0 → Good z P := by
    intro a ha
    obtain ⟨hirr, hpos⟩ := ordinaryRootFactorClasses_spec flat ha
    have hflatDegree : degreeOf none flat ≤ mu := by
      simpa only [flat, degreeOf_none_ordinaryFlatten] using hdegree
    have hadegree : degreeOf none (ordinaryFactorRepresentative a) ≤ D :=
      (Finset.single_le_sum
        (fun b _ ↦ Nat.zero_le (degreeOf none (ordinaryFactorRepresentative b))) ha).trans
        ((ordinary_root_degree_sum_le flat hflat).trans (hflatDegree.trans hmuD))
    obtain ⟨ex, hcard, hgood⟩ := exists_exceptional_irreducibleOrdinaryPowerEquation_sharp
      domain values iota (ordinaryUnflatten E (ordinaryFactorRepresentative a)) D
      (height (ordinaryFactorRepresentative a)) A hD hell hDA hAn
      (challengeHeightLE_ordinaryUnflatten_of_degreeOf_le _ le_rfl)
      (hirr.map (ordinaryUnflatten E)) (by simpa only [hdegUnflat] using hpos)
      (by simpa only [hdegUnflat] using hadegree)
    refine ⟨ex, ?_, ?_⟩
    · simpa only [hdegUnflat] using hcard
    · intro z hz P hroot hP hagree
      exact hgood z hz P hP hroot hagree
  obtain ⟨ex, hcard, hgood⟩ := exists_exceptional_sharpOrdinaryPowerFactorAssembly
    flat hflat ev Good height (((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ))
    n D ell mu h (by positivity) hell hmu
    (by simpa only [flat, degreeOf_none_ordinaryFlatten] using hdegree)
    ((ordinary_degree_sum_le flat hflat (some 1)).trans
      (degreeOf_challenge_ordinaryFlatten_le Q hheight)) hc hf
  refine ⟨ex, hcard, ?_⟩
  intro z hz P hP hroot hagree
  apply hgood z hz P _ hP hagree
  rw [hev]
  simpa only [flat, ordinaryUnflatten, AlgEquiv.symm_apply_apply] using hroot

end

end ReedSolomon.FirstOrder.Squarefree
