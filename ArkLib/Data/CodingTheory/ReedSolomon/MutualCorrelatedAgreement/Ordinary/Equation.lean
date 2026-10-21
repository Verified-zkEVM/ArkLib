/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.FactorAssembly
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.IrreducibleEquation
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.EquationDescent
public import ArkLib.Data.Polynomial.Differential.ContentExceptions
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerToLine

/-!
# Exceptional challenges for ordinary equations

Every nonzero ordinary differential equation has one bounded exceptional set controlling all
accepted roots with the stated root-degree and challenge-height budgets in every characteristic.
Outside this set, every sufficiently agreeing low-degree root has exact power agreement with the
power-batched word of a polynomial curve. The bound is the free-retention charge at a retention
threshold `L`; its value at `L = D + 1` is bounded by the curve-factor charge, and the two-word
case gives exact correlated pairs.

The factorization of the equation is taken over an algebraically closed field. Over an arbitrary
field, the exceptional set of the algebraic closure restricts to the base field, and exact power
agreement descends.

## Main statements

* `ReedSolomon.exists_exceptional_ordinaryPowerEquation_unifiedAt` gives the free-retention bound
  for polynomial curves over an algebraically closed field.
* `ReedSolomon.exists_exceptional_ordinaryPowerEquation` gives the curve-factor bound.
* `ReedSolomon.exists_exceptional_ordinaryEquation` gives the bound for arbitrary nonzero
  ordinary equations and exact correlated pairs.
* `ReedSolomon.exists_baseExceptional_ordinaryPowerEquation` gives the free-retention bound over
  an arbitrary field, charging an equation of root degree zero by its height.

## References

* [DKT26]
-/

@[expose] public section

namespace ReedSolomon

open Polynomial MvPolynomial PolynomialDifferential

open Classical in
/-- Every nonzero ordinary equation with root degree at most `B ≥ 1` and coefficient height at
most `h` has one exceptional set of size at most `ordinaryUnifiedPowerFactorAt n D ℓ B h A L`.
For `0 < D, ℓ` and `D < L ≤ A`, every degree-`< D + 1` root of the specialized equation with at
least `A` agreements has exact power agreement outside this set, in every characteristic. -/
theorem exists_exceptional_ordinaryPowerEquation_unifiedAt
    {F E : Type*} [Field F] [Field E] [IsAlgClosed E] {n ℓ : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F) (ι : F →+* E)
    (Q : DifferentialPolynomial E[X] 0) (D h B L A : ℕ)
    (hQ : Q ≠ 0) (hD : 0 < D) (hℓ : 0 < ℓ) (hB : 1 ≤ B) (hDL : D < L) (hLA : L ≤ A)
    (hheight : CoeffNatDegreeLE Q h) (hdegree : Q.degreeOf (some 0) ≤ B) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤ ordinaryUnifiedPowerFactorAt n D ℓ B h A L ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < D + 1 →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        A ≤ (polynomialAgreementSet (domain.trans ⟨ι, ι.injective⟩)
          (powerBatchedWord (fun t i ↦ ι (values t i)) z) P).card →
        HasExactPowerAgreement domain values ι (D + 1) z P := by
  classical
  let flat := ordinaryFlatten E Q
  let height (R : MvPolynomial (Option (Fin 2)) E) := R.degreeOf (some 1)
  let theta : ℚ := ((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)
  let ev (z : E) (P : E[X]) :=
    ((differentialSpecializationHom P).toRingHom.comp
      (MvPolynomial.map (σ := JetVariable 0) (Polynomial.aeval z).toRingHom)).comp
        (ordinaryUnflatten E).toRingHom
  let Good (z : E) (P : E[X]) := P.degree < D + 1 →
    A ≤ (polynomialAgreementSet (domain.trans ⟨ι, ι.injective⟩)
      (powerBatchedWord (fun t i ↦ ι (values t i)) z) P).card →
    HasExactPowerAgreement domain values ι (D + 1) z P
  have hflat : flat ≠ 0 := (ordinaryFlatten E).map_ne_zero_iff.mpr hQ
  have hflatHeight : flat.degreeOf (some 1) ≤ h :=
    degreeOf_challenge_ordinaryFlatten_le Q hheight
  have hdegUnflat (R : MvPolynomial (Option (Fin 2)) E) :
      (ordinaryUnflatten E R).degreeOf (some 0) = R.degreeOf none := by
    rw [← degreeOf_none_ordinaryFlatten]
    simp [ordinaryUnflatten]
  have hev (z : E) (P : E[X]) (R : MvPolynomial (Option (Fin 2)) E) :
      ev z P R = differentialSpecialization
        (challengeSpecialization (ordinaryUnflatten E R) z) P := rfl
  have hc : ∃ ex : Finset E, ex.card ≤ height (radicalContent none flat) ∧
      ∀ z ∉ ex, ∀ P, ev z P (radicalContent none flat) ≠ 0 := by
    obtain ⟨ex, hcard, hgood⟩ := exists_exceptional_jet_independent_content
      (ordinaryUnflatten E (radicalContent none flat))
      ((ordinaryUnflatten E).map_ne_zero_iff.mpr (radicalContent_ne_zero none flat))
      (by rw [hdegUnflat, degreeOf_radicalContent])
      (coeffNatDegreeLE_ordinaryUnflatten_of_degreeOf_le _ le_rfl)
    exact ⟨ex, hcard, hgood⟩
  have hf : ∀ c ∈ positiveDegreeFactorClasses none flat, ∃ ex : Finset E,
      (ex.card : ℚ) ≤ ordinaryUnifiedPowerFactorRawAt theta n D ℓ
        (c.rep.degreeOf none) (height c.rep) L ∧
      ∀ z ∉ ex, ∀ P, ev z P c.rep = 0 → Good z P := by
    intro c hc
    obtain ⟨ex, hcard, hgood⟩ := exists_exceptional_irreducibleOrdinaryPowerEquation_unifiedAt
      domain values ι (ordinaryUnflatten E c.rep) D (height c.rep) L A hD hℓ hDL hLA
      (coeffNatDegreeLE_ordinaryUnflatten_of_degreeOf_le _ le_rfl)
      (irreducible_rep_of_mem_positiveDegreeFactorClasses hc |>.map (ordinaryUnflatten E))
      (by simpa only [hdegUnflat] using (mem_positiveDegreeFactorClasses.mp hc).2)
    refine ⟨ex, ?_, ?_⟩
    · simpa only [hdegUnflat, ordinaryUnifiedPowerFactorAt] using hcard
    · intro z hz P hzero hP hagree
      exact hgood z hz P hP (by simpa only [hev] using hzero) hagree
  have hroot : flat.degreeOf none ≤ B := by
    simpa only [flat, degreeOf_none_ordinaryFlatten] using hdegree
  have hbudgetHeight : height (radicalContent none flat) +
      ∑ c ∈ positiveDegreeFactorClasses none flat, height c.rep ≤ h := by
    simpa only [height] using (add_sum_degreeOf_positiveDegreeFactorClasses_le
      none (some 1) flat).trans hflatHeight
  obtain ⟨ex, hcard, hgood⟩ := exists_exceptional_ordinaryUnifiedPowerFactorAssembly
    (i := none) (Q := flat) hflat ev Good height theta n D ℓ B h L (by positivity) hB hroot
    hbudgetHeight hc hf
  refine ⟨ex, hcard, ?_⟩
  intro z hz P hP hroot hagree
  exact hgood z hz P (by
    rw [hev]
    simpa only [flat, ordinaryUnflatten, AlgEquiv.symm_apply_apply] using hroot) hP hagree

open Classical in
/-- Every nonzero ordinary equation has one finite exceptional set for every accepted
polynomial-curve root, bounded by the curve-factor charge `ordinaryCurveFactorRaw` at incidence
ratio `(n - D) / (A - D)`, in arbitrary characteristic. -/
theorem exists_exceptional_ordinaryPowerEquation
    {F E : Type*} [Field F] [Field E] [IsAlgClosed E] {n ℓ : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F) (ι : F →+* E)
    (Q : DifferentialPolynomial E[X] 0) (D h mu A : ℕ)
    (hQ : Q ≠ 0) (hD : 0 < D) (hℓ : 0 < ℓ) (hmu : 1 ≤ mu)
    (hDA : D + 1 ≤ A) (hAn : A ≤ n)
    (hheight : CoeffNatDegreeLE Q h) (hdegree : Q.degreeOf (some 0) ≤ mu) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤ ordinaryCurveFactorRaw
        (((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ)) n D ℓ mu h ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < D + 1 →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        A ≤ (polynomialAgreementSet (domain.trans ⟨ι, ι.injective⟩)
          (powerBatchedWord (fun t i ↦ ι (values t i)) z) P).card →
        HasExactPowerAgreement domain values ι (D + 1) z P := by
  obtain ⟨ex, hcard, hex⟩ := exists_exceptional_ordinaryPowerEquation_unifiedAt
    domain values ι Q D h mu (D + 1) A hQ hD hℓ hmu (by omega) hDA hheight hdegree
  rw [ordinaryUnifiedPowerFactorAt_succ_eq n D ℓ mu h A hDA hAn] at hcard
  exact ⟨ex, hcard.trans (ordinaryUnifiedPowerFactorRaw_le_ordinaryCurveFactorRaw n ℓ mu h
    (by positivity) hD), hex⟩

open Classical in
/-- Every nonzero ordinary equation has one finite exceptional set for all accepted roots,
with the stated root-degree and challenge-height budgets in arbitrary characteristic. -/
theorem exists_exceptional_ordinaryEquation
    {F E : Type*} [Field F] [Field E] [IsAlgClosed E] {n : ℕ}
    (domain : Fin n ↪ F) (f g : Fin n → F) (ι : F →+* E)
    (Q : DifferentialPolynomial E[X] 0) (D h mu A : ℕ)
    (hQ : Q ≠ 0) (hD : 0 < D) (hmu : 1 ≤ mu) (hDA : D + 1 ≤ A) (hAn : A ≤ n)
    (hheight : CoeffNatDegreeLE Q h) (hdegree : Q.degreeOf (some 0) ≤ mu) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤ ordinaryFactorRaw
        (((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ)) n D mu h ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < D + 1 →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        A ≤ (polynomialAgreementSet (domain.trans ⟨ι, ι.injective⟩)
          (fun i ↦ ι (f i) + z * ι (g i)) P).card →
        HasExactCorrelatedPair domain f g ι (D + 1) z P := by
  classical
  obtain ⟨exceptional, hcard, hgood⟩ := exists_exceptional_ordinaryPowerEquation
    (ℓ := 1) domain ![f, g] ι Q D h mu A hQ hD (by omega) hmu hDA hAn hheight hdegree
  have hcharge : ordinaryCurveFactorRaw
      (((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ)) n D 1 mu h =
        ordinaryFactorRaw (((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ)) n D mu h := by
    simp [ordinaryCurveFactorRaw, ordinaryFactorRaw]
  refine ⟨exceptional, hcharge ▸ hcard, ?_⟩
  intro z hz P hdegree hroot hagree
  have hpowerAgreement : A ≤
      (polynomialAgreementSet (domain.trans ⟨ι, ι.injective⟩)
        (powerBatchedWord (fun t i ↦ ι (![f, g] t i)) z) P).card := by
    rw [powerBatchedWord_pair_eq]
    exact hagree
  exact exactCorrelatedPair_of_powerAgreement_one domain ![f, g] ι z P
    (hgood z hz P hdegree hroot hpowerAgreement)

/-- Over an arbitrary field, every nonzero ordinary equation with root degree at most `B` and
coefficient height at most `h` has one exceptional set of size at most
`ordinaryUnifiedPowerFactorAtOrHeight n D ℓ B h A L`. For `0 < D, ℓ` and `D < L ≤ A`, every
degree-`< D + 1` root of the specialized equation with at least `A` agreements has exact power
agreement over the base field outside this set. -/
theorem exists_baseExceptional_ordinaryPowerEquation
    {F : Type*} [Field F] [instF : DecidableEq F] {n ℓ : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F)
    (Q : DifferentialPolynomial F[X] 0) (D h B L A : ℕ)
    (hQ : Q ≠ 0) (hD : 0 < D) (hℓ : 0 < ℓ) (hDL : D < L) (hLA : L ≤ A)
    (hheight : CoeffNatDegreeLE Q h) (hdegree : Q.degreeOf (some 0) ≤ B) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℚ) ≤ ordinaryUnifiedPowerFactorAtOrHeight n D ℓ B h A L ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < D + 1 →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        A ≤ (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F) (D + 1) z P := by
  have hdecF : instF = (fun a b : F ↦ Classical.propDecidable (a = b)) :=
    Subsingleton.elim _ _
  subst hdecF
  classical
  rcases Nat.eq_zero_or_pos B with rfl | hB
  · obtain ⟨exceptional, hcard, hnonzero⟩ :=
      exists_exceptional_jet_independent_content Q hQ (Nat.eq_zero_of_le_zero hdegree) hheight
    refine ⟨exceptional, by simpa using (show (exceptional.card : ℚ) ≤ h by exact_mod_cast hcard),
      ?_⟩
    intro z hz P _ hroot _
    exact absurd hroot (hnonzero z hz P)
  let E := AlgebraicClosure F
  let ι := algebraMap F E
  let QE := MvPolynomial.map (Polynomial.mapRingHom ι) Q
  have hQE : QE ≠ 0 := by
    intro hz
    apply hQ
    apply MvPolynomial.map_injective (Polynomial.mapRingHom ι)
      (Polynomial.map_injective ι ι.injective)
    simpa only [map_zero] using hz
  have hQdegree : QE.degreeOf (some 0) ≤ B := (jetDegree_map_le _ Q 0).trans hdegree
  obtain ⟨ex, hexCard, hex⟩ := exists_exceptional_ordinaryPowerEquation_unifiedAt
    domain values ι QE D h B L A hQE hD hℓ hB hDL hLA
    (CoeffNatDegreeLE.map_coefficients ι Q hheight) hQdegree
  obtain ⟨baseEx, hbaseCard, hbase⟩ := exists_exceptional_equation_powerAgreement_descend
    domain values ι Q (D + 1) A ex fun z hz P hP hagree hroot ↦ hex z hz P hP hroot hagree
  refine ⟨baseEx, ?_, fun z hz P hP hroot hagree ↦ hbase z hz P hP hagree hroot⟩
  rw [ordinaryUnifiedPowerFactorAtOrHeight_of_pos n D ℓ B h A L hB]
  exact (show (baseEx.card : ℚ) ≤ ex.card by exact_mod_cast hbaseCard).trans hexCard

end ReedSolomon
