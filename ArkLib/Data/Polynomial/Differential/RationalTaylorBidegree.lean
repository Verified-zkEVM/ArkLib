/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Differential.TaylorChartAlgebra
public import ArkLib.Data.Polynomial.Differential.TaylorChart
public import ArkLib.Data.Polynomial.Differential.JetDegree
public import ArkLib.Data.Polynomial.Differential.RationalTaylorDerivativeDegree
public import ArkLib.Data.Polynomial.Differential.RationalTaylorJointDegree
public import ArkLib.ToMathlib.MvPolynomial.OptionWeightedDegree
public import ArkLib.ToMathlib.MvPolynomial.PolynomialCoefficients
public import ArkLib.ToMathlib.RingTheory.MvPolynomial.Bidegree
public import ArkLib.ToMathlib.RingTheory.MvPolynomial.CappedBidegree

/-!
# Capped bidegrees of rational Taylor chart equations

For a differential polynomial over `F[X]`, coefficient degree measures the challenge variable and
total degree in the jet variables measures the initial jet. The flattened initial equation, initial
separant, padded Taylor numerators, and agreement equations therefore lie in bidegree rectangles.

## Main statements

* `initialJetEquation_mem_restrictBidegree` and
  `initialJetSeparant_mem_restrictBidegree`: the initial equation and separant rectangles.
* `commonTaylorNumeratorOver_mem_restrictBidegree`: the rectangle for a padded Taylor numerator.
* `taylorAgreementEquationOver_mem_restrictBidegree`: the rectangle for an agreement equation
  with a received polynomial of bounded degree.
* `degreeOf_taylorAgreementEquationOver_firstOrder`: a separate degree bound in the first
  derivative variable for an agreement equation.
* `degreeOf_taylorAgreementEquation_firstOrder_le`: its field-valued first-order specialization.
* `initialJetEquation_mem_restrictCappedBidegree`,
  `commonTaylorNumeratorOver_mem_restrictCappedBidegree`, and
  `taylorAgreementEquationOver_mem_restrictCappedBidegree`: the same equations with a separate
  bound on their highest jet variable.

## References

* [DKT26]
-/

@[expose] public section

namespace PolynomialDifferential

open MvPolynomial Polynomial

variable {F : Type*} [Field F] {r : ℕ}

/-- The flattened initial equation lies in the rectangle given by the coefficient and jet degrees
of `Q`. -/
theorem initialJetEquation_mem_restrictBidegree (center : F)
    (Q : DifferentialPolynomial (Polynomial F) r) (h v : ℕ)
    (hheight : CoeffNatDegreeLE Q h) (hjet : jetTotalDegree Q ≤ v) :
    (optionEquivRight F (Fin (r + 1))).symm
      (initialJetEquation (Polynomial.C center) Q) ∈
        restrictBidegree (Fin (r + 1)) F h v := by
  apply optionEquivRight_symm_mem_restrictBidegree
  · exact coeffNatDegreeLE_initialJetEquation center Q hheight
  · exact (totalDegree_initialJetEquation_le (Polynomial.C center) Q).trans hjet

/-- The flattened initial separant lies in the rectangle with jet bound `v - 1`. -/
theorem initialJetSeparant_mem_restrictBidegree (center : F)
    (Q : DifferentialPolynomial (Polynomial F) r) (h v : ℕ)
    (hheight : CoeffNatDegreeLE Q h) (hjet : jetTotalDegree Q ≤ v) :
    (optionEquivRight F (Fin (r + 1))).symm
      (initialJetSeparant (Polynomial.C center) Q) ∈
        restrictBidegree (Fin (r + 1)) F h (v - 1) := by
  apply optionEquivRight_symm_mem_restrictBidegree
  · exact coeffNatDegreeLE_initialJetSeparant Q center hheight
  · exact (totalDegree_initialJetSeparant_le (Polynomial.C center) Q).trans
      (Nat.sub_le_sub_right hjet 1)

/-- A common Taylor numerator padded to a sufficient exponent lies in its challenge and jet degree
rectangle. -/
theorem commonTaylorNumeratorOver_mem_restrictBidegree (center : F)
    (Q : DifferentialPolynomial (Polynomial F) r) (h v K τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ) (hheight : CoeffNatDegreeLE Q h)
    (hv : 0 < v) (hjet : jetTotalDegree Q ≤ v) (l : Fin K) :
    (optionEquivRight F (Fin (r + 1))).symm
      (commonTaylorNumeratorOver F (Polynomial.C center) Q τ l.val) ∈
        restrictBidegree (Fin (r + 1)) F (τ * h) (1 + τ * (v - 1)) := by
  apply optionEquivRight_symm_mem_restrictBidegree
  · exact coeffNatDegreeLE_commonTaylorNumeratorOver_le center Q h τ l.val
      (hτ l) hheight
  · exact totalDegree_commonTaylorNumeratorOver_le_of_jet_and_exponent
      (Polynomial.C center) Q v K τ hv hτ hjet l

/-- Agreement with a received polynomial of degree at most `ell`, padded to a sufficient exponent,
lies in the corresponding bidegree rectangle. -/
theorem taylorAgreementEquationOver_mem_restrictBidegree (center x : F) (y : Polynomial F)
    (Q : DifferentialPolynomial (Polynomial F) r) (ell h v K τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ) (hy : y.natDegree ≤ ell)
    (hheight : CoeffNatDegreeLE Q h) (hv : 0 < v) (hjet : jetTotalDegree Q ≤ v) :
    (optionEquivRight F (Fin (r + 1))).symm
      (taylorAgreementEquationOver (F := F) (A := Polynomial F)
        (Polynomial.C center) Q K (Polynomial.C x) y (τ := τ)) ∈
        restrictBidegree (Fin (r + 1)) F (ell + τ * h) (1 + τ * (v - 1)) := by
  apply optionEquivRight_symm_mem_restrictBidegree
  · unfold taylorAgreementEquationOver
    rw [sub_eq_add_neg]
    apply CoeffNatDegreeLE.add
    · apply coeffNatDegreeLE_sum
      intro l _
      apply (coeffNatDegreeLE_C (by simp)).mul
      exact (coeffNatDegreeLE_commonTaylorNumeratorOver_le center Q h τ l.val
        (hτ l) hheight).mono (by omega)
    · intro m
      simpa using (((coeffNatDegreeLE_C hy).mul
        ((coeffNatDegreeLE_initialJetSeparant Q center hheight).pow τ)) m)
  · unfold taylorAgreementEquationOver
    apply (totalDegree_sub _ _).trans
    apply max_le
    · apply totalDegree_finsetSum_le
      intro l _
      apply (totalDegree_mul _ _).trans
      simpa only [totalDegree_C, zero_add] using
        totalDegree_commonTaylorNumeratorOver_le_of_jet_and_exponent
          (Polynomial.C center) Q v K τ hv hτ hjet l
    · apply (totalDegree_mul _ _).trans
      simp only [totalDegree_C, zero_add]
      have hs := (totalDegree_pow
          (initialJetSeparant (Polynomial.C center) Q) τ).trans
        (Nat.mul_le_mul_left τ
          ((totalDegree_initialJetSeparant_le (Polynomial.C center) Q).trans
            (Nat.sub_le_sub_right hjet 1)))
      exact hs.trans (by omega)

/-- The initial equation lies in the capped rectangle given by the coefficient, total jet, and
highest-jet degrees of `Q`. -/
theorem initialJetEquation_mem_restrictCappedBidegree (center : F)
    (Q : DifferentialPolynomial (Polynomial F) r) (h v c : ℕ)
    (hheight : CoeffNatDegreeLE Q h) (hjet : jetTotalDegree Q ≤ v)
    (hhighest : Q.degreeOf (some (Fin.last r)) ≤ c) :
    (optionEquivRight F (Fin (r + 1))).symm
      (initialJetEquation (Polynomial.C center) Q) ∈
        restrictCappedBidegree (Fin (r + 1)) F (Fin.last r) h v (min v c) := by
  apply optionEquivRight_symm_mem_restrictCappedBidegree
  · exact coeffNatDegreeLE_initialJetEquation center Q hheight
  · exact (totalDegree_initialJetEquation_le _ _).trans hjet
  · exact (degreeOf_initialJetEquation_le _ _).trans hhighest

/-- A common Taylor numerator lies in the capped rectangle that records its degree in the first
derivative variable separately. -/
theorem commonTaylorNumeratorOver_mem_restrictCappedBidegree (center : F)
    (Q : DifferentialPolynomial (Polynomial F) 1) (h v r K τ : ℕ)
    (hτ : TaylorExponentSufficient 1 K τ) (hheight : CoeffNatDegreeLE Q h)
    (hv : 0 < v) (hjet : jetTotalDegree Q ≤ v) (hr : 0 < r)
    (hderiv : Q.degreeOf (some 1) ≤ r) (l : Fin K) :
    (optionEquivRight F (Fin 2)).symm
      (commonTaylorNumeratorOver F (Polynomial.C center) Q τ l.val) ∈
        restrictCappedBidegree (Fin 2) F 1 (τ * h) (1 + τ * (v - 1))
          (min (1 + τ * (v - 1)) (τ * (r - 1) + l.val)) := by
  apply optionEquivRight_symm_mem_restrictCappedBidegree
  · exact coeffNatDegreeLE_commonTaylorNumeratorOver_le center Q h τ l.val (hτ l) hheight
  · exact totalDegree_commonTaylorNumeratorOver_le_of_jet_and_exponent
      (Polynomial.C center) Q v K τ hv hτ hjet l
  · exact (degreeOf_commonTaylorNumeratorOver_firstOrder
      (Polynomial.C center) Q r K τ hτ hr hderiv l).trans (by omega)

/-- Agreement with a received polynomial of bounded degree has the same separate first-derivative
degree bound as the common Taylor numerators. -/
theorem degreeOf_taylorAgreementEquationOver_firstOrder (center x y : Polynomial F)
    (Q : DifferentialPolynomial (Polynomial F) 1) (r K τ : ℕ)
    (hτ : TaylorExponentSufficient 1 K τ) (hr : 0 < r)
    (hderiv : Q.degreeOf (some 1) ≤ r) :
    (taylorAgreementEquationOver (F := F) center Q K x y (τ := τ)).degreeOf 1 ≤
      τ * (r - 1) + (K - 1) := by
  unfold taylorAgreementEquationOver
  apply (degreeOf_sub_le _ _ _).trans
  apply max_le
  · apply (degreeOf_sum_le _ _ _).trans
    apply Finset.sup_le
    intro l _
    apply (degreeOf_mul_le _ _ _).trans
    simp only [degreeOf_C, zero_add]
    exact (degreeOf_commonTaylorNumeratorOver_firstOrder
      center Q r K τ hτ hr hderiv l).trans (by omega)
  · apply (degreeOf_mul_le _ _ _).trans
    simp only [degreeOf_C, zero_add]
    exact (degreeOf_pow_le _ _ _).trans
      ((Nat.mul_le_mul_left τ ((degreeOf_initialJetSeparant_le _ Q).trans
        (Nat.sub_le_sub_right hderiv 1))).trans (by omega))

/-- In a first-order Taylor chart over a field, the agreement equation has degree at most
`τ * (r - 1) + (K - 1)` in the first-derivative variable when `Q` has degree at most `r` there. -/
theorem degreeOf_taylorAgreementEquation_firstOrder_le (center : F)
    (Q : DifferentialPolynomial F 1) (r K τ : ℕ)
    (hτ : TaylorExponentSufficient 1 K τ) (hr : 0 < r)
    (hderiv : Q.degreeOf (some 1) ≤ r) (x y : F) :
    (taylorAgreementEquation center Q K x y (τ := τ)).degreeOf 1 ≤
      τ * (r - 1) + (K - 1) := by
  let Qover : DifferentialPolynomial (Polynomial F) 1 := MvPolynomial.map Polynomial.C Q
  have hQover : Qover.degreeOf (some 1) ≤ r :=
    (degreeOf_map_le Polynomial.C Q (some 1)).trans hderiv
  have hover := degreeOf_taylorAgreementEquationOver_firstOrder
    (Polynomial.C center) (Polynomial.C x) (Polynomial.C y) Qover r K τ hτ hr hQover
  have hmap := degreeOf_map_le (Polynomial.aeval (0 : F)).toRingHom
    (taylorAgreementEquationOver (F := F) (Polynomial.C center) Qover K
      (Polynomial.C x) (Polynomial.C y) (τ := τ)) 1
  have hQeval :
      MvPolynomial.map (Polynomial.aeval (0 : F)).toRingHom Qover = Q := by
    dsimp only [Qover]
    rw [MvPolynomial.map_map]
    have he : (Polynomial.aeval (0 : F)).toRingHom.comp Polynomial.C = RingHom.id F := by
      ext a
      simp
    rw [he]
    exact MvPolynomial.map_id Q
  have hspec := map_taylorAgreementEquationOver_eq
    (F := F) (φ := Polynomial.aeval (0 : F)) (Polynomial.C center) Qover K
      (Polynomial.C x) (Polynomial.C y) τ
  rw [hQeval] at hspec
  have hspec' :
      MvPolynomial.map (Polynomial.aeval (0 : F)).toRingHom
          (taylorAgreementEquationOver (F := F) (Polynomial.C center) Qover K
            (Polynomial.C x) (Polynomial.C y) (τ := τ)) =
        taylorAgreementEquation center Q K x y (τ := τ) := by
    simpa using hspec
  rw [← hspec']
  exact hmap.trans hover

/-- Agreement with a received polynomial of bounded degree lies in the capped rectangle whose
third bound records the first-derivative degree. -/
theorem taylorAgreementEquationOver_mem_restrictCappedBidegree (center x : F)
    (y : Polynomial F) (Q : DifferentialPolynomial (Polynomial F) 1)
    (ell h v r K τ : ℕ) (hτ : TaylorExponentSufficient 1 K τ)
    (hy : y.natDegree ≤ ell) (hheight : CoeffNatDegreeLE Q h) (hv : 0 < v)
    (hr : 0 < r) (hjet : jetTotalDegree Q ≤ v) (hderiv : Q.degreeOf (some 1) ≤ r) :
    (optionEquivRight F (Fin 2)).symm
        (taylorAgreementEquationOver (F := F) (Polynomial.C center) Q K
          (Polynomial.C x) y (τ := τ)) ∈
        restrictCappedBidegree (Fin 2) F 1 (ell + τ * h) (1 + τ * (v - 1))
          (min (1 + τ * (v - 1)) (τ * (r - 1) + (K - 1))) := by
  apply mem_restrictCappedBidegree_of_mem_restrictBidegree
    (taylorAgreementEquationOver_mem_restrictBidegree center x y Q ell h v K τ hτ hy
      hheight hv hjet)
  have heq : ((optionEquivRight F (Fin 2)).symm
      (taylorAgreementEquationOver (F := F) (Polynomial.C center) Q K
        (Polynomial.C x) y (τ := τ))).degreeOf (some 1) =
      (taylorAgreementEquationOver (F := F) (Polynomial.C center) Q K
        (Polynomial.C x) y (τ := τ)).degreeOf 1 := by
    have hweighted := weightedTotalDegree_optionEquivRight (Pi.single (1 : Fin 2) 1)
      ((optionEquivRight F (Fin 2)).symm
        (taylorAgreementEquationOver (F := F) (Polynomial.C center) Q K
          (Polynomial.C x) y (τ := τ)))
    have hweight : (fun v : Option (Fin 2) ↦ v.elim 0 (Pi.single (1 : Fin 2) 1)) =
        Pi.single (some 1) 1 := by
      funext v
      cases v <;> simp [Pi.single_apply]
    simpa only [hweight, AlgEquiv.apply_symm_apply, weightedTotalDegree_piSingle] using
      hweighted.symm
  rw [heq]
  exact degreeOf_taylorAgreementEquationOver_firstOrder (Polynomial.C center) (Polynomial.C x) y
    Q r K τ hτ hr hderiv

end PolynomialDifferential
