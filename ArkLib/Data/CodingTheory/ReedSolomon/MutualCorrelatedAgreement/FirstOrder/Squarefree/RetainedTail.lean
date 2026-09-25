/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.Polynomial.Differential.RetainedCurve
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Squarefree.TailBound
public import ArkLib.Data.Polynomial.Differential.BaseChange
public import ArkLib.Data.Polynomial.Differential.FrobeniusEquation
public import ArkLib.Data.MvPolynomial.RadicalSplit.Separable
public import ArkLib.Data.Polynomial.ResultantDegree
public import ArkLib.Data.Polynomial.ResultantSpecialization
public import ArkLib.ToMathlib.MvPolynomial.OptionWeightedDegree

/-!
# Singular tails with a retained challenge

This file constructs the content-resultant equation while keeping the challenge as a polynomial
coordinate. The resulting equation bounds solutions outside the regular positive-factor locus;
its degree bounds control `Y₀` and the challenge.

## Main statements

* `flattenedSingularPolynomial` combines the retained content with a padded derivative resultant.
* `singularCurveEquation` turns that polynomial into an order-zero differential equation.
* `singularCurveEquation_routes_nonregular` routes every nonregular solution to the singular
  equation.
* `singularCurveEquation_degree_le` and `singularCurveEquation_coeffNatDegreeLE` bound its
  `Y₀` degree and challenge coefficient degrees.

## References

* [DKT26]
-/

@[expose] public section

namespace ReedSolomon.FirstOrder.Squarefree

open MvPolynomial Polynomial PolynomialDifferential
open Polynomial.Bivariate
open ReedSolomon.HiddenDerivative

noncomputable section

variable {F : Type*} [Field F]

private def retainedRootJetWeight : Option (JetVariable 1) → ℕ
  | none => 1
  | some i => i.elim 0 (fun j ↦ if j = 0 then 1 else 0)

private theorem retainedRootJetWeight_curveJetView
    (R : MvPolynomial (Option (JetVariable 1)) F) :
    R.weightedTotalDegree retainedRootJetWeight = (curveJetView R).totalDegree := by
  change R.weightedTotalDegree retainedRootJetWeight =
    (optionEquivRight F[X] (Fin 2)
      (optionEquivRight F (Option (Fin 2)) (rename curveJetReindex R))).totalDegree
  rw [totalDegree_optionEquivRight, weightedTotalDegree_optionEquivRight,
    weightedTotalDegree_rename_of_injective curveJetReindex.injective]
  congr 1
  funext v
  rcases v with _ | (_ | i)
  · rfl
  · rfl
  · fin_cases i <;> rfl

/-- The coefficient left after extracting the root-coordinate constant coefficient of the
retained content. -/
def flattenedContentCoefficient (Q : DifferentialPolynomial F[X] 1) :
    MvPolynomial (JetVariable 1) F :=
  (optionEquivLeft F (JetVariable 1)
    (radicalContent none (challengeRetainingRootFirst Q))).coeff 0

/-- The retained content times the original-size derivative resultant. -/
def flattenedSingularPolynomial (Q : DifferentialPolynomial F[X] 1) :
    MvPolynomial (JetVariable 1) F :=
  flattenedContentCoefficient Q *
    Polynomial.resultant (ordinaryRootPolynomial (challengeRetainingRootFirst Q))
      (ordinaryRootPolynomial (challengeRetainingRootFirst Q)).derivative
      (degreeOf none (radicalPrimPart none (challengeRetainingRootFirst Q)))
      (degreeOf none (radicalPrimPart none (challengeRetainingRootFirst Q)) - 1)

/-- Make a chosen remaining coordinate the outer polynomial variable. -/
def remainingCoordinateEquiv (i : JetVariable 1) :
    MvPolynomial (JetVariable 1) F ≃+* (MvPolynomial (Fin 2) F)[X] :=
  (renameEquiv F (Equiv.swap none i)).toRingEquiv.trans
    (optionEquivLeft F (Fin 2)).toRingEquiv

/-- The outer natural degree reads the degree in the chosen coordinate. -/
theorem remainingCoordinateEquiv_natDegree (i : JetVariable 1)
    (R : MvPolynomial (JetVariable 1) F) :
    (remainingCoordinateEquiv i R).natDegree = degreeOf i R := by
  unfold remainingCoordinateEquiv
  change (optionEquivLeft F (Fin 2) (rename (Equiv.swap none i) R)).natDegree = _
  rw [natDegree_optionEquivLeft]
  have hrename := degreeOf_rename_of_injective
    (Equiv.swap none i).injective i (p := R)
  simpa using hrename

/-- Express the retained content with a chosen remaining coordinate as its outer variable. -/
def retainedContentAsPolynomial (Q : DifferentialPolynomial F[X] 1)
    (i : JetVariable 1) : (MvPolynomial (Fin 2) F)[X] :=
  remainingCoordinateEquiv i (flattenedContentCoefficient Q)

/-- Express the positive root polynomial with a chosen remaining coordinate as its outer
variable. -/
def retainedPositiveAsPolynomial (Q : DifferentialPolynomial F[X] 1)
    (i : JetVariable 1) : (MvPolynomial (Fin 2) F)[X][X] :=
  (ordinaryRootPolynomial (challengeRetainingRootFirst Q)).map
    (remainingCoordinateEquiv i).toRingHom

/-- The nonzero radical content has a nonzero coefficient at root degree zero. -/
theorem flattenedContentCoefficient_ne_zero (Q : DifferentialPolynomial F[X] 1) :
    flattenedContentCoefficient Q ≠ 0 := by
  let U := optionEquivLeft F (JetVariable 1)
    (radicalContent none (challengeRetainingRootFirst Q))
  have hU : U ≠ 0 :=
    (optionEquivLeft F (JetVariable 1)).injective.ne_iff.mpr
      (radicalContent_ne_zero none (challengeRetainingRootFirst Q))
  have hdeg : U.natDegree = 0 := by
    dsimp only [U]
    rw [natDegree_optionEquivLeft, degreeOf_radicalContent]
  rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg] at hU
  simpa [U, flattenedContentCoefficient] using hU

/-- The retained positive root polynomial has its declared root degree. -/
theorem retainedPositiveAsPolynomial_natDegree (Q : DifferentialPolynomial F[X] 1)
    (i : JetVariable 1) :
    (retainedPositiveAsPolynomial Q i).natDegree =
      degreeOf none (radicalPrimPart none (challengeRetainingRootFirst Q)) := by
  unfold retainedPositiveAsPolynomial
  rw [Polynomial.natDegree_map_eq_of_injective
    (remainingCoordinateEquiv i).injective,
    natDegree_ordinaryRootPolynomial]

/-- The content degree plus the positive-factor jet degree is bounded by the input jet degree.
-/
theorem retainedContent_add_positiveJetDegree_le (Q : DifferentialPolynomial F[X] 1) :
    jetTotalDegree (fromFlattenedRootFirst
        (radicalContent none (challengeRetainingRootFirst Q))) +
      jetTotalDegree (positiveCurveEquation Q) ≤ jetTotalDegree Q := by
  have hadd := jetTotalDegree_fromFlattenedRootFirst_mul (F := F)
  have hdegree := MvPolynomial.map_radicalContent_add_map_radicalPrimPart_le
    (d := fun R ↦ jetTotalDegree (fromFlattenedRootFirst R)) hadd none
      (challengeRetainingRootFirst Q)
  change jetTotalDegree (fromFlattenedRootFirst
      (radicalContent none (challengeRetainingRootFirst Q))) +
    jetTotalDegree (fromFlattenedRootFirst
      (radicalPrimPart none (challengeRetainingRootFirst Q))) ≤ _ at hdegree
  simpa only [positiveCurveEquation, fromFlattenedRootFirst_rootFirstChallenge] using hdegree

/-- The singular polynomial becomes the generic singular tail in a chosen coordinate view. -/
theorem remainingCoordinateEquiv_flattenedSingularPolynomial
    (Q : DifferentialPolynomial F[X] 1) (i : JetVariable 1) :
    remainingCoordinateEquiv i (flattenedSingularPolynomial Q) =
      singularTail (retainedContentAsPolynomial Q i)
        (retainedPositiveAsPolynomial Q i)
        (degreeOf none (radicalPrimPart none (challengeRetainingRootFirst Q))) := by
  unfold flattenedSingularPolynomial singularTail retainedContentAsPolynomial
    retainedPositiveAsPolynomial
  rw [map_mul]
  congr 1
  change (remainingCoordinateEquiv i).toRingHom
    (Polynomial.resultant (ordinaryRootPolynomial (challengeRetainingRootFirst Q))
      (ordinaryRootPolynomial (challengeRetainingRootFirst Q)).derivative _ _) = _
  rw [← Polynomial.resultant_map_map]
  congr 2
  exact (Polynomial.derivative_map _ (remainingCoordinateEquiv i).toRingHom).symm

/-- The retained content's degree in `Y₀` is bounded by its jet degree. -/
theorem retainedContent_yZeroDegree_le (Q : DifferentialPolynomial F[X] 1) :
    (retainedContentAsPolynomial Q (some 0)).natDegree ≤
      jetTotalDegree (fromFlattenedRootFirst
        (radicalContent none (challengeRetainingRootFirst Q))) := by
  rw [retainedContentAsPolynomial, remainingCoordinateEquiv_natDegree]
  change degreeOf (some (0 : Fin 2))
      ((optionEquivLeft F (JetVariable 1)
        (radicalContent none (challengeRetainingRootFirst Q))).coeff 0) ≤ _
  let R := challengeRetainingRootFirst Q
  apply degreeOf_le_iff.mpr
  intro u hu
  have hoption : u.optionElim 0 = u.embDomain .some := by
    ext (_ | j) <;> simp
  have hsource : u.embDomain .some ∈ (radicalContent none R).support := by
    rw [← hoption]
    exact (mem_support_coeff_optionEquivLeft F).mp hu
  have hle := le_weightedTotalDegree retainedRootJetWeight hsource
  have hcoord : u (some (0 : Fin 2)) ≤
      (u.embDomain .some).weight retainedRootJetWeight := by
    rw [Finsupp.weight_eq_sum]
    simp [retainedRootJetWeight]
  exact (hcoord.trans hle).trans_eq (by
    rw [retainedRootJetWeight_curveJetView, curveJetView_totalDegree])

/-- Every coefficient of the retained positive root polynomial fits its `Y₀` degree triangle.
-/
theorem retainedPositive_yZeroCoefficientTriangle (Q : DifferentialPolynomial F[X] 1)
    (i : ℕ)
    (hi : i ≤ degreeOf none (radicalPrimPart none (challengeRetainingRootFirst Q))) :
    i + ((retainedPositiveAsPolynomial Q (some 0)).coeff i).natDegree ≤
      jetTotalDegree (positiveCurveEquation Q) := by
  rw [retainedPositiveAsPolynomial, Polynomial.coeff_map, add_comm]
  change (remainingCoordinateEquiv (some 0)
    ((ordinaryRootPolynomial (challengeRetainingRootFirst Q)).coeff i)).natDegree + i ≤ _
  rw [remainingCoordinateEquiv_natDegree]
  change degreeOf (some (0 : Fin 2))
      ((optionEquivLeft F (JetVariable 1)
        (radicalPrimPart none (challengeRetainingRootFirst Q))).coeff i) + i ≤ _
  have h := degreeOf_coeff_optionEquivLeft_add_le_weight retainedRootJetWeight
    (some (0 : Fin 2)) (by decide) (by simp [retainedRootJetWeight])
    (radicalPrimPart none (challengeRetainingRootFirst Q)) i
    (degreeOf none (radicalPrimPart none (challengeRetainingRootFirst Q))) hi rfl
  exact h.trans_eq (by
    rw [retainedRootJetWeight_curveJetView, curveJetView_totalDegree,
      positiveCurveEquation])

/-- The `Y₀` degree of the retained singular polynomial fits the ordinary degree envelope. -/
theorem flattenedSingularPolynomial_yZeroDegree_le
    (Q : DifferentialPolynomial F[X] 1)
    {B M : ℕ} (hjet : jetTotalDegree Q ≤ B)
    (hderiv : jetDegree Q 1 ≤ M) (hMB : M ≤ B) :
    degreeOf (some (0 : Fin 2)) (flattenedSingularPolynomial Q) ≤
      ordinaryDegreeEnvelope B M := by
  rw [← remainingCoordinateEquiv_natDegree (F := F) (some 0),
    remainingCoordinateEquiv_flattenedSingularPolynomial]
  let r := degreeOf none (radicalPrimPart none (challengeRetainingRootFirst Q))
  let bU := jetTotalDegree (fromFlattenedRootFirst
    (radicalContent none (challengeRetainingRootFirst Q)))
  let j := jetTotalDegree (positiveCurveEquation Q)
  have hbudget : bU + j ≤ B :=
    (retainedContent_add_positiveJetDegree_le Q).trans hjet
  have hcontent : (retainedContentAsPolynomial Q (some 0)).natDegree ≤ bU :=
    retainedContent_yZeroDegree_le Q
  by_cases hrzero : r = 0
  · change (singularTail (retainedContentAsPolynomial Q (some 0))
      (retainedPositiveAsPolynomial Q (some 0)) r).natDegree ≤ _
    rw [hrzero, singularTail]
    simp only [Nat.zero_sub, Polynomial.resultant_zero_left_deg, pow_zero, mul_one]
    exact hcontent.trans ((Nat.le_add_right _ _).trans hbudget)
      |>.trans (self_le_ordinaryDegreeEnvelope B M)
  · have hr : 0 < r := Nat.pos_of_ne_zero hrzero
    have hrj : r ≤ j := by
      dsimp [r, j]
      rw [← positiveCurveEquation_yOneDegree Q]
      exact jetDegree_le_total (positiveCurveEquation Q) 1
    have hrM : r ≤ M := by
      calc
        r = jetDegree (positiveCurveEquation Q) 1 := by
          change degreeOf none (radicalPrimPart none
            (challengeRetainingRootFirst Q)) =
              degreeOf (some (1 : Fin 2)) (positiveCurveEquation Q)
          exact (positiveCurveEquation_yOneDegree Q).symm
        _ ≤ jetDegree Q 1 := positiveCurveEquation_yOneDegree_le Q
        _ ≤ M := hderiv
    exact natDegree_singularTail_le
      (retainedContentAsPolynomial Q (some 0))
      (retainedPositiveAsPolynomial Q (some 0))
      hrM hMB hcontent hbudget (retainedPositive_yZeroCoefficientTriangle Q)

/-- The degree of the retained content coefficient in a remaining coordinate is bounded by the
degree of the content in that coordinate. -/
theorem degreeOf_flattenedContentCoefficient_le
    (Q : DifferentialPolynomial F[X] 1) (i : JetVariable 1) :
    degreeOf i (flattenedContentCoefficient Q) ≤
      degreeOf (some i) (radicalContent none (challengeRetainingRootFirst Q)) := by
  apply degreeOf_le_iff.mpr
  intro u hu
  have hsource : u.optionElim 0 ∈
      (radicalContent none (challengeRetainingRootFirst Q)).support :=
    (mem_support_coeff_optionEquivLeft F).mp hu
  simpa only [Finsupp.optionElim_apply_some] using
    MvPolynomial.monomial_le_degreeOf (some i) hsource

/-- The challenge degree of each coefficient of the retained positive root polynomial is bounded
by the challenge degree of the positive-factor product. -/
theorem retainedPositive_degreeX_le
    (Q : DifferentialPolynomial F[X] 1) (i : JetVariable 1) :
    Polynomial.Bivariate.degreeX (retainedPositiveAsPolynomial Q i) ≤
      degreeOf (some i) (radicalPrimPart none (challengeRetainingRootFirst Q)) := by
  classical
  unfold Polynomial.Bivariate.degreeX
  apply Finset.sup_le
  intro j _
  rw [retainedPositiveAsPolynomial, Polynomial.coeff_map]
  change (remainingCoordinateEquiv i
    ((ordinaryRootPolynomial (challengeRetainingRootFirst Q)).coeff j)).natDegree ≤ _
  rw [remainingCoordinateEquiv_natDegree]
  apply degreeOf_le_iff.mpr
  intro u hu
  simpa only [Finsupp.optionElim_apply_some, Finsupp.some_apply] using
    MvPolynomial.monomial_le_degreeOf (some i)
      ((mem_support_coeff_optionEquivLeft F).mp hu)

private theorem retainedChallengeDegree_le_of_coeffNatDegreeLE
    (Q : DifferentialPolynomial F[X] 1) {H : ℕ}
    (hheight : CoeffNatDegreeLE Q H) :
    degreeOf (some (some (1 : Fin 2))) (challengeRetainingRootFirst Q) ≤ H := by
  classical
  let T := (optionEquivRight F (JetVariable 1)).symm Q
  have hT : degreeOf none T ≤ H := by
    have hweight : T.weightedTotalDegree (fun v ↦ v.elim 1 fun _ ↦ 0) ≤ H :=
      weightedTotalDegree_optionEquivRight_symm_coefficientDegree_le hheight
    have hweights : (fun v : Option (JetVariable 1) ↦ v.elim 1 fun _ ↦ 0) =
        Pi.single none 1 := by
      funext v
      cases v <;> simp
    have hweight' : T.weightedTotalDegree (Pi.single none 1) ≤ H := by
      simpa only [hweights] using hweight
    rw [← weightedTotalDegree_piSingle none T]
    exact hweight'
  have hrename := degreeOf_rename_of_injective
    (Equiv.swap none (some (some (1 : Fin 2)))).injective none (p := T)
  change degreeOf (some (some (1 : Fin 2)))
      (rename (Equiv.swap none (some (some 1))) T) ≤ H
  have hrename' : degreeOf (some (some (1 : Fin 2)))
      (rename (Equiv.swap none (some (some 1))) T) = degreeOf none T := by
    simpa [Equiv.swap_apply_def] using hrename
  exact hrename'.le.trans hT

/-- The retained content and positive product together use at most the input challenge degree.
-/
private theorem retainedContent_add_positiveChallengeDegree_le
    (Q : DifferentialPolynomial F[X] 1) {H : ℕ}
    (hheight : CoeffNatDegreeLE Q H) :
    degreeOf (some (some (1 : Fin 2)))
        (radicalContent none (challengeRetainingRootFirst Q)) +
      degreeOf (some (some (1 : Fin 2)))
        (radicalPrimPart none (challengeRetainingRootFirst Q)) ≤ H := by
  let R := challengeRetainingRootFirst Q
  let z := some (some (1 : Fin 2))
  have hbudget := add_sum_degreeOf_positiveDegreeFactorClasses_le none z R
  have hprod :
      degreeOf z (radicalPrimPart none R) =
        ∑ c ∈ positiveDegreeFactorClasses none R, degreeOf z c.rep := by
    unfold radicalPrimPart
    rw [degreeOf_prod_eq]
    intro c hc
    exact irreducible_rep_of_mem_positiveDegreeFactorClasses hc |>.ne_zero
  rw [← hprod] at hbudget
  exact hbudget.trans (retainedChallengeDegree_le_of_coeffNatDegreeLE Q hheight)

/-- The retained singular polynomial has challenge degree at most `(2M - 1)H`. -/
theorem flattenedSingularPolynomial_challengeDegree_le
    (Q : DifferentialPolynomial F[X] 1)
    {H M : ℕ} (hheight : CoeffNatDegreeLE Q H) (hM : 0 < M)
    (hderiv : jetDegree Q 1 ≤ M) :
    degreeOf (some (1 : Fin 2)) (flattenedSingularPolynomial Q) ≤
      resultantChallengeEnvelope H M := by
  rw [← remainingCoordinateEquiv_natDegree (F := F) (some 1),
    remainingCoordinateEquiv_flattenedSingularPolynomial]
  let r := degreeOf none (radicalPrimPart none (challengeRetainingRootFirst Q))
  let hU := degreeOf (some (some (1 : Fin 2)))
    (radicalContent none (challengeRetainingRootFirst Q))
  let hV := degreeOf (some (some (1 : Fin 2)))
    (radicalPrimPart none (challengeRetainingRootFirst Q))
  have hbudget : hU + hV ≤ H := retainedContent_add_positiveChallengeDegree_le Q hheight
  have hcontent : (retainedContentAsPolynomial Q (some 1)).natDegree ≤ hU := by
    rw [retainedContentAsPolynomial, remainingCoordinateEquiv_natDegree]
    exact degreeOf_flattenedContentCoefficient_le Q (some 1)
  by_cases hrzero : r = 0
  · change (singularTail (retainedContentAsPolynomial Q (some 1))
      (retainedPositiveAsPolynomial Q (some 1)) r).natDegree ≤ _
    rw [hrzero, singularTail]
    simp only [Nat.zero_sub, Polynomial.resultant_zero_left_deg, pow_zero, mul_one]
    calc
      (retainedContentAsPolynomial Q (some 1)).natDegree ≤ hU := hcontent
      _ ≤ H := (Nat.le_add_right _ _).trans hbudget
      _ ≤ resultantChallengeEnvelope H M := by
        rw [resultantChallengeEnvelope]
        have hone : 1 ≤ 2 * M - 1 := by omega
        simpa using Nat.mul_le_mul_right H hone
  · have hr : 0 < r := Nat.pos_of_ne_zero hrzero
    have hrM : r ≤ M := by
      calc
      r = jetDegree (positiveCurveEquation Q) 1 := by
          change degreeOf none (radicalPrimPart none (challengeRetainingRootFirst Q)) = _
          simpa only [jetDegree] using (positiveCurveEquation_yOneDegree Q).symm
        _ ≤ jetDegree Q 1 := positiveCurveEquation_yOneDegree_le Q
        _ ≤ M := hderiv
    have hresultant :
        (Polynomial.resultant (retainedPositiveAsPolynomial Q (some 1))
          (retainedPositiveAsPolynomial Q (some 1)).derivative r (r - 1)).natDegree ≤
          (2 * r - 1) * hV := by
      have h := Polynomial.natDegree_resultant_derivative_padded_le
        (retainedPositiveAsPolynomial Q (some 1))
      rw [retainedPositiveAsPolynomial_natDegree] at h
      exact h.trans (Nat.mul_le_mul_left _ (retainedPositive_degreeX_le Q (some 1)))
    have htail := natDegree_mul_le.trans (Nat.add_le_add hcontent hresultant)
    exact htail.trans (content_add_resultantChallenge_le hM hrM hbudget
      (d := (2 * r - 1) * hV) (Nat.le_refl _))

/-- Move `Y₀` to the distinguished ordinary root coordinate while retaining `X` and the
challenge. -/
def singularCoordinateEquiv : JetVariable 1 ≃ Option (Fin 2) :=
  Equiv.swap none (some 0)

/-- The retained singular tail as an order-zero differential equation over the challenge ring.
-/
def singularCurveEquation (Q : DifferentialPolynomial F[X] 1) :
    DifferentialPolynomial F[X] 0 :=
  ordinaryUnflatten F
    (renameEquiv F singularCoordinateEquiv (flattenedSingularPolynomial Q))

/-- Flattening the singular curve equation recovers its remaining coordinates. -/
theorem ordinaryFlatten_singularCurveEquation
    (Q : DifferentialPolynomial F[X] 1) :
    ordinaryFlatten F (singularCurveEquation Q) =
      renameEquiv F singularCoordinateEquiv (flattenedSingularPolynomial Q) := by
  exact (ordinaryFlatten F).apply_symm_apply _

/-- The order-zero singular equation has the ordinary degree envelope. -/
theorem singularCurveEquation_degree_le
    (Q : DifferentialPolynomial F[X] 1)
    {B M : ℕ} (hjet : jetTotalDegree Q ≤ B)
    (hderiv : jetDegree Q 1 ≤ M) (hMB : M ≤ B) :
    (singularCurveEquation Q).degreeOf (some 0) ≤ ordinaryDegreeEnvelope B M := by
  rw [← degreeOf_none_ordinaryFlatten, ordinaryFlatten_singularCurveEquation]
  have hrename := degreeOf_rename_of_injective singularCoordinateEquiv.injective
    (some (0 : Fin 2)) (p := flattenedSingularPolynomial Q)
  have he : singularCoordinateEquiv (some (0 : Fin 2)) = none := by rfl
  rw [he] at hrename
  change degreeOf none
    (rename singularCoordinateEquiv (flattenedSingularPolynomial Q)) ≤ _
  rw [hrename]
  exact flattenedSingularPolynomial_yZeroDegree_le Q hjet hderiv hMB

/-- The singular equation's challenge coefficient degrees fit the derivative-resultant
envelope. -/
theorem singularCurveEquation_coeffNatDegreeLE
    (Q : DifferentialPolynomial F[X] 1)
    {H M : ℕ} (hheight : CoeffNatDegreeLE Q H) (hM : 0 < M)
    (hderiv : jetDegree Q 1 ≤ M) :
    CoeffNatDegreeLE (singularCurveEquation Q) (resultantChallengeEnvelope H M) := by
  apply coeffNatDegreeLE_ordinaryUnflatten_of_degreeOf_le
  have hrename := degreeOf_rename_of_injective singularCoordinateEquiv.injective
    (some (1 : Fin 2)) (p := flattenedSingularPolynomial Q)
  have he : singularCoordinateEquiv (some (1 : Fin 2)) = some 1 := by rfl
  rw [he] at hrename
  change degreeOf (some 1)
    (rename singularCoordinateEquiv (flattenedSingularPolynomial Q)) ≤ _
  rw [hrename]
  exact flattenedSingularPolynomial_challengeDegree_le Q hheight hM hderiv

private theorem challengeRetainingRootFirst_yOneDegree
    (Q : DifferentialPolynomial F[X] 1) :
    degreeOf none (challengeRetainingRootFirst Q) = jetDegree Q 1 := by
  let T := (optionEquivRight F (JetVariable 1)).symm Q
  have hrename := degreeOf_rename_of_injective
    (Equiv.swap none (some (some (1 : Fin 2)))).injective
      (some (some (1 : Fin 2))) (p := T)
  change degreeOf none (rename (Equiv.swap none (some (some 1))) T) = _ at hrename
  calc
    degreeOf none (challengeRetainingRootFirst Q) =
        degreeOf none (rename (Equiv.swap none (some (some 1))) T) := by
          simp [challengeRetainingRootFirst, T]
    _ = degreeOf (some (some (1 : Fin 2))) T := hrename
    _ = degreeOf (some 1) Q := by
      simpa only [AlgEquiv.apply_symm_apply] using
        (degreeOf_optionEquivRight
          ((optionEquivRight F (JetVariable 1)).symm Q) (some 1)).symm

/-- The singular equation is nonzero when the derivative resultant is protected by the
characteristic bound. -/
theorem singularCurveEquation_ne_zero
    (Q : DifferentialPolynomial F[X] 1) {M : ℕ}
    (hdegree : jetDegree Q 1 ≤ M)
    (hchar : ringChar F = 0 ∨ M < ringChar F) :
    singularCurveEquation Q ≠ 0 := by
  have hchar' : ringChar F = 0 ∨
      degreeOf none (challengeRetainingRootFirst Q) < ringChar F := by
    rcases hchar with hzero | hpositive
    · exact Or.inl hzero
    · exact Or.inr ((challengeRetainingRootFirst_yOneDegree Q).trans_le hdegree |>.trans_lt
        hpositive)
  have hresultant := Polynomial.resultant_derivative_ne_zero_ordinaryRootPolynomial
    (challengeRetainingRootFirst Q) hchar'
  have hresultant' :
      Polynomial.resultant (ordinaryRootPolynomial (challengeRetainingRootFirst Q))
        (ordinaryRootPolynomial (challengeRetainingRootFirst Q)).derivative
        (degreeOf none (radicalPrimPart none (challengeRetainingRootFirst Q)))
        (degreeOf none (radicalPrimPart none (challengeRetainingRootFirst Q)) - 1) ≠ 0 := by
    simpa only [natDegree_ordinaryRootPolynomial] using hresultant
  have hproduct : flattenedSingularPolynomial Q ≠ 0 :=
    mul_ne_zero (flattenedContentCoefficient_ne_zero Q) hresultant'
  intro hzero
  have hflat := congrArg (ordinaryFlatten F) hzero
  rw [ordinaryFlatten_singularCurveEquation, map_zero] at hflat
  exact (renameEquiv F singularCoordinateEquiv).injective.ne_iff.mpr hproduct hflat

/-- Evaluate the remaining coordinates at `X`, `P`, and challenge `z`. -/
def retainedSpecializationHom (z : F) (P : F[X]) :
    MvPolynomial (JetVariable 1) F →+* F[X] :=
  eval₂Hom Polynomial.C fun v ↦
    v.elim Polynomial.X fun i ↦ Fin.cases P (fun _ ↦ Polynomial.C z) i

/-- Evaluate the root-first coordinates at the first jet of `P`. -/
def retainedRootSpecializationHom (z : F) (P : F[X]) :
    MvPolynomial (Option (JetVariable 1)) F →+* F[X] :=
  eval₂Hom Polynomial.C fun v ↦
    v.elim (P.hasseDeriv 1) fun i ↦ retainedSpecializationHom z P (X i)

/-- Root-first specialization is evaluation of the positive-root polynomial at the first jet. -/
theorem retainedRootSpecializationHom_eq_eval_rootPolynomial
    (R : MvPolynomial (Option (JetVariable 1)) F) (z : F) (P : F[X]) :
    retainedRootSpecializationHom z P R =
      ((optionEquivLeft F (JetVariable 1) R).map
        (retainedSpecializationHom z P)).eval (P.hasseDeriv 1) := by
  let lhs : MvPolynomial (Option (JetVariable 1)) F →+* F[X] :=
    retainedRootSpecializationHom z P
  let rhs : MvPolynomial (Option (JetVariable 1)) F →+* F[X] :=
    (Polynomial.evalRingHom (P.hasseDeriv 1)).comp
      ((Polynomial.mapRingHom (retainedSpecializationHom z P)).comp
        (optionEquivLeft F (JetVariable 1)).toRingHom)
  change lhs R = rhs R
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [lhs, rhs, retainedRootSpecializationHom, retainedSpecializationHom]
  · intro v
    rcases v with _ | i
    · simp [lhs, rhs, retainedRootSpecializationHom]
    · simp [lhs, rhs, retainedRootSpecializationHom, retainedSpecializationHom]

/-- Root-first specialization of the retained content is its root-coordinate constant
coefficient. -/
theorem retainedRootSpecializationHom_flattenedContent
    (Q : DifferentialPolynomial F[X] 1) (z : F) (P : F[X]) :
    retainedRootSpecializationHom z P (radicalContent none
      (challengeRetainingRootFirst Q)) =
      retainedSpecializationHom z P (flattenedContentCoefficient Q) := by
  rw [retainedRootSpecializationHom_eq_eval_rootPolynomial]
  have hdegree : (optionEquivLeft F (JetVariable 1)
      (radicalContent none (challengeRetainingRootFirst Q))).natDegree = 0 := by
    rw [natDegree_optionEquivLeft, degreeOf_radicalContent]
  rw [Polynomial.eq_C_of_natDegree_eq_zero hdegree, Polynomial.map_C,
    Polynomial.eval_C]
  rfl

/-- The retained positive equation is the positive radical factor in root-first coordinates. -/
theorem challengeRetainingRootFirst_positiveCurveEquation
    (Q : DifferentialPolynomial F[X] 1) :
    challengeRetainingRootFirst (positiveCurveEquation Q) =
      radicalPrimPart none (challengeRetainingRootFirst Q) := by
  rw [positiveCurveEquation, challengeRetainingRootFirst_fromFlattenedRootFirst]

/-- Root-first specialization agrees with challenge specialization of the recovered equation. -/
theorem retainedRootSpecializationHom_flattenedRootFirst
    (Q : DifferentialPolynomial F[X] 1) (z : F) (P : F[X]) :
    retainedRootSpecializationHom z P (challengeRetainingRootFirst Q) =
      differentialSpecialization (challengeSpecialization Q z) P := by
  let lhs : DifferentialPolynomial F[X] 1 →+* F[X] :=
    (retainedRootSpecializationHom z P).comp
      ((renameEquiv F (Equiv.swap none (some (some 1)))).toRingHom.comp
        ((optionEquivRight F (JetVariable 1)).symm).toRingHom)
  let rhs : DifferentialPolynomial F[X] 1 →+* F[X] :=
    (differentialSpecializationHom P).toRingHom.comp
      (MvPolynomial.map (Polynomial.aeval z).toRingHom)
  have hhom : lhs = rhs := by
    apply MvPolynomial.ringHom_ext
    · intro r
      induction r using Polynomial.induction_on' with
      | add r s hr hs => simp only [map_add, hr, hs]
      | monomial n a =>
          rw [← Polynomial.C_mul_X_pow_eq_monomial]
          have hvalue : Fin.cases P (fun _ ↦ Polynomial.C z) (1 : Fin 2) =
              Polynomial.C z := by rfl
          simp [lhs, rhs, retainedRootSpecializationHom, retainedSpecializationHom,
            differentialSpecializationHom, hvalue]
    · intro v
      rcases v with _ | i
      · simp [lhs, rhs, retainedRootSpecializationHom,
          retainedSpecializationHom, differentialSpecializationHom,
          Equiv.swap_apply_def, MvPolynomial.eval₂Hom_X']
      · fin_cases i <;>
          simp [lhs, rhs, retainedRootSpecializationHom,
            retainedSpecializationHom, differentialSpecializationHom,
            Equiv.swap_apply_def, MvPolynomial.eval₂Hom_X']
  exact DFunLike.congr_fun hhom Q

/-- The positive-curve equation specializes to the ordinary positive-root polynomial. -/
theorem positiveCurveEquation_specialization_eq
    (Q : DifferentialPolynomial F[X] 1) (z : F) (P : F[X]) :
    differentialSpecialization (challengeSpecialization (positiveCurveEquation Q) z) P =
      ((ordinaryRootPolynomial (challengeRetainingRootFirst Q)).map
        (retainedSpecializationHom z P)).eval (P.hasseDeriv 1) := by
  rw [← retainedRootSpecializationHom_flattenedRootFirst]
  rw [challengeRetainingRootFirst_positiveCurveEquation,
    retainedRootSpecializationHom_eq_eval_rootPolynomial]
  rfl

/-- The retained positive equation's separant is the root derivative of its positive factor. -/
theorem challengeRetainingRootFirst_separant_positiveCurveEquation
    (Q : DifferentialPolynomial F[X] 1) :
    challengeRetainingRootFirst
        (separant (positiveCurveEquation Q) (1 : Fin 2)) =
      pderiv none (radicalPrimPart none (challengeRetainingRootFirst Q)) := by
  rw [separant, challengeRetainingRootFirst_pderiv,
    challengeRetainingRootFirst_positiveCurveEquation]

/-- The positive-curve separant specializes to the derivative of the positive-root polynomial.
-/
theorem positiveCurveSeparant_specialization_eq
    (Q : DifferentialPolynomial F[X] 1) (z : F) (P : F[X]) :
    differentialSpecialization (challengeSpecialization
        (separant (positiveCurveEquation Q) (1 : Fin 2)) z) P =
      ((ordinaryRootPolynomial (challengeRetainingRootFirst Q)).map
        (retainedSpecializationHom z P)).derivative.eval (P.hasseDeriv 1) := by
  rw [← retainedRootSpecializationHom_flattenedRootFirst,
    challengeRetainingRootFirst_separant_positiveCurveEquation,
    retainedRootSpecializationHom_eq_eval_rootPolynomial,
    optionEquivLeft_pderiv_none, Polynomial.derivative_map]
  rfl

private theorem retainedSpecializationHom_ordinaryUnflatten
    (R : MvPolynomial (JetVariable 1) F) (z : F) (P : F[X]) :
    retainedSpecializationHom z P R = differentialSpecialization
      (challengeSpecialization
        (ordinaryUnflatten F (renameEquiv F singularCoordinateEquiv R)) z) P := by
  let H := renameEquiv F singularCoordinateEquiv R
  have h := eval₂_ordinaryUnflatten Polynomial.C H
    Polynomial.X P (Polynomial.C z)
  have heval : Polynomial.eval₂RingHom Polynomial.C (Polynomial.C z) =
      Polynomial.C.comp (Polynomial.evalRingHom z) := by
    ext
    · simp
    · simp
  rw [heval] at h
  have hdiff : differentialSpecialization
      (challengeSpecialization (ordinaryUnflatten F H) z) P =
        eval₂ Polynomial.C
          (fun o ↦ o.elim P (fun i ↦ Fin.cases Polynomial.X
            (fun _ ↦ Polynomial.C z) i)) H := by
    unfold differentialSpecialization differentialSpecializationHom challengeSpecialization
    rw [MvPolynomial.aeval_eq_eval₂Hom, MvPolynomial.eval₂Hom_map_hom]
    have haeval : (Polynomial.aeval z).toRingHom = Polynomial.evalRingHom z := by
      ext <;> simp
    rw [haeval, MvPolynomial.coe_eval₂Hom, ← h]
    apply MvPolynomial.eval₂_congr
    intro i _ _ _
    rcases i with _ | j
    · rfl
    · fin_cases j
      simp
  change retainedSpecializationHom z P R =
    differentialSpecialization (challengeSpecialization (ordinaryUnflatten F H) z) P
  rw [hdiff]
  dsimp only [H]
  rw [renameEquiv_apply, eval₂_rename]
  apply MvPolynomial.eval₂_congr
  intro i _ _ _
  rcases i with _ | j
  · simp [singularCoordinateEquiv]
  · fin_cases j
    · simp [singularCoordinateEquiv]
    · simp only [Nat.reduceAdd, Fin.mk_one, Fin.isValue, Option.elim_some,
        Function.comp_apply]
      rw [show (1 : Fin 2) = Fin.succ 0 by decide]
      rfl

/-- Specializing the retained singular polynomial agrees with the singular equation. -/
theorem retainedSpecializationHom_flattenedSingularPolynomial
    (Q : DifferentialPolynomial F[X] 1) (z : F) (P : F[X]) :
    retainedSpecializationHom z P (flattenedSingularPolynomial Q) =
      differentialSpecialization (challengeSpecialization (singularCurveEquation Q) z) P := by
  exact retainedSpecializationHom_ordinaryUnflatten
    (flattenedSingularPolynomial Q) z P

/-- Common roots of the specialized positive polynomial and its derivative kill the retained
singular polynomial. -/
theorem flattenedSingularPolynomial_map_eq_zero_of_content_or_commonRoot
    {S : Type*} [CommRing S]
    (Q : DifferentialPolynomial F[X] 1)
    (f : MvPolynomial (JetVariable 1) F →+* S) (u : S)
    (hroute : f (flattenedContentCoefficient Q) = 0 ∨
      (((ordinaryRootPolynomial (challengeRetainingRootFirst Q)).map f).eval u = 0 ∧
        ((ordinaryRootPolynomial (challengeRetainingRootFirst Q)).map f).derivative.eval u = 0)) :
    f (flattenedSingularPolynomial Q) = 0 := by
  rw [flattenedSingularPolynomial, map_mul]
  rcases hroute with hcontent | ⟨hroot, hderivative⟩
  · rw [hcontent, zero_mul]
  · let R := challengeRetainingRootFirst Q
    let A := ordinaryRootPolynomial R
    let r := degreeOf none (radicalPrimPart none R)
    by_cases hrzero : r = 0
    · have hone := radicalPrimPart_eq_one_of_degreeOf_eq_zero none R hrzero
      have honePolynomial : ordinaryRootPolynomial R = 1 := by
        simp [ordinaryRootPolynomial, hone]
      rw [honePolynomial, Polynomial.map_one, Polynomial.eval_one] at hroot
      have hS : Subsingleton S := subsingleton_of_zero_eq_one hroot.symm
      exact hS.elim _ _
    · have hr : 0 < r := Nat.pos_of_ne_zero hrzero
      have hdegreeA : A.natDegree = r := by
        dsimp [A, r]
        exact natDegree_ordinaryRootPolynomial R
      have hderivativeDegree : A.derivative.natDegree ≤ r - 1 :=
        (Polynomial.natDegree_derivative_le A).trans
          (Nat.sub_le_sub_right hdegreeA.le 1)
      have hresultant := Polynomial.map_resultant_eq_zero_of_common_root f A A.derivative
        hdegreeA.le hderivativeDegree
        (Or.inl hr.ne') u hroot (by rwa [← Polynomial.derivative_map])
      rw [hresultant, mul_zero]

/-- If `Q` specializes to zero and its positive equation is nonzero or its separant is zero,
then its singular equation specializes to zero. -/
theorem singularCurveEquation_routes_nonregular
    (Q : DifferentialPolynomial F[X] 1) (hQ : Q ≠ 0) (z : F) (P : F[X])
    (hroot : differentialSpecialization (challengeSpecialization Q z) P = 0)
    (hnonregular : differentialSpecialization
        (challengeSpecialization (positiveCurveEquation Q) z) P ≠ 0 ∨
      differentialSpecialization (challengeSpecialization
        (separant (positiveCurveEquation Q) (1 : Fin 2)) z) P = 0) :
    differentialSpecialization (challengeSpecialization (singularCurveEquation Q) z) P = 0 := by
  have hR : challengeRetainingRootFirst Q ≠ 0 := by
    intro hzero
    have hfrom : fromFlattenedRootFirst (challengeRetainingRootFirst Q) = 0 := by
      rw [hzero]
      simp [fromFlattenedRootFirst]
    have hQzero : Q = 0 := by
      simpa only [fromFlattenedRootFirst_rootFirstChallenge] using hfrom
    exact hQ hQzero
  have hsplit := (map_radicalContent_mul_radicalPrimPart_eq_zero_iff
    (retainedRootSpecializationHom z P) none hR).mpr
      (by simpa only [retainedRootSpecializationHom_flattenedRootFirst] using hroot)
  rw [map_mul] at hsplit
  rw [← retainedSpecializationHom_flattenedSingularPolynomial]
  apply flattenedSingularPolynomial_map_eq_zero_of_content_or_commonRoot
    Q (retainedSpecializationHom z P) (P.hasseDeriv 1)
  rcases mul_eq_zero.mp hsplit with hcontent | hpositive
  · left
    rw [← retainedRootSpecializationHom_flattenedContent]
    exact hcontent
  · have hpositive' :
        ((ordinaryRootPolynomial (challengeRetainingRootFirst Q)).map
          (retainedSpecializationHom z P)).eval (P.hasseDeriv 1) = 0 := by
      calc
        _ = retainedRootSpecializationHom z P
            (radicalPrimPart none (challengeRetainingRootFirst Q)) := by
          simpa only [ordinaryRootPolynomial] using
            (retainedRootSpecializationHom_eq_eval_rootPolynomial
              (radicalPrimPart none (challengeRetainingRootFirst Q)) z P).symm
        _ = 0 := hpositive
    rcases hnonregular with hnot | hseparant
    · exact (hnot (by rw [positiveCurveEquation_specialization_eq]; exact hpositive')).elim
    · right
      constructor
      · exact hpositive'
      · rw [← positiveCurveSeparant_specialization_eq]
        exact hseparant

end

end ReedSolomon.FirstOrder.Squarefree
