/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Squarefree.RetainedCurve
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Squarefree.TailBound
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.Frobenius.Equation
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Symbolic.TaylorWitnessEmbedding

/-!
# Retained-challenge singular tail

This file forms the content times padded-resultant equation without specializing the challenge.
Two coordinate views give the sharp ordinary `Y₀` degree and the independent challenge-height
bound, while the original Sylvester dimensions preserve routing through degree drops.
-/

@[expose] public section

namespace ReedSolomon.FirstOrder.Squarefree

open MvPolynomial Polynomial PolynomialDifferential
open Polynomial.Bivariate
open ReedSolomon.HiddenDerivative

noncomputable section

variable {F : Type*} [Field F]

/-- Extract the retained `Y₁`-independent content. -/
def flattenedContentCoefficient (Q : DifferentialPolynomial F[X] 1) :
    MvPolynomial (JetVariable 1) F :=
  (optionEquivLeft F (JetVariable 1) (flattenedContent Q)).coeff 0

/-- Content times the original-size derivative resultant in `(X,Y₀,Z)`. -/
def flattenedSingularPolynomial (Q : DifferentialPolynomial F[X] 1) :
    MvPolynomial (JetVariable 1) F :=
  flattenedContentCoefficient Q * paddedDerivativeResultant
    (ordinaryRootPolynomial (flattenedRootFirst Q))
    (degreeOf none (flattenedPositiveRootProduct Q))

/-- Make a chosen remaining coordinate the outer polynomial variable. -/
def remainingCoordinateEquiv (i : JetVariable 1) :
    MvPolynomial (JetVariable 1) F ≃+* (MvPolynomial (Fin 2) F)[X] :=
  (renameEquiv F (Equiv.swap none i)).toRingEquiv.trans
    (optionEquivLeft F (Fin 2)).toRingEquiv

theorem remainingCoordinateEquiv_natDegree (i : JetVariable 1)
    (R : MvPolynomial (JetVariable 1) F) :
    (remainingCoordinateEquiv i R).natDegree = degreeOf i R := by
  unfold remainingCoordinateEquiv
  change (optionEquivLeft F (Fin 2) (rename (Equiv.swap none i) R)).natDegree = _
  rw [natDegree_optionEquivLeft]
  have hrename := degreeOf_rename_of_injective
    (Equiv.swap none i).injective i (p := R)
  simpa using hrename

/-- The content in a chosen remaining coordinate. -/
def retainedContentAsPolynomial (Q : DifferentialPolynomial F[X] 1)
    (i : JetVariable 1) : (MvPolynomial (Fin 2) F)[X] :=
  remainingCoordinateEquiv i (flattenedContentCoefficient Q)

/-- The positive product in `Y₁`, with a chosen remaining coordinate polynomialized. -/
def retainedPositiveAsPolynomial (Q : DifferentialPolynomial F[X] 1)
    (i : JetVariable 1) : (MvPolynomial (Fin 2) F)[X][X] :=
  (ordinaryRootPolynomial (flattenedRootFirst Q)).map
    (remainingCoordinateEquiv i).toRingHom

theorem flattenedContentCoefficient_ne_zero (Q : DifferentialPolynomial F[X] 1) :
    flattenedContentCoefficient Q ≠ 0 := by
  let U := optionEquivLeft F (JetVariable 1) (flattenedContent Q)
  have hU : U ≠ 0 :=
    (optionEquivLeft F (JetVariable 1)).injective.ne_iff.mpr
      (flattenedContent_ne_zero Q)
  have hdeg : U.natDegree = 0 := by
    dsimp only [U]
    rw [natDegree_optionEquivLeft, flattenedContent_rootDegree]
  rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg] at hU
  simpa [U, flattenedContentCoefficient] using hU

theorem retainedPositiveAsPolynomial_natDegree (Q : DifferentialPolynomial F[X] 1)
    (i : JetVariable 1) :
    (retainedPositiveAsPolynomial Q i).natDegree =
      degreeOf none (flattenedPositiveRootProduct Q) := by
  unfold retainedPositiveAsPolynomial
  rw [Polynomial.natDegree_map_eq_of_injective
    (remainingCoordinateEquiv i).injective,
    natDegree_ordinaryRootPolynomial]
  rfl

/-- Root-first weight counting `Y₀,Y₁` and ignoring `X,Z`. -/
def retainedRootJetWeight : Option (JetVariable 1) → ℕ
  | none => 1
  | some i => flattenedRootJetWeight (some i)

theorem degreeOf_coeff_add_le_retainedRootJetWeight
    (V : MvPolynomial (Option (JetVariable 1)) F) (i b : ℕ) (hi : i ≤ b)
    (hdegree : degreeOf none V = b) :
    degreeOf (some (0 : Fin 2))
        ((optionEquivLeft F (JetVariable 1) V).coeff i) + i ≤
      V.weightedTotalDegree retainedRootJetWeight := by
  classical
  have hiweight : i ≤ V.weightedTotalDegree retainedRootJetWeight := by
    calc
      i ≤ b := hi
      _ = degreeOf none V := hdegree.symm
      _ ≤ V.weightedTotalDegree retainedRootJetWeight := by
        apply degreeOf_le_iff.mpr
        intro u hu
        have h := le_weightedTotalDegree retainedRootJetWeight hu
        have hnone : u none ≤ u.weight retainedRootJetWeight := by
          rw [Finsupp.weight_eq_sum]
          simp [retainedRootJetWeight]
        exact hnone.trans h
  have hdeg : degreeOf (some (0 : Fin 2))
      ((optionEquivLeft F (JetVariable 1) V).coeff i) ≤
        V.weightedTotalDegree retainedRootJetWeight - i := by
    apply degreeOf_le_iff.mpr
    intro u hu
    have hexp : u.embDomain .some + Finsupp.single none i = u.optionElim i := by
      ext (_ | j) <;> simp
    have hsource : u.embDomain .some + Finsupp.single none i ∈ V.support := by
      rw [hexp]
      exact (mem_support_coeff_optionEquivLeft F).mp hu
    have hle := le_weightedTotalDegree retainedRootJetWeight hsource
    have hemb : Finsupp.weight retainedRootJetWeight (u.embDomain .some) =
        u (some (0 : Fin 2)) := by
      have hw : (fun j : JetVariable 1 ↦ retainedRootJetWeight (some j)) =
          Pi.single (some (0 : Fin 2)) 1 := by
        funext j
        rcases j with _ | k
        · rfl
        · fin_cases k <;> rfl
      rw [Finsupp.weight_apply, Finsupp.sum_embDomain, ← Finsupp.weight_apply]
      change Finsupp.weight (fun j ↦ retainedRootJetWeight (some j)) u = _
      rw [hw, Finsupp.weight_single_one_apply]
    have hsingle : u (some (0 : Fin 2)) + i =
        (u.embDomain .some + Finsupp.single none i).weight retainedRootJetWeight := by
      rw [map_add, hemb, Finsupp.weight_single]
      simp [retainedRootJetWeight]
    omega
  omega

theorem flattenedContent_add_positive_jetWeight_le
    (Q : DifferentialPolynomial F[X] 1) (hQ : Q ≠ 0) :
    (curveJetView (flattenedContent Q)).totalDegree +
        SymbolicSeparantChain.jetWeight (positiveCurveEquation Q) ≤
      SymbolicSeparantChain.jetWeight Q := by
  have hproduct : flattenedContent Q * flattenedPositiveRootProduct Q ∣
      flattenedRootFirst Q := by
    rw [flattenedContent, flattenedPositiveRootProduct, ordinary_split_product]
    exact ordinarySquarefreeProduct_dvd (flattenedRootFirst Q)
      (flattenedRootFirst_ne_zero_iff Q |>.mpr hQ)
  have hmapDvd : curveJetView
      (flattenedContent Q * flattenedPositiveRootProduct Q) ∣
        curveJetView (flattenedRootFirst Q) := map_dvd curveJetView hproduct
  have hdegree := totalDegree_le_of_dvd_of_isDomain hmapDvd
    ((curveJetView).injective.ne_iff.mpr
      (flattenedRootFirst_ne_zero_iff Q |>.mpr hQ))
  rw [map_mul, totalDegree_mul_of_isDomain
    ((curveJetView).injective.ne_iff.mpr (flattenedContent_ne_zero Q))
    ((curveJetView).injective.ne_iff.mpr (flattenedPositiveRootProduct_ne_zero Q))]
    at hdegree
  rw [positiveCurveEquation_jetWeight]
  exact hdegree.trans (by
    rw [curveJetView_totalDegree]
    have hrename :
        (flattenedRootFirst Q).weightedTotalDegree flattenedRootJetWeight =
          (flattenFirstOrderChallenge Q).weightedTotalDegree
            (liftedSourceWeight (fun v : JetVariable 1 ↦ v.elim 0 fun _ ↦ 1)) := by
      change weightedTotalDegree flattenedRootJetWeight
        (rename flattenedRootFirstEquiv (flattenFirstOrderChallenge Q)) = _
      rw [weightedTotalDegree_rename_of_injective flattenedRootFirstEquiv.injective]
      congr 1
      funext v
      rcases v with _ | (_ | j)
      · rfl
      · rfl
      · fin_cases j <;> rfl
    rw [hrename]
    exact flattenFirstOrderChallenge_jetWeight_le Q)

theorem remainingCoordinateEquiv_flattenedSingularPolynomial
    (Q : DifferentialPolynomial F[X] 1) (i : JetVariable 1) :
    remainingCoordinateEquiv i (flattenedSingularPolynomial Q) =
      singularTail (retainedContentAsPolynomial Q i)
        (retainedPositiveAsPolynomial Q i)
        (degreeOf none (flattenedPositiveRootProduct Q)) := by
  unfold flattenedSingularPolynomial singularTail retainedContentAsPolynomial
  rw [map_mul]
  congr 1
  rw [paddedDerivativeResultant, separableResultant]
  change (remainingCoordinateEquiv i).toRingHom
    (Polynomial.resultant (ordinaryRootPolynomial (flattenedRootFirst Q)).derivative
      (ordinaryRootPolynomial (flattenedRootFirst Q))
      (degreeOf none (flattenedPositiveRootProduct Q) - 1)
      (degreeOf none (flattenedPositiveRootProduct Q))) = _
  rw [← Polynomial.resultant_map_map]
  congr 2
  exact (Polynomial.derivative_map _ (remainingCoordinateEquiv i).toRingHom).symm

theorem retainedContent_yZeroDegree_le (Q : DifferentialPolynomial F[X] 1) :
    (retainedContentAsPolynomial Q (some 0)).natDegree ≤
      (curveJetView (flattenedContent Q)).totalDegree := by
  rw [retainedContentAsPolynomial, remainingCoordinateEquiv_natDegree]
  change degreeOf (some (0 : Fin 2))
      ((optionEquivLeft F (JetVariable 1) (flattenedContent Q)).coeff 0) ≤ _
  rw [curveJetView_totalDegree]
  apply degreeOf_le_iff.mpr
  intro u hu
  have hoption : u.optionElim 0 = u.embDomain .some := by
    ext (_ | j) <;> simp
  have hsource : u.embDomain .some ∈ (flattenedContent Q).support := by
    rw [← hoption]
    exact (mem_support_coeff_optionEquivLeft F).mp hu
  have hle := le_weightedTotalDegree flattenedRootJetWeight hsource
  have hcoord : u (some (0 : Fin 2)) ≤
      (u.embDomain .some).weight flattenedRootJetWeight := by
    rw [Finsupp.weight_eq_sum]
    simp [flattenedRootJetWeight]
  exact hcoord.trans hle

theorem retainedPositive_yZeroCoefficientTriangle
    (Q : DifferentialPolynomial F[X] 1) (i : ℕ)
    (hi : i ≤ degreeOf none (flattenedPositiveRootProduct Q)) :
    i + ((retainedPositiveAsPolynomial Q (some 0)).coeff i).natDegree ≤
      SymbolicSeparantChain.jetWeight (positiveCurveEquation Q) := by
  rw [retainedPositiveAsPolynomial, Polynomial.coeff_map,
    add_comm]
  change (remainingCoordinateEquiv (some 0)
    ((ordinaryRootPolynomial (flattenedRootFirst Q)).coeff i)).natDegree + i ≤ _
  rw [remainingCoordinateEquiv_natDegree]
  rw [positiveCurveEquation_jetWeight, curveJetView_totalDegree]
  change degreeOf (some (0 : Fin 2))
      ((optionEquivLeft F (JetVariable 1)
        (flattenedPositiveRootProduct Q)).coeff i) + i ≤ _
  have h := degreeOf_coeff_add_le_retainedRootJetWeight
    (flattenedPositiveRootProduct Q) i
    (degreeOf none (flattenedPositiveRootProduct Q)) hi rfl
  convert h using 1
  congr 1
  funext v
  rcases v with _ | (_ | k)
  · rfl
  · rfl
  · fin_cases k <;> rfl

/-- The retained singular tail has the exact manuscript `Y₀` envelope
`max(B,(2M-1)B-M²)`. -/
theorem flattenedSingularPolynomial_yZeroDegree_le
    (Q : DifferentialPolynomial F[X] 1) (hQ : Q ≠ 0)
    {B M : ℕ} (hjet : SymbolicSeparantChain.jetWeight Q ≤ B)
    (hderiv : Q.degreeOf (some 1) ≤ M) (hMB : M ≤ B) :
    degreeOf (some (0 : Fin 2)) (flattenedSingularPolynomial Q) ≤
      ordinaryDegreeEnvelope B M := by
  rw [← remainingCoordinateEquiv_natDegree (F := F) (some 0),
    remainingCoordinateEquiv_flattenedSingularPolynomial]
  let r := degreeOf none (flattenedPositiveRootProduct Q)
  let bU := (curveJetView (flattenedContent Q)).totalDegree
  let j := SymbolicSeparantChain.jetWeight (positiveCurveEquation Q)
  have hbudget : bU + j ≤ B :=
    (flattenedContent_add_positive_jetWeight_le Q hQ).trans hjet
  have hcontent : (retainedContentAsPolynomial Q (some 0)).natDegree ≤ bU :=
    retainedContent_yZeroDegree_le Q
  by_cases hrzero : r = 0
  · change (singularTail (retainedContentAsPolynomial Q (some 0))
      (retainedPositiveAsPolynomial Q (some 0)) r).natDegree ≤ _
    have hresultant : separableResultant
        (retainedPositiveAsPolynomial Q (some 0)) 0 = 1 := by
      simp [separableResultant]
    rw [hrzero, singularTail, hresultant, mul_one]
    exact hcontent.trans ((Nat.le_add_right _ _).trans hbudget) |>.trans
      (ordinaryDegreeEnvelope_ge_total B M)
  · have hr : 0 < r := Nat.pos_of_ne_zero hrzero
    have hrj : r ≤ j := by
      change degreeOf none (flattenedPositiveRootProduct Q) ≤
        SymbolicSeparantChain.jetWeight (positiveCurveEquation Q)
      rw [positiveCurveEquation_jetWeight, curveJetView_totalDegree]
      apply degreeOf_le_iff.mpr
      intro u hu
      have hle := le_weightedTotalDegree flattenedRootJetWeight hu
      have hnone : u none ≤ u.weight flattenedRootJetWeight := by
        rw [Finsupp.weight_eq_sum]
        simp [flattenedRootJetWeight]
      exact hnone.trans hle
    have hrM : r ≤ M := by
      exact (positiveCurveEquation_yOneDegree Q).ge.trans
        ((positiveCurveEquation_yOneDegree_le Q hQ).trans hderiv)
    exact natDegree_singularTail_le
      (retainedContentAsPolynomial Q (some 0))
      (retainedPositiveAsPolynomial Q (some 0))
      hr hrj hrM hMB hcontent hbudget
      (retainedPositiveAsPolynomial_natDegree Q (some 0))
      (retainedPositive_yZeroCoefficientTriangle Q)

theorem degreeOf_flattenedContentCoefficient_le
    (Q : DifferentialPolynomial F[X] 1) (i : JetVariable 1) :
    degreeOf i (flattenedContentCoefficient Q) ≤
      degreeOf (some i) (flattenedContent Q) := by
  apply degreeOf_le_iff.mpr
  intro u hu
  have hsource : u.optionElim 0 ∈ (flattenedContent Q).support :=
    (mem_support_coeff_optionEquivLeft F).mp hu
  have hle := MvPolynomial.monomial_le_degreeOf (some i) hsource
  simpa using hle

theorem retainedPositive_degreeX_le
    (Q : DifferentialPolynomial F[X] 1) (i : JetVariable 1) :
    Polynomial.Bivariate.degreeX (retainedPositiveAsPolynomial Q i) ≤
      degreeOf (some i) (flattenedPositiveRootProduct Q) := by
  classical
  unfold Polynomial.Bivariate.degreeX
  apply Finset.sup_le
  intro j _
  rw [retainedPositiveAsPolynomial, Polynomial.coeff_map]
  change (remainingCoordinateEquiv i
    ((ordinaryRootPolynomial (flattenedRootFirst Q)).coeff j)).natDegree ≤ _
  rw [remainingCoordinateEquiv_natDegree]
  apply degreeOf_le_iff.mpr
  intro u hu
  simpa [flattenedPositiveRootProduct] using
    MvPolynomial.monomial_le_degreeOf (some i)
      ((mem_support_coeff_optionEquivLeft F).mp hu)

theorem flattened_content_add_positive_challengeDegree_le
    (Q : DifferentialPolynomial F[X] 1) (hQ : Q ≠ 0)
    {H : ℕ} (hheight : ChallengeHeightLE Q H) :
    degreeOf (some (some (1 : Fin 2))) (flattenedContent Q) +
        degreeOf (some (some (1 : Fin 2))) (flattenedPositiveRootProduct Q) ≤ H := by
  have h := flattened_content_add_factorChallengeDegrees_le Q hQ hheight
  rw [flattenedPositiveRootProduct, ordinaryRootProduct, degreeOf_prod_eq]
  · exact h
  · intro a ha
    exact (ordinaryRootFactorClasses_spec (flattenedRootFirst Q) ha).1.ne_zero

/-- The retained singular tail has challenge height at most `(2M-1)H`, independently of
its sharp `Y₀` degree. -/
theorem flattenedSingularPolynomial_challengeDegree_le
    (Q : DifferentialPolynomial F[X] 1) (hQ : Q ≠ 0)
    {H M : ℕ} (hheight : ChallengeHeightLE Q H) (hM : 0 < M)
    (hderiv : Q.degreeOf (some 1) ≤ M) :
    degreeOf (some (1 : Fin 2)) (flattenedSingularPolynomial Q) ≤
      resultantChallengeEnvelope H M := by
  rw [← remainingCoordinateEquiv_natDegree (F := F) (some 1),
    remainingCoordinateEquiv_flattenedSingularPolynomial]
  let r := degreeOf none (flattenedPositiveRootProduct Q)
  let hU := degreeOf (some (some (1 : Fin 2))) (flattenedContent Q)
  let hV := degreeOf (some (some (1 : Fin 2))) (flattenedPositiveRootProduct Q)
  have hbudget : hU + hV ≤ H :=
    flattened_content_add_positive_challengeDegree_le Q hQ hheight
  have hcontent : (retainedContentAsPolynomial Q (some 1)).natDegree ≤ hU := by
    rw [retainedContentAsPolynomial, remainingCoordinateEquiv_natDegree]
    exact degreeOf_flattenedContentCoefficient_le Q (some 1)
  by_cases hrzero : r = 0
  · change (singularTail (retainedContentAsPolynomial Q (some 1))
      (retainedPositiveAsPolynomial Q (some 1)) r).natDegree ≤ _
    have hresultant : separableResultant
        (retainedPositiveAsPolynomial Q (some 1)) 0 = 1 := by
      simp [separableResultant]
    rw [hrzero, singularTail, hresultant, mul_one]
    calc
      (retainedContentAsPolynomial Q (some 1)).natDegree ≤ hU := hcontent
      _ ≤ H := (Nat.le_add_right _ _).trans hbudget
      _ ≤ resultantChallengeEnvelope H M := by
        rw [resultantChallengeEnvelope]
        have hone : 1 ≤ 2 * M - 1 := by omega
        simpa using Nat.mul_le_mul_right H hone
  · have hr : 0 < r := Nat.pos_of_ne_zero hrzero
    have hrM : r ≤ M := by
      exact (positiveCurveEquation_yOneDegree Q).ge.trans
        ((positiveCurveEquation_yOneDegree_le Q hQ).trans hderiv)
    have hresultant :
        (separableResultant (retainedPositiveAsPolynomial Q (some 1)) r).natDegree ≤
          (2 * r - 1) * hV := by
      apply natDegree_separableResultant_le_of_height
      · exact retainedPositiveAsPolynomial_natDegree Q (some 1)
      · exact hr
      · exact retainedPositive_degreeX_le Q (some 1)
    exact natDegree_mul_le.trans ((Nat.add_le_add hcontent hresultant).trans
      (content_add_resultantChallenge_le hr hrM hbudget le_rfl))

/-- Move `Y₀` to the distinguished ordinary root coordinate, retaining `X,Z`. -/
def singularCoordinateEquiv : JetVariable 1 ≃ Option (Fin 2) :=
  Equiv.swap none (some 0)

/-- The retained singular tail as an order-zero differential equation over `F[Z]`. -/
def singularCurveEquation (Q : DifferentialPolynomial F[X] 1) :
    DifferentialPolynomial F[X] 0 :=
  ordinaryUnflatten F
    (renameEquiv F singularCoordinateEquiv (flattenedSingularPolynomial Q))

theorem ordinaryFlatten_singularCurveEquation
    (Q : DifferentialPolynomial F[X] 1) :
    ordinaryFlatten F (singularCurveEquation Q) =
      renameEquiv F singularCoordinateEquiv (flattenedSingularPolynomial Q) := by
  exact (ordinaryFlatten F).apply_symm_apply _

theorem singularCurveEquation_ne_zero
    (Q : DifferentialPolynomial F[X] 1) (hQ : Q ≠ 0) {M : ℕ}
    (hdegree : Q.degreeOf (some 1) ≤ M)
    (hchar : ringChar F = 0 ∨ M < ringChar F) :
    singularCurveEquation Q ≠ 0 := by
  have hproduct : flattenedSingularPolynomial Q ≠ 0 :=
    mul_ne_zero (flattenedContentCoefficient_ne_zero Q)
      (flattenedPositiveRootProduct_resultant_ne_zero Q hQ hdegree hchar)
  intro hzero
  have hmapped := congrArg (ordinaryFlatten F) hzero
  rw [ordinaryFlatten_singularCurveEquation, map_zero] at hmapped
  exact (renameEquiv F singularCoordinateEquiv).injective.ne_iff.mpr hproduct hmapped

theorem singularCurveEquation_degree_le
    (Q : DifferentialPolynomial F[X] 1) (hQ : Q ≠ 0)
    {B M : ℕ} (hjet : SymbolicSeparantChain.jetWeight Q ≤ B)
    (hderiv : Q.degreeOf (some 1) ≤ M) (hMB : M ≤ B) :
    (singularCurveEquation Q).degreeOf (some 0) ≤ ordinaryDegreeEnvelope B M := by
  rw [← degreeOf_none_ordinaryFlatten, ordinaryFlatten_singularCurveEquation]
  have hrename := degreeOf_rename_of_injective singularCoordinateEquiv.injective
    (some (0 : Fin 2)) (p := flattenedSingularPolynomial Q)
  have he : singularCoordinateEquiv (some (0 : Fin 2)) = none := by rfl
  rw [he] at hrename
  change degreeOf none
    (rename singularCoordinateEquiv (flattenedSingularPolynomial Q)) ≤ _
  rw [hrename]
  exact flattenedSingularPolynomial_yZeroDegree_le Q hQ hjet hderiv hMB

theorem singularCurveEquation_challengeHeightLE
    (Q : DifferentialPolynomial F[X] 1) (hQ : Q ≠ 0)
    {H M : ℕ} (hheight : ChallengeHeightLE Q H) (hM : 0 < M)
    (hderiv : Q.degreeOf (some 1) ≤ M) :
    ChallengeHeightLE (singularCurveEquation Q) (resultantChallengeEnvelope H M) := by
  apply challengeHeightLE_ordinaryUnflatten_of_degreeOf_le
  have hrename := degreeOf_rename_of_injective singularCoordinateEquiv.injective
    (some (1 : Fin 2)) (p := flattenedSingularPolynomial Q)
  have he : singularCoordinateEquiv (some (1 : Fin 2)) = some 1 := by rfl
  rw [he] at hrename
  change degreeOf (some 1)
    (rename singularCoordinateEquiv (flattenedSingularPolynomial Q)) ≤ _
  rw [hrename]
  exact flattenedSingularPolynomial_challengeDegree_le Q hQ hheight hM hderiv

theorem flattenedPositiveRootProduct_eq_one_of_rootDegree_eq_zero
    (Q : DifferentialPolynomial F[X] 1)
    (hdegree : degreeOf none (flattenedPositiveRootProduct Q) = 0) :
    flattenedPositiveRootProduct Q = 1 := by
  classical
  have hempty : ordinaryRootFactorClasses (flattenedRootFirst Q) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a ha
    have hpos := (ordinaryRootFactorClasses_spec (flattenedRootFirst Q) ha).2
    have hle : degreeOf none (ordinaryFactorRepresentative a) ≤
        degreeOf none (flattenedPositiveRootProduct Q) := by
      rw [flattenedPositiveRootProduct, ordinaryRootProduct, degreeOf_prod_eq]
      · exact Finset.single_le_sum
          (fun b _ ↦ Nat.zero_le (degreeOf none (ordinaryFactorRepresentative b))) ha
      · intro b hb
        exact (ordinaryRootFactorClasses_spec (flattenedRootFirst Q) hb).1.ne_zero
    omega
  rw [flattenedPositiveRootProduct, ordinaryRootProduct, hempty]
  simp

/-- Algebraic routing core: either retained content vanishes, or a common positive-product
root and derivative kills the original-size resultant. -/
theorem flattenedSingularPolynomial_map_eq_zero_of_content_or_commonRoot
    {S : Type*} [CommRing S] [IsDomain S]
    (Q : DifferentialPolynomial F[X] 1)
    (f : MvPolynomial (JetVariable 1) F →+* S) (u : S)
    (hroute : f (flattenedContentCoefficient Q) = 0 ∨
      (((ordinaryRootPolynomial (flattenedRootFirst Q)).map f).eval u = 0 ∧
        ((ordinaryRootPolynomial (flattenedRootFirst Q)).map f).derivative.eval u = 0)) :
    f (flattenedSingularPolynomial Q) = 0 := by
  rw [flattenedSingularPolynomial, map_mul]
  rcases hroute with hcontent | ⟨hroot, hderivative⟩
  · rw [hcontent, zero_mul]
  · let r := degreeOf none (flattenedPositiveRootProduct Q)
    by_cases hrzero : r = 0
    · have hone := flattenedPositiveRootProduct_eq_one_of_rootDegree_eq_zero Q hrzero
      have honePolynomial : ordinaryRootPolynomial (flattenedRootFirst Q) = 1 := by
        unfold flattenedPositiveRootProduct at hone
        rw [ordinaryRootPolynomial, hone]
        simp
      rw [honePolynomial, Polynomial.map_one, Polynomial.eval_one] at hroot
      exact (one_ne_zero hroot).elim
    · have hr : 0 < r := Nat.pos_of_ne_zero hrzero
      have hresultant :=
        Polynomial.paddedDerivativeResultant_map_eq_zero_of_common_root
          (ordinaryRootPolynomial (flattenedRootFirst Q)) hr
          (by rw [natDegree_ordinaryRootPolynomial]; rfl)
          f u hroot hderivative
      rw [hresultant, mul_zero]

/-- Evaluate `(X,Y₀,Z)` at `(X,P,z)`. -/
def retainedSpecializationHom (z : F) (P : F[X]) :
    MvPolynomial (JetVariable 1) F →+* F[X] :=
  eval₂Hom Polynomial.C fun v ↦
    v.elim Polynomial.X fun i ↦ Fin.cases P (fun _ ↦ Polynomial.C z) i

/-- Evaluate root-first `(Y₁;X,Y₀,Z)` coordinates on the first jet of `P`. -/
def retainedRootSpecializationHom (z : F) (P : F[X]) :
    MvPolynomial (Option (JetVariable 1)) F →+* F[X] :=
  eval₂Hom Polynomial.C fun v ↦
    v.elim (P.hasseDeriv 1) fun i ↦ retainedSpecializationHom z P (X i)

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
    · simp [lhs, rhs, retainedRootSpecializationHom,
        retainedSpecializationHom]

theorem retainedRootSpecializationHom_flattenedContent
    (Q : DifferentialPolynomial F[X] 1) (z : F) (P : F[X]) :
    retainedRootSpecializationHom z P (flattenedContent Q) =
      retainedSpecializationHom z P (flattenedContentCoefficient Q) := by
  rw [retainedRootSpecializationHom_eq_eval_rootPolynomial]
  have hdegree : (optionEquivLeft F (JetVariable 1)
      (flattenedContent Q)).natDegree = 0 := by
    rw [natDegree_optionEquivLeft, flattenedContent_rootDegree]
  rw [Polynomial.eq_C_of_natDegree_eq_zero hdegree, Polynomial.map_C,
    Polynomial.eval_C]
  rfl

@[simp]
theorem flattenedRootFirst_positiveCurveEquation
    (Q : DifferentialPolynomial F[X] 1) :
    flattenedRootFirst (positiveCurveEquation Q) =
      flattenedPositiveRootProduct Q := by
  rw [flattenedRootFirst, flattenFirstOrderChallenge, positiveCurveEquation,
    flattenChallenge_fromFlattenedRootFirst]
  change (renameEquiv F flattenedRootFirstEquiv)
    ((renameEquiv F flattenedRootFirstEquiv).symm
      (flattenedPositiveRootProduct Q)) = _
  exact (renameEquiv F flattenedRootFirstEquiv).apply_symm_apply _

private theorem flattenChallenge_pderiv
    (Q : DifferentialPolynomial F[X] 1) (i : JetVariable 1) :
    flattenChallenge (MvPolynomial.pderiv i Q) =
      MvPolynomial.pderiv (some i) (flattenChallenge Q) := by
  induction Q using MvPolynomial.induction_on with
  | C p =>
      simp [flattenChallenge_C]
  | add P R hP hR =>
      simp [hP, hR]
  | mul_X P j hP =>
      by_cases hji : j = i
      · subst j
        simp [hP]
      · simp [hP, hji]

theorem flattenedRootFirst_separant_positiveCurveEquation
    (Q : DifferentialPolynomial F[X] 1) :
    flattenedRootFirst
        (separant (positiveCurveEquation Q) (1 : Fin 2)) =
      MvPolynomial.pderiv none (flattenedPositiveRootProduct Q) := by
  rw [flattenedRootFirst, flattenFirstOrderChallenge, separant,
    flattenChallenge_pderiv, positiveCurveEquation,
    flattenChallenge_fromFlattenedRootFirst]
  simp only [renameEquiv_apply]
  rw [show some (some (1 : Fin 2)) = flattenedRootFirstEquiv.symm none by rfl,
    MvPolynomial.pderiv_rename flattenedRootFirstEquiv.symm.injective]
  change (renameEquiv F flattenedRootFirstEquiv)
    ((renameEquiv F flattenedRootFirstEquiv).symm
      (MvPolynomial.pderiv none (flattenedPositiveRootProduct Q))) = _
  exact (renameEquiv F flattenedRootFirstEquiv).apply_symm_apply _

private theorem flattenChallenge_specialization
    (Q : DifferentialPolynomial F[X] 1) (z : F) (P : F[X]) :
    eval₂Hom Polynomial.C
        (fun v ↦ v.elim (Polynomial.C z)
          (fun i ↦ i.elim Polynomial.X fun j ↦ P.hasseDeriv j))
        (flattenChallenge Q) =
      differentialSpecialization (challengeSpecialization Q z) P := by
  let lhs : DifferentialPolynomial F[X] 1 →+* F[X] :=
    (eval₂Hom Polynomial.C
      (fun v ↦ v.elim (Polynomial.C z)
        (fun i ↦ i.elim Polynomial.X fun j ↦ P.hasseDeriv j))).comp
      flattenChallenge.toRingHom
  let rhs : DifferentialPolynomial F[X] 1 →+* F[X] :=
    (differentialSpecializationHom P).toRingHom.comp
      (MvPolynomial.map (Polynomial.aeval z).toRingHom)
  change lhs Q = rhs Q
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simp only [map_add, hp, hq]
    | monomial n a =>
        rw [← Polynomial.C_mul_X_pow_eq_monomial]
        simp [lhs, rhs, flattenChallenge_C]
  · intro i
    rcases i with _ | j
    · simp [lhs, rhs, flattenChallenge_X, differentialSpecializationHom]
    · simp [lhs, rhs, flattenChallenge_X, differentialSpecializationHom]

theorem retainedRootSpecializationHom_flattenedRootFirst
    (Q : DifferentialPolynomial F[X] 1) (z : F) (P : F[X]) :
    retainedRootSpecializationHom z P (flattenedRootFirst Q) =
      differentialSpecialization (challengeSpecialization Q z) P := by
  rw [retainedRootSpecializationHom, flattenedRootFirst, renameEquiv_apply,
    eval₂Hom_rename]
  rw [← flattenChallenge_specialization Q z P]
  apply eval₂Hom_congr
  · rfl
  · funext v
    simp only [Function.comp_apply]
    rcases v with _ | (_ | i)
    · change retainedSpecializationHom z P (X (some (1 : Fin 2))) =
        Polynomial.C z
      rw [retainedSpecializationHom, eval₂Hom_X']
      rw [show (1 : Fin 2) = Fin.succ 0 by decide]
      rfl
    · simp [flattenedRootFirstEquiv, Equiv.swap_apply_def, retainedSpecializationHom]
    · fin_cases i <;>
        simp [flattenedRootFirstEquiv, Equiv.swap_apply_def, retainedSpecializationHom]
  · rfl

theorem positiveCurveEquation_specialization_eq
    (Q : DifferentialPolynomial F[X] 1) (z : F) (P : F[X]) :
    differentialSpecialization (challengeSpecialization
        (positiveCurveEquation Q) z) P =
      ((ordinaryRootPolynomial (flattenedRootFirst Q)).map
        (retainedSpecializationHom z P)).eval (P.hasseDeriv 1) := by
  rw [← retainedRootSpecializationHom_flattenedRootFirst]
  rw [flattenedRootFirst_positiveCurveEquation]
  exact retainedRootSpecializationHom_eq_eval_rootPolynomial
    (flattenedPositiveRootProduct Q) z P

theorem positiveCurveSeparant_specialization_eq
    (Q : DifferentialPolynomial F[X] 1) (z : F) (P : F[X]) :
    differentialSpecialization (challengeSpecialization
        (separant (positiveCurveEquation Q) (1 : Fin 2)) z) P =
      ((ordinaryRootPolynomial (flattenedRootFirst Q)).map
        (retainedSpecializationHom z P)).derivative.eval (P.hasseDeriv 1) := by
  rw [← retainedRootSpecializationHom_flattenedRootFirst]
  rw [flattenedRootFirst_separant_positiveCurveEquation]
  rw [retainedRootSpecializationHom_eq_eval_rootPolynomial]
  rw [optionEquivLeft_pderiv_none, Polynomial.derivative_map]
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
    rw [differentialSpecialization, challengeSpecialization,
      MvPolynomial.eval₂Hom_map_hom]
    have haeval : (Polynomial.aeval z).toRingHom = Polynomial.evalRingHom z := by
      ext <;> simp
    rw [haeval]
    rw [MvPolynomial.coe_eval₂Hom]
    rw [← h]
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

theorem retainedSpecializationHom_flattenedSingularPolynomial
    (Q : DifferentialPolynomial F[X] 1) (z : F) (P : F[X]) :
    retainedSpecializationHom z P (flattenedSingularPolynomial Q) =
      differentialSpecialization
        (challengeSpecialization (singularCurveEquation Q) z) P := by
  exact retainedSpecializationHom_ordinaryUnflatten
    (flattenedSingularPolynomial Q) z P

/-- Every solution outside the retained positive-product regular locus solves the single
content-times-resultant tail equation at the same challenge. -/
theorem singularCurveEquation_routes_nonregular
    (Q : DifferentialPolynomial F[X] 1) (hQ : Q ≠ 0) (z : F) (P : F[X])
    (hroot : differentialSpecialization (challengeSpecialization Q z) P = 0)
    (hnonregular : differentialSpecialization (challengeSpecialization
        (positiveCurveEquation Q) z) P ≠ 0 ∨
      differentialSpecialization (challengeSpecialization
        (separant (positiveCurveEquation Q) (1 : Fin 2)) z) P = 0) :
    differentialSpecialization
      (challengeSpecialization (singularCurveEquation Q) z) P = 0 := by
  have hsplit := (flattened_split_zero_iff Q hQ
    (retainedRootSpecializationHom z P)).mpr
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
        ((ordinaryRootPolynomial (flattenedRootFirst Q)).map
          (retainedSpecializationHom z P)).eval (P.hasseDeriv 1) = 0 := by
      calc
        _ = retainedRootSpecializationHom z P
            (flattenedPositiveRootProduct Q) := by
          simpa only [ordinaryRootPolynomial, flattenedPositiveRootProduct] using
            (retainedRootSpecializationHom_eq_eval_rootPolynomial
              (flattenedPositiveRootProduct Q) z P).symm
        _ = 0 := hpositive
    rcases hnonregular with hnot | hseparant
    · exact (hnot (by
        rw [positiveCurveEquation_specialization_eq]
        exact hpositive')).elim
    · right
      constructor
      · exact hpositive'
      · rw [← positiveCurveSeparant_specialization_eq]
        exact hseparant

end

end ReedSolomon.FirstOrder.Squarefree
