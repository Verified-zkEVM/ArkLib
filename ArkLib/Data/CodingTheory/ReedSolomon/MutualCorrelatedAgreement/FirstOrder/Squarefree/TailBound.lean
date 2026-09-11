/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Squarefree.FactorwiseList
public import ArkLib.ToMathlib.Polynomial.PaddedDerivativeResultantCommonRoot

/-!
# The fixed-word squarefree singular-tail bound

This file constructs the ordinary equation required by factorwise first-order list counting.
It multiplies the retained root-independent content by the derivative resultant of the distinct
positive-`Y₁` product.  The resultant keeps the original Sylvester sizes, so specializations
that lower the actual `Y₁` degree are still routed correctly.
-/

@[expose] public section

namespace ReedSolomon.FirstOrder.Squarefree

open MvPolynomial Polynomial PolynomialDifferential
open ReedSolomon.HiddenDerivative

noncomputable section

universe u

variable {F : Type u} [Field F]

/-- The root-independent content after taking the constant `Y₁` coefficient. -/
def contentCoefficient (Q : DifferentialPolynomial F 1) : MvPolynomial (Fin 2) F :=
  (optionEquivLeft F (Fin 2) (content Q)).coeff 0

/-- Content times the padded derivative resultant, still in the remaining `(Y₀, X)`
coordinates. -/
def singularPolynomial (Q : DifferentialPolynomial F 1) : MvPolynomial (Fin 2) F :=
  contentCoefficient Q * paddedDerivativeResultant
    (ordinaryRootPolynomial (rootFirst Q)) (degreeOf none (positiveRootProduct Q))

/-- Regard `(Y₀, X)` as a polynomial in `Y₀` with coefficients in `F[X]`. -/
def remainingPolynomialEquiv : MvPolynomial (Fin 2) F ≃+* F[X][X] :=
  (MvPolynomial.finSuccEquiv F 1).toRingEquiv.trans
    (Polynomial.mapEquiv (MvPolynomial.uniqueAlgEquiv F (Fin 1)).toRingEquiv)

theorem remainingPolynomialEquiv_natDegree (R : MvPolynomial (Fin 2) F) :
    (remainingPolynomialEquiv R).natDegree = degreeOf (0 : Fin 2) R := by
  unfold remainingPolynomialEquiv
  rw [RingEquiv.trans_apply]
  change (Polynomial.map (MvPolynomial.uniqueAlgEquiv F (Fin 1)).toRingHom
    (MvPolynomial.finSuccEquiv F 1 R)).natDegree = degreeOf (0 : Fin 2) R
  rw [Polynomial.natDegree_map_eq_of_injective
    (MvPolynomial.uniqueAlgEquiv F (Fin 1)).injective]
  exact MvPolynomial.natDegree_finSuccEquiv R

/-- The singular tail as an ordinary polynomial in `Y₀`. -/
def singularAsPolynomial (Q : DifferentialPolynomial F 1) : F[X][X] :=
  remainingPolynomialEquiv (singularPolynomial Q)

/-- The positive product as a polynomial in `Y₁`, whose coefficients are polynomials in
`Y₀` over `F[X]`. -/
def positiveAsPolynomial (Q : DifferentialPolynomial F 1) : F[X][X][X] :=
  (ordinaryRootPolynomial (rootFirst Q)).map remainingPolynomialEquiv.toRingHom

/-- The retained content as a polynomial in `Y₀` over `F[X]`. -/
def contentAsPolynomial (Q : DifferentialPolynomial F 1) : F[X][X] :=
  remainingPolynomialEquiv (contentCoefficient Q)

/-- Turn a polynomial in `Y₀` over `F[X]` back into an order-zero differential equation. -/
def orderZeroOfPolynomial (R : F[X][X]) : DifferentialPolynomial F 0 :=
  (MvPolynomial.renameEquiv F orderZeroVariableEquiv).symm
    ((MvPolynomial.finSuccEquiv F 1).symm
      ((Polynomial.mapEquiv
        (MvPolynomial.uniqueAlgEquiv F (Fin 1)).toRingEquiv).symm R))

@[simp]
theorem orderZeroAsPolynomial_orderZeroOfPolynomial (R : F[X][X]) :
    orderZeroAsPolynomial (orderZeroOfPolynomial R) = R := by
  unfold orderZeroAsPolynomial orderZeroOfPolynomial
  rw [← MvPolynomial.renameEquiv_apply, AlgEquiv.apply_symm_apply,
    AlgEquiv.apply_symm_apply]
  change (Polynomial.mapEquiv
    (MvPolynomial.uniqueAlgEquiv F (Fin 1)).toRingEquiv)
      ((Polynomial.mapEquiv
        (MvPolynomial.uniqueAlgEquiv F (Fin 1)).toRingEquiv).symm R) = R
  exact RingEquiv.apply_symm_apply _ R

theorem orderZeroOfPolynomial_jetWeight (R : F[X][X]) :
    SymbolicSeparantChain.jetWeight (orderZeroOfPolynomial R) = R.natDegree := by
  have hweight : SymbolicSeparantChain.jetWeight (orderZeroOfPolynomial R) =
      MvPolynomial.degreeOf (some (0 : Fin 1)) (orderZeroOfPolynomial R) := by
    classical
    unfold SymbolicSeparantChain.jetWeight
    rw [← MvPolynomial.weightedTotalDegree_piSingle (some (0 : Fin 1))]
    congr 1
    funext i
    rcases i with _ | j
    · simp
    · fin_cases j
      simp
  rw [hweight]
  have hdegree : MvPolynomial.degreeOf (0 : Fin 2)
      (MvPolynomial.rename orderZeroVariableEquiv (orderZeroOfPolynomial R)) =
        MvPolynomial.degreeOf (some (0 : Fin 1)) (orderZeroOfPolynomial R) := by
    have hrename := MvPolynomial.degreeOf_rename_of_injective
      orderZeroVariableEquiv.injective (some (0 : Fin 1))
        (p := orderZeroOfPolynomial R)
    rw [show orderZeroVariableEquiv (some (0 : Fin 1)) = (0 : Fin 2) by decide] at hrename
    exact hrename
  rw [← hdegree, ← MvPolynomial.natDegree_finSuccEquiv]
  have hmapdeg := Polynomial.natDegree_map_eq_of_injective
    (f := (MvPolynomial.uniqueAlgEquiv F (Fin 1)).toRingHom)
    (MvPolynomial.uniqueAlgEquiv F (Fin 1)).injective
    (MvPolynomial.finSuccEquiv F 1
      (MvPolynomial.rename orderZeroVariableEquiv (orderZeroOfPolynomial R)))
  rw [← hmapdeg]
  change (orderZeroAsPolynomial (orderZeroOfPolynomial R)).natDegree = R.natDegree
  exact congrArg Polynomial.natDegree (orderZeroAsPolynomial_orderZeroOfPolynomial R)

/-- The constructed order-zero singular equation. -/
def singularEquation (Q : DifferentialPolynomial F 1) : DifferentialPolynomial F 0 :=
  orderZeroOfPolynomial (singularAsPolynomial Q)

/-- Evaluate the remaining coordinates at `(Y₀, X) = (P, X)`. -/
def remainingSpecializationHom (P : F[X]) : MvPolynomial (Fin 2) F →+* F[X] :=
  eval₂Hom Polynomial.C (Fin.cases P fun _ ↦ Polynomial.X)

theorem singularAsPolynomial_eval (Q : DifferentialPolynomial F 1) (P : F[X]) :
    (singularAsPolynomial Q).eval P =
      remainingSpecializationHom P (singularPolynomial Q) := by
  let lhs : MvPolynomial (Fin 2) F →+* F[X] :=
    (Polynomial.evalRingHom P).comp
      ((Polynomial.mapRingHom
        (MvPolynomial.uniqueAlgEquiv F (Fin 1)).toRingHom).comp
          (MvPolynomial.finSuccEquiv F 1).toRingHom)
  let rhs : MvPolynomial (Fin 2) F →+* F[X] := remainingSpecializationHom P
  change lhs (singularPolynomial Q) = rhs (singularPolynomial Q)
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [lhs, rhs, remainingSpecializationHom, MvPolynomial.finSuccEquiv_apply]
  · intro i
    fin_cases i
    · dsimp [lhs, rhs, remainingSpecializationHom]
      rw [MvPolynomial.finSuccEquiv_X_zero, Polynomial.map_X, Polynomial.eval_X,
        MvPolynomial.eval₂_X]
      congr
    · dsimp [lhs, rhs, remainingSpecializationHom]
      rw [show (1 : Fin 2) = (0 : Fin 1).succ by decide,
        MvPolynomial.finSuccEquiv_X_succ, Polynomial.map_C, Polynomial.eval_C]
      simp [MvPolynomial.X]
      congr

theorem rootFirstSpecializationHom_eq_eval_rootPolynomial
    (R : MvPolynomial (Option (Fin 2)) F) (P : F[X]) :
    rootFirstSpecializationHom P R =
      ((optionEquivLeft F (Fin 2) R).map (remainingSpecializationHom P)).eval
        (P.hasseDeriv 1) := by
  let lhs : MvPolynomial (Option (Fin 2)) F →+* F[X] := rootFirstSpecializationHom P
  let rhs : MvPolynomial (Option (Fin 2)) F →+* F[X] :=
    (Polynomial.evalRingHom (P.hasseDeriv 1)).comp
      ((Polynomial.mapRingHom (remainingSpecializationHom P)).comp
        (optionEquivLeft F (Fin 2)).toRingHom)
  change lhs R = rhs R
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [lhs, rhs, rootFirstSpecializationHom, remainingSpecializationHom]
  · intro v
    rcases v with _ | j
    · simp [lhs, rhs, rootFirstSpecializationHom, rootFirstEquiv]
    · fin_cases j
      · have hj : rootFirstEquiv.symm (some (0 : Fin 2)) = some 0 := by decide
        simp [lhs, rhs, rootFirstSpecializationHom, remainingSpecializationHom, hj]
      · have hj : rootFirstEquiv.symm (some (1 : Fin 2)) = none := by decide
        simp [lhs, rhs, rootFirstSpecializationHom, remainingSpecializationHom, hj]
        congr

theorem contentCoefficient_ne_zero (Q : DifferentialPolynomial F 1) :
    contentCoefficient Q ≠ 0 := by
  let U := optionEquivLeft F (Fin 2) (content Q)
  have hU : U ≠ 0 := (optionEquivLeft F (Fin 2)).injective.ne_iff.mpr (content_ne_zero Q)
  have hdeg : U.natDegree = 0 := by
    dsimp only [U]
    rw [natDegree_optionEquivLeft, content_rootDegree]
  rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg] at hU
  simpa [U, contentCoefficient] using hU

theorem remainingSpecializationHom_contentCoefficient (Q : DifferentialPolynomial F 1)
    (P : F[X]) :
    remainingSpecializationHom P (contentCoefficient Q) =
      differentialSpecialization (contentEquation Q) P := by
  rw [← rootFirstSpecializationHom_rootFirst]
  rw [contentEquation, rootFirst_fromRootFirst]
  rw [rootFirstSpecializationHom_eq_eval_rootPolynomial]
  have hdeg : (optionEquivLeft F (Fin 2) (content Q)).natDegree = 0 := by
    rw [natDegree_optionEquivLeft, content_rootDegree]
  rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg, Polynomial.map_C, Polynomial.eval_C]
  rfl

theorem rootFirst_separant_positiveEquation (Q : DifferentialPolynomial F 1) :
    rootFirst (separant (positiveEquation Q) (1 : Fin 2)) =
      MvPolynomial.pderiv none (positiveRootProduct Q) := by
  rw [rootFirst, separant, positiveEquation, fromRootFirst]
  simp only [MvPolynomial.renameEquiv_apply]
  rw [← MvPolynomial.pderiv_rename rootFirstEquiv.injective]
  have hrename : MvPolynomial.rename rootFirstEquiv
      (MvPolynomial.rename rootFirstEquiv.symm (positiveRootProduct Q)) =
        positiveRootProduct Q := by
    change (MvPolynomial.renameEquiv F rootFirstEquiv)
      ((MvPolynomial.renameEquiv F rootFirstEquiv).symm (positiveRootProduct Q)) = _
    exact (MvPolynomial.renameEquiv F rootFirstEquiv).apply_symm_apply _
  rw [hrename]
  rfl

theorem positiveEquation_specialization_eq (Q : DifferentialPolynomial F 1) (P : F[X]) :
    differentialSpecialization (positiveEquation Q) P =
      ((ordinaryRootPolynomial (rootFirst Q)).map (remainingSpecializationHom P)).eval
        (P.hasseDeriv 1) := by
  rw [← rootFirstSpecializationHom_rootFirst]
  rw [positiveEquation, rootFirst_fromRootFirst]
  exact rootFirstSpecializationHom_eq_eval_rootPolynomial (positiveRootProduct Q) P

theorem positiveSeparant_specialization_eq (Q : DifferentialPolynomial F 1) (P : F[X]) :
    differentialSpecialization (separant (positiveEquation Q) (1 : Fin 2)) P =
      ((ordinaryRootPolynomial (rootFirst Q)).map
        (remainingSpecializationHom P)).derivative.eval (P.hasseDeriv 1) := by
  rw [← rootFirstSpecializationHom_rootFirst]
  rw [rootFirst_separant_positiveEquation]
  rw [rootFirstSpecializationHom_eq_eval_rootPolynomial]
  rw [optionEquivLeft_pderiv_none, Polynomial.derivative_map]
  rfl

/-- The jet weight in root-first coordinates: `Y₁` and `Y₀` have weight one, while `X`
has weight zero. -/
def rootJetWeight : Option (Fin 2) → ℕ
  | none => 1
  | some j => if j = 0 then 1 else 0

theorem fromRootFirst_rootJetWeight (R : MvPolynomial (Option (Fin 2)) F) :
    R.weightedTotalDegree rootJetWeight = jetTotalDegree (fromRootFirst R) := by
  rw [jetTotalDegree_eq_weightedTotalDegree_elim]
  rw [fromRootFirst, MvPolynomial.renameEquiv_apply,
    MvPolynomial.weightedTotalDegree_rename_of_injective rootFirstEquiv.symm.injective]
  congr 1
  funext v
  rcases v with _ | j
  · rfl
  · fin_cases j <;> rfl

theorem positiveRootProduct_rootJetWeight (Q : DifferentialPolynomial F 1) :
    (positiveRootProduct Q).weightedTotalDegree rootJetWeight =
      jetTotalDegree (positiveEquation Q) :=
  fromRootFirst_rootJetWeight (positiveRootProduct Q)

/-- Each `Y₁` coefficient obeys the exact `Y₀`/`Y₁` homogeneous triangle.  The
explicit `i ≤ b` premise handles zero coefficients beyond the actual root degree. -/
theorem degreeOf_coeff_optionEquivLeft_add_le_rootJetWeight
    (V : MvPolynomial (Option (Fin 2)) F) (i b : ℕ) (hi : i ≤ b)
    (hdegree : degreeOf none V = b) :
    degreeOf (0 : Fin 2) ((optionEquivLeft F (Fin 2) V).coeff i) + i ≤
      V.weightedTotalDegree rootJetWeight := by
  classical
  have hiweight : i ≤ V.weightedTotalDegree rootJetWeight := by
    calc
      i ≤ b := hi
      _ = degreeOf none V := hdegree.symm
      _ ≤ V.weightedTotalDegree rootJetWeight := by
        apply degreeOf_le_iff.mpr
        intro u hu
        have h := le_weightedTotalDegree rootJetWeight hu
        have hnone : u none ≤ u.weight rootJetWeight := by
          rw [Finsupp.weight_eq_sum]
          simp [rootJetWeight]
        simpa [rootJetWeight] using hnone.trans h
  have hdeg : degreeOf (0 : Fin 2) ((optionEquivLeft F (Fin 2) V).coeff i) ≤
      V.weightedTotalDegree rootJetWeight - i := by
    apply degreeOf_le_iff.mpr
    intro u hu
    have hexp : u.embDomain .some + Finsupp.single none i = u.optionElim i := by
      ext (_ | j) <;> simp
    have hsource : u.embDomain .some + Finsupp.single none i ∈ V.support := by
      rw [hexp]
      exact (MvPolynomial.mem_support_coeff_optionEquivLeft F).mp hu
    have hle := le_weightedTotalDegree rootJetWeight hsource
    have hemb : Finsupp.weight rootJetWeight (u.embDomain .some) = u 0 := by
      have hw : (fun j : Fin 2 ↦ rootJetWeight (Function.Embedding.some j)) =
          Pi.single 0 1 := by
        funext j
        fin_cases j <;> simp [rootJetWeight]
      rw [Finsupp.weight_apply]
      rw [Finsupp.sum_embDomain, ← Finsupp.weight_apply, hw,
        Finsupp.weight_single_one_apply]
    have hsingle : u 0 + i =
        (u.embDomain .some + Finsupp.single none i).weight rootJetWeight := by
      rw [map_add, hemb, Finsupp.weight_single]
      simp [rootJetWeight]
    omega
  omega

theorem positiveAsPolynomial_natDegree (Q : DifferentialPolynomial F 1) :
    (positiveAsPolynomial Q).natDegree = degreeOf none (positiveRootProduct Q) := by
  unfold positiveAsPolynomial
  rw [Polynomial.natDegree_map_eq_of_injective remainingPolynomialEquiv.injective,
    natDegree_ordinaryRootPolynomial]
  rfl

theorem positiveAsPolynomial_coeff_triangle (Q : DifferentialPolynomial F 1)
    (i : ℕ) (hi : i ≤ degreeOf none (positiveRootProduct Q)) :
    i + ((positiveAsPolynomial Q).coeff i).natDegree ≤
      jetTotalDegree (positiveEquation Q) := by
  rw [positiveAsPolynomial, Polynomial.coeff_map, add_comm]
  change (remainingPolynomialEquiv
    ((ordinaryRootPolynomial (rootFirst Q)).coeff i)).natDegree + i ≤ _
  rw [remainingPolynomialEquiv_natDegree]
  rw [← positiveRootProduct_rootJetWeight]
  exact degreeOf_coeff_optionEquivLeft_add_le_rootJetWeight
    (positiveRootProduct Q) i (degreeOf none (positiveRootProduct Q)) hi rfl

theorem contentAsPolynomial_natDegree_le (Q : DifferentialPolynomial F 1) :
    (contentAsPolynomial Q).natDegree ≤ jetTotalDegree (contentEquation Q) := by
  rw [contentAsPolynomial, remainingPolynomialEquiv_natDegree, contentCoefficient]
  change degreeOf (0 : Fin 2) ((optionEquivLeft F (Fin 2) (content Q)).coeff 0) ≤
    jetTotalDegree (fromRootFirst (content Q))
  rw [← fromRootFirst_rootJetWeight (content Q)]
  simpa only [zero_add, Nat.add_zero] using degreeOf_coeff_optionEquivLeft_add_le_rootJetWeight
    (content Q) 0 0 le_rfl (content_rootDegree Q)

theorem singularAsPolynomial_eq_singularTail (Q : DifferentialPolynomial F 1) :
    singularAsPolynomial Q = singularTail (contentAsPolynomial Q)
      (positiveAsPolynomial Q) (degreeOf none (positiveRootProduct Q)) := by
  unfold singularAsPolynomial singularPolynomial singularTail contentAsPolynomial
  rw [map_mul]
  congr 1
  rw [paddedDerivativeResultant, separableResultant]
  change remainingPolynomialEquiv.toRingHom
    (Polynomial.resultant (ordinaryRootPolynomial (rootFirst Q)).derivative
      (ordinaryRootPolynomial (rootFirst Q))
      (degreeOf none (positiveRootProduct Q) - 1)
      (degreeOf none (positiveRootProduct Q))) = _
  rw [← Polynomial.resultant_map_map]
  congr 2
  exact (Polynomial.derivative_map _ remainingPolynomialEquiv.toRingHom).symm

theorem singularEquation_degree_le (Q : DifferentialPolynomial F 1) (hQ : Q ≠ 0)
    {B M : ℕ} (hjet : jetTotalDegree Q ≤ B)
    (hderiv : jetDegree Q 1 ≤ M) (hMB : M ≤ B) :
    SymbolicSeparantChain.jetWeight (singularEquation Q) ≤
      ordinaryDegreeEnvelope B M := by
  rw [singularEquation, orderZeroOfPolynomial_jetWeight]
  let r := degreeOf none (positiveRootProduct Q)
  let bU := jetTotalDegree (contentEquation Q)
  let j := jetTotalDegree (positiveEquation Q)
  have hbudget : bU + j ≤ B :=
    (contentEquation_jetTotalDegree_add_positiveEquation_le Q hQ).trans hjet
  have hcontent : (contentAsPolynomial Q).natDegree ≤ bU :=
    contentAsPolynomial_natDegree_le Q
  by_cases hrzero : r = 0
  · rw [singularAsPolynomial_eq_singularTail,
      show degreeOf none (positiveRootProduct Q) = r by rfl, hrzero]
    have hresultant : separableResultant (positiveAsPolynomial Q) 0 = 1 := by
      simp [separableResultant]
    rw [singularTail, hresultant, mul_one]
    exact hcontent.trans ((Nat.le_add_right _ _).trans hbudget) |>.trans
      (ordinaryDegreeEnvelope_ge_total B M)
  · have hr : 0 < r := Nat.pos_of_ne_zero hrzero
    have hrj : r ≤ j := by
      change degreeOf none (positiveRootProduct Q) ≤ jetTotalDegree (positiveEquation Q)
      calc
        degreeOf none (positiveRootProduct Q) =
            degreeOf none (rootFirst (positiveEquation Q)) := by
              rw [positiveEquation, rootFirst_fromRootFirst]
        _ = jetDegree (positiveEquation Q) 1 := rootDegree_rootFirst _
        _ ≤ jetTotalDegree (positiveEquation Q) := jetDegree_le_total _ 1
    have hrM : r ≤ M := by
      change degreeOf none (positiveRootProduct Q) ≤ M
      calc
        degreeOf none (positiveRootProduct Q) =
            degreeOf none (rootFirst (positiveEquation Q)) := by
              rw [positiveEquation, rootFirst_fromRootFirst]
        _ = jetDegree (positiveEquation Q) 1 := rootDegree_rootFirst _
        _ ≤ jetDegree Q 1 := positiveEquation_yOneDegree_le Q hQ
        _ ≤ M := hderiv
    rw [singularAsPolynomial_eq_singularTail]
    exact natDegree_singularTail_le
      (contentAsPolynomial Q) (positiveAsPolynomial Q)
      hr hrj hrM hMB hcontent hbudget
      (positiveAsPolynomial_natDegree Q)
      (positiveAsPolynomial_coeff_triangle Q)

theorem positiveResultant_ne_zero (Q : DifferentialPolynomial F 1) (hQ : Q ≠ 0)
    {M : ℕ} (hdegree : jetDegree Q 1 ≤ M)
    (hchar : ringChar F = 0 ∨ M < ringChar F) :
    paddedDerivativeResultant (ordinaryRootPolynomial (rootFirst Q))
      (degreeOf none (positiveRootProduct Q)) ≠ 0 := by
  apply paddedDerivativeResultant_ordinaryRootPolynomial_ne_zero
    (rootFirst Q) (rootFirst_ne_zero_iff Q |>.mpr hQ)
  rcases hchar with hzero | hpositive
  · exact Or.inl hzero
  · exact Or.inr ((rootDegree_rootFirst Q).trans_le hdegree |>.trans_lt hpositive)

theorem singularEquation_ne_zero (Q : DifferentialPolynomial F 1) (hQ : Q ≠ 0)
    {M : ℕ} (hdegree : jetDegree Q 1 ≤ M)
    (hchar : ringChar F = 0 ∨ M < ringChar F) :
    singularEquation Q ≠ 0 := by
  have hproduct : singularPolynomial Q ≠ 0 :=
    mul_ne_zero (contentCoefficient_ne_zero Q)
      (positiveResultant_ne_zero Q hQ hdegree hchar)
  intro hzero
  apply hproduct
  have heq : singularAsPolynomial Q = 0 := by
    rw [← orderZeroAsPolynomial_orderZeroOfPolynomial (singularAsPolynomial Q)]
    rw [show orderZeroOfPolynomial (singularAsPolynomial Q) = singularEquation Q by rfl,
      hzero]
    simp [orderZeroAsPolynomial]
  exact remainingPolynomialEquiv.injective (by simpa [singularAsPolynomial] using heq)

theorem positiveRootProduct_eq_one_of_rootDegree_eq_zero
    (Q : DifferentialPolynomial F 1)
    (hdegree : degreeOf none (positiveRootProduct Q) = 0) :
    positiveRootProduct Q = 1 := by
  classical
  have hempty : ordinaryRootFactorClasses (rootFirst Q) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a ha
    have hpos := (ordinaryRootFactorClasses_spec (rootFirst Q) ha).2
    have hle : degreeOf none (ordinaryFactorRepresentative a) ≤
        degreeOf none (positiveRootProduct Q) := by
      rw [positiveRootProduct, ordinaryRootProduct, degreeOf_prod_eq]
      · exact Finset.single_le_sum
          (fun b _ ↦ Nat.zero_le (degreeOf none (ordinaryFactorRepresentative b))) ha
      · intro b hb
        exact (ordinaryRootFactorClasses_spec (rootFirst Q) hb).1.ne_zero
    omega
  rw [positiveRootProduct, ordinaryRootProduct, hempty]
  simp

theorem singularEquation_routes_nonregular
    (Q : DifferentialPolynomial F 1) (hQ : Q ≠ 0) (P : F[X])
    (hroot : differentialSpecialization Q P = 0)
    (hnonregular : differentialSpecialization (positiveEquation Q) P ≠ 0 ∨
      differentialSpecialization
        (separant (positiveEquation Q) (1 : Fin 2)) P = 0) :
    differentialSpecialization (singularEquation Q) P = 0 := by
  have hsplit := root_content_or_positive Q hQ P hroot
  rw [← orderZeroAsPolynomial_eval]
  rw [show singularEquation Q = orderZeroOfPolynomial (singularAsPolynomial Q) by rfl,
    orderZeroAsPolynomial_orderZeroOfPolynomial, singularAsPolynomial_eval,
    singularPolynomial, map_mul]
  rcases hsplit with hcontent | hpositive
  · rw [remainingSpecializationHom_contentCoefficient, hcontent, zero_mul]
  · rcases hnonregular with hnot | hseparant
    · exact (hnot hpositive).elim
    · let r := degreeOf none (positiveRootProduct Q)
      have hr : 0 < r := by
        by_contra! hrzero
        have hrzero' : r = 0 := Nat.eq_zero_of_le_zero hrzero
        have hone := positiveRootProduct_eq_one_of_rootDegree_eq_zero Q hrzero'
        have hrootOne : differentialSpecialization (positiveEquation Q) P = 1 := by
          rw [← rootFirstSpecializationHom_rootFirst, positiveEquation,
            rootFirst_fromRootFirst, hone, map_one]
        rw [hrootOne] at hpositive
        exact one_ne_zero hpositive
      have hresultant :=
        Polynomial.paddedDerivativeResultant_map_eq_zero_of_common_root
          (ordinaryRootPolynomial (rootFirst Q)) hr
          (by rw [natDegree_ordinaryRootPolynomial]; rfl)
          (remainingSpecializationHom P) (P.hasseDeriv 1)
          (by simpa only [positiveEquation_specialization_eq] using hpositive)
          (by simpa only [positiveSeparant_specialization_eq] using hseparant)
      rw [hresultant, mul_zero]

/-- The content-resultant construction supplies the tail data consumed by factorwise list
counting. -/
def fixedWordSingularTailOfBounds
    (Q : DifferentialPolynomial F 1) (hQ : Q ≠ 0) (B M : ℕ)
    (hjet : jetTotalDegree Q ≤ B) (hderiv : jetDegree Q 1 ≤ M)
    (hMB : M ≤ B) (hchar : ringChar F = 0 ∨ M < ringChar F) :
    FixedWordSingularTail Q B M where
  equation := singularEquation Q
  nonzero := singularEquation_ne_zero Q hQ hderiv hchar
  degree_le := singularEquation_degree_le Q hQ hjet hderiv hMB
  routes_nonregular := singularEquation_routes_nonregular Q hQ

open Classical in
/-- The fully constructed factorwise fixed-word list bound. -/
theorem finite_squarefree_agreement_solutions_card_le
    {n D A B M : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F)
    (Q : DifferentialPolynomial F 1) (hQ : Q ≠ 0)
    (hD : 1 ≤ D) (hkA : D + 1 ≤ A) (hAn : A ≤ n)
    (hB : 0 < B) (hM : 0 < M) (hMB : M ≤ B)
    (hjet : jetTotalDegree Q ≤ B) (hderiv : jetDegree Q 1 ≤ M)
    (hchar : ringChar F = 0 ∨ max D M < ringChar F)
    (S : Finset F[X])
    (hsol : ∀ P ∈ S, differentialSpecialization Q P = 0)
    (haccept : ∀ P ∈ S, IsAgreementSolution domain received (D + 1) A P) :
    (S.card : ℝ) ≤
      (firstOrderCurveFiberStageOne (D + 1) B M (2 * D - 1) : ℝ) *
          ((n - D : ℕ) : ℝ) / (A - D : ℕ) + ordinaryDegreeEnvelope B M := by
  have htailChar : ringChar F = 0 ∨ M < ringChar F := by
    rcases hchar with hzero | hpositive
    · exact Or.inl hzero
    · exact Or.inr ((Nat.le_max_right D M).trans_lt hpositive)
  exact finite_factorwise_agreement_solutions_card_le domain received Q hQ
    hD hkA hAn hB hM hMB hjet hderiv hchar
    (fixedWordSingularTailOfBounds Q hQ B M hjet hderiv hMB htailChar)
    S hsol haccept

end

end ReedSolomon.FirstOrder.Squarefree
