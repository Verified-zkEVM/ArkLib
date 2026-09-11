/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Squarefree.PositiveProduct
public import ArkLib.ToMathlib.MvPolynomial.OptionWeightedDegreeGeneral

/-!
# Retained-challenge equations for squarefree first-order transfer

The challenge is kept as a genuine coordinate while the first-derivative variable is factored.
This file transports the distinct positive-root product back to a differential polynomial over
the polynomial coefficient ring and records its exact source-degree views.  These are the
algebraic inputs needed by the polynomial-curve regular and singular transfers.
-/

@[expose] public section

namespace ReedSolomon.FirstOrder.Squarefree

open MvPolynomial Polynomial PolynomialDifferential
open ReedSolomon.HiddenDerivative

noncomputable section

variable {F : Type*} [Field F]

/-- Undo challenge flattening and the root-first swap. -/
def fromFlattenedRootFirst
    (R : MvPolynomial (Option (JetVariable 1)) F) :
    DifferentialPolynomial F[X] 1 :=
  flattenChallenge.symm (renameEquiv F flattenedRootFirstEquiv.symm R)

/-- The challenge-retaining distinct positive-`Y₁` factor product. -/
def positiveCurveEquation (Q : DifferentialPolynomial F[X] 1) :
    DifferentialPolynomial F[X] 1 :=
  fromFlattenedRootFirst (flattenedPositiveRootProduct Q)

@[simp]
theorem flattenChallenge_fromFlattenedRootFirst
    (R : MvPolynomial (Option (JetVariable 1)) F) :
    flattenChallenge (fromFlattenedRootFirst R) =
      renameEquiv F flattenedRootFirstEquiv.symm R := by
  simp [fromFlattenedRootFirst]

theorem positiveCurveEquation_ne_zero (Q : DifferentialPolynomial F[X] 1) :
    positiveCurveEquation Q ≠ 0 := by
  intro hzero
  have hmapped := congrArg flattenChallenge hzero
  rw [positiveCurveEquation, flattenChallenge_fromFlattenedRootFirst, map_zero] at hmapped
  exact (renameEquiv F flattenedRootFirstEquiv.symm).injective.ne_iff.mpr
    (flattenedPositiveRootProduct_ne_zero Q) hmapped

/-- Exact arbitrary-weight form of challenge flattening. -/
theorem flattenChallenge_weightedTotalDegree_eq
    (Q : MvPolynomial (JetVariable 1) F[X]) (w : JetVariable 1 → ℕ) :
    (flattenChallenge Q).weightedTotalDegree (fun v ↦ v.elim 0 w) =
      Q.weightedTotalDegree w := by
  have h := weightedTotalDegree_optionEquivRight_general w (flattenChallenge Q)
  simpa only [flattenChallenge, AlgEquiv.apply_symm_apply] using h.symm

/-- Flattening preserves every original variable degree exactly. -/
theorem flattenChallenge_degreeOf_eq
    (Q : MvPolynomial (JetVariable 1) F[X]) (i : JetVariable 1) :
    (flattenChallenge Q).degreeOf (some i) = Q.degreeOf i := by
  classical
  rw [← weightedTotalDegree_piSingle, ← weightedTotalDegree_piSingle]
  have h := flattenChallenge_weightedTotalDegree_eq Q (Pi.single i 1)
  rw [← h]
  congr 1
  funext v
  rcases v with _ | j
  · simp
  · simp [Pi.single_apply]

/-- Reindex root-first coordinates as two jet variables followed by the independent and
challenge coordinates. -/
def curveJetReindex : Option (JetVariable 1) ≃ Option (Option (Fin 2)) where
  toFun
    | none => some (some 1)
    | some none => none
    | some (some i) => Fin.cases (some (some 0)) (fun _ ↦ some none) i
  invFun
    | none => some none
    | some none => some (some 1)
    | some (some i) => Fin.cases (some (some 0)) (fun _ ↦ none) i
  left_inv x := by
    rcases x with _ | (_ | i)
    · rfl
    · rfl
    · fin_cases i <;> rfl
  right_inv x := by
    rcases x with _ | (_ | i)
    · rfl
    · rfl
    · fin_cases i <;> rfl

/-- View the two jet coordinates as polynomial variables over the two weight-zero coordinates
`X` and `Z`. -/
def curveJetView :
    MvPolynomial (Option (JetVariable 1)) F ≃+*
      MvPolynomial (Fin 2) F[X][X] :=
  (renameEquiv F curveJetReindex).toRingEquiv |>.trans
    ((optionEquivRight F (Option (Fin 2))).toRingEquiv |>.trans
      (optionEquivRight F[X] (Fin 2)).toRingEquiv)

/-- Root-first jet weight: count `Y₀,Y₁`, but not `X,Z`. -/
def flattenedRootJetWeight : Option (JetVariable 1) → ℕ
  | none => 1
  | some none => 0
  | some (some i) => Fin.cases 1 (fun _ ↦ 0) i

/-- The two-variable view realizes root-first jet weight as ordinary total degree. -/
theorem curveJetView_totalDegree
    (R : MvPolynomial (Option (JetVariable 1)) F) :
    (curveJetView R).totalDegree =
      R.weightedTotalDegree flattenedRootJetWeight := by
  change
    (optionEquivRight F[X] (Fin 2)
      (optionEquivRight F (Option (Fin 2))
        (rename curveJetReindex R))).totalDegree = _
  rw [totalDegree_optionEquivRight,
    weightedTotalDegree_optionEquivRight_general,
    weightedTotalDegree_rename_of_injective curveJetReindex.injective]
  congr 1
  funext v
  rcases v with _ | (_ | i)
  · rfl
  · rfl
  · fin_cases i <;> rfl

/-- The retained positive product's exact jet weight is its two-variable view degree. -/
theorem positiveCurveEquation_jetWeight
    (Q : DifferentialPolynomial F[X] 1) :
    SymbolicSeparantChain.jetWeight (positiveCurveEquation Q) =
      (curveJetView (flattenedPositiveRootProduct Q)).totalDegree := by
  rw [curveJetView_totalDegree]
  unfold SymbolicSeparantChain.jetWeight
  rw [← flattenChallenge_weightedTotalDegree_eq]
  rw [positiveCurveEquation, flattenChallenge_fromFlattenedRootFirst]
  change
    weightedTotalDegree _
      (rename flattenedRootFirstEquiv.symm (flattenedPositiveRootProduct Q)) = _
  rw [weightedTotalDegree_rename_of_injective flattenedRootFirstEquiv.symm.injective]
  congr 1
  funext v
  rcases v with _ | (_ | i)
  · rfl
  · rfl
  · fin_cases i <;> rfl

/-- The distinct positive product retains the source total jet-degree budget. -/
theorem positiveCurveEquation_jetWeight_le
    (Q : DifferentialPolynomial F[X] 1) (hQ : Q ≠ 0) :
    SymbolicSeparantChain.jetWeight (positiveCurveEquation Q) ≤
      SymbolicSeparantChain.jetWeight Q := by
  have hroot : flattenedPositiveRootProduct Q ∣ flattenedRootFirst Q := by
    apply dvd_trans
      (show flattenedPositiveRootProduct Q ∣
          flattenedContent Q * flattenedPositiveRootProduct Q from
        ⟨flattenedContent Q, by ac_rfl⟩)
    rw [flattenedContent, flattenedPositiveRootProduct, ordinary_split_product]
    exact ordinarySquarefreeProduct_dvd (flattenedRootFirst Q)
      (flattenedRootFirst_ne_zero_iff Q |>.mpr hQ)
  have hviewDvd : curveJetView (flattenedPositiveRootProduct Q) ∣
      curveJetView (flattenedRootFirst Q) := map_dvd curveJetView hroot
  rw [positiveCurveEquation_jetWeight]
  apply (totalDegree_le_of_dvd_of_isDomain hviewDvd
    ((curveJetView).injective.ne_iff.mpr
      (flattenedRootFirst_ne_zero_iff Q |>.mpr hQ))).trans
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
    rcases v with _ | (_ | i)
    · rfl
    · rfl
    · fin_cases i <;> rfl
  rw [hrename]
  exact flattenFirstOrderChallenge_jetWeight_le Q

/-- The retained product keeps the actual `Y₁` degree of the root-first product. -/
theorem positiveCurveEquation_yOneDegree
    (Q : DifferentialPolynomial F[X] 1) :
    (positiveCurveEquation Q).degreeOf (some 1) =
      degreeOf none (flattenedPositiveRootProduct Q) := by
  rw [← flattenChallenge_degreeOf_eq]
  rw [positiveCurveEquation, flattenChallenge_fromFlattenedRootFirst]
  have hrename := degreeOf_rename_of_injective
    flattenedRootFirstEquiv.symm.injective none
    (p := flattenedPositiveRootProduct Q)
  have he : flattenedRootFirstEquiv.symm none = some (some (1 : Fin 2)) := by
    rfl
  change degreeOf (some (some (1 : Fin 2)))
    (rename flattenedRootFirstEquiv.symm (flattenedPositiveRootProduct Q)) = _
  simpa only [he] using hrename

/-- The retained product's `Y₁` degree is bounded by the source cap. -/
theorem positiveCurveEquation_yOneDegree_le
    (Q : DifferentialPolynomial F[X] 1) (hQ : Q ≠ 0) :
    (positiveCurveEquation Q).degreeOf (some 1) ≤ Q.degreeOf (some 1) := by
  rw [positiveCurveEquation_yOneDegree]
  have hroot : degreeOf none (flattenedPositiveRootProduct Q) ≤
      degreeOf none (flattenedRootFirst Q) := by
    calc
      degreeOf none (flattenedPositiveRootProduct Q) =
          ∑ a ∈ ordinaryRootFactorClasses (flattenedRootFirst Q),
            degreeOf none (ordinaryFactorRepresentative a) := by
        rw [flattenedPositiveRootProduct, ordinaryRootProduct, degreeOf_prod_eq]
        intro a ha
        exact (ordinaryRootFactorClasses_spec (flattenedRootFirst Q) ha).1.ne_zero
      _ ≤ degreeOf none (flattenedRootFirst Q) :=
        ordinary_root_degree_sum_le (flattenedRootFirst Q)
          (flattenedRootFirst_ne_zero_iff Q |>.mpr hQ)
  exact hroot.trans (flattenedRootFirst_rootDegree_le Q)

/-- The retained product's challenge height is its literal `Z` degree in root-first
coordinates. -/
theorem positiveCurveEquation_challengeHeightLE
    (Q : DifferentialPolynomial F[X] 1) :
    ChallengeHeightLE (positiveCurveEquation Q)
      (degreeOf (some (some (1 : Fin 2))) (flattenedPositiveRootProduct Q)) := by
  classical
  let R := flattenChallenge (positiveCurveEquation Q)
  have hR : R = rename flattenedRootFirstEquiv.symm
      (flattenedPositiveRootProduct Q) := by
    dsimp [R]
    rw [positiveCurveEquation, flattenChallenge_fromFlattenedRootFirst]
    rfl
  have hdegree : degreeOf none R =
      degreeOf (some (some (1 : Fin 2))) (flattenedPositiveRootProduct Q) := by
    rw [hR]
    have hrename := degreeOf_rename_of_injective
      flattenedRootFirstEquiv.symm.injective (some (some (1 : Fin 2)))
      (p := flattenedPositiveRootProduct Q)
    have he : flattenedRootFirstEquiv.symm (some (some (1 : Fin 2))) = none := by
      rfl
    simpa only [he] using hrename
  intro d
  have hQeq : positiveCurveEquation Q = optionEquivRight F (JetVariable 1) R := by
    dsimp [R]
    exact ((optionEquivRight F (JetVariable 1)).apply_symm_apply
      (positiveCurveEquation Q)).symm
  have hcoeff : coeff d (positiveCurveEquation Q) =
      coeff d (optionEquivRight F (JetVariable 1) R) :=
    congrArg (MvPolynomial.coeff d) hQeq
  rw [hcoeff]
  by_cases hc : coeff d (optionEquivRight F (JetVariable 1) R) = 0
  · rw [hc]
    exact Nat.zero_le _
  · have hmem := Polynomial.natDegree_mem_support_of_nonzero hc
    have hsource : d.optionElim
        (coeff d (optionEquivRight F (JetVariable 1) R)).natDegree ∈ R.support := by
      apply MvPolynomial.mem_support_iff.mpr
      rw [← optionEquivRight_coeff_coeff]
      exact Polynomial.mem_support_iff.mp hmem
    simpa using (MvPolynomial.monomial_le_degreeOf none hsource).trans_eq hdegree

end

end ReedSolomon.FirstOrder.Squarefree
