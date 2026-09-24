/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.MvPolynomial.WeightedDegree.Products
public import ArkLib.Data.Polynomial.Differential.JetDegree
public import ArkLib.ToMathlib.MvPolynomial.OptionWeightedDegree
public import ArkLib.ToMathlib.MvPolynomial.PolynomialCoefficients
public import ArkLib.ToMathlib.MvPolynomial.RadicalSplit

/-!
# Retained-challenge equations for first-order curves

This file forms a first-order equation from the distinct factors that depend on `Y₁`, while
keeping the coefficient challenge as a polynomial coordinate. Its two-variable view records the
exact jet degree and the separate bounds on `Y₁` and the challenge.

## Main statements

* `positiveCurveEquation`: the first-order equation formed from the positive-`Y₁` radical factor.
* `positiveCurveEquation_jetTotalDegree_le` and `positiveCurveEquation_yOneDegree_le`: the jet
  and `Y₁` degree bounds for the retained equation.
* `positiveCurveEquation_coeffNatDegreeLE`: the coefficient challenge height bound.
* `curveJetView_totalDegree`: the two-variable view computes the jet degree.
* `fromFlattenedRootFirst_rootFirstChallenge`: the root-first coordinate map is invertible.

## References

* [DKT26]
-/

@[expose] public section

namespace PolynomialDifferential

open MvPolynomial Polynomial

noncomputable section

variable {F : Type*} [Field F]

/-- Put `Y₁` in the distinguished root coordinate while retaining the challenge coordinate. -/
def challengeRetainingRootFirst (Q : DifferentialPolynomial F[X] 1) :
    MvPolynomial (Option (JetVariable 1)) F :=
  renameEquiv F (Equiv.swap none (some (some 1)))
    ((optionEquivRight F (JetVariable 1)).symm Q)

/-- Recover the differential polynomial from coordinates with `Y₁` in the root position. -/
def fromFlattenedRootFirst
    (R : MvPolynomial (Option (JetVariable 1)) F) : DifferentialPolynomial F[X] 1 :=
  optionEquivRight F (JetVariable 1)
    (renameEquiv F (Equiv.swap none (some (some 1))) R)

/-- Flattening the recovered equation returns its root-first coordinates. -/
theorem flattenedCoordinates_fromFlattenedRootFirst
    (R : MvPolynomial (Option (JetVariable 1)) F) :
    (optionEquivRight F (JetVariable 1)).symm (fromFlattenedRootFirst R) =
      renameEquiv F (Equiv.swap none (some (some 1))) R := by
  rw [fromFlattenedRootFirst]
  exact AlgEquiv.symm_apply_apply _ _

private theorem fromFlattenedRootFirst_ne_zero_iff
    (R : MvPolynomial (Option (JetVariable 1)) F) :
    fromFlattenedRootFirst R ≠ 0 ↔ R ≠ 0 := by
  constructor
  · intro h hR
    apply h
    simp [fromFlattenedRootFirst, hR]
  · intro h hfrom
    apply h
    have hrename :
        renameEquiv F (Equiv.swap none (some (some 1))) R = 0 := by
      apply (optionEquivRight F (JetVariable 1)).injective
      simpa [fromFlattenedRootFirst] using hfrom
    exact (renameEquiv F (Equiv.swap none (some (some 1)))).injective hrename

/-- The product of the distinct positive-`Y₁` factors, returned to challenge-retaining
coordinates. -/
def positiveCurveEquation (Q : DifferentialPolynomial F[X] 1) :
    DifferentialPolynomial F[X] 1 :=
  fromFlattenedRootFirst (radicalPrimPart none (challengeRetainingRootFirst Q))

/-- The retained positive-factor equation is nonzero, including when the input is zero. -/
theorem positiveCurveEquation_ne_zero (Q : DifferentialPolynomial F[X] 1) :
    positiveCurveEquation Q ≠ 0 := by
  unfold positiveCurveEquation
  rw [fromFlattenedRootFirst_ne_zero_iff]
  exact radicalPrimPart_ne_zero none (challengeRetainingRootFirst Q)

/-- Reindex root-first coordinates as the two jet variables followed by the independent and
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

/-- View the two jet coordinates as polynomial variables over the independent and challenge
coordinates. -/
def curveJetView :
    MvPolynomial (Option (JetVariable 1)) F ≃+*
      MvPolynomial (Fin 2) F[X][X] :=
  (renameEquiv F curveJetReindex).toRingEquiv |>.trans
    ((optionEquivRight F (Option (Fin 2))).toRingEquiv |>.trans
      (optionEquivRight F[X] (Fin 2)).toRingEquiv)

/-- The two-variable view computes the jet degree after returning to differential coordinates. -/
theorem curveJetView_totalDegree
    (R : MvPolynomial (Option (JetVariable 1)) F) :
    (curveJetView R).totalDegree = jetTotalDegree (fromFlattenedRootFirst R) := by
  change
    (optionEquivRight F[X] (Fin 2)
      (optionEquivRight F (Option (Fin 2)) (rename curveJetReindex R))).totalDegree =
        (optionEquivRight F (JetVariable 1)
          (rename (Equiv.swap none (some (some 1))) R)).weightedTotalDegree jetDegreeWeight
  rw [totalDegree_optionEquivRight, weightedTotalDegree_optionEquivRight,
    weightedTotalDegree_rename_of_injective curveJetReindex.injective,
    weightedTotalDegree_optionEquivRight,
    weightedTotalDegree_rename_of_injective
      (Equiv.swap none (some (some 1))).injective]
  congr 1
  funext v
  rcases v with _ | (_ | i)
  · rfl
  · rfl
  · fin_cases i <;> rfl

/-- The retained equation's jet degree is the total degree of its two-variable view. -/
theorem positiveCurveEquation_jetTotalDegree_eq_curveJetView
    (Q : DifferentialPolynomial F[X] 1) :
    jetTotalDegree (positiveCurveEquation Q) =
      (curveJetView (radicalPrimPart none (challengeRetainingRootFirst Q))).totalDegree := by
  rw [curveJetView_totalDegree]
  rfl

/-- Recovering the root-first form of an equation returns the original equation. -/
theorem fromFlattenedRootFirst_rootFirstChallenge
    (Q : DifferentialPolynomial F[X] 1) :
    fromFlattenedRootFirst (challengeRetainingRootFirst Q) = Q := by
  rw [challengeRetainingRootFirst, fromFlattenedRootFirst]
  have hswap : renameEquiv F (Equiv.swap none (some (some 1)))
      (renameEquiv F (Equiv.swap none (some (some 1)))
        ((optionEquivRight F (JetVariable 1)).symm Q)) =
      (optionEquivRight F (JetVariable 1)).symm Q := by
    let e : MvPolynomial (Option (JetVariable 1)) F ≃ₐ[F]
        MvPolynomial (Option (JetVariable 1)) F :=
      renameEquiv F (Equiv.swap none (some (some (1 : Fin 2))))
    have he : e = e.symm := by
      simp [e, Equiv.symm_swap]
    calc
      e (e ((optionEquivRight F (JetVariable 1)).symm Q)) =
          e.symm (e ((optionEquivRight F (JetVariable 1)).symm Q)) :=
        congrArg (fun f : _ ≃ₐ[F] _ ↦ f _) he
      _ = _ := AlgEquiv.symm_apply_apply _ _
  rw [hswap, AlgEquiv.apply_symm_apply]

/-- Removing repeated positive-`Y₁` factors does not increase total jet degree. -/
theorem positiveCurveEquation_jetTotalDegree_le (Q : DifferentialPolynomial F[X] 1) :
    jetTotalDegree (positiveCurveEquation Q) ≤ jetTotalDegree Q := by
  have hadd : ∀ p q : MvPolynomial (Option (JetVariable 1)) F,
      p ≠ 0 → q ≠ 0 →
        jetTotalDegree (fromFlattenedRootFirst (p * q)) =
          jetTotalDegree (fromFlattenedRootFirst p) +
            jetTotalDegree (fromFlattenedRootFirst q) := by
    intro p q hp hq
    have hp' : fromFlattenedRootFirst p ≠ 0 :=
      fromFlattenedRootFirst_ne_zero_iff p |>.2 hp
    have hq' : fromFlattenedRootFirst q ≠ 0 :=
      fromFlattenedRootFirst_ne_zero_iff q |>.2 hq
    rw [show fromFlattenedRootFirst (p * q) =
      fromFlattenedRootFirst p * fromFlattenedRootFirst q by
        simp [fromFlattenedRootFirst]]
    exact weightedTotalDegree_mul jetDegreeWeight _ _ hp' hq'
  have hdegree := MvPolynomial.map_radicalPrimPart_le
    (d := fun R ↦ jetTotalDegree (fromFlattenedRootFirst R)) hadd none
      (challengeRetainingRootFirst Q)
  change jetTotalDegree (fromFlattenedRootFirst
    (radicalPrimPart none (challengeRetainingRootFirst Q))) ≤ _ at hdegree
  simpa only [positiveCurveEquation, fromFlattenedRootFirst_rootFirstChallenge] using hdegree

/-- The `Y₁` degree of the retained equation is the degree of the positive-factor product in its
root coordinate. -/
theorem positiveCurveEquation_yOneDegree
    (Q : DifferentialPolynomial F[X] 1) :
    (positiveCurveEquation Q).degreeOf (some 1) =
      degreeOf none (radicalPrimPart none (challengeRetainingRootFirst Q)) := by
  rw [positiveCurveEquation, fromFlattenedRootFirst]
  calc
    degreeOf (some 1)
        (optionEquivRight F (JetVariable 1)
          (rename (Equiv.swap none (some (some 1)))
            (radicalPrimPart none (challengeRetainingRootFirst Q)))) =
        degreeOf (some (some 1))
          (rename (Equiv.swap none (some (some 1)))
            (radicalPrimPart none (challengeRetainingRootFirst Q))) :=
      degreeOf_optionEquivRight _ _
    _ = degreeOf none (radicalPrimPart none (challengeRetainingRootFirst Q)) := by
      have hrename := degreeOf_rename_of_injective
        (Equiv.swap none (some (some 1))).injective none
        (p := radicalPrimPart none (challengeRetainingRootFirst Q))
      change degreeOf (some (some 1))
        (rename (Equiv.swap none (some (some 1)))
          (radicalPrimPart none (challengeRetainingRootFirst Q))) = _ at hrename
      exact hrename

private theorem degreeOf_challengeRetainingRootFirst
    (Q : DifferentialPolynomial F[X] 1) :
    degreeOf none (challengeRetainingRootFirst Q) = degreeOf (some 1) Q := by
  calc
    degreeOf none
        (rename (Equiv.swap none (some (some 1)))
          ((optionEquivRight F (JetVariable 1)).symm Q)) =
        degreeOf (some (some 1)) ((optionEquivRight F (JetVariable 1)).symm Q) := by
      have hrename := degreeOf_rename_of_injective
        (Equiv.swap none (some (some 1))).injective (some (some 1))
        (p := (optionEquivRight F (JetVariable 1)).symm Q)
      change degreeOf none
        (rename (Equiv.swap none (some (some 1)))
          ((optionEquivRight F (JetVariable 1)).symm Q)) = _ at hrename
      exact hrename
    _ = degreeOf (some 1) Q := by
      simpa only [AlgEquiv.apply_symm_apply] using
        (degreeOf_optionEquivRight ((optionEquivRight F (JetVariable 1)).symm Q) (some 1)).symm

/-- The retained equation's `Y₁` degree stays within the input `Y₁` degree. -/
theorem positiveCurveEquation_yOneDegree_le (Q : DifferentialPolynomial F[X] 1) :
    (positiveCurveEquation Q).degreeOf (some 1) ≤ Q.degreeOf (some 1) := by
  rw [positiveCurveEquation_yOneDegree]
  exact (degreeOf_radicalPrimPart_le none none
      (challengeRetainingRootFirst Q)).trans_eq
    (degreeOf_challengeRetainingRootFirst Q)

/-- The coefficient challenge height is bounded by the degree of the positive-factor product in
the root-first challenge coordinate. -/
theorem positiveCurveEquation_coeffNatDegreeLE (Q : DifferentialPolynomial F[X] 1) :
    CoeffNatDegreeLE (positiveCurveEquation Q)
      (degreeOf (some (some 1))
        (radicalPrimPart none (challengeRetainingRootFirst Q))) := by
  let product := radicalPrimPart none (challengeRetainingRootFirst Q)
  let R := (optionEquivRight F (JetVariable 1)).symm (positiveCurveEquation Q)
  have hopt : optionEquivRight F (JetVariable 1) R = positiveCurveEquation Q := by
    dsimp [R]
    exact AlgEquiv.apply_symm_apply _ _
  have hR : R = rename (Equiv.swap none (some (some 1))) product := by
    dsimp [R, positiveCurveEquation, product]
    exact flattenedCoordinates_fromFlattenedRootFirst product
  have hdegree : degreeOf none R = degreeOf (some (some 1)) product := by
    rw [hR]
    have hrename := degreeOf_rename_of_injective
      (Equiv.swap none (some (some 1))).injective (some (some 1)) (p := product)
    change degreeOf none (rename (Equiv.swap none (some (some 1))) product) = _ at hrename
    exact hrename
  intro m
  by_cases hc : (positiveCurveEquation Q).coeff m = 0
  · simp [hc]
  · have hmem := Polynomial.natDegree_mem_support_of_nonzero hc
    have hsource : m.optionElim
        ((positiveCurveEquation Q).coeff m).natDegree ∈ R.support := by
      apply MvPolynomial.mem_support_iff.mpr
      rw [← optionEquivRight_coeff_coeff]
      rw [hopt]
      exact Polynomial.mem_support_iff.mp hmem
    simpa using (MvPolynomial.monomial_le_degreeOf none hsource).trans_eq hdegree

end

end PolynomialDifferential
