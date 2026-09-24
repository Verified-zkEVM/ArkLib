/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Differential.JetDegree
public import ArkLib.ToMathlib.MvPolynomial.OptionWeightedDegree
public import ArkLib.ToMathlib.MvPolynomial.PolynomialCoefficients

/-!
# Flattening first-order challenge polynomials

A differential polynomial over `F[X]` becomes a polynomial over `F` by moving the coefficient
variable into the `none` coordinate. The first-order API records nonvanishing and degree bounds
for this flattened challenge, separating challenge degree from degree in the jet coordinates.

## Main statements

* `flattenFirstOrderChallenge`: the flattened first-order challenge polynomial.
* `flattenFirstOrderChallenge_ne_zero_iff`: flattening preserves nonvanishing.
* `flattenFirstOrderChallenge_challengeDegree_le`: coefficient degree bounds challenge degree.
* `flattenFirstOrderChallenge_yOneDegree_le` and
  `flattenFirstOrderChallenge_jetWeight_le`: flattening does not increase derivative-variable or
  total jet degree.

## References

* [DKT26]
-/

@[expose] public section

namespace ReedSolomon.FirstOrder.Squarefree

open MvPolynomial Polynomial PolynomialDifferential

noncomputable section

variable {F : Type*} [Field F]

/-- Lift a source-variable weight across challenge flattening, assigning weight zero to the
new challenge coordinate. -/
def liftedSourceWeight {σ : Type*} (w : σ → ℕ) : Option σ → ℕ
  | none => 0
  | some i => w i

/-- A first-order differential polynomial with coefficient variable `X` flattened over `F`.

The coefficient variable becomes coordinate `none`, while each jet coordinate `i` becomes
`some i`. -/
def flattenFirstOrderChallenge (Q : DifferentialPolynomial F[X] 1) :
    MvPolynomial (Option (JetVariable 1)) F :=
  (optionEquivRight F (JetVariable 1)).symm Q

/-- Flattening preserves whether a first-order challenge polynomial is zero. -/
@[simp]
theorem flattenFirstOrderChallenge_ne_zero_iff (Q : DifferentialPolynomial F[X] 1) :
    flattenFirstOrderChallenge Q ≠ 0 ↔ Q ≠ 0 := by
  change (optionEquivRight F (JetVariable 1)).symm Q ≠ 0 ↔ Q ≠ 0
  simpa only [map_zero] using
    ((optionEquivRight F (JetVariable 1)).symm.injective.ne_iff :
      (optionEquivRight F (JetVariable 1)).symm Q ≠
          (optionEquivRight F (JetVariable 1)).symm 0 ↔ Q ≠ 0)

/-- The degree of the coefficient variable bounds the degree of coordinate `none`. -/
theorem flattenFirstOrderChallenge_challengeDegree_le (Q : DifferentialPolynomial F[X] 1)
    {H : ℕ} (hQ : CoeffNatDegreeLE Q H) :
    degreeOf none (flattenFirstOrderChallenge Q) ≤ H := by
  rw [← weightedTotalDegree_piSingle]
  have hw : (fun v : Option (JetVariable 1) ↦ v.elim 1 fun _ ↦ 0) = Pi.single none 1 := by
    funext v
    cases v <;> simp
  change ((optionEquivRight F (JetVariable 1)).symm Q).weightedTotalDegree
    (Pi.single none 1) ≤ H
  rw [← hw]
  exact weightedTotalDegree_optionEquivRight_symm_coefficientDegree_le hQ

/-- Flattening does not increase the degree in the derivative variable `Y₁`. -/
theorem flattenFirstOrderChallenge_yOneDegree_le (Q : DifferentialPolynomial F[X] 1) :
    degreeOf (some (some (1 : Fin 2))) (flattenFirstOrderChallenge Q) ≤
      degreeOf (some (1 : Fin 2)) Q := by
  have hw : (fun v : Option (JetVariable 1) ↦
      v.elim 0 (Pi.single (some (1 : Fin 2)) 1)) =
        Pi.single (some (some (1 : Fin 2))) 1 := by
    funext v
    cases v with
    | none => simp
    | some v => cases v with
      | none => simp
      | some j => fin_cases j <;> simp
  have h := weightedTotalDegree_optionEquivRight (Pi.single (some (1 : Fin 2)) 1)
    ((optionEquivRight F (JetVariable 1)).symm Q)
  rw [AlgEquiv.apply_symm_apply] at h
  rw [hw] at h
  simpa only [weightedTotalDegree_piSingle, flattenFirstOrderChallenge] using h.symm.le

/-- Flattening does not increase the total degree in the jet coordinates. -/
theorem flattenFirstOrderChallenge_jetWeight_le (Q : DifferentialPolynomial F[X] 1) :
    (flattenFirstOrderChallenge Q).weightedTotalDegree
        (liftedSourceWeight (fun v : JetVariable 1 ↦ v.elim 0 fun _ ↦ 1)) ≤
      jetTotalDegree Q := by
  have hlw : (fun v : Option (JetVariable 1) ↦
      v.elim 0 jetDegreeWeight) =
        liftedSourceWeight (fun v : JetVariable 1 ↦ v.elim 0 fun _ ↦ 1) := by
    funext v
    cases v with
    | none => simp [liftedSourceWeight]
    | some v => cases v <;> simp [liftedSourceWeight, jetDegreeWeight]
  have h := weightedTotalDegree_optionEquivRight
    (jetDegreeWeight (d := 1))
    ((optionEquivRight F (JetVariable 1)).symm Q)
  rw [AlgEquiv.apply_symm_apply] at h
  rw [hlw] at h
  exact h.symm.le

end

end ReedSolomon.FirstOrder.Squarefree
