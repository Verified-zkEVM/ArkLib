/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Regular.JetPrefix
import Mathlib.Algebra.Field.ZMod
/-!
# Canary for lifting at a non-top active jet

The ambient equation below has room for `Y₂` but depends only on `Y₁`.  Its regular lift must
therefore perturb degree `k + 1`, not degree `k + 2`.  This example exercises the prefix restriction
used to apply the literal-top-coordinate lifting theorem at an arbitrary highest active jet.
-/

namespace ReedSolomon.HiddenDerivative

open Polynomial

open PolynomialDifferential

noncomputable section

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The ambient-depth-two equation `Y₁ = 0`. -/
private def middleJetEquation : DifferentialPolynomial (ZMod 5) 2 :=
  MvPolynomial.X (some (1 : Fin 3))

/-- Its highest active jet is the middle coordinate, not the ambient top coordinate. -/
private theorem middleJetEquation_highest :
    IsHighestActiveJet middleJetEquation (1 : Fin 3) := by
  constructor
  · simp [DependsOnJet, jetDegree, middleJetEquation]
  · intro j hj
    have hne : (some j : JetVariable 2) ≠ some (1 : Fin 3) := by
      intro heq
      have hjEq : j = (1 : Fin 3) := Option.some.inj heq
      subst j
      simp at hj
    rw [DependsOnJet, jetDegree, middleJetEquation,
      MvPolynomial.degreeOf_X_of_ne hne]
    omega

/-- The zero polynomial gives a regular initial jet for `Y₁`. -/
private theorem middleJetEquation_regular :
    IsRegularJet middleJetEquation (1 : Fin 3) 0
      (polynomialJet (d := 2) 0 (0 : (ZMod 5)[X])) := by
  simp [IsRegularJet, middleJetEquation, separant, jetEvaluation, polynomialJet]

/-- The initial residual vanishes, hence has every positive order. -/
private theorem middleJetEquation_residual :
    (X - C 0) ^ 1 ∣
      differentialSpecialization middleJetEquation (0 : (ZMod 5)[X]) := by
  simp [middleJetEquation, differentialSpecialization]

/- The generic adapter applies with the degree shift dictated by `Y₁`. -/
example :
    ∃! gamma : ZMod 5,
      (X - C 0) ^ (1 + 1) ∣
        differentialSpecialization middleJetEquation
          (regularLiftCandidate 0 gamma 1 (1 : Fin 3).val 0) := by
  exact existsUnique_regularLiftCoefficient_centered_of_isHighestActiveJet
    (F := ZMod 5) (d := 2) (k := 1) (D := 3) (s := (1 : Fin 3))
      (Q := middleJetEquation) (center := 0) (P := 0) (hk := by decide)
      (hs := middleJetEquation_highest) (hregular := middleJetEquation_regular)
      (hdegree := by decide) (hD := by simp [ZMod.ringChar_zmod_n])
      (hresidual := middleJetEquation_residual)

end

end ReedSolomon.HiddenDerivative
