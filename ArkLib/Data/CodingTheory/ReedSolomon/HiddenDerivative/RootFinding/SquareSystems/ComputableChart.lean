/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Lifting.Step
import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Taylor.Chart
import ArkLib.ToCompPoly.Multivariate.PartialDerivative
import ArkLib.ToCompPoly.Multivariate.Substitution
/-!
# Computable initial Taylor-chart equations

These constructors specialize the independent variable of a concrete differential equation while
keeping the initial jet variables symbolic. The denominator is obtained by differentiating the
concrete equation in its highest jet variable before specialization. Their semantic theorems make
the resulting `CMvPolynomial`s usable with the existing rational Taylor chart.
-/

namespace ReedSolomon.HiddenDerivative.SquareSystems

open PolynomialDifferential

variable {F : Type*} [Field F] [DecidableEq F]

/-- Substitute the center for concrete variable zero and retain all jet variables. -/
def computableInitialJetSubstitution (center : F) (r : ℕ) :
    Fin (r + 2) → CPoly.CMvPolynomial (r + 1) F :=
  Fin.cases (CPoly.CMvPolynomial.C center) CPoly.CMvPolynomial.X

/-- Concrete initial hypersurface equation at a fixed center. -/
def computableInitialJetEquation {r : ℕ} (center : F)
    (Q : CPoly.CMvPolynomial (r + 2) F) : CPoly.CMvPolynomial (r + 1) F :=
  CPoly.CMvPolynomial.bind₁ (computableInitialJetSubstitution center r) Q

/-- Concrete initial separant, obtained from the highest-jet partial derivative. -/
def computableInitialJetSeparant {r : ℕ} (center : F)
    (Q : CPoly.CMvPolynomial (r + 2) F) : CPoly.CMvPolynomial (r + 1) F :=
  CPoly.CMvPolynomial.bind₁ (computableInitialJetSubstitution center r)
    (CPoly.CMvPolynomial.partialDerivative (Fin.last (r + 1)) Q)

theorem finToJetVariable_injective (r : ℕ) :
    Function.Injective (finToJetVariable r) := by
  intro i j hij
  revert hij
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases (fun _ => rfl) (fun j hij => ?_) j
    simp [finToJetVariable] at hij
  · refine Fin.cases (fun hij => ?_) (fun j hij => ?_) j
    · simp [finToJetVariable] at hij
    · exact congrArg Fin.succ (Option.some.inj hij)

@[simp]
theorem finToJetVariable_last (r : ℕ) :
    finToJetVariable r (Fin.last (r + 1)) = some (Fin.last r) := by
  rfl

/-- The concrete initial equation denotes the mathematical initial chart equation. -/
theorem fromCMvPolynomial_computableInitialJetEquation {r : ℕ} (center : F)
    (Q : CPoly.CMvPolynomial (r + 2) F) :
    CPoly.fromCMvPolynomial (computableInitialJetEquation center Q) =
      initialJetEquation center (semanticEquation Q) := by
  rw [computableInitialJetEquation, CPoly.CMvPolynomial.fromCMvPolynomial_bind₁]
  rw [initialJetEquation, semanticEquation, MvPolynomial.aeval_rename]
  have hsubstitution :
      (fun i => CPoly.fromCMvPolynomial (computableInitialJetSubstitution center r i)) =
        (fun i => Option.elim i (MvPolynomial.C center) MvPolynomial.X) ∘
          finToJetVariable r := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact CPoly.CMvPolynomial.fromCMvPolynomial_C center
    · exact CPoly.CMvPolynomial.fromCMvPolynomial_X j
  rw [hsubstitution]

/-- The concrete denominator denotes the mathematical initial separant. -/
theorem fromCMvPolynomial_computableInitialJetSeparant {r : ℕ} (center : F)
    (Q : CPoly.CMvPolynomial (r + 2) F) :
    CPoly.fromCMvPolynomial (computableInitialJetSeparant center Q) =
      initialJetSeparant center (semanticEquation Q) := by
  rw [computableInitialJetSeparant, CPoly.CMvPolynomial.fromCMvPolynomial_bind₁]
  rw [CPoly.CMvPolynomial.fromCMvPolynomial_partialDerivative]
  unfold initialJetSeparant semanticEquation separant
  have hderivative := MvPolynomial.pderiv_rename (finToJetVariable_injective r)
    (Fin.last (r + 1)) (CPoly.fromCMvPolynomial Q)
  rw [finToJetVariable_last] at hderivative
  rw [hderivative]
  rw [MvPolynomial.aeval_rename]
  have hsubstitution :
      (fun i => CPoly.fromCMvPolynomial (computableInitialJetSubstitution center r i)) =
        (fun i => Option.elim i (MvPolynomial.C center) MvPolynomial.X) ∘
          finToJetVariable r := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact CPoly.CMvPolynomial.fromCMvPolynomial_C center
    · exact CPoly.CMvPolynomial.fromCMvPolynomial_X j
  rw [hsubstitution]

end ReedSolomon.HiddenDerivative.SquareSystems
