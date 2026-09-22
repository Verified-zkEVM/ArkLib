/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Differential.DerivativeDescent
import Mathlib.Data.ZMod.Basic

/-!
# Acceptance tests for derivative descent

* Over `ℚ`, the full descent of `Y₁ ^ 2 * Y₀` in `Y₁` is `2 * Y₀`. The general theorems show it is
  nonzero and depends only on `Y₀`.
* Over `ZMod 2`, the full descent of `Y₀ ^ 2` is zero and the cast hypothesis fails, so
  `derivativeDescent_ne_zero` needs it.
* Over `ZMod 4`, `2 * Y₀ ^ 2` satisfies the cast hypothesis but its separant is zero, so the
  nonvanishing theorems need `NoZeroDivisors`.
* The source statements with `jetDegree Q s < ringChar F` follow from the general ones.
-/

namespace PolynomialDifferential

noncomputable section

open MvPolynomial

/-! ### A computed descent over `ℚ` -/

/-- `Y₁ ^ 2 * Y₀` in depth `1`. -/
private abbrev cubicEquation : DifferentialPolynomial ℚ 1 :=
  X (some 1) ^ 2 * X (some 0)

private theorem cubicEquation_eq_monomial :
    cubicEquation = monomial (Finsupp.single (some 1) 2 + Finsupp.single (some 0) 1) 1 := by
  rw [cubicEquation, X_pow_eq_monomial, X, monomial_mul_monomial, one_mul]

private theorem jetDegree_cubicEquation (j : Fin 2) :
    jetDegree cubicEquation j = if j = 1 then 2 else 1 := by
  classical
  rw [jetDegree, cubicEquation_eq_monomial, degreeOf_monomial_eq _ _ one_ne_zero]
  fin_cases j <;> simp

private theorem isHighestActiveJet_cubicEquation : IsHighestActiveJet cubicEquation 1 :=
  ⟨by simp [DependsOnJet, jetDegree_cubicEquation], fun j hj ↦ absurd j.le_last (not_le.mpr hj)⟩

private theorem castsNeZero_rat (Q : DifferentialPolynomial ℚ 1) (s : Fin 2) :
    JetDegreeCastsNeZero Q s :=
  jetDegreeCastsNeZero_of_ringChar (Or.inl ringChar.eq_zero)

/-- The full descent of `Y₁ ^ 2 * Y₀` in `Y₁` is `2 * Y₀`. -/
example : derivativeDescent cubicEquation 1 = 2 * X (some 0) := by
  rw [derivativeDescent, jetDegree_cubicEquation]
  simp [jetDerivative, sq, pderiv_X]
  ring

/-- The general theorem shows the descent is nonzero; characteristic zero gives the cast
hypothesis. -/
example : derivativeDescent cubicEquation 1 ≠ 0 :=
  derivativeDescent_ne_zero (by simp [cubicEquation]) 1 (castsNeZero_rat _ 1)

/-- Every jet variable on which the descent depends is `Y₀`. -/
example (j : Fin 2) (hj : DependsOnJet (derivativeDescent cubicEquation 1) j) : j = 0 := by
  have := active_lt_of_derivativeDescent isHighestActiveJet_cubicEquation hj
  omega

/-- One derivative in `Y₁` lowers the degree in `Y₁` from `2` to `1`. -/
example : jetDegree (separant cubicEquation 1) 1 = 1 := by
  rw [jetDegree_separant_eq_sub_one _ _
    ((castsNeZero_rat _ 1).natCast_jetDegree_ne_zero isHighestActiveJet_cubicEquation.1),
    jetDegree_cubicEquation]
  rfl

/-! ### The cast hypothesis is needed -/

/-- `Y₀ ^ 2` in depth `0`, over a commutative semiring. -/
private abbrev squareEquation (F : Type) [CommSemiring F] : DifferentialPolynomial F 0 :=
  X (some 0) ^ 2

private theorem squareEquation_eq_monomial (F : Type) [CommSemiring F] :
    squareEquation F = monomial (Finsupp.single (some 0) 2) 1 :=
  X_pow_eq_monomial

private theorem jetDegree_squareEquation (F : Type) [CommSemiring F] [Nontrivial F] :
    jetDegree (squareEquation F) 0 = 2 := by
  classical
  rw [jetDegree, squareEquation_eq_monomial, degreeOf_monomial_eq _ _ one_ne_zero]
  simp

/-- Over `ZMod 2`, the separant of `Y₀ ^ 2` is zero. -/
private theorem separant_squareEquation_zmod_two : separant (squareEquation (ZMod 2)) 0 = 0 := by
  rw [separant, squareEquation_eq_monomial, pderiv_monomial, Finsupp.single_eq_same,
    show (1 : ZMod 2) * ((2 : ℕ) : ZMod 2) = 0 by decide, monomial_zero]

/-- Over `ZMod 2`, the full descent of `Y₀ ^ 2` is zero. -/
example : derivativeDescent (squareEquation (ZMod 2)) 0 = 0 := by
  rw [derivativeDescent, jetDegree_squareEquation, jetDerivative_succ, jetDerivative_one,
    separant_squareEquation_zmod_two, separant, map_zero]

/-- Over `ZMod 2`, `Y₀ ^ 2` fails the cast hypothesis. -/
example : ¬JetDegreeCastsNeZero (squareEquation (ZMod 2)) 0 := fun h ↦
  h 2 (by decide) (jetDegree_squareEquation _).ge (by decide)

/-! ### `NoZeroDivisors` is needed -/

/-- `2 * Y₀ ^ 2` in depth `0` over `ZMod 4`. -/
private abbrev doubledSquare : DifferentialPolynomial (ZMod 4) 0 :=
  C 2 * X (some 0) ^ 2

private theorem doubledSquare_eq_monomial :
    doubledSquare = monomial (Finsupp.single (some 0) 2) 2 := by
  rw [doubledSquare, X_pow_eq_monomial, C_mul_monomial, mul_one]

private theorem jetDegree_doubledSquare : jetDegree doubledSquare 0 = 2 := by
  classical
  rw [jetDegree, doubledSquare_eq_monomial, degreeOf_monomial_eq _ _ (by decide)]
  simp

/-- `2 * Y₀ ^ 2` satisfies the cast hypothesis over `ZMod 4`: `1` and `2` are nonzero. -/
example : JetDegreeCastsNeZero doubledSquare 0 := by
  intro k hk hkt
  rw [jetDegree_doubledSquare] at hkt
  interval_cases k <;> decide

/-- The separant of `2 * Y₀ ^ 2` over `ZMod 4` is `4 * Y₀ = 0`, although `(2 : ZMod 4) ≠ 0`. -/
example : separant doubledSquare 0 = 0 := by
  rw [separant, doubledSquare_eq_monomial, pderiv_monomial, Finsupp.single_eq_same,
    show (2 : ZMod 4) * ((2 : ℕ) : ZMod 4) = 0 by decide, monomial_zero]

/-! ### Source-shaped statements -/

section Source

variable {F : Type*} [CommSemiring F] [NoZeroDivisors F] [Nontrivial F] {d : ℕ}

/-- The source form of `jetDegree_jetDerivative_eq_sub`. -/
example (Q : DifferentialPolynomial F d) (s : Fin (d + 1)) (a : ℕ) (_ha : a ≤ jetDegree Q s)
    (hchar : jetDegree Q s < ringChar F) :
    jetDegree (jetDerivative Q s a) s = jetDegree Q s - a :=
  jetDegree_jetDerivative_eq_sub Q s a (jetDegreeCastsNeZero_of_ringChar (Or.inr hchar))

/-- The source form of `derivativeDescent_ne_zero`, with `DependsOnJet Q s` in place of
`Q ≠ 0`. -/
example (Q : DifferentialPolynomial F d) (s : Fin (d + 1)) (hs : DependsOnJet Q s)
    (hchar : jetDegree Q s < ringChar F) : derivativeDescent Q s ≠ 0 := by
  refine derivativeDescent_ne_zero ?_ s (jetDegreeCastsNeZero_of_ringChar (Or.inr hchar))
  rintro rfl
  simp [DependsOnJet, jetDegree] at hs

/-- The source form of `derivativeDescent_spec_of_highestActiveJet_eq_some`, with bounds at every
jet. -/
example (Q : DifferentialPolynomial F d) (s : Fin (d + 1))
    (hdegrees : ∀ j, jetDegree Q j < ringChar F) (hs : highestActiveJet Q = some s) :
    derivativeDescent Q s ≠ 0 ∧ ∀ j, DependsOnJet (derivativeDescent Q s) j → j < s :=
  derivativeDescent_spec_of_highestActiveJet_eq_some hs
    (jetDegreeCastsNeZero_of_ringChar (Or.inr (hdegrees s)))

end Source

end

end PolynomialDifferential
