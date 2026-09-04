/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.DifferentialEquation

/-!
# Characteristic-safe descent in the highest jet variable

The singular-solution recursion for a polynomial differential equation repeatedly differentiates
in its highest active Hasse-jet variable. This file proves one complete descent step. If `Q`
depends on `Y_s` with individual degree `t < ringChar F`, then differentiating exactly `t` times
produces a nonzero polynomial independent of `Y_s`. Degrees in every other variable do not
increase. Consequently, if `s` was the highest active jet, every active jet in the residual
polynomial has order strictly below `s`.

The strict characteristic hypothesis is essential: the derivative of `Y_s ^ p` is zero in
characteristic `p`.

## References

* [Kopparty, S., *List-Decoding Multiplicity Codes*][Kop15]
-/

namespace ReedSolomon
namespace HiddenDerivative

noncomputable section

variable {F : Type*} {d : ℕ} [CommSemiring F]

/-- The `a`-fold partial derivative of `Q` in the formal Hasse variable `Y_s`. -/
def jetDerivative (Q : DifferentialPolynomial F d) (s : Fin (d + 1)) (a : ℕ) :
    DifferentialPolynomial F d :=
  MvPolynomial.iteratePDeriv (some s) a Q

@[simp]
theorem jetDerivative_zero (Q : DifferentialPolynomial F d) (s : Fin (d + 1)) :
    jetDerivative Q s 0 = Q := by
  simp [jetDerivative]

@[simp]
theorem jetDerivative_succ (Q : DifferentialPolynomial F d) (s : Fin (d + 1)) (a : ℕ) :
    jetDerivative Q s (a + 1) = separant (jetDerivative Q s a) s := by
  simp [jetDerivative, separant]

/-- The first jet derivative is the separant. -/
theorem jetDerivative_one (Q : DifferentialPolynomial F d) (s : Fin (d + 1)) :
    jetDerivative Q s 1 = separant Q s := by
  simp [jetDerivative, separant]

/-- Below the characteristic, an initial segment of the jet-derivative chain has the expected
individual degree. -/
theorem jetDegree_jetDerivative_eq_sub_of_lt_ringChar [NoZeroDivisors F] [Nontrivial F]
    (Q : DifferentialPolynomial F d)
    (s : Fin (d + 1)) (a : ℕ) (ha : a ≤ jetDegree Q s)
    (hchar : jetDegree Q s < ringChar F) :
    jetDegree (jetDerivative Q s a) s = jetDegree Q s - a := by
  exact MvPolynomial.degreeOf_iteratePDeriv_eq_sub_of_lt_ringChar (some s) a Q ha hchar

/-- Differentiating in one jet variable cannot increase the individual degree in another. -/
theorem jetDegree_jetDerivative_le (Q : DifferentialPolynomial F d) (s j : Fin (d + 1))
    (a : ℕ) : jetDegree (jetDerivative Q s a) j ≤ jetDegree Q j := by
  exact MvPolynomial.degreeOf_iteratePDeriv_le (some s) (some j) a Q

/-- The full descent derivative in `Y_s`, obtained after differentiating through its entire
individual degree. -/
def derivativeDescent (Q : DifferentialPolynomial F d) (s : Fin (d + 1)) :
    DifferentialPolynomial F d :=
  jetDerivative Q s (jetDegree Q s)

/-- A full descent step eliminates dependence on the selected jet variable. -/
theorem jetDegree_derivativeDescent_eq_zero [NoZeroDivisors F] [Nontrivial F]
    (Q : DifferentialPolynomial F d)
    (s : Fin (d + 1)) (hchar : jetDegree Q s < ringChar F) :
    jetDegree (derivativeDescent Q s) s = 0 := by
  rw [derivativeDescent, jetDegree_jetDerivative_eq_sub_of_lt_ringChar Q s _ le_rfl hchar,
    Nat.sub_self]

/-- A full descent step is nonzero when the selected jet variable is active and its degree is
strictly below the characteristic. -/
theorem derivativeDescent_ne_zero [NoZeroDivisors F] [Nontrivial F]
    (Q : DifferentialPolynomial F d) (s : Fin (d + 1))
    (hs : DependsOnJet Q s) (hchar : jetDegree Q s < ringChar F) :
    derivativeDescent Q s ≠ 0 := by
  exact MvPolynomial.iteratePDeriv_ne_zero_of_lt_ringChar (some s) (jetDegree Q s) Q hs le_rfl
    hchar

/-- A full descent step does not increase any individual jet degree. -/
theorem jetDegree_derivativeDescent_le (Q : DifferentialPolynomial F d) (s j : Fin (d + 1)) :
    jetDegree (derivativeDescent Q s) j ≤ jetDegree Q j :=
  jetDegree_jetDerivative_le Q s j _

/-- Every active variable in the residual polynomial has lower order than the variable eliminated
by a full descent step. -/
theorem active_lt_of_derivativeDescent [NoZeroDivisors F] [Nontrivial F]
    (Q : DifferentialPolynomial F d) (s j : Fin (d + 1))
    (hs : IsHighestActiveJet Q s) (hchar : jetDegree Q s < ringChar F)
    (hj : DependsOnJet (derivativeDescent Q s) j) : j < s := by
  rcases lt_trichotomy j s with hjs | hjs | hsj
  · exact hjs
  · subst j
    rw [DependsOnJet, jetDegree_derivativeDescent_eq_zero Q s hchar] at hj
    exact (Nat.not_lt_zero _ hj).elim
  · have hactive : DependsOnJet Q j :=
      lt_of_lt_of_le hj (jetDegree_derivativeDescent_le Q s j)
    exact (hs.2 j hsj hactive).elim

/-- If the residual polynomial still has an active jet variable, its computed highest one has
strictly smaller order. -/
theorem highestActiveJet_derivativeDescent_lt [NoZeroDivisors F] [Nontrivial F]
    (Q : DifferentialPolynomial F d)
    (s j : Fin (d + 1)) (hs : IsHighestActiveJet Q s)
    (hchar : jetDegree Q s < ringChar F)
    (hj : highestActiveJet (derivativeDescent Q s) = some j) : j < s := by
  exact active_lt_of_derivativeDescent Q s j hs hchar
    (isHighestActiveJet_of_highestActiveJet_eq_some hj).1

/-- Under global individual-degree bounds, a full derivative descent from the computed highest
variable is nonzero and strictly decreases every remaining active order. -/
theorem derivativeDescent_spec_of_highestActiveJet_eq_some [NoZeroDivisors F] [Nontrivial F]
    (Q : DifferentialPolynomial F d)
    (s : Fin (d + 1)) (hdegrees : ∀ j, jetDegree Q j < ringChar F)
    (hs : highestActiveJet Q = some s) :
    derivativeDescent Q s ≠ 0 ∧
      ∀ j, DependsOnJet (derivativeDescent Q s) j → j < s := by
  have hhighest := isHighestActiveJet_of_highestActiveJet_eq_some hs
  exact ⟨derivativeDescent_ne_zero Q s hhighest.1 (hdegrees s),
    fun j hj ↦ active_lt_of_derivativeDescent Q s j hhighest (hdegrees s) hj⟩

end

end HiddenDerivative
end ReedSolomon
