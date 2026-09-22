/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.GradedRank

/-!
# Graded local constraint acceptance tests

The source's center-zero statements are derived from the general ones. At `d = 0` and received
value `1`, the image of `Y₀` is `1 + T E`, whose constant term has local jet degree zero; so the
grading needs received value zero. The center may be nonzero: with center `3` the constraint
coefficient of a source monomial still vanishes outside its grade. Translating `Y₀`, of jet
degree one, produces only monomials of jet degree at most one.
-/

open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative

variable {d m : ℕ}

/-- Source shape `unscaledLocalSubstitution_zero_Y_zero_isWeightedHomogeneous`. -/
example : (unscaledLocalSubstitution (R := ℤ) d 0 0 (X (some 0))).IsWeightedHomogeneous
    (localJetDegreeWeight d) 1 := by
  simpa using unscaledLocalSubstitution_isWeightedHomogeneous (R := ℤ) (d := d) 0
    (isWeightedHomogeneous_X ℤ jetDegreeWeight (some 0))

/-- Source shape `unscaledLocalSubstitution_zero_sourceMonomial_isWeightedHomogeneous`. -/
example (x b : ℕ) (higher : Fin d → ℕ) :
    (unscaledLocalSubstitution (R := ℤ) d 0 0 (sourceMonomial x b higher)).IsWeightedHomogeneous
      (localJetDegreeWeight d) (b + ∑ j, higher j) :=
  unscaledLocalSubstitution_isWeightedHomogeneous 0
    (sourceMonomial_isWeightedHomogeneous_jetDegreeWeight x b higher)

/-- Source shape `localConstraintAt_zero_sourceMonomial_isWeightedHomogeneous`. -/
example (x b : ℕ) (higher : Fin d → ℕ) :
    (localConstraintAt (R := ℤ) m 0 0 (sourceMonomial x b higher)).IsWeightedHomogeneous
      (localJetDegreeWeight d) (b + ∑ j, higher j) :=
  localConstraintAt_isWeightedHomogeneous 0
    (sourceMonomial_isWeightedHomogeneous_jetDegreeWeight x b higher)

/-- The received value must be zero: at `d = 0` and received value `1`, the image of `Y₀` has
constant term `1`, so it is not homogeneous of local jet degree one. -/
example : ¬ (unscaledLocalSubstitution (R := ℤ) 0 0 1 (X (some 0))).IsWeightedHomogeneous
    (localJetDegreeWeight 0) 1 := by
  intro h
  have hcoeff : (unscaledLocalSubstitution (R := ℤ) 0 0 1 (X (some 0))).coeff 0 ≠ 0 := by
    rw [unscaledLocalSubstitution_Y_zero]
    simp [localCorrection, coeff_X_mul']
  have := h hcoeff
  simp at this

/-- A nonzero center is allowed: at center `3`, the constraint coefficient of the source monomial
`Y₀²` vanishes at the row `E`, whose local jet degree is one. -/
example : (localConstraintAt (R := ℤ) m 3 0 (sourceMonomial (d := d) 0 2 0)).coeff
    (Finsupp.single (localE d) 1) = 0 := by
  refine coeff_localConstraintAt_eq_zero_of_weight_ne 3
    (sourceMonomial_isWeightedHomogeneous_jetDegreeWeight 0 2 0) _ ?_
  rw [Finsupp.weight_single]
  simp [localJetDegreeWeight, localE, localAux]

/-- The graded map at center `3` in grade two sends `Y₀²` to its constraint image. -/
example : (gradedLocalConstraintAt (R := ℤ) (d := d) m 3 2
    ⟨X (some 0) ^ 2, (isWeightedHomogeneous_X ℤ jetDegreeWeight (some 0)).pow 2⟩ :
      LocalPolynomial ℤ d) = localConstraintAt m 3 0 (X (some 0) ^ 2) :=
  rfl

/-- Translating `Y₀`, of jet degree one, cannot produce a monomial of jet degree two. -/
example (center received : ℤ) (e : JetVariable d →₀ ℕ)
    (he : e ∈ (globalPointTranslation center received (X (some 0))).support) :
    totalJetDegree e ≤ 1 :=
  totalJetDegree_le_of_mem_globalPointTranslation_support center received
    (fun u hu => by
      rw [support_X, Finset.mem_singleton] at hu
      subst hu
      simp [totalJetDegree, Finsupp.weight_single]) he
