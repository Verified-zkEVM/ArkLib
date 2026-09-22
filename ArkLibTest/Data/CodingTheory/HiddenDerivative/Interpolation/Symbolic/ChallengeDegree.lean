/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.ChallengeDegree

/-!
# Challenge degree acceptance tests

For a received line `f + Z g` every coefficient of a substituted column has challenge degree at
most `y₀`. At `d = 0` the bound is attained by `Y₀²` with received value `Z`, whose constant
coefficient is `Z²`. With the nonconstant center `Z`, the column `X` has constant coefficient `Z`,
so the center must be constant. Local monomials above the column's jet degree do not occur.
-/

open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped Polynomial

namespace ChallengeDegreeTest

/-- For a received line `f + Z g`, every coefficient has challenge degree at most `y₀`. -/
example {F : Type*} [Field F] {d : ℕ} (a f g : F) (c : SourceColumn d)
    (e : LocalVariable d →₀ ℕ) :
    ((unscaledLocalSubstitution d (Polynomial.C a)
      (Polynomial.C f + Polynomial.X * Polynomial.C g) c.polynomial).coeff e).natDegree ≤
      c.y₀ := by
  simpa using SourceColumn.natDegree_coeff_unscaledLocalSubstitution_le 1 a
    (by compute_degree) c e

/-- For a received line, a local monomial of jet degree `t` has challenge degree at most
`y₀ + ∑_j higher j - t`. -/
example {F : Type*} [Field F] {d : ℕ} (a f g : F) (c : SourceColumn d)
    (e : LocalVariable d →₀ ℕ) :
    ((unscaledLocalSubstitution d (Polynomial.C a)
      (Polynomial.C f + Polynomial.X * Polynomial.C g) c.polynomial).coeff e).natDegree ≤
      c.y₀ + ∑ j, c.higher j - e.weight (localJetDegreeWeight d) := by
  simpa using SourceColumn.natDegree_coeff_unscaledLocalSubstitution_le_sub 1 a
    (by compute_degree) c e

/-- The bound `ℓ * y₀` is attained: at `d = 0`, `Y₀²` with center `0` and received value `Z`
has constant coefficient `Z²`, of challenge degree `1 * 2`. -/
example : (unscaledLocalSubstitution 0 (Polynomial.C (0 : ℚ)) Polynomial.X
    (SourceColumn.polynomial (R := ℚ[X]) ⟨0, 2, ![]⟩)).coeff 0 = Polynomial.X ^ 2 := by
  rw [SourceColumn.polynomial_eq_sourceMonomial, ← constantCoeff_eq]
  simp [sourceMonomial, localCorrection]

/-- The center must be constant: at `d = 0`, the column `X` with center `Z` and received value
`0` has constant coefficient `Z`, of challenge degree `1`, above the bound `0 * 0`. -/
example : ((unscaledLocalSubstitution 0 (Polynomial.X : ℚ[X]) 0
    (SourceColumn.polynomial (R := ℚ[X]) ⟨1, 0, ![]⟩)).coeff 0).natDegree = 1 := by
  rw [SourceColumn.polynomial_eq_sourceMonomial, ← constantCoeff_eq]
  simp [sourceMonomial]

/-- At `d = 0`, the column `Y₀` has jet degree `1`, so `E²` does not occur in its substitution. -/
example (center received : ℚ) :
    (unscaledLocalSubstitution 0 center received
      (SourceColumn.polynomial (R := ℚ) ⟨0, 1, ![]⟩)).coeff (Finsupp.single (localE 0) 2) = 0 :=
  SourceColumn.coeff_unscaledLocalSubstitution_eq_zero_of_lt center received _
    (by simp [Finsupp.weight_single, localJetDegreeWeight, localAux])

end ChallengeDegreeTest
