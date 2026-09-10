/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.SquareSystems.ComputableChart
public import ArkLib.ToCompPoly.Multivariate.ClearedSubstitution
/-!
# Computable rational Taylor numerators

This file mirrors the mathematical rational Taylor recurrence with concrete multivariate
polynomials. The recurrence uses executable head-coefficient extraction and denominator-cleared
substitution, while its denotation theorem identifies every computed numerator with the symbolic
one used by the Taylor chart.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.SquareSystems

open PolynomialDifferential

variable {F : Type*} [Field F] [DecidableEq F]

/-- Concrete residual coefficient used at step `l` of the Taylor recurrence. -/
def computableTaylorResidualCoefficient {r : ℕ} (l : ℕ) (center : F)
    (Q : CPoly.CMvPolynomial (r + 2) F) : CPoly.CMvPolynomial l F :=
  CPoly.CMvPolynomial.headCoefficient (l - r)
    (computableUniversalTaylorResidual l center Q)

/-- Recursive specification of every rational Taylor numerator. Production callers use the
bottom-up table in `TaylorTable`, which computes each lower coefficient once. -/
def computableRationalTaylorNumerator {r : ℕ} (center : F)
    (Q : CPoly.CMvPolynomial (r + 2) F) (l : ℕ) :
    CPoly.CMvPolynomial (r + 1) F :=
  if hl : l < r + 1 then CPoly.CMvPolynomial.X ⟨l, hl⟩ else
    -CPoly.CMvPolynomial.C ((l.choose r : F)⁻¹) *
      CPoly.CMvPolynomial.clearedSubstitution
        (computableInitialJetSeparant center Q)
        (fun i : Fin l => computableRationalTaylorNumerator center Q i.val)
        (fun i => 2 * (i.val - r) - 1) (2 * (l - r) - 2)
        (computableTaylorResidualCoefficient l center Q)
termination_by l

/-- Residual coefficient extraction agrees with the symbolic Taylor residual. -/
theorem fromCMvPolynomial_computableTaylorResidualCoefficient {r : ℕ} (l : ℕ)
    (center : F) (Q : CPoly.CMvPolynomial (r + 2) F) :
    CPoly.fromCMvPolynomial (computableTaylorResidualCoefficient l center Q) =
      ((MvPolynomial.optionEquivLeft F (Fin l)
        (universalTaylorResidual l center (semanticEquation Q))).coeff (l - r)) := by
  rw [computableTaylorResidualCoefficient,
    CPoly.CMvPolynomial.fromCMvPolynomial_headCoefficient]
  change (MvPolynomial.optionEquivLeft F (Fin l)
    (MvPolynomial.rename (finToTaylorVariable l)
      (CPoly.fromCMvPolynomial
        (computableUniversalTaylorResidual l center Q)))).coeff (l - r) = _
  rw [rename_fromCMvPolynomial_computableUniversalTaylorResidual]

theorem fromCMvPolynomial_neg_C {n : ℕ} (a : F) :
    CPoly.fromCMvPolynomial (-CPoly.CMvPolynomial.C (n := n) a) =
      (-MvPolynomial.C a : MvPolynomial (Fin n) F) := by
  change CPoly.polyRingEquiv (-CPoly.CMvPolynomial.C (n := n) a) = _
  rw [map_neg]
  exact congrArg Neg.neg (CPoly.CMvPolynomial.fromCMvPolynomial_C a)

/-- Every computed numerator denotes the corresponding symbolic rational Taylor numerator. -/
theorem fromCMvPolynomial_computableRationalTaylorNumerator {r : ℕ} (center : F)
    (Q : CPoly.CMvPolynomial (r + 2) F) (l : ℕ) :
    CPoly.fromCMvPolynomial (computableRationalTaylorNumerator center Q l) =
      rationalTaylorNumerator center (semanticEquation Q) l := by
  induction l using Nat.strong_induction_on with
  | h l ih =>
    rw [computableRationalTaylorNumerator, rationalTaylorNumerator]
    split_ifs with hl
    · exact CPoly.CMvPolynomial.fromCMvPolynomial_X ⟨l, hl⟩
    · rw [CPoly.CMvPolynomial.fromCMvPolynomial_mul', fromCMvPolynomial_neg_C,
        CPoly.CMvPolynomial.fromCMvPolynomial_clearedSubstitution,
        fromCMvPolynomial_computableInitialJetSeparant,
        fromCMvPolynomial_computableTaylorResidualCoefficient]
      congr 2
      funext i
      exact ih i.val i.isLt

/-! ### Common-denominator chart coordinates -/

/-- Executable common denominator of the rational Taylor chart. -/
def computableTaylorDenominator {r : ℕ} (center : F)
    (Q : CPoly.CMvPolynomial (r + 2) F) (τ : ℕ) :
    CPoly.CMvPolynomial (r + 1) F :=
  computableInitialJetSeparant center Q ^ τ

/-- The computed denominator is the literal common separant power. -/
theorem fromCMvPolynomial_computableTaylorDenominator {r : ℕ} (center : F)
    (Q : CPoly.CMvPolynomial (r + 2) F) (τ : ℕ) :
    CPoly.fromCMvPolynomial (computableTaylorDenominator center Q τ) =
      initialJetSeparant center (semanticEquation Q) ^ τ := by
  rw [computableTaylorDenominator, CPoly.CMvPolynomial.fromCMvPolynomial_pow,
    fromCMvPolynomial_computableInitialJetSeparant]

end ReedSolomon.HiddenDerivative.SquareSystems
