/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Differential.Types
public import CompPoly.Multivariate.MvPolyEquiv.Eval

/-!
# Concrete coordinates for a differential equation

Executable differential polynomials number their variables `X,Y₀,…,Y_r` by `Fin (r+2)`.
The mathematical presentation uses `none` for X and `some i` for Yᵢ. This module contains only
that coordinate correspondence and its polynomial interpretation, so new symbolic constructors
can use the representation without importing any particular lifting algorithm.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative
open PolynomialDifferential
variable {F : Type*} [Field F] [DecidableEq F]

/-- Interpret concrete variables `0, 1, ..., r+1` as `X, Y₀, ..., Y_r`. -/
def finToJetVariable (r : ℕ) : Fin (r + 2) → JetVariable r :=
  Fin.cases none some

/-- Mathematical differential polynomial denoted by a concrete differential equation. -/
noncomputable def semanticEquation {r : ℕ} (Q : CPoly.CMvPolynomial (r + 2) F) :
    DifferentialPolynomial F r :=
  MvPolynomial.rename (finToJetVariable r) (CPoly.fromCMvPolynomial Q)

end ReedSolomon.HiddenDerivative
