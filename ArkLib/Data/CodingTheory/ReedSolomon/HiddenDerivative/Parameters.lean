/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

/-!
# Exact parameters for hidden-derivative interpolation

The hidden-derivative engine consumes natural-number parameters. Rates, asymptotics, and named
choices such as `multiplicity = derivOrder ^ 3` belong in later parameter-discharge theorems.
Keeping this record data-only allows stronger parameter regimes and improved constants to reuse the
same interpolation and decoder interfaces.
-/

namespace ReedSolomon
namespace HiddenDerivative

/-- Natural-number parameters controlled by the hidden-derivative interpolation proof.

The record intentionally does not include the target message dimension: interpolation and root
finding occur at `designDim`, while decoder integration separately assumes
`messageDim ≤ designDim` and filters back to the target code. It also does not fix a root-solver
list bound or hitting-extension degree; those belong to the solver contract. -/
structure Parameters where
  /-- Ambient polynomial degree bound used for interpolation and root finding. -/
  designDim : Nat
  /-- Absolute number of required agreement positions. -/
  minAgreement : Nat
  /-- Highest Hasse-derivative order appearing in the interpolant. -/
  derivOrder : Nat
  /-- Root multiplicity imposed at every agreement point. -/
  multiplicity : Nat
  /-- Degree cap for the distinguished low-derivative variable. -/
  yDegreeCap : Nat
  /-- Anisotropic weighted-degree cap for high-derivative variables. -/
  weightCap : Nat
  /-- Total-exponent cap for the high-derivative variables. -/
  l1Cap : Nat
  deriving DecidableEq, Repr

end HiddenDerivative
end ReedSolomon
