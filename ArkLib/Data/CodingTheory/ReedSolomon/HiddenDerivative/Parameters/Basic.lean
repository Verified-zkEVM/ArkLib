/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kai Zhe Zheng, Pratyush Mishra
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Free-order parameters for hidden-derivative interpolation

This file records the rounded natural-number parameters used by the hidden-derivative
interpolation argument. The derivative order `d` is an explicit input: no definition here ties it
to the agreement fraction. This separation is essential for choosing one order uniformly across
all rates at a fixed additive capacity gap.

The definitions are adapted, with permission, from Kai Zhe Zheng's `rs-ld-mca` formalization at
commit `9699ee7a6143f6efe1d8cfed84998a4f8c79c40f`. The free-order extension was contributed through
PR 1 by Pratyush Mishra; its source commit records Codex as author and Pratyush Mishra as
committer. The two assumed Kopparty theorems and the donor's `FieldCost` wrapper are deliberately
not imported.

## Main definitions

* `multiplicity`: the multiplicity `m = d^3`.
* `agreementThreshold`: the integer threshold `A = ceil(epsilon n)`.
* `ambientDimension`: the padded interpolation dimension `K`.
* `interpolationDegreeBudget`: the individual jet-degree budget `B`.
* `interpolationWeightBudget`: the anisotropic higher-jet budget `W`.
* `higherJetDegreeBudget`: the ordinary higher-jet cutoff `C`.
* `interpolationBoxWidth`: the rectangular width used in the dimension injection.

## References

* Brakensiek, Chen, Putterman, Zhang, and Zheng, *Algorithmic List Decoding of Reed-Solomon Codes
  up to Capacity in the Low-Rate Regime*, ECCC TR26-164.
* Dao and Thaler, *Reed-Solomon List Decoding at All Rates via Hidden Derivatives*, manuscript.
-/

namespace ReedSolomon
namespace HiddenDerivative

noncomputable section

/-- Multiplicity `m = d^3` at a freely chosen derivative order. -/
def multiplicity (d : ℕ) : ℕ := d ^ 3

/-- Integer agreement threshold `A = ceil(epsilon n)`. -/
def agreementThreshold (epsilon : ℝ) (n : ℕ) : ℕ :=
  ⌈epsilon * n⌉₊

/-- Ambient interpolation dimension `K = floor((1 - theta) epsilon n)`. -/
def ambientDimension (epsilon theta : ℝ) (n : ℕ) : ℕ :=
  ⌊(1 - theta) * epsilon * n⌋₊

/-- Interpolation degree budget `B = ceil(m A / (K - 1))`.

Later theorems assume `d < K`, so the displayed denominator is positive. -/
def interpolationDegreeBudget (d : ℕ) (epsilon theta : ℝ) (n : ℕ) : ℕ :=
  ⌈(((multiplicity d * agreementThreshold epsilon n : ℕ) : ℝ) /
      ((ambientDimension epsilon theta n - 1 : ℕ) : ℝ))⌉₊

/-- Anisotropic higher-jet budget
`W = floor((1 + theta / 2) d m / (1 + log d))`. -/
def interpolationWeightBudget (theta : ℝ) (d : ℕ) : ℕ :=
  ⌊((1 + theta / 2) * (d : ℝ) * (multiplicity d : ℝ)) /
      (1 + Real.log (d : ℝ))⌋₊

/-- Ordinary higher-jet cutoff `C = floor((1 + 3 theta / 4) m)`. -/
def higherJetDegreeBudget (theta : ℝ) (d : ℕ) : ℕ :=
  ⌊(1 + 3 * theta / 4) * (multiplicity d : ℝ)⌋₊

/-- Width `H = floor(theta m / 16)` of the rectangular monomial family. -/
def interpolationBoxWidth (theta : ℝ) (d : ℕ) : ℕ :=
  ⌊theta * (multiplicity d : ℝ) / 16⌋₊

/-- The donor proof's coarse public list-size expression, retained only as parameter data.

This definition does not assert the Kopparty root-counting theorem needed to establish the bound.
-/
def coarseListBound (q d : ℕ) : ℕ :=
  q ^ (4 * d + 6)

end
end HiddenDerivative
end ReedSolomon
