/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.AgreementThreshold
public import Mathlib.Analysis.SpecialFunctions.Exp
/-!
# Weighted-support capacity parameters

These numerical choices precede the field, evaluation points, and received word.
They retain the existing weighted-support order and its order-zero branch.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

/-- The prescribed derivative order for uniform prime-field capacity decoding.

The order-zero branch covers every gap at least `1 / 4`. Below that boundary, the constant
`27 / 10` is the prescribed no-band weighted-support constant. -/
def capacityDerivativeOrder (delta : ℝ) : ℕ :=
  if (1 / 4 : ℝ) ≤ delta then 0
  else Nat.ceil (Real.exp (((27 : ℝ) / 10) / delta))

@[simp]
theorem capacityDerivativeOrder_eq_zero {delta : ℝ} (hdelta : (1 / 4 : ℝ) ≤ delta) :
    capacityDerivativeOrder delta = 0 := by
  rw [capacityDerivativeOrder, if_pos hdelta]

theorem capacityDerivativeOrder_eq_ceil {delta : ℝ} (hdelta : delta < (1 / 4 : ℝ)) :
    capacityDerivativeOrder delta = Nat.ceil (Real.exp (((27 : ℝ) / 10) / delta)) := by
  rw [capacityDerivativeOrder, if_neg (not_le_of_gt hdelta)]

/-- The harmonic number `H_r = sum_{i=1}^r 1/i` used by the weighted-support parameters. -/
def harmonicNumber (r : ℕ) : ℝ :=
  ∑ i ∈ Finset.range r, (1 : ℝ) / (i + 1)

/-- The weighted-support multiplicity `ceil(100 d^2 H_{d-1})`. This parameter package
is used only below gap `1 / 4`; the order-zero branch instead uses an instance-dependent
multiplicity and is deliberately specified separately. -/
def weightedSupportMultiplicity (delta : ℝ) : ℕ :=
  let derivOrder := capacityDerivativeOrder delta
  Nat.ceil (100 * (derivOrder : ℝ) ^ 2 * harmonicNumber (derivOrder - 1))

/-- The ambient dimension in the prescribed weighted-support certificate. -/
def weightedSupportAmbientDimension (delta : ℝ) (blockLength messageDim : ℕ) : ℕ :=
  max messageDim ⌊(delta * (blockLength : ℝ)) / 2⌋₊

/-- The larger-field condition under which the weighted-support target improves its root exponent
from `2d` to `d`. The truncated natural subtraction represents
`max {0, m * A - K + d}` from the manuscript. -/
def LargeFieldCondition (delta : ℝ)
    (blockLength messageDim fieldSize derivOrder multiplicity : ℕ) :
    Prop :=
  2 * (multiplicity * agreementThreshold delta blockLength messageDim + derivOrder -
    weightedSupportAmbientDimension delta blockLength messageDim) ≤ fieldSize

end ReedSolomon
