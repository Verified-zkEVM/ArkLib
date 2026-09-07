/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLibExamples.ReedSolomon.CurveProfile

/-!
# ZisK first-order interpolation certificates

This module checks every interpolation profile in `goldilocks-beyond-poseidon.json`: the initial
Poseidon2 powers row and the five folding rows on domains of sizes `65536`, `8192`, `1024`, `128`,
and `32`.

For each line row, Lean evaluates the exact finite first-order support data and the shifted
graded-row surplus

```text
firstOrderCurveShiftedRowSlotBound (k - 1) A m M mu n 1 h
  < firstOrderCurveShiftedHeightSlotCount (k - 1) A m M mu 1 h.
```

The full-support constructor turns this numerical surplus into a primitive symbolic
interpolant over `F[Z]`.  Its specialization remains nonzero over every extension field, and every
degree-`< k` polynomial agreeing with the specialized received line at `A` positions satisfies
the resulting differential equation.

The initial degree-181 row additionally checks the polynomial-curve surplus at height 22707 and
constructs that curve certificate. The folding rows expose their affine-line certificates.
-/

open PolynomialDifferential Polynomial

namespace ArkLibExamples.ReedSolomon.ZisKInterpolation

open CurveProfile
open ReedSolomon.HiddenDerivative
open ReedSolomon.HiddenDerivative.SymbolicWeightedSupportInterpolation

noncomputable section

universe u v

/-! ## Initial powers row -/

/-- Initial Poseidon2 profile on the domain of size `524288`. -/
def initial : LineProfile where
  n := 524288
  k := 131072
  agreement := 260512
  multiplicity := 9
  firstDerivativeCap := 3
  totalJetCap := 17
  batchingDegree := 181
  supportDimension := 75053054
  localRank := 140
  columnY₀Weight := 388950086
  height := 22707
  heightSlots := 1703915800146

/-- Lean recomputes the revised degree-181 shifted source and row slots at height 22707. -/
theorem initial_verified : initial.CurveVerification := by decide

/-- The revised ZisK row constructs its actual degree-181 polynomial-curve certificate at
height 22707. -/
theorem exists_initial_curveCertificate {F : Type u} [Field F]
    (centers : Fin initial.n ↪ F) (w : Fin initial.n → F[X])
    (hw : ∀ i, (w i).natDegree ≤ initial.batchingDegree) :
    Nonempty (FirstOrderCurveCertificate initial.D initial.agreement initial.multiplicity
      initial.firstDerivativeCap initial.totalJetCap initial.k initial.height centers w
      initial.columns) :=
  initial_verified.exists_certificate centers w hw

/-! ## Folding rows -/

/-- The five folding rows in decreasing domain order. -/
def folds : Fin 5 → LineProfile := ![
  { n := 65536, k := 16384, agreement := 32564, multiplicity := 9,
    firstDerivativeCap := 3, totalJetCap := 17, batchingDegree := 7,
    supportDimension := 9382246, localRank := 140, columnY₀Weight := 48624814,
    height := 1642, heightSlots := 15366405364 },
  { n := 8192, k := 2048, agreement := 4071, multiplicity := 9,
    firstDerivativeCap := 3, totalJetCap := 17, batchingDegree := 7,
    supportDimension := 1173692, localRank := 140, columnY₀Weight := 6086468,
    height := 1589, heightSlots := 1860083812 },
  { n := 1024, k := 256, agreement := 509, multiplicity := 9,
    firstDerivativeCap := 3, totalJetCap := 17, batchingDegree := 7,
    supportDimension := 147400, localRank := 140, columnY₀Weight := 767440,
    height := 1329, heightSlots := 195274560 },
  { n := 128, k := 32, agreement := 64, multiplicity := 9,
    firstDerivativeCap := 3, totalJetCap := 17, batchingDegree := 7,
    supportDimension := 19262, localRank := 140, columnY₀Weight := 103718,
    height := 541, heightSlots := 10336286 },
  { n := 32, k := 8, agreement := 16, multiplicity := 9,
    firstDerivativeCap := 3, totalJetCap := 17, batchingDegree := 3,
    supportDimension := 5342, localRank := 140, columnY₀Weight := 31118,
    height := 108, heightSlots := 551160 }
]

/-- Every folding row has its claimed actual dimension, rank, height count, and strict surplus. -/
theorem folds_verified : ∀ i, (folds i).Verification := by
  intro i
  fin_cases i <;> constructor <;> decide

/-- Every folding row produces an actual primitive and specialization-sound symbolic line
certificate.  The recorded batching degrees identify the script rows but require a separate
transfer theorem. -/
theorem exists_fold_symbolicCertificate {F : Type u} [Field F] (i : Fin 5)
    (centers : Fin (folds i).n ↪ F) (f g : Fin (folds i).n → F) :
    Nonempty ((folds i).SymbolicCertificate.{u, v} centers f g) :=
  (folds_verified i).exists_symbolicCertificate centers f g

end

end ArkLibExamples.ReedSolomon.ZisKInterpolation
