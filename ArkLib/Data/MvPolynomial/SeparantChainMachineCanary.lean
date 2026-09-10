/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.MvPolynomial.SeparantChainBounds
public import Mathlib.Algebra.Field.ZMod

/-!
# Ordered separant-chain execution regressions

Literal kernel computations retain original stage equations and exact metadata, including a
drop in highest active jet. Costs include both nested wrapper levels and stage-list reversal.
-/

@[expose] public section

namespace MvPolynomial.SeparantChainMachine

/-- Differentiating `Y₀Y₁` changes the highest jet from `Y₁` to `Y₀`, then reaches a constant. -/
example : runFuel 69 (initial [(1, [(0, 0), (1, 1), (2, 1)])] : Configuration (ZMod 5)) =
    (.done [⟨[(1, [(0, 0), (1, 1), (2, 1)])], some (2, 1)⟩,
      ⟨[(1, [(0, 0), (1, 1), (2, 0)])], some (1, 1)⟩,
      ⟨[(1, [(0, 0), (1, 0), (2, 0)])], none⟩],
      ⟨⟨2, 0, 138, 420, 60, 17⟩, 5⟩) := by decide +kernel

/-- Repeated differentiation retains the X exponent and updates each exact selected degree. -/
example : runFuel 65 (initial [(2, [(0, 3), (1, 2)])] : Configuration ℕ) =
    (.done [⟨[(2, [(0, 3), (1, 2)])], some (1, 2)⟩,
      ⟨[(4, [(0, 3), (1, 1)])], some (1, 1)⟩,
      ⟨[(4, [(0, 3), (1, 0)])], none⟩],
      ⟨⟨3, 0, 130, 388, 46, 17⟩, 5⟩) := by decide +kernel

/-- A nonconstant X-only equation is terminal and must still be recorded. -/
example : runFuel 14 (initial [(2, [(0, 3), (1, 0)])] : Configuration ℕ) =
    (.done [⟨[(2, [(0, 3), (1, 0)])], none⟩],
      ⟨⟨0, 0, 28, 79, 10, 5⟩, 1⟩) := by decide +kernel

/-- Stage equations retain their raw terms while selection detects coefficient cancellation. -/
example : runFuel 79 (initial [(2, [(0, 0), (1, 2)]), (3, [(0, 0), (1, 2)]),
    (1, [(0, 0), (1, 1)])] : Configuration (ZMod 5)) =
    (.done [⟨[(2, [(0, 0), (1, 2)]), (3, [(0, 0), (1, 2)]),
        (1, [(0, 0), (1, 1)])], some (1, 1)⟩,
      ⟨[(4, [(0, 0), (1, 1)]), (1, [(0, 0), (1, 1)]),
        (1, [(0, 0), (1, 0)])], none⟩],
      ⟨⟨7, 0, 178, 530, 53, 13⟩, 11⟩) := by decide +kernel

/-- One step before final emission, all records have been restored to derivative order. -/
example : runFuel 68 (initial [(1, [(0, 0), (1, 1), (2, 1)])] : Configuration (ZMod 5)) =
    (.reverse [] [⟨[(1, [(0, 0), (1, 1), (2, 1)])], some (2, 1)⟩,
      ⟨[(1, [(0, 0), (1, 1), (2, 0)])], some (1, 1)⟩,
      ⟨[(1, [(0, 0), (1, 0), (2, 0)])], none⟩],
      ⟨⟨2, 0, 137, 418, 60, 16⟩, 5⟩) := by decide +kernel

/-- Even zero input produces an explicit terminal record; nonzero is a semantic chain premise. -/
example : runFuel 7 (initial [] : Configuration ℕ) =
    (.done [⟨[], none⟩], ⟨⟨0, 0, 11, 29, 0, 5⟩, 0⟩) := by decide +kernel

end MvPolynomial.SeparantChainMachine
