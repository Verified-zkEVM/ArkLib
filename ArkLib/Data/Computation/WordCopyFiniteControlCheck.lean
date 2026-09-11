/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.WordCopyFiniteControl

/-! # Kernel checks of finite-head word copying and instruction selection -/

@[expose] public section

namespace Computation.WordCopyFiniteControl

open FiniteHeadProgram

private def source : List Bool := [true, false, false]
private def destination : List Bool := [false, true]
private def initial : Configuration 4 3 := ⟨0, ![source, [], destination]⟩
private def view (s : Configuration 4 3) : Fin 4 × List Bool × List Bool × List Bool :=
  (s.control, s.bank 0, s.bank 1, s.bank 2)

/-- The real finite controller clears a populated destination and copies a nonpalindromic word. -/
example : view (runFuel program 11 initial) = (3, source, [], source) ∧
    view (runFuel program 37 initial) = (3, source, [], source) ∧
    view (runFuel program 6 ⟨0, ![[], [], [true, false, true]]⟩) = (3, [], [], []) := by
  decide +kernel

/-- Clearing and saving keep the same physical tape positions, with one bit moved per edge. -/
example : view (runFuel program 2 initial) = (0, source, [], []) ∧
    view (runFuel program 3 initial) = (1, source, [], []) ∧
    view (runFuel program 4 initial) = (1, [false, false], [true], []) ∧
    view (runFuel program 8 initial) = (2, [false], [false, true], [false]) := by
  decide +kernel

/-- Identical heads hide arbitrarily different tails from the dispatch table. -/
theorem dispatch_uses_only_visible_heads :
    decision program ⟨2, ![[true], [false, true, true], [false, false]]⟩ =
      decision program ⟨2, ![[true, false, true], [false], [false, true, true]]⟩ ∧
    step program ⟨3, ![[true], [false], [true, false]]⟩ = none := by decide +kernel

end Computation.WordCopyFiniteControl
