/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.HigherOrderProducer.DirectSelection

/-! Regression checks for direct position-only system enumeration. -/

namespace ArkLibTest.DirectSelection

open ReedSolomon.ListDecoding.HigherOrderProducer

/-- Stored test equations have one hypersurface marker and distinct agreement markers. -/
def systems := directSystems 2 (99 : Nat) (fun i : Fin 4 ↦ i.val)

example : (directSystems 0 (99 : Nat) (fun i : Fin 4 ↦ i.val)).card = 1 := by decide
example : (directSystems 5 (99 : Nat) (fun i : Fin 4 ↦ i.val)).card = 0 := by decide

/-- Force actual enumeration, including empty selections, insufficient positions and every row. -/
def run : IO Unit := do
  unless systems.card == 6 do throw (IO.userError "missing two-position subset")
  unless decide (∀ rows ∈ systems, rows 0 = 99 ∧ rows 1 < rows 2 ∧ rows 2 < 4) do
    throw (IO.userError "direct rows changed or repeated")
  unless (directSystems 0 (99 : Nat) (fun i : Fin 4 ↦ i.val)).card == 1 do
    throw (IO.userError "zero-order selection missing")
  unless (directSystems 5 (99 : Nat) (fun i : Fin 4 ↦ i.val)).card == 0 do
    throw (IO.userError "fabricated oversized selection")

end ArkLibTest.DirectSelection
