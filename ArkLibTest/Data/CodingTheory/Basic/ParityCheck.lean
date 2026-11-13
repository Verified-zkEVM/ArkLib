/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/

import ArkLib.Data.CodingTheory.Basic.ParityCheck
import Mathlib.Algebra.Field.ZMod

/-! # Parity-check code acceptance tests -/

open CodingTheory

-- One coordinate functional cuts out that coordinate's kernel.
example : pcCode 1 (fun _ => (LinearMap.proj 0 : Module.Dual (ZMod 2) (Fin 2 → ZMod 2))) =
    LinearMap.ker (LinearMap.proj 0 : Module.Dual (ZMod 2) (Fin 2 → ZMod 2)) := by
  simp [pcCode]

-- At `n = 2`, `m = 1`, one independent parity check leaves a code of dimension `1`.
example : Module.finrank (ZMod 2)
    (pcCode 1 fun _ => (LinearMap.proj 0 : Module.Dual (ZMod 2) (Fin 2 → ZMod 2))) = 1 := by
  have h := finrank_pcCode (fun _ : Fin 1 =>
    (LinearMap.proj 0 : Module.Dual (ZMod 2) (Fin 2 → ZMod 2)))
    (linearIndependent_unique_iff.2 fun h => by
      simpa using LinearMap.congr_fun h (Pi.single 0 1))
  simpa using h

-- At `n = 2`, `m = 1`, the parity checks whose code contains the line through `e₁` are the
-- `2 ^ (1 * (2 - 1)) = 2` functionals vanishing on `e₁`.
example : Nat.card {H : Fin 1 → Module.Dual (ZMod 2) (Fin 2 → ZMod 2) //
    Submodule.span (ZMod 2) {(Pi.single 1 1 : Fin 2 → ZMod 2)} ≤ pcCode 1 H} = 2 := by
  rw [card_pc_contains, finrank_span_singleton (by simp)]
  simp
