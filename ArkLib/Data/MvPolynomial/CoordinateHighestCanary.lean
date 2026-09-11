/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.MvPolynomial.CoordinateHighestRefinement

/-! # Kernel checks for selection after actual coordinate cancellation -/

@[expose] public section

namespace MvPolynomial.QuadraticHighestMachine

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private abbrev run := runFuel (2 : ZMod 5)
private def ts : List (Term (ZMod 5)) :=
  [((1, 2), [(3, 1)]), ((4, 3), [(3, 1)]), ((0, 1), [(1, 2)])]
private def output : Configuration (ZMod 5) → Option (Option (ℕ × ℕ))
  | .done out => some out
  | _ => none

example : output (run 63 (.normalizing (.ready (.terms ts [])))).1 = some (some (1, 2)) := by
  decide +kernel
example : (run 63 (.normalizing (.ready (.terms ts [])))).2 =
    ⟨{ additions := 2, equalities := 8, control := 165, data := 512,
       constants := 58, output := 7 }, 7⟩ := by decide +kernel
theorem normalization_wrapper_charges_control :
    let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
    (runFuel (2 : ZMod 5) 1 (.normalizing (.ready (.terms [] [])))).2.base.control = 2 := by
  decide +kernel
example : (run 1 (.factors [(2, 3)] [] none)).2.natural = 5 := by decide +kernel
example : output (run 3 (.factors [(0, 7)] [] none)).1 = some none := by decide +kernel
example : output (run 3 (.factors [(2, 0)] [] none)).1 = some none := by decide +kernel
example : output (run 3 (.factors [(2, 3)] [] (some (1, 9)))).1 = some (some (2, 3)) := by
  decide +kernel
example : output (run 3 (.factors [(2, 3)] [] (some (2, 7)))).1 = some (some (2, 7)) := by
  decide +kernel
example : (run 1 (.terms [] none)).2.base.output = 1 := by decide +kernel

end MvPolynomial.QuadraticHighestMachine
