/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.FiniteHeadProgramPlacement
public import ArkLib.Data.Computation.WordCopyFiniteControl
public import ArkLib.Data.Computation.FieldLiteralFiniteControl

/-! # Kernel checks of noncontiguous and twenty-eight-tape physical placement -/

@[expose] public section

namespace Computation.FiniteHeadProgramPlacement

open FiniteHeadProgram

private def shuffled : Wiring 3 5 where
  place :=
    { toFun := ![4, 0, 2]
      inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all }
  owner j := match j.val with
    | 0 => some 1
    | 2 => some 2
    | 4 => some 0
    | _ => none
  owner_place i := by fin_cases i <;> rfl
  place_owner j i h := by fin_cases j <;> fin_cases i <;> cases h <;> rfl

private def word : List Bool := [true, false, false]
private def copyInitial : Configuration 4 5 :=
  ⟨0, ![[], [true, true], [false, true], [false, true, false], word]⟩
private def view {states tapes : ℕ} (s : Configuration states tapes) :=
  (s.control, List.ofFn s.bank)

/-- Noncontiguous routing keeps scratch zero, destination two and source four distinct. -/
example :
    view (runFuel (placeProgram shuffled WordCopyFiniteControl.program) 11 copyInitial) =
      (3, [[], [true, true], word, [false, true, false], word]) ∧
    view (runFuel (placeProgram shuffled WordCopyFiniteControl.program) 37 copyInitial) =
      (3, [[], [true, true], word, [false, true, false], word]) := by decide +kernel

private def literalWiring : Wiring 6 28 := offset 6 9 13
private def reference : List Bool := [true, false, true, true]
private def literalInitial : Configuration 24 28 :=
  ⟨1, fun j ↦ if j.val = 13 then reference else
    if 9 ≤ j.val ∧ j.val < 15 then [] else [decide (j.val % 2 = 0), true]⟩

/-- Literal one writes physical nine and preserves reference thirteen and all outsiders. -/
example :
    (runFuel (placeProgram literalWiring FieldLiteralFiniteControl.program)
      15 literalInitial).control = 22 ∧
    ∀ j : Fin 28, (runFuel (placeProgram literalWiring FieldLiteralFiniteControl.program)
      15 literalInitial).bank j =
        if j.val = 9 then [true, false, false, false] else literalInitial.bank j := by
  decide +kernel

/-- The placed zero-width rejection preserves every physical word, including nonempty outsiders. -/
theorem placed_zero_width_rejection_preserves_every_word :
    let initial : Configuration 24 28 :=
      ⟨1, fun j ↦ if 9 ≤ j.val ∧ j.val < 15 then [] else [true, false, true]⟩
    (runFuel (placeProgram (offset 6 9 13) FieldLiteralFiniteControl.program)
      6 initial).control = 23 ∧
    ∀ j : Fin 28, (runFuel (placeProgram (offset 6 9 13) FieldLiteralFiniteControl.program)
      6 initial).bank j = initial.bank j := by decide +kernel

end Computation.FiniteHeadProgramPlacement
