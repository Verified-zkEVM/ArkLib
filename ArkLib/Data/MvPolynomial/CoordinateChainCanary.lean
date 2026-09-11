/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.MvPolynomial.CoordinateChainRefinement

/-! # Kernel replay of ordered coordinate separant stages -/

@[expose] public section

namespace MvPolynomial.QuadraticChainMachine

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private abbrev run := runFuel (2 : ZMod 5)
private def ts : List (Term (ZMod 5)) := [((1, 1), [(1, 2)])]
private def output : Configuration (ZMod 5) → Option (List (Stage (ZMod 5)))
  | .done out => some out
  | _ => none
private def index : Configuration (ZMod 5) → Option ℕ
  | .derivingAt i _ _ => some i
  | _ => none

example : output (run 130 (initial ts)).1 = some
    [⟨ts, some (1, 2)⟩, ⟨[((2, 2), [(1, 1)])], some (1, 1)⟩,
      ⟨[((2, 2), [(1, 0)])], none⟩] := by decide +kernel
example : (run 130 (initial ts)).2 =
    ⟨{ additions := 6, equalities := 10, control := 356, data := 1056,
       constants := 94, output := 25 }, 29⟩ := by decide +kernel
example : index (run 1 (.record ts (some (3, 2)) [])).1 = some 3 := by decide +kernel
example : (run 1 (initial ts)).2.base.control = 3 := by decide +kernel
theorem deriving_stage_charges_wrapped_control :
    let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
    (runFuel (2 : ZMod 5) 1 (.derivingAt 1 [] (.ready (.terms [] [])))).2.base.control = 2 := by
  decide +kernel
example : output (run 3 (.record ts none [])).1 = some [⟨ts, none⟩] := by decide +kernel
example : output (run 3 (.reverse [⟨ts, some (1, 2)⟩, ⟨[], none⟩] [])).1 =
    some [⟨[], none⟩, ⟨ts, some (1, 2)⟩] := by decide +kernel
example : (run 1 (.record ts (some (1, 2)) [])).2.base.data = 8 := by decide +kernel
example : (run 1 (.reverse [] [])).2.base.output = 1 := by decide +kernel

end MvPolynomial.QuadraticChainMachine
