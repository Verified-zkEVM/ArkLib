/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks, Quang Dao
-/
import ArkLib.Data.OracleComp.MeasuredProgram

/-! A shared measured program for one charged addition on a view of the input. -/

open OracleComp OracleSpec

namespace AddProgramTest

/-- One addition instruction, whose response is certified to be the sum. -/
def addSpec (v : ℕ × ℕ) : OracleSpec.{0, 0} Unit :=
  fun _ => {r : ℕ // r = v.1 + v.2}

/-- A program performing one charged addition on the view of its input. -/
def addProgram {Input : Type} (view : Input → ℕ × ℕ) : MeasuredProgram Input ℕ ℕ where
  View := ℕ × ℕ
  view := view
  Op := Unit
  spec := addSpec
  program v := do
    let r ← liftM (OracleSpec.query (spec := addSpec v) ())
    return r.1
  answer v := fun _ => ⟨v.1 + v.2, rfl⟩
  cost := fun _ => 1

/-- The program realizes addition of the two numbers in the view. -/
theorem addProgram_realizes {Input : Type} (view : Input → ℕ × ℕ) :
    (addProgram view).Realizes (fun x => (view x).1 + (view x).2) :=
  fun _ => rfl

/-- The program costs at most one addition on every input. -/
theorem addProgram_costAtMost_one {Input : Type} (view : Input → ℕ × ℕ) :
    (addProgram view).CostAtMost 1 :=
  MeasuredProgram.costAtMost_of_forall_eq_answer _ 1 (fun _ _ u => Subtype.ext u.2)
    (fun _ => le_rfl)

end AddProgramTest
