/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.QuadraticRegisterInitialization

/-! # Kernel replay of physical register initialization and its last flag transition -/

@[expose] public section

namespace Computation.QuadraticRegisterInitialization

open BinaryWordMachine (Word)

private def observe (s : Control) : List Word :=
  List.ofFn (work s) ++ List.ofFn (registers s) ++ List.ofFn (flagWords s)

private def expected (q : Word) : List Word :=
  [[], [], [], [], q, [], [], [], [], [], [], [], []] ++
    List.replicate 8 (List.replicate q.length false) ++ [[false], [false]]

example : ([[], [true], [false, true], [true, false, true], [false, false, false]] : List Word).all
    (fun q ↦ decide (observe (runFuel (19 * q.length + 40) (.literal (.start q false))) =
      expected q)) = true := by decide +kernel

theorem final_flag_transition_boundary :
    flagWords (runFuel 96 (.literal (.start [true, false, true] false))) 0 = [] ∧
    flagWords (runFuel 97 (.literal (.start [true, false, true] false))) 0 = [false] := by
  decide +kernel

example : (List.ofFn (registers (.literal (.start [true, false] false)))).all
    (fun word ↦ decide (word = [])) = true := by decide +kernel

end Computation.QuadraticRegisterInitialization
