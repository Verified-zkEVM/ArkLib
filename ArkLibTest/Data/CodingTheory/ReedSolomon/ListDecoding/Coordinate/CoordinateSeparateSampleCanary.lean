/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Coordinate.CoordinateSeparateSampleRefinement
/-! # Kernel checks distinguish guard samples from recovery samples -/

namespace ReedSolomon.ListDecoding.QuadraticSeparateSampleDecoder

open QuadraticPreparedDecoderMachine (Input Configuration Term)

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private def input : Input (ZMod 5) := ⟨[(0, 0)], [(0, 0)], [(0, 0)], 0, 0, 1, 1, 1⟩
private def ts : List (Term (ZMod 5)) := [(1, [(1, 1)])]
private def ri : HiddenDerivative.QuadraticStageRootsMachine.Input (ZMod 5) :=
  ⟨[(0, 0)], [((1, 0), [(1, 1)])], 0⟩
private def rec : HiddenDerivative.StageRootsMachine.Record (ZMod 5 × ZMod 5) :=
  ⟨⟨⟨ri.terms, some (1, 1)⟩, [], [((1, 0), [])]⟩, (0, 0), [(0, 0)]⟩
private abbrev run := runFuel (2 : ZMod 5) input [(1, 0)]
private def output : Configuration (ZMod 5) → Option (Option (List (List (ZMod 5))))
  | .done out => some out
  | _ => none
private def guardGrid : Configuration (ZMod 5) → Option (List (ZMod 5 × ZMod 5))
  | .collect (.accept _ _ _ payload _) => some payload.samples
  | _ => none
private def recoveryGrid : Configuration (ZMod 5) → Option (List (ZMod 5 × ZMod 5))
  | .roots _ (.start samples) => some samples
  | _ => none

example : output (run 420 (.start ts)).1 = some (some []) := by decide +kernel
example : (run 420 (.start ts)).2 = 9637 := by decide +kernel
example : guardGrid (run 2 (.collect (.start [rec]))).1 = some [(1, 0)] := by decide +kernel
example : recoveryGrid (run 1 (.convert (.done ri.terms))).1 = some [(0, 0)] := by decide +kernel
example : output (run 2 (.roots ri (.done none))).1 = some none := by decide +kernel
example : (run 1 (.collect (.start []))).2 = 7 := by decide +kernel
example : (run 1 (.roots ri (.start [(0, 0)]))).2 = 11 := by decide +kernel
example : (run 1 (.done (some []))).2 = 0 := by decide +kernel

end ReedSolomon.ListDecoding.QuadraticSeparateSampleDecoder
