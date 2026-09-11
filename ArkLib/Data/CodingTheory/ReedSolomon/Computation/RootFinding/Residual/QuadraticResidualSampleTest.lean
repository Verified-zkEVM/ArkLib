/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Residual.QuadraticResidualSampleSpec
/-!
# Kernel checks for complete coordinate residual samples

The nontrivial sample computes X*Y0+Y1 from a linear jet, with nonzero center translation.
The intermediate handoff checks point and jet order before packing. The empty sample checks
initialization, zero accumulation and all child/outer emissions with literal cost vectors.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.QuadraticResidualSample

private def observe : Configuration (ZMod 3) → Option (Pair (ZMod 3))
  | .done v => some v
  | _ => none

private def input : Input (ZMod 3) :=
  ⟨[(1, 1), (1, 1)], [((1, 0), [(0, 1), (1, 1)]), ((1, 0), [(2, 1)])], (2, 0), (2, 1), 1⟩

private def full := runFuel (2 : ZMod 3) input 218 .start

example : (observe full.1, full.2) =
    (some (2, 1), ⟨⟨28, 35, 0, 0, 0, 590, 1856, 146, 18⟩, 24⟩) := by decide +kernel

private def packed : Configuration (ZMod 3) → Option (Pair (ZMod 3) × List (Pair (ZMod 3)))
  | .pack js p => some (p, js)
  | _ => none

example : packed (runFuel (2 : ZMod 3) input 133 .start).1 =
    some ((1, 1), [(2, 1), (1, 1)]) := by decide +kernel

private def empty := runFuel (2 : ZMod 3) ⟨[], [], (1, 1), (2, 1), 0⟩ 20 .start

example : (observe empty.1, empty.2) =
    (some (0, 0), ⟨⟨2, 0, 0, 0, 0, 35, 116, 14, 4⟩, 4⟩) := by decide +kernel

-- The retained payload, rather than reconstructed external inputs, drives the actual child.
theorem retained_payload_drives_sample_child :
    let input : Input (ZMod 3) :=
      ⟨[(1, 1), (1, 1)], [((1, 0), [(0, 1), (1, 1)]), ((1, 0), [(2, 1)])],
        (2, 0), (2, 1), 1⟩
    (match (runFuel (2 : ZMod 3) input 9
      (.adding [] ⟨2, (0, 0), (1, 0)⟩ (.start .add))).1 with
    | .pack js p => some (p, js)
    | _ => none) = some ((1, 0), []) := by decide +kernel

end ReedSolomon.HiddenDerivative.QuadraticResidualSample
