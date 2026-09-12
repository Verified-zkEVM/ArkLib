/-
Copyright (c) 2026 ArkLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Graph.GabberGalilConstruction.Basic

/-!
Regression tests for the actual eight affine maps. The small moduli intentionally
force loops and parallel edges, so a simple-graph implementation fails these tests.
-/

namespace GabberGalilTest

open GabberGalil

example (m : ℕ) (v : Graph m) : Nat.card (Quiver.Star v) = 8 := regular v

example (m : ℕ) (v w : Graph m) (e : v ⟶ w) : reverseEdge (reverseEdge e) = e :=
  reverseEdge_reverseEdge e

example : neighbors ((0, 0) : Vertex 1) = List.replicate 8 (0, 0) := by decide

example : neighbors ((0, 0) : Vertex 2) =
    [(0, 0), (0, 0), (1, 0), (1, 0), (0, 0), (0, 0), (0, 1), (0, 1)] := by decide

example : neighbors ((1, 1) : Vertex 3) =
    [(0, 1), (2, 1), (1, 1), (1, 1), (1, 0), (1, 2), (1, 1), (1, 1)] := by decide

/-- Execute loop, parallel-edge, affine-shift and reverse-label regressions. -/
def run : IO Unit := do
  unless neighbors ((0, 0) : Vertex 1) == List.replicate 8 (0, 0) do
    throw <| IO.userError "modulus one must retain all eight loop darts"
  unless neighbors ((0, 0) : Vertex 2) ==
      [(0, 0), (0, 0), (1, 0), (1, 0), (0, 0), (0, 0), (0, 1), (0, 1)] do
    throw <| IO.userError "modulus two lost a loop or a parallel dart"
  unless neighbors ((1, 1) : Vertex 3) ==
      [(0, 1), (2, 1), (1, 1), (1, 1), (1, 0), (1, 2), (1, 1), (1, 1)] do
    throw <| IO.userError "modulus three affine maps differ from the construction"
  for x in List.finRange 5 do
    for y in List.finRange 5 do
      let v : Vertex 5 := (x.val, y.val)
      for l in List.finRange 8 do
        unless step (reverseLabel l) (step l v) == v do
          throw <| IO.userError "reverse-edge correspondence failed"
        unless reverseLabel l != l do
          throw <| IO.userError "opposite loop orientations must have distinct labels"
  IO.println "Gabber–Galil: loops, parallel darts, affine maps and 200 reversals passed"

end GabberGalilTest
