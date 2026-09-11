/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Matrix.QuadraticForwardEchelonRefinement

/-!
# Kernel checks for coordinate forward-echelon execution

Full runs exercise a skipped column, nontrivial RHS elimination, pivot movement and ordered
multiple pivots. Empty/zero-width input retains residual RHS values. Malformed returns and
partial child/store states expose rejection, wrappers, indices and allocation charges.
-/

@[expose] public section

namespace Matrix.QuadraticForwardEchelonMachine

private instance : DecidableEq (Row (ZMod 3)) := inferInstance
private instance : DecidableEq (Pivot (ZMod 3)) := inferInstance

private def observe : Configuration (ZMod 3) →
    Option (List (Pivot (ZMod 3)) × List (Row (ZMod 3)))
  | .ready (.done ps rest) => some (ps, rest)
  | _ => none

private def rejected : Configuration (ZMod 3) → Bool
  | .ready .rejected => true
  | _ => false

private def skipped := runFuel (2 : ZMod 3) 228 (.ready (.loop 0 2
  [([(0, 0), (1, 1)], (2, 1)), ([(0, 0), (2, 1)], (1, 2))] []))

example : (observe skipped.1, skipped.2) =
    (some ([(1, ([(0, 0), (1, 1)], (2, 1)))], [([(0, 0), (0, 0)], (2, 0))]),
      ⟨⟨15, 25, 4, 1, 10, 999, 2706, 150, 21⟩, 23⟩) := by decide +kernel

private def multiple := runFuel (2 : ZMod 3) 252 (.ready (.loop 0 2
  [([(0, 0), (0, 1)], (1, 2)), ([(1, 1), (2, 0)], (2, 1))] []))

example : (observe multiple.1, multiple.2) =
    (some ([(0, ([(1, 1), (2, 0)], (2, 1))), (1, ([(0, 0), (0, 1)], (1, 2)))], []),
      ⟨⟨15, 25, 4, 1, 12, 1069, 2922, 162, 24⟩, 25⟩) := by decide +kernel

private def noColumns := runFuel (2 : ZMod 3) 2 (.ready (.loop 0 0 [([], (1, 2))] []))

example : (observe noColumns.1, noColumns.2) =
    (some ([], [([], (1, 2))]), ⟨⟨0, 0, 0, 0, 0, 2, 7, 0, 1⟩, 1⟩) := by decide +kernel

private def empty := runFuel (2 : ZMod 3) 12 (.ready (.loop 0 2 [] []))

example : (observe empty.1, empty.2) =
    (some ([], []), ⟨⟨0, 0, 0, 0, 0, 18, 47, 0, 3⟩, 7⟩) := by decide +kernel

private def malformed := runFuel (2 : ZMod 3) 4 (.ready (.loop 0 1 [([], (1, 2))] []))

example : (rejected malformed.1, malformed.2) =
    (true, ⟨⟨0, 0, 0, 0, 0, 6, 18, 0, 2⟩, 2⟩) := by decide +kernel

theorem malformed_selection_return_is_rejected :
    (match (runFuel (2 : ZMod 3) 1 (.select 0 0 [] (.ready (.done true [])))).1 with
    | .ready .rejected => true
    | _ => false) =
    true := by decide +kernel

example : rejected (runFuel (2 : ZMod 3) 1 (.eliminate 0 0 [] (.ready (.done [])))).1 =
    true := by decide +kernel

private def pending : Configuration (ZMod 3) → Bool
  | .select _ _ _ (.ready (.restore none [] [])) => true
  | _ => false

private def child := runFuel (2 : ZMod 3) 1 (.select 0 0 [] (.ready (.scan [] [])))

example : (pending child.1, child.2) =
    (true, ⟨⟨0, 0, 0, 0, 0, 2, 4, 0, 0⟩, 0⟩) := by decide +kernel

private def indices : Configuration (ZMod 3) → Option (ℕ × List ℕ)
  | .ready (.loop j _ _ rev) => some (j, rev.map Prod.fst)
  | _ => none

private def stored := runFuel (2 : ZMod 3) 1
  (.eliminate 3 0 [] (.ready (.done [([(1, 1)], (2, 0))])))

example : (indices stored.1, stored.2) =
    (some (4, [3]), ⟨⟨0, 0, 0, 0, 0, 1, 10, 0, 0⟩, 1⟩) := by decide +kernel

private def finishedIndices : Configuration (ZMod 3) → Option (List ℕ)
  | .ready (.done ps _) => some (ps.map Prod.fst)
  | _ => none

private def reversed := runFuel (2 : ZMod 3) 3 (.ready (.reverse
  [(2, ([(0, 1)], (2, 1))), (0, ([(1, 1)], (1, 0)))] [] []))

example : (finishedIndices reversed.1, reversed.2) =
    (some [0, 2], ⟨⟨0, 0, 0, 0, 0, 3, 15, 0, 1⟩, 0⟩) := by decide +kernel

end Matrix.QuadraticForwardEchelonMachine
