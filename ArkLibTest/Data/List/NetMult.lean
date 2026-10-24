/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
import ArkLib.Data.List.NetMult
import Mathlib.Data.ZMod.Defs

/-!
# Net multiplicity runtime checks

Ordinary callers compute net multiplicities and witness multiplicities at runtime.

The expected values are counted by hand.

The tables include duplicate entries, and the queries include values outside the table.
-/

namespace ArkLibTest.NetMult

/-- A lookup witness in ZMod 7, computed by an ordinary caller. -/
private def witness (f t : List ℕ) : List (ZMod 7) :=
  List.lastMults (ZMod 7) f t

private def check (ok : Bool) (msg : String) : IO Unit :=
  unless ok do throw (IO.userError msg)

-- This ordinary caller requires generated code for the public list API.
private def netMultRuntimeChecks : IO Unit := do
  -- Net multiplicities sum per key; an absent key gets zero.
  check (List.netMult [(1, 2), (2, 3), (1, 4)] 1 = 6) "Incorrect net multiplicity of key 1"
  check (List.netMult [(1, 2), (2, 3), (1, 4)] 2 = 3) "Incorrect net multiplicity of key 2"
  check (List.netMult [(1, 2), (2, 3), (1, 4)] 5 = 0) "Absent key has nonzero multiplicity"
  -- Opposite multiplicities balance in ZMod 7.
  check (List.netMult [(1, (3 : ZMod 7)), (1, 4)] 1 = 0) "Opposite multiplicities do not cancel"
  -- Queries 1, 1, 2 against table 1, 2, 1, 3: the duplicate 1 carries the count once.
  check (List.lastMults ℕ [1, 1, 2] [1, 2, 1, 3] = [0, 1, 2, 0])
    "Incorrect witness over a table with a duplicate entry"
  check (witness [1, 1, 2] [1, 2, 1, 3] = [0, 1, 2, 0])
    "Incorrect witness in ZMod 7 over a table with a duplicate entry"
  -- The net multiplicity of each table value is its query count.
  check (List.netMult ([1, 2, 1, 3].zip (witness [1, 1, 2] [1, 2, 1, 3])) 1 = 2)
    "Duplicate table value does not carry its query count"
  check (List.netMult ([1, 2, 1, 3].zip (witness [1, 1, 2] [1, 2, 1, 3])) 3 = 0)
    "Unqueried table value carries a nonzero multiplicity"
  -- A query outside the table gets no multiplicity.
  check (witness [4, 4] [1, 2] = [0, 0]) "Query outside the table gets a multiplicity"
  -- Seven equal queries wrap to zero in ZMod 7.
  check (witness (List.replicate 7 1) [1] = [0]) "Seven queries do not wrap in ZMod 7"
  -- One multiplicity per table entry, all on the last copy of a repeated value.
  check (witness [2] [2, 2, 2] = [0, 0, 1]) "Incorrect witness over a repeated table"
  IO.println "Net multiplicity runtime checks passed."

/-- info: Net multiplicity runtime checks passed. -/
#guard_msgs in
#eval netMultRuntimeChecks

end ArkLibTest.NetMult
