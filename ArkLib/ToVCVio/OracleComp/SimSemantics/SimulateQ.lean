/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
import VCVio.OracleComp.SimSemantics.StateT.Basic
import ArkLib.ToVCVio.ToMathlib.Control.StateT

/-!
# Additions to VCVio's `OracleComp.SimSemantics.SimulateQ`
-/

open OracleSpec OracleComp

/-- Simulating the random oracle leaves a mapped uniform `Fin` sample unchanged. -/
lemma simulateQ_randomOracle_map_uniformFin {α : Type} (n : ℕ) (f : Fin (n + 1) → α) :
    ((simulateQ (unifSpec.randomOracle :
      QueryImpl unifSpec (StateT unifSpec.QueryCache ProbComp))
      (f <$> uniformSample (Fin (n + 1)) : ProbComp α) :
        StateT unifSpec.QueryCache ProbComp α).run' ∅) =
      (f <$> uniformSample (Fin (n + 1))) := by
  rw [simulateQ_map, StateT.run'_map_comm]
  congr 1
