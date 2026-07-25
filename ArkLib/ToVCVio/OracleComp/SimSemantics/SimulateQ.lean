/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
import VCVio.OracleComp.SimSemantics.StateT.Basic
import ToMathlib.Control.StateT

/-! Compatibility import for additions that now live in VCVio.

`simulateQ_randomOracle_map_uniformFin` was upstreamed verbatim (statement and proof) to
`VCVio/OracleComp/QueryTracking/RandomOracle/Simulation.lean`, which this file now imports so the
name keeps resolving for downstream consumers. The local copy escaped the v4.31.0 dedup pass only
because it and its upstream twin sit at root scope in *different* modules — this file imported
`RandomOracle/Basic`, never `RandomOracle/Simulation`, so the two never met and no
"already declared" error fired. -/
