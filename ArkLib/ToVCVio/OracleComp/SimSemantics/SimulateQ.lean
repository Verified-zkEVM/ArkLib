/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
import VCVio.OracleComp.SimSemantics.StateT.Basic
import ToMathlib.Control.StateT

/-! Compatibility import for additions that now live in VCVio.

`simulateQ_randomOracle_map_uniformFin` now lives in
`VCVio/OracleComp/QueryTracking/RandomOracle/Simulation.lean`, which this file imports so the name
keeps resolving for downstream consumers.

Worth knowing when deduplicating against VCVio: the local copy was identical in statement and proof,
yet no "already declared" error ever fired, because the two sat at root scope in *different* modules
— nothing imported both at once. A green build therefore does not certify the absence of duplicates;
names must also be checked against the dependency's sources directly. -/
