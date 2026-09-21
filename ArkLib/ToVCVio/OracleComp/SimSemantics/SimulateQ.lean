/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks, Cody Gunton, Quang Dao, Tobias Rothmann
-/
module

public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
public import VCVio.OracleComp.SimSemantics.OptionT.Basic
public import VCVio.OracleComp.SimSemantics.StateT.Basic

/-! Compatibility import for additions that now live in VCVio.

`simulateQ_randomOracle_map_uniformFin` now lives in
`VCVio/OracleComp/QueryTracking/RandomOracle/Simulation.lean` and `simulateQ_optionT_pure` in
`VCVio/OracleComp/SimSemantics/OptionT/Basic.lean`; this file imports both so the names keep
resolving for downstream consumers.

Worth knowing when deduplicating against VCVio: the local copy was identical in statement and proof,
yet no "already declared" error ever fired, because the two sat at root scope in *different* modules
— nothing imported both at once. A green build therefore does not certify the absence of duplicates;
names must also be checked against the dependency's sources directly. -/

@[expose] public section

open OracleComp
