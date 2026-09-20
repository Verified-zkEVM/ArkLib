/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import VCVio.OracleComp.QueryTracking.LoggingOracle

/-! Compatibility import for additions that now live in VCVio.

`loggingOracle.run_simulateQ_optionT_pure` and `loggingOracle.map_fst_run_simulateQ` now live in
`VCVio/OracleComp/QueryTracking/LoggingOracle/Core.lean`, which this file imports so the names keep
resolving for downstream consumers. -/
