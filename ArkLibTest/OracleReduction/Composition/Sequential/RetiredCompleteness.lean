/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.Composition.Sequential.OracleCompleteness

/-!
# Retired fixed-initial-state completeness contracts

These names must remain absent: their premises do not account for the shared oracle state left
by the prefix. The maintained composition interfaces require explicit shared-state hypotheses.
-/

open Lean in
run_cmd do
  let env ← getEnv
  for name in [
      `Reduction.append_completeness,
      `Reduction.append_perfectCompleteness,
      `OracleReduction.append_completeness,
      `OracleReduction.append_perfectCompleteness,
      `Reduction.seqCompose_completeness,
      `Reduction.seqCompose_perfectCompleteness,
      `OracleReduction.seqCompose_completeness,
      `OracleReduction.seqCompose_perfectCompleteness] do
    if env.contains name then
      throwError "Retired completeness declaration is present: {name}"
