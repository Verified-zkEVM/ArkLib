/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Composition.Sequential.Append.Basic
import ArkLib.OracleReduction.Composition.Sequential.Append.StateFunction
import ArkLib.OracleReduction.Composition.Sequential.Append.Execution
import ArkLib.OracleReduction.Composition.Sequential.Append.Security

/-!
  # Sequential Composition of Two (Oracle) Reductions

  This is the umbrella module for the sequential composition of two (oracle) reductions. For
  composition to be valid, we need that the output context (statement + oracle statement + witness)
  for the first (oracle) reduction is the same as the input context for the second.

  The composition logic for `ProtocolSpec` and its associated structures lives in
  `ProtocolSpec/SeqCompose.lean`; we use the definitions from there.

  * `Append.Basic` — the `append` operations themselves, plus challenge-sampling transport.
  * `Append.StateFunction` — composition of extractors and verifier state functions.
  * `Append.Execution` — running an appended prover / verifier, and `Prover.append_run`.
  * `Append.Security` — completeness and soundness of the composition.
-/
