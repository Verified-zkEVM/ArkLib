/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.OracleReduction.Composition.Sequential.Append.Basic
public import ArkLib.OracleReduction.Composition.Sequential.Append.StateFunction
public import ArkLib.OracleReduction.Composition.Sequential.Append.Execution
public import ArkLib.OracleReduction.Composition.Sequential.Append.Simulation
public import ArkLib.OracleReduction.Composition.Sequential.Append.Completeness
public import ArkLib.OracleReduction.Composition.Sequential.Append.OneMessage
public import ArkLib.OracleReduction.Composition.Sequential.Append.RoundByRound
public import ArkLib.OracleReduction.Composition.Sequential.Append.Security

/-!
  # Sequential Composition of Two (Oracle) Reductions

  This is the umbrella module for the sequential composition of two (oracle) reductions. For
  composition to be valid, we need that the output context (statement + oracle statement + witness)
  for the first (oracle) reduction is the same as the input context for the second.

  The composition logic for `ProtocolSpec` and its associated structures lives in
  `ProtocolSpec/SeqCompose.lean`; we use the definitions from there.

  * `Append.Basic` — the `append` operations themselves, plus challenge-sampling transport.
  * `Append.StateFunction` — composition of extractors and verifier state functions.
  * `Append.Execution` — running appended provers / verifiers, with explicit seam conditions.
  * `Append.Simulation` — exact simulated execution, preserving the shared oracle state.
  * `Append.Completeness` — completeness from simulated factorization and state-uniform suffixes.
  * `Append.OneMessage` — the effectful-prover, one-message completeness specialization.
  * `Append.RoundByRound` — soundness from fixed-prefix bounds under a pure first verifier.
  * `Append.Security` — legacy admitted soundness claims and their inherited wrappers.
-/

@[expose] public section
