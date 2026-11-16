/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Defs
public import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Nondegeneracy
public import ArkLib.OracleReduction.FiatShamir.DuplexSponge.QueryBounds
public import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Proofs.Backtrack
public import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Proofs.Lookahead
public import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Proofs.ProverTransform
public import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Proofs.TraceTransform
public import
  ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Proofs.ZeroKnowledge.SimulationReduction
public import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Salted

/-!
# Duplex sponge Fiat–Shamir (umbrella)

This module exposes one canonical DSFS construction parameterized by salt length.
`Security/Salted.lean` re-exports its perfect-completeness theorem for arbitrary salt lengths.
Supporting execution and completeness arguments live under `Security/Proofs/`.
The initial-object modules provide the separate initial-object runner and its query bounds.
Downstream code may import specific leaf modules to keep dependencies narrow.
-/

@[expose] public section
