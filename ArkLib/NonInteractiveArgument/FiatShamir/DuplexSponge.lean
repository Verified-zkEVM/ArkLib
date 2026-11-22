/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.NonInteractiveArgument.FiatShamir.DuplexSponge.Construction
public import ArkLib.NonInteractiveArgument.FiatShamir.DuplexSponge.Nondegeneracy
public import ArkLib.NonInteractiveArgument.FiatShamir.DuplexSponge.Completeness

/-!
# Duplex sponge Fiat–Shamir (umbrella)

This module exposes one canonical DSFS construction parameterized by salt length.
`Completeness.lean` states perfect completeness for arbitrary salt lengths.
Supporting arguments live in `Security/Proofs/` and `Completeness/Perfect.lean`.
Downstream code may import specific leaf modules to keep dependencies narrow.
-/

@[expose] public section
