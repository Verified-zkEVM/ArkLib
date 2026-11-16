/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/
module

public import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Proofs.ProverTransform.Query
public import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Proofs.ProverTransform.D2SAlgo
public import
  ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Proofs.ProverTransform.RateOnly

/-!
# Prover transformation

This file contains the prover transformation (via the oracle wrapper `D2SQuery`) for the
analysis of duplex sponge Fiat-Shamir, following Section 5.4 in the paper.

Note: The paper's §5.5.2 D2STrace Step 3 `bin(τ) ∈ {0,1}^{δ_*}` salt binarization is modeled
using the `SaltCodec` class from `Defs.lean`, decoupling the FS-standard `Salt` type from
the on-sponge `Vector U δ` type.

The development is split into:

- `ProverTransform.Query` — the `D2SQuery` state, samplers, branch handlers and step.
- `ProverTransform.D2SAlgo` — the codec bridge, `D2SAlgo`, and query counting.
- `ProverTransform.RateOnly` — rate-only step normal forms (Claim 5.24).
-/
