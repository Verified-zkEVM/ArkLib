/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/
module

public import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Proofs.Backtrack.Basic
public import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Proofs.Backtrack.Algorithm
public import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Proofs.Backtrack.HonestChain
public import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Proofs.Backtrack.Converse

/-!
# Backtracking sequence family and procedure

Re-exports the [CO25, §5.2] `BackTrack` development:

- `Backtrack.Basic` — `BacktrackSequence`, `S_BT`, the linear scan and the sponge-walk vocabulary.
- `Backtrack.Algorithm` — candidate extraction, `backTrack` and `backTrackFwd`.
- `Backtrack.HonestChain` — the positive direction on honest chains.
- `Backtrack.Converse` — the certificate a successful `BackTrack` carries.
-/
