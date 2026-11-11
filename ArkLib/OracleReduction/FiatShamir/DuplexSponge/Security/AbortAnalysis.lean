/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEvents

/-!
# Definition and analysis of aborts

This file contains the definition and analysis of aborts for the analysis of duplex sponge
Fiat-Shamir, following Section 5.7 in the paper.
-/

@[expose] public section

/- Lemma 5.17: If `E(tr) = 0`, then `StdTrace(tr)` does not abort. -/

/- Lemma 5.18: If `E(tr_𝒜) = 0`, then `𝒜 ^ D2SQuery` does not abort. -/

/- Claim 5.19 (CO25): if `E_inv(tr, s) = E_prp(tr) = E_fork(tr, s) = 0`, then
`BackTrack(tr, s) ≠ err`. This is false for `backTrackFwd`, whose `err` is a scan-time fork rather
than `|Outs| > 1`; `linearBackTrack` gives a trace with `|S_BT| ≤ 1` on which it returns `err`.
The statement to prove instead, and the one Lemmas 5.17 and 5.18 need, is
`¬E(tr) ⇒ backTrackFwd(tr, s) ≠ err`: a fork needs two forward-first pairs with equal output
capacity (`E_dup`) or two hash anchors with equal capacity (`E_h`). -/

/- Claim 5.20: If `E_prp(tr) = 0`, then `lookAhead(tr.p, s, i) ≠ err` for all `(s, i)`. -/
