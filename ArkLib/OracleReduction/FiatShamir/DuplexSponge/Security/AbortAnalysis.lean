/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEvents

/-!
# Definition and analysis of aborts

This file contains the definition and analysis of aborts for the analysis of duplex sponge
Fiat-Shamir, following Section 5.7 in the paper.
-/

/- Lemma 5.17: If `E(tr) = 0`, then `StdTrace(tr)` does not abort. -/

/- Lemma 5.18: If `E(tr_𝒜) = 0`, then `𝒜 ^ D2SQuery` does not abort. -/

/- Claim 5.19: If `E_inv(tr, s) = E_prp(tr) = E_fork(tr, s) = 0`, then `backTrack(tr, s) ≠ err`. -/

/- Claim 5.20: If `E_prp(tr) = 0`, then `lookAhead(tr.p, s, i) ≠ err` for all `(s, i)`. -/
