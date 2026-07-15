/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.Infrastructure
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.Hash
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.PermForward
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.PermInverse
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.Function

/-!
# Paper-facing Lemma 5.8 reductions

This upper layer follows the four predicates of CO25 Lemma 5.8.  Each module
reduces its paper event to named contracts supplied by `Infrastructure`; the
final façade assembles those reductions with the common union bound.
-/
