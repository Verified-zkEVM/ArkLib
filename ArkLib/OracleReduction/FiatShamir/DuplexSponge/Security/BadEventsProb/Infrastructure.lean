/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.CapacityTargets
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.PrefixEvents
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.SpongeTrace
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.Representatives
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.PermTraceFacts
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.PermCausality
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.PermNoReplacement
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.HashCredit
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.HashStopping
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.PermInverseCredit
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.FunctionInvariant
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.Foundational

/-!
# Operational infrastructure for the DSFS Lemma 5.8 proof

This is the infrastructure component of the Lemma 5.8 development.  It contains no final
paper-facing event bound.  Instead it packages the reusable work needed by
those bounds:

* probability and finite-target accounting;
* base-trace representatives and permutation-table invariants;
* eager-sponge trace facts and lazy-simulator state bridges; and
* the two explicitly isolated simulator contracts which remain open.

The files `Hash`, `PermForward`, `PermInverse`, and `Function` form the upper,
paper-specific layer.  They should import this module rather than selecting
individual implementation modules.  This mirrors the `ToVCVio/Lemmas` /
`ToVCVio/Simulation` split used in `arklib-binius`.
-/
