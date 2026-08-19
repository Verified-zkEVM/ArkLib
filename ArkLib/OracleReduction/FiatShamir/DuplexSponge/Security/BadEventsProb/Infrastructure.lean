/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/


import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.Core
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.PermNoReplacement
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.PrefixEvents

/-!
# Operational infrastructure for the DSFS Lemma 5.8 proof

This is the infrastructure component of the Lemma 5.8 development.  It contains no final
paper-facing event bound.  Instead it packages the reusable work needed by
those bounds:

* probability and finite-target accounting;
* base-trace representatives and permutation-table invariants;
* eager-sponge trace facts and the stateful first-event bridges.

The files `Hash`, `PermForward`, `PermInverse`, and `Function` form the upper,
paper-specific layer.  They should import this module rather than selecting
individual implementation modules.  This mirrors the `ToVCVio/Lemmas` /
`ToVCVio/Simulation` split used in `arklib-binius`.
-/
