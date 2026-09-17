/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen
-/
module

public import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEvents.Core

/-!
# DSFS bad events

Public façade for the CO25 Section 5 bad-event definitions and their proved deterministic
consequences. The probabilistic Lemma 5.8 statement is deferred to a later proof-focused PR.
-/

@[expose] public section
