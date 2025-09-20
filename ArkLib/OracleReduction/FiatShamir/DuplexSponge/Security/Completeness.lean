/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Defs

/-!
# Theorem about completeness

This file contains the theorem that duplex sponge Fiat-Shamir is complete, assuming the underlying
interactive protocol is complete.

(do we even have to go through basic Fiat-Shamir? any complication with handling completeness
error?)
-/
