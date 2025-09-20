/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.KeyLemma

/-!
# Theorems about soundness and knowledge soundness

This file contains the main theorems that soundness and knowledge soundness of duplex sponge
Fiat-Shamir reduces to that of basic Fiat-Shamir, following Section 6 in the paper.

This relies on the key lemma (Lemma 5.1 in the paper).
-/
