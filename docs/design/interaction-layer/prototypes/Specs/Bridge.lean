/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Specs.Bridge.Rounds
import Specs.Bridge.Sumcheck

/-!
# The bridge from specifications to the kit

This module collects the bridge between a specification's `rounds` block and the iteration kit.

* `Specs.Bridge.Rounds`: the certificate `Bridge.cert` of a `rounds` block, the bridge theorem
  `Bridge.verdict_roundsGo` (the block's verdict is the kit's verdict), and
  `Bridge.rbrSound_of_kit` and `Bridge.sound_of_kit` (a specification is sound from the kit's
  per-round obligation `Kit.RoundSound`).
* `Specs.Bridge.Sumcheck`: the acceptance instance. `Bridge.sumcheckSpec_sound` proves soundness
  of the verifier that `sumcheckSpec` derives, with ArkLib's error `n · (d / |R|)`, through the
  bridge theorem and `Kit.sumcheck_roundSound`, without `Sumcheck.indexedVerifier`.

## Design choices

* **The generic theorems and the instance are separate modules.** *Why:* the generic module
  depends only on `Specs.Security` and the kit's iteration theorem, so other protocols can use it
  without importing sum-check.
-/

#print axioms Specs.Bridge.verdict_roundsGo
#print axioms Specs.Bridge.rbrSound_of_kit
#print axioms Specs.Bridge.sound_of_kit
#print axioms Specs.Bridge.sumcheckSpec_rbrSound
#print axioms Specs.Bridge.sumcheckSpec_sound
