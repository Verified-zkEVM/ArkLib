/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Fri.Spec.Soundness
import ArkLib.ProofSystem.Fri.ErrorBounds

/-!
# Computable FRI soundness trust checks

These checks inspect proof bodies from a classic client. They protect both the exact
computable-verifier bridge and the final security theorems against admitted dependencies.
-/

/--
info: 'Fri.Spec.reduction_run' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Fri.Spec.reduction_run

/--
info: 'Fri.Spec.soundness_proximity' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Fri.Spec.soundness_proximity

/--
info: 'Fri.Spec.soundness' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Fri.Spec.soundness

/--
info: 'Fri.Spec.rbrSoundness' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Fri.Spec.rbrSoundness

/--
info: 'Fri.foldingAgreementFailure_prob_le_generalizedJohnson' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Fri.foldingAgreementFailure_prob_le_generalizedJohnson

/--
info: 'Verifier.prob_terminal_event_le_of_badEvents' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.prob_terminal_event_le_of_badEvents

/--
info: 'Verifier.soundness_of_rejection_event' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.soundness_of_rejection_event
