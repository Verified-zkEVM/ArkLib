/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Sumcheck.Spec.SingleRound

/-!
# Sumcheck composition certificate trust checks

The output-purity and guarded-verifier certificates are independent of the remaining admitted
context-completeness theorem. Each certificate depends only on the standard axioms.
-/

/--
info: 'Sumcheck.Spec.SingleRound.Simple.instOutputIsPureProver' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Sumcheck.Spec.SingleRound.Simple.instOutputIsPureProver

/--
info: 'Sumcheck.Spec.SingleRound.Simple.verifierGuardedForm' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Sumcheck.Spec.SingleRound.Simple.verifierGuardedForm

/--
info: 'Sumcheck.Spec.SingleRound.instOutputIsPureReduction' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Sumcheck.Spec.SingleRound.instOutputIsPureReduction

/--
info: 'Sumcheck.Spec.SingleRound.verifierGuardedForm' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Sumcheck.Spec.SingleRound.verifierGuardedForm
