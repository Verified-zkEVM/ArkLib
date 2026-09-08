/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Commitments.Functional.Hachi.Params

/-!
# Hachi completeness and correctness axiom boundaries

The nonrecursive chain retains its current public hypotheses and protocol definitions while using
proved state-aware composition. These assertions protect all nine migrated declarations, their
verifier certificates, and the completeness/soundness relation alignment at the supported profile.
-/

/--
info: 'ArkLib.Lattices.Ajtai.InnerOuter.roundsReductionAux_perfectCompleteness' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ArkLib.Lattices.Ajtai.InnerOuter.roundsReductionAux_perfectCompleteness

/--
info: 'ArkLib.Lattices.Ajtai.InnerOuter.roundsReduction_perfectCompleteness' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ArkLib.Lattices.Ajtai.InnerOuter.roundsReduction_perfectCompleteness

/--
info: 'ArkLib.Lattices.Ajtai.InnerOuter.sumcheckReduction_perfectCompleteness' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ArkLib.Lattices.Ajtai.InnerOuter.sumcheckReduction_perfectCompleteness

/--
info: 'ArkLib.Lattices.Ajtai.InnerOuter.completePrefixReduction_perfectCompleteness'
depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ArkLib.Lattices.Ajtai.InnerOuter.completePrefixReduction_perfectCompleteness

/--
info: 'ArkLib.Lattices.Ajtai.InnerOuter.completeThroughSumcheckReduction_perfectCompleteness'
depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ArkLib.Lattices.Ajtai.InnerOuter.completeThroughSumcheckReduction_perfectCompleteness

/--
info: 'ArkLib.Lattices.Ajtai.InnerOuter.nonrecursiveOpeningReduction_perfectCompleteness'
depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ArkLib.Lattices.Ajtai.InnerOuter.nonrecursiveOpeningReduction_perfectCompleteness

/--
info: 'ArkLib.Lattices.Ajtai.InnerOuter.hachiNonrecursiveOpening_perfectCompleteness'
depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ArkLib.Lattices.Ajtai.InnerOuter.hachiNonrecursiveOpening_perfectCompleteness

/--
info: 'ArkLib.Lattices.Ajtai.InnerOuter.hachiNonrecursive_perfectCorrectness' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ArkLib.Lattices.Ajtai.InnerOuter.hachiNonrecursive_perfectCorrectness

/--
info: 'ArkLib.Lattices.Ajtai.InnerOuter.hachiNonrecursiveConcrete_perfectCorrectness'
depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ArkLib.Lattices.Ajtai.InnerOuter.hachiNonrecursiveConcrete_perfectCorrectness

/--
info: 'ArkLib.Lattices.Ajtai.InnerOuter.roundsReductionAuxGuardedForm' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ArkLib.Lattices.Ajtai.InnerOuter.roundsReductionAuxGuardedForm

/--
info: 'ArkLib.Lattices.Ajtai.InnerOuter.sumcheckReductionGuardedForm' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ArkLib.Lattices.Ajtai.InnerOuter.sumcheckReductionGuardedForm

/--
info: 'ArkLib.Lattices.Ajtai.InnerOuter.completePrefixReductionPureForm' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ArkLib.Lattices.Ajtai.InnerOuter.completePrefixReductionPureForm

/--
info: 'ArkLib.Lattices.Ajtai.InnerOuter.completePrefixReduction_outputIsPure' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ArkLib.Lattices.Ajtai.InnerOuter.completePrefixReduction_outputIsPure

/--
info: 'ArkLib.Lattices.Ajtai.InnerOuter.completeThroughSumcheckReductionGuardedForm'
depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ArkLib.Lattices.Ajtai.InnerOuter.completeThroughSumcheckReductionGuardedForm

/--
info: 'ArkLib.Lattices.Ajtai.InnerOuter.nonrecursiveTerminalReductionGuardedForm' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ArkLib.Lattices.Ajtai.InnerOuter.nonrecursiveTerminalReductionGuardedForm

/--
info: 'ArkLib.Lattices.Ajtai.InnerOuter.nonrecursiveOpeningReductionGuardedForm' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ArkLib.Lattices.Ajtai.InnerOuter.nonrecursiveOpeningReductionGuardedForm

/--
info: 'ArkLib.Lattices.Ajtai.InnerOuter.HachiParams.packageAtProfile_relOut' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ArkLib.Lattices.Ajtai.InnerOuter.HachiParams.packageAtProfile_relOut

/--
info:
'ArkLib.Lattices.Ajtai.InnerOuter.HachiParams.relInMsgShort_atProfile_subset_packageAtProfile_relIn'
depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  ArkLib.Lattices.Ajtai.InnerOuter.HachiParams.relInMsgShort_atProfile_subset_packageAtProfile_relIn
