/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import ArkLib.ProofSystem.Fri.Spec.KnowledgeSoundness
import ArkLib.ProofSystem.Fri.Spec.Extraction.ClosedCost
import ArkLib.ProofSystem.Fri.Spec.MeasuredKnowledgeSoundness

/-!
# Certified FRI extractor acceptance checks

Classic clients inspect proof dependencies for the concrete extractor, its recovery guarantees,
its all-input logged knowledge game, its complete-program resource bounds, and the game packaged
with those bounds. Compiled small histories are checked separately by
`scripts/FriExtractorRuntime.lean`.
-/

/--
info: 'Fri.Spec.Extractor.extract' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Fri.Spec.Extractor.extract

/--
info: 'Fri.Spec.Extractor.extractHistory_eq_profile' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Fri.Spec.Extractor.extractHistory_eq_profile

/--
info: 'Fri.Spec.Extractor.extract_eq_of_queryPrefix_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Fri.Spec.Extractor.extract_eq_of_queryPrefix_eq

/--
info: 'Fri.Spec.Extractor.extractHistory_eq_some_of_safeHistory' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Fri.Spec.Extractor.extractHistory_eq_some_of_safeHistory

/--
info: 'Fri.Spec.Extractor.extractHistory_eq_some_of_density' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Fri.Spec.Extractor.extractHistory_eq_some_of_density

/--
info: 'Fri.Spec.knowledge_soundness_with' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Fri.Spec.knowledge_soundness_with

/--
info: 'Fri.Spec.knowledge_soundness' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Fri.Spec.knowledge_soundness

/--
info: 'Verifier.knowledgeSoundnessWith_of_transcript_event' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.knowledgeSoundnessWith_of_transcript_event

/--
info: 'Fri.Spec.Extractor.profile_extractProgram_word_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Fri.Spec.Extractor.profile_extractProgram_word_le

/--
info: 'Fri.Spec.Extractor.profile_extractProgram_apply_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Fri.Spec.Extractor.profile_extractProgram_apply_le

/--
info: 'Fri.Spec.Extractor.profile_extractProgram_inv_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Fri.Spec.Extractor.profile_extractProgram_inv_le

/--
info: 'Fri.Spec.Extractor.profile_extractProgram_domainRead_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Fri.Spec.Extractor.profile_extractProgram_domainRead_le

/--
info: 'Fri.Spec.Extractor.profile_extractProgram_challengeRead_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Fri.Spec.Extractor.profile_extractProgram_challengeRead_le

/--
info: 'Fri.Spec.Extractor.profile_extractProgram_finalPolynomialRead' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Fri.Spec.Extractor.profile_extractProgram_finalPolynomialRead

/--
info: 'Fri.Spec.Extractor.profile_extractProgram_add_sub_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Fri.Spec.Extractor.profile_extractProgram_add_sub_le

/--
info: 'Fri.Spec.Extractor.profile_extractProgram_mul_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Fri.Spec.Extractor.profile_extractProgram_mul_le

/--
info: 'Fri.Spec.Extractor.profile_extractProgram_eq_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Fri.Spec.Extractor.profile_extractProgram_eq_le

/--
info: 'Fri.Spec.knowledgeSoundnessWithResources_extract' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Fri.Spec.knowledgeSoundnessWithResources_extract
