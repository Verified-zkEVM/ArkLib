/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

import ArkLib.Data.CodingTheory.ReedMuller.AffineCombiner.Theorem

/-!
# Acceptance cases for the Reed–Muller affine MCA bound

The general count has no sampler or concrete-field assumptions.
-/

/-- info: 'ReedMuller.exists_affineExceptional_finset_card_le_of_interpolation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.exists_affineExceptional_finset_card_le_of_interpolation

/-- info: 'ReedMuller.affineMcaError_le_of_interpolation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.affineMcaError_le_of_interpolation
