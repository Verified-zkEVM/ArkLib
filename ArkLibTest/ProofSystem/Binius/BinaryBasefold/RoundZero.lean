/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Alexander Hicks
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Relations.Initial

/-!
# Binary Basefold round-zero invariants

Axiom checks for the initial-relation facts owned by the library.
-/

open Binius.BinaryBasefold

/--
info: 'Binius.BinaryBasefold.not_foldingBadEventAtBlock_of_lt' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms not_foldingBadEventAtBlock_of_lt

/--
info: 'Binius.BinaryBasefold.not_hasIncrementalBadEvent_zero' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms not_hasIncrementalBadEvent_zero

/--
info: 'Binius.BinaryBasefold.mem_roundRelation_zero_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms mem_roundRelation_zero_iff
