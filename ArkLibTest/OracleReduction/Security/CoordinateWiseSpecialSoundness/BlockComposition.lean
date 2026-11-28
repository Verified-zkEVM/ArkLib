/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.BlockComposition
import ArkLibTest.OracleReduction.Security.CoordinateWiseSpecialSoundness.BlockStructure

/-!
# Append of structures with layouts: concrete tests

The fixtures are those of the structure test: a one-round protocol whose challenge has a first
coordinate over `ZMod 5` and a second over `ZMod 3`, thresholds `(3, 2)`, the flat structure `Dflat`
(one block, `4` children) and the nested structure `Dnested` (two blocks, `3 * 2 = 6` leaves).

`Dflat.append Dnested` has two challenge rounds. `nodeOk_inl_iff` and `nodeOk_inr_iff` read its node
predicate at each round as the tree condition of the flat and of the nested layout, by definitional
unfolding of the append. They fail if the append gives a round the other factor's layout, or reads
its challenges through anything but the factor's own identification. On concrete challenges:

* at the first round it accepts the star of the flat block and rejects a family with a repeated
  member;
* at the second round it accepts the nested tree and rejects the collapsed and the acausal family.

Swapping the factors swaps the arities. The leaf count `4 * 6 = 24` is evaluated.
-/

open CoordinateWise ProtocolSpec CoordinateWiseLayoutTest

namespace CoordinateWiseAppendTest

/-- The challenge round of `pSpec`. -/
def r : pSpec.ChallengeIdx := ⟨0, rfl⟩

/-- The two-round structure: the flat layout, then the nested one. -/
abbrev D := Dflat.append Dnested

/-- The arities are `4` and `6` in this order. -/
example : D.arity (ChallengeIdx.inl r) = 4 ∧ D.arity (ChallengeIdx.inr r) = 6 := by
  decide +kernel

/-- Swapping the factors swaps the arities. -/
example : (Dnested.append Dflat).arity (ChallengeIdx.inl r) = 6 ∧
    (Dnested.append Dflat).arity (ChallengeIdx.inr r) = 4 := by
  decide +kernel

/-- Challenges at the first round, given by a family of points of the flat block. -/
def leftChallenges (c : Fin 4 → ((u : Fin 2) → alph u))
    (q : Fin (D.arity (ChallengeIdx.inl r))) : (pSpec ++ₚ pSpec).Challenge (ChallengeIdx.inl r) :=
  c (Fin.cast (by decide +kernel) q)

/-- Challenges at the second round, given by a family of points of the nested layout. -/
def rightChallenges (c : Fin 6 → nestedLayout.Point)
    (q : Fin (D.arity (ChallengeIdx.inr r))) : (pSpec ++ₚ pSpec).Challenge (ChallengeIdx.inr r) :=
  (Layout.nestedEquiv 2 alph k).symm (c (Fin.cast (by decide +kernel) q))

/-- The first round has the flat layout and reads its challenges through `Dflat.decompose`, so its
node predicate is the tree condition of the flat layout on the family read through `Dflat`. -/
theorem nodeOk_inl_iff (c : Fin 4 → ((u : Fin 2) → alph u)) :
    D.nodeOk (ChallengeIdx.inl r) (leftChallenges c) ↔
      flatLayout.IsTree fun j => Dflat.decompose r (c j) :=
  Layout.isTree_congr rfl HEq.rfl

/-- The second round has the nested layout and reads its challenges through `Dnested.decompose`. -/
theorem nodeOk_inr_iff (c : Fin 6 → nestedLayout.Point) :
    D.nodeOk (ChallengeIdx.inr r) (rightChallenges c) ↔ nestedLayout.IsTree c := by
  refine (Layout.isTree_congr rfl ?_).trans Iff.rfl
  refine Function.hfunext rfl fun j j' hj => ?_
  cases hj
  exact heq_of_eq ((Layout.nestedEquiv 2 alph k).apply_symm_apply _)

/-- The first round accepts the star of the flat block. -/
example : D.nodeOk (ChallengeIdx.inl r) (leftChallenges star) := by
  rw [nodeOk_inl_iff]
  unfold Layout.IsTree
  decide +kernel

/-- The first round rejects a family with a repeated member. -/
example :
    ¬ D.nodeOk (ChallengeIdx.inl r) (leftChallenges ![vec 0 0, vec 1 0, vec 1 0, vec 0 1]) := by
  rw [nodeOk_inl_iff]
  unfold Layout.IsTree
  decide +kernel

/-- The second round accepts the nested tree. -/
example : D.nodeOk (ChallengeIdx.inr r) (rightChallenges nestedTree) := by
  rw [nodeOk_inr_iff]
  unfold Layout.IsTree
  decide +kernel

/-- The second round rejects the family that repeats a label below a prefix. -/
example : ¬ D.nodeOk (ChallengeIdx.inr r) (rightChallenges collapsedTree) := by
  rw [nodeOk_inr_iff]
  unfold Layout.IsTree
  decide +kernel

/-- The second round rejects the family that fails only causality. -/
example : ¬ D.nodeOk (ChallengeIdx.inr r) (rightChallenges acausalTree) := by
  rw [nodeOk_inr_iff]
  unfold Layout.IsTree
  decide +kernel

/-- info: 24 -/
#guard_msgs in
#eval D.treeSize

end CoordinateWiseAppendTest
