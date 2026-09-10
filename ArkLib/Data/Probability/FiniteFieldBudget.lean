/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Probability.UniformQueryBoundary

/-!
# Exact finite-field error and payload budgets

This module records the elementary arithmetic shared by concrete coding applications.  The
predicates are deliberately local: each compares one modeled error term with `2^-security`.
They do not compose those terms into a protocol theorem.

The query predicate includes an inclusive grinding threshold.  The OOD predicate is the union
bound for an unordered pair from a list after repeated independent extension-field samples.
The tensor predicate combines a height-dependent exceptional-set term with two polynomial-identity
terms. The remaining definitions give raw byte accounting for uniformly sampled Merkle leaves.
-/

@[expose] public section

namespace ArkLib.FiniteFieldBudget

open scoped BigOperators
open UniformQueryBoundary

/-- Exact cross-multiplied query inequality with an inclusive grinding threshold. -/
def QueryMeetsTarget (nonceSpace threshold agreement domain queries security : ℕ) : Prop :=
  (threshold + 1) * agreement ^ queries * 2 ^ security ≤
    nonceSpace * domain ^ queries

/-- The strict converse of `QueryMeetsTarget` for a fixed row. -/
def QueryFailsTarget (nonceSpace threshold agreement domain queries security : ℕ) : Prop :=
  nonceSpace * domain ^ queries <
    (threshold + 1) * agreement ^ queries * 2 ^ security

/-- Repeated OOD collision union bound for an unordered pair from a finite list. -/
def RepeatedOodMeetsTarget
    (listSize vectorSize fieldSize samples security : ℕ) : Prop :=
  listSize * (listSize - 1) * (vectorSize - 1) ^ samples * 2 ^ security ≤
    2 * fieldSize ^ samples

/-- Height-`h` levelwise tensor bad-count plus two identity tests, cross-multiplied exactly. -/
def TensorFoldIdentityMeetsTarget
    (height exceptionalCount listSize fieldSize security : ℕ) : Prop :=
  (height * exceptionalCount + 2 * listSize) * 2 ^ security ≤ fieldSize

/-- One full-set line-transfer exceptional count, kept apart from tensor folding. -/
def LineTransferMeetsTarget (exceptionalCount fieldSize security : ℕ) : Prop :=
  exceptionalCount * 2 ^ security ≤ fieldSize

/-- Union bound for a fixed number of field-collision terms. Independence is not needed. -/
def FieldCollisionMeetsTarget (count fieldSize security : ℕ) : Prop :=
  count * 2 ^ security ≤ fieldSize

/-- Combination of a source opening with a target list after the target OOD samples. -/
def TransitionMeetsTarget
    (sourceQueries targetOod targetListSize fieldSize security : ℕ) : Prop :=
  2 * (sourceQueries + targetOod) * targetListSize * 2 ^ security ≤ fieldSize

/-- An algebraic bad-set count after `grindingBits` bits of ideal uniform grinding. -/
def GroundCountMeetsTarget
    (count fieldSize grindingBits security : ℕ) : Prop :=
  count * 2 ^ security ≤ 2 ^ grindingBits * fieldSize

/-- Exact raw saving in a fixed per-query payload model, after charging extra bytes. -/
def fixedPayloadSaving
    (oldQueries newQueries bytesPerQuery extraBytes : ℕ) : ℕ :=
  (oldQueries - newQueries) * bytesPerQuery - extraBytes

/-- Conservative raw saving when each removed query may add one authentication hash. -/
def conservativePayloadSaving
    (oldQueries newQueries rowBytes hashBytes extraOodBytes : ℕ) : ℕ :=
  fixedPayloadSaving oldQueries newQueries (rowBytes - hashBytes) extraOodBytes

/-- Expected authentication hashes in the binary sibling-boundary model. -/
def expectedAuthenticationHashes (n height queries : ℕ) : ℚ :=
  ∑ j ∈ Finset.range height,
    (n / 2 ^ j : ℕ) *
      ((((n - 2 ^ j : ℕ) : ℚ) / n) ^ queries -
        (((n - 2 ^ (j + 1) : ℕ) : ℚ) / n) ^ queries)

/-- Expected raw byte saving after query rows, authentication hashes, and extra OOD values. -/
def expectedPayloadSaving (n height oldQueries newQueries rowBytes hashBytes
    extraOodBytes : ℕ) : ℚ :=
  ((oldQueries - newQueries) * rowBytes : ℕ) +
    hashBytes *
      (expectedAuthenticationHashes n height oldQueries -
        expectedAuthenticationHashes n height newQueries) -
    extraOodBytes

/-- The finite-sample theorem justifying one level of the expected authentication formula. -/
theorem expected_level_authentication_hashes
    {alpha node : Type*} [Fintype alpha] [Fintype node] [DecidableEq alpha]
    {queries s b : ℕ} (subtree sibling : node → Finset alpha)
    (hnonempty : 0 < Fintype.card alpha) (hnodes : Fintype.card node = b)
    (hsubtree : ∀ v, (subtree v).card = s)
    (hsibling : ∀ v, (sibling v).card = s)
    (hdisjoint : ∀ v, Disjoint (subtree v) (sibling v)) :
    uniformQueryExpectation queries (authenticationHashCount subtree sibling) =
      (b : ℚ) * ((((Fintype.card alpha - s : ℕ) : ℚ) /
          Fintype.card alpha) ^ queries -
        (((Fintype.card alpha - 2 * s : ℕ) : ℚ) /
          Fintype.card alpha) ^ queries) := by
  exact uniformQueryExpectation_authenticationHashCount_of_uniformSize_probability
    subtree sibling hnonempty hnodes hsubtree hsibling hdisjoint

end ArkLib.FiniteFieldBudget
