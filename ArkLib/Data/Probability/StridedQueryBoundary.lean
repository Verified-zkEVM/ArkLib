/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Probability.DistinctQueries
public import ArkLib.Data.Probability.FiniteFieldBudget

/-!
# Authentication paths for queries at a power-of-two stride

Embedding leaf `i` as leaf `2^s * i` appends `s` zero bits below the original tree.
At each added level, every distinct queried leaf has an unqueried sibling. The upper
authentication paths are exactly those of the original tree. Consequently the number of
additional hashes is `s` times the number of distinct queries, not `s` times the query count.

We first prove this identity for each finite set of queried leaves, by removing one binary
level at a time. Taking the uniform expectation then uses the existing occupancy theorem.
This concerns the binary authentication boundary; it makes no claim about a serializer.
-/

@[expose] public section

namespace ArkLib.UniformQueryBoundary

open scoped BigOperators

/-- Occupied parents one level above a set of occupied binary-tree nodes. -/
def binaryParents (leaves : Finset ℕ) : Finset ℕ := leaves.image (fun i ↦ i / 2)

/-- Both children of every occupied parent. -/
def binaryChildren (parents : Finset ℕ) : Finset ℕ :=
  parents.biUnion (fun i ↦ {2 * i, 2 * i + 1})

theorem binaryChildren_card (parents : Finset ℕ) :
    (binaryChildren parents).card = 2 * parents.card := by
  unfold binaryChildren
  rw [Finset.card_biUnion]
  · simp [Nat.mul_comm]
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro x hx hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    omega

theorem subset_binaryChildren_binaryParents (leaves : Finset ℕ) :
    leaves ⊆ binaryChildren (binaryParents leaves) := by
  intro x hx
  apply Finset.mem_biUnion.mpr
  refine ⟨x / 2, Finset.mem_image.mpr ⟨x, hx, rfl⟩, ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

/-- Counting absent children gives the arithmetic used at each binary level. -/
theorem missingBinaryChildren_card (leaves : Finset ℕ) :
    (binaryChildren (binaryParents leaves) \ leaves).card =
      2 * (binaryParents leaves).card - leaves.card := by
  rw [Finset.card_sdiff_of_subset (subset_binaryChildren_binaryParents leaves),
    binaryChildren_card]

/-- Number of missing children along the authentication boundary, through `height` levels.
Every occupied parent has two children; the occupied children need no authentication hash. -/
def binaryAuthenticationCount : ℕ → Finset ℕ → ℕ
  | 0, _ => 0
  | height + 1, leaves =>
      2 * (binaryParents leaves).card - leaves.card +
        binaryAuthenticationCount height (binaryParents leaves)

/-- Embed a leaf set in the zero branch of each of `levels` additional binary levels. -/
def strideLeaves (levels : ℕ) (leaves : Finset ℕ) : Finset ℕ :=
  leaves.image (fun i ↦ 2 ^ levels * i)

theorem strideLeaves_card (levels : ℕ) (leaves : Finset ℕ) :
    (strideLeaves levels leaves).card = leaves.card := by
  apply Finset.card_image_of_injective
  exact fun _ _ h ↦ Nat.eq_of_mul_eq_mul_left (by positivity) h

theorem strideLeaves_zero (leaves : Finset ℕ) : strideLeaves 0 leaves = leaves := by
  simp [strideLeaves]

theorem binaryParents_strideLeaves_succ (levels : ℕ) (leaves : Finset ℕ) :
    binaryParents (strideLeaves (levels + 1) leaves) = strideLeaves levels leaves := by
  simp only [binaryParents, strideLeaves, Finset.image_image]
  congr 1
  funext i
  change 2 ^ (levels + 1) * i / 2 = 2 ^ levels * i
  rw [pow_succ, Nat.mul_right_comm, Nat.mul_div_cancel]
  decide

/-- The exact authentication-boundary cost of a power-of-two stride, before averaging.
If the original leaves lie below `2^height`, the strided leaves lie below
`2^(height+levels)`, so these are the corresponding finite binary trees. -/
theorem binaryAuthenticationCount_strideLeaves
    (height levels : ℕ) (leaves : Finset ℕ) :
    binaryAuthenticationCount (height + levels) (strideLeaves levels leaves) =
      binaryAuthenticationCount height leaves + levels * leaves.card := by
  induction levels with
  | zero => simp [strideLeaves_zero]
  | succ levels ih =>
    rw [Nat.add_succ, binaryAuthenticationCount, binaryParents_strideLeaves_succ,
      strideLeaves_card, strideLeaves_card, ih]
    simp only [Nat.add_mul, Nat.one_mul]
    omega

/-- Uniform expectation respects addition of natural-valued statistics. -/
theorem uniformQueryExpectation_add
    {α : Type*} [Fintype α] (t : ℕ) (f g : (Fin t → α) → ℕ) :
    uniformQueryExpectation t (fun queries ↦ f queries + g queries) =
      uniformQueryExpectation t f + uniformQueryExpectation t g := by
  simp [uniformQueryExpectation, Nat.cast_add, Finset.sum_add_distrib, add_div]

/-- Uniform expectation respects multiplication by a fixed natural number. -/
theorem uniformQueryExpectation_nat_mul
    {α : Type*} [Fintype α] (t c : ℕ) (f : (Fin t → α) → ℕ) :
    uniformQueryExpectation t (fun queries ↦ c * f queries) =
      c * uniformQueryExpectation t f := by
  simp [uniformQueryExpectation, Nat.cast_mul, ← Finset.mul_sum, mul_div_assoc]

/-- Expected authentication cost of striding uniform queries, expressed in terms of the
ordinary-tree expectation. Repeated queries contribute only once to each new bottom level. -/
theorem uniformQueryExpectation_binaryAuthenticationCount_stride
    (height levels samples domain : ℕ) (hdomain : 0 < domain) :
    uniformQueryExpectation samples
        (fun queries : Fin samples → Fin domain ↦
          binaryAuthenticationCount (height + levels)
            (strideLeaves levels (Finset.univ.image (fun i ↦ (queries i).val)))) =
      uniformQueryExpectation samples
        (fun queries : Fin samples → Fin domain ↦
          binaryAuthenticationCount height (Finset.univ.image (fun i ↦ (queries i).val))) +
        levels * (domain : ℚ) * (1 - (((domain - 1 : ℕ) : ℚ) / domain) ^ samples) := by
  have hcard (queries : Fin samples → Fin domain) :
      (Finset.univ.image (fun i ↦ (queries i).val)).card = distinctQueryCount queries := by
    rw [show (fun i ↦ (queries i).val) = Fin.val ∘ queries from rfl,
      ← Finset.image_image, Finset.card_image_of_injective _ Fin.val_injective]
    rfl
  simp_rw [binaryAuthenticationCount_strideLeaves, hcard]
  rw [uniformQueryExpectation_add, uniformQueryExpectation_nat_mul,
    uniformQueryExpectation_distinctQueryCount samples (by simpa using hdomain)]
  simp [mul_assoc]

end ArkLib.UniformQueryBoundary

namespace ArkLib.FiniteFieldBudget

/-- Authentication expectation for queries in a tree of size `domain * 2^levels`, restricted
to leaves `2^levels * i`. Here `domain` is the number of possible query positions; a complete
binary tree has `domain = 2^height`. -/
def expectedStridedAuthenticationHashes (domain height levels queries : ℕ) : ℚ :=
  expectedAuthenticationHashes domain height queries +
    levels * (domain : ℚ) * (1 - (((domain - 1 : ℕ) : ℚ) / domain) ^ queries)

/-- Any ordinary-tree expectation theorem transports to strided queries by the exact
pointwise boundary identity. The hypothesis isolates the ordinary tree's level-count model;
the stride contributes no further independence assumption. -/
theorem expectedStridedAuthenticationHashes_of_ordinary
    (domain height levels samples : ℕ) (hdomain : 0 < domain)
    (hordinary : UniformQueryBoundary.uniformQueryExpectation samples
      (fun queries : Fin samples → Fin domain ↦
        UniformQueryBoundary.binaryAuthenticationCount height
          (Finset.univ.image (fun i ↦ (queries i).val))) =
      expectedAuthenticationHashes domain height samples) :
    UniformQueryBoundary.uniformQueryExpectation samples
      (fun queries : Fin samples → Fin domain ↦
        UniformQueryBoundary.binaryAuthenticationCount (height + levels)
          (UniformQueryBoundary.strideLeaves levels
            (Finset.univ.image (fun i ↦ (queries i).val)))) =
      expectedStridedAuthenticationHashes domain height levels samples := by
  rw [UniformQueryBoundary.uniformQueryExpectation_binaryAuthenticationCount_stride
    height levels samples domain hdomain, hordinary]
  rfl

end ArkLib.FiniteFieldBudget
