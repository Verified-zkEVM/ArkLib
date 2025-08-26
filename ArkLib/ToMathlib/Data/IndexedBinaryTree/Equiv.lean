import ArkLib.ToMathlib.Data.IndexedBinaryTree.Basic


/-!
# Equivalences

This section contains theorems about equivalences between different tree indexing types
and data structures.
-/

namespace BinaryTree

section Equivalences

/-- `LeafData`s are equivalent to functions from `SkeletonLeafIndex` to values -/
def LeafData.EquivIndexFun {α : Type} (s : Skeleton) :
    LeafData α s ≃ (SkeletonLeafIndex s → α) where
  toFun := fun tree idx => tree.get idx
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

/-- `InternalData`s are equivalent to functions from `SkeletonInternalIndex` to values -/
def InternalData.EquivIndexFun {α : Type} (s : Skeleton) :
    InternalData α s ≃ (SkeletonInternalIndex s → α) where
  toFun := fun tree idx => tree.get idx
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

/-- `FullData`s are equivalent to functions from `SkeletonNodeIndex` to values -/
def FullData.EquivIndexFun {α : Type} (s : Skeleton) :
    FullData α s ≃ (SkeletonNodeIndex s → α) where
  toFun := fun tree idx => tree.get idx
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

/-- A `LeafData` can be interpreted as a function from `SkeletonLeafIndex` to values -/
instance {α : Type} {s : Skeleton} :
    CoeFun (LeafData α s) fun (_ : LeafData α s) => SkeletonLeafIndex s → α where
  coe := fun tree idx => tree.get idx

/-- An `InternalData` can be interpreted as a function from `SkeletonInternalIndex` to values -/
instance {α : Type} {s : Skeleton} :
    CoeFun (InternalData α s) fun (_ : InternalData α s) => SkeletonInternalIndex s → α where
  coe := fun tree idx => tree.get idx

/-- A `FullData` can be interpreted as a function from `SkeletonNodeIndex` to values -/
instance {α : Type} {s : Skeleton} :
    CoeFun (FullData α s) fun (_ : FullData α s) => SkeletonNodeIndex s → α where
  coe := fun tree idx => tree.get idx

/--
A function taking a `SkeletonNodeIndex s`
to either a `SkeletonInternalIndex s` or a `SkeletonLeafIndex s`
-/
def SkeletonNodeIndex.toSum {s : Skeleton} :
    SkeletonNodeIndex s → SkeletonInternalIndex s ⊕ SkeletonLeafIndex s :=
  fun idx =>
    match idx with
    | SkeletonNodeIndex.ofLeaf => Sum.inr (SkeletonLeafIndex.ofLeaf)
    | SkeletonNodeIndex.ofInternal => Sum.inl (SkeletonInternalIndex.ofInternal)
    | SkeletonNodeIndex.ofLeft idxLeft => match idxLeft.toSum with
      | .inl idxLeft => Sum.inl (SkeletonInternalIndex.ofLeft idxLeft)
      | .inr idxLeft => Sum.inr (SkeletonLeafIndex.ofLeft idxLeft)
    | SkeletonNodeIndex.ofRight idxRight => match idxRight.toSum with
      | .inl idxRight => Sum.inl (SkeletonInternalIndex.ofRight idxRight)
      | .inr idxRight => Sum.inr (SkeletonLeafIndex.ofRight idxRight)

/-- Equivalence between node indices and the sum of internal and leaf indices -/
def SkeletonNodeIndex.SumEquiv (s : Skeleton) :
    SkeletonInternalIndex s ⊕ SkeletonLeafIndex s ≃ SkeletonNodeIndex s :=
{
  toFun x := match x with
    | Sum.inl idx => idx.toNodeIndex
    | Sum.inr idx => idx.toNodeIndex,
  invFun idx := idx.toSum,
  left_inv := sorry,
  right_inv := sorry,
}

/-- Equivalence between `FullData` and the product of `InternalData` and `LeafData` -/
def FullData.Equiv {α} (s : Skeleton) :
    FullData α s ≃ InternalData α s × LeafData α s := by
  calc
    FullData α s ≃ (SkeletonNodeIndex s → α) := FullData.EquivIndexFun s
    _ ≃ (SkeletonInternalIndex s ⊕ SkeletonLeafIndex s → α) := by sorry
    _ ≃ (SkeletonInternalIndex s → α) × (SkeletonLeafIndex s → α) := by sorry
    _ ≃ InternalData α s × LeafData α s := by sorry


end Equivalences

end BinaryTree
