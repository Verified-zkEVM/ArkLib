import ArkLib.ToMathlib.Data.IndexedBinaryTree.Basic


/-!
# Lemmas about Indexed Binary Trees

## TODOs

- More relationships between tree navigations
  - Which navigation sequences are equivalent to each other?
  - How do these navigations affect depth?
- API for flattening a tree to a list
- Define `Lattice` structure on trees
  - a subset relation on trees, mappings of indices to indices of supertrees


-/

namespace BinaryTree

section Navigation

/-- The parent of a leftChild is none or the node -/
theorem SkeletonNodeIndex.leftChild_bind_parent {s : Skeleton}
    (idx : SkeletonNodeIndex s) :
    idx.leftChild >>= parent = (if idx.isLeaf then none else some idx) := by
  sorry

/-- The parent of a rightChild is none or the node -/
theorem SkeletonNodeIndex.rightChild_bind_parent {s : Skeleton}
    (idx : SkeletonNodeIndex s) :
    idx.rightChild >>= parent = (if idx.isLeaf then none else some idx) := by
  sorry

/-- The parent of a leftChild is none or the node -/

theorem SkeletonNodeIndex.parent_of_depth_zero {s : Skeleton}
    (idx : SkeletonNodeIndex s) (h : idx.depth = 0) :
    parent idx = none := by
  cases idx with
  | ofLeaf => rfl
  | ofInternal => rfl
  | ofLeft idxLeft =>
    unfold depth at h
    simp_all
  | ofRight idxRight =>
    unfold depth at h
    simp_all

-- TODO?: reorder the arguments to `LeafData` etc. so that the skeleton comes first?

instance {s} : Functor (fun α => LeafData α s) where
  map f x := x.map f

instance {s} : Functor (fun α => InternalData α s) where
  map f x := x.map f

instance {s} : Functor (fun α => FullData α s) where
  map f x := x.map f


instance {s} : LawfulFunctor (fun α => LeafData α s) := by sorry
instance {s} : LawfulFunctor (fun α => InternalData α s) := by sorry
instance {s} : LawfulFunctor (fun α => FullData α s) := by sorry
