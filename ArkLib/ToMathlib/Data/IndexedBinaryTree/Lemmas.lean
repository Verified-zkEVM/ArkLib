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

/-- The parent of a left child, when it exists, is the node itself. -/
theorem SkeletonNodeIndex.leftChild_bind_parent {s : Skeleton}
    (idx : SkeletonNodeIndex s) :
    idx.leftChild >>= parent = idx.leftChild.map (fun _ => idx) := by
  induction idx with
  | ofLeaf =>
    simp [SkeletonNodeIndex.leftChild, Option.bind]
  | @ofInternal left right =>
    cases left
    <;>
    simp [SkeletonNodeIndex.leftChild, SkeletonNodeIndex.parent, Option.bind, getRootIndex]
  | @ofLeft left right idxLeft ih =>
    -- Analyze whether the left child of idxLeft exists
    cases hchild : idxLeft.leftChild with
    | none =>
      simp [SkeletonNodeIndex.leftChild, Option.bind, hchild]
    | some child =>
      -- From the IH specialized with hchild, we get that the parent of child is idxLeft
      have hc : parent child = some idxLeft := by
        simpa [SkeletonNodeIndex.leftChild, Option.bind, hchild] using ih
      -- Now consider the shape of the child to compute the parent of (ofLeft child)
      cases child with
      | ofLeaf => cases hc
      | ofInternal => cases hc
      | ofLeft _ =>
        simp [SkeletonNodeIndex.leftChild, SkeletonNodeIndex.parent, Option.bind, hchild, hc]
      | ofRight _ =>
        simp [SkeletonNodeIndex.leftChild, SkeletonNodeIndex.parent, Option.bind, hchild, hc]
  | @ofRight left right idxRight ih =>
    -- Analyze whether the left child of idxRight exists
    cases hchild : idxRight.leftChild with
    | none =>
      simp [SkeletonNodeIndex.leftChild, Option.bind, hchild]
    | some child =>
      have hc : parent child = some idxRight := by
        simpa [SkeletonNodeIndex.leftChild, Option.bind, hchild] using ih
      cases child with
      | ofLeaf => cases hc
      | ofInternal => cases hc
      | ofLeft _ =>
        simp [SkeletonNodeIndex.leftChild, SkeletonNodeIndex.parent, Option.bind, hchild, hc]
      | ofRight _ =>
        simp [SkeletonNodeIndex.leftChild, SkeletonNodeIndex.parent, Option.bind, hchild, hc]

/-- The parent of a right child, when it exists, is the node itself. -/
theorem SkeletonNodeIndex.rightChild_bind_parent {s : Skeleton}
    (idx : SkeletonNodeIndex s) :
    idx.rightChild >>= parent = idx.rightChild.map (fun _ => idx) := by
  induction idx with
  | ofLeaf =>
    simp [SkeletonNodeIndex.rightChild, Option.bind]
  | @ofInternal left right =>
    cases right
    <;>
    simp [SkeletonNodeIndex.rightChild, SkeletonNodeIndex.parent, Option.bind, getRootIndex]
  | @ofLeft left right idxLeft ih =>
    -- Analyze whether the right child of idxLeft exists
    cases hchild : idxLeft.rightChild with
    | none =>
      simp [SkeletonNodeIndex.rightChild, Option.bind, hchild]
    | some child =>
      have hc : parent child = some idxLeft := by
        simpa [SkeletonNodeIndex.rightChild, Option.bind, hchild] using ih
      cases child with
      | ofLeaf => cases hc
      | ofInternal => cases hc
      | ofLeft _ =>
        simp [SkeletonNodeIndex.rightChild, SkeletonNodeIndex.parent, Option.bind, hchild, hc]
      | ofRight _ =>
        simp [SkeletonNodeIndex.rightChild, SkeletonNodeIndex.parent, Option.bind, hchild, hc]
  | @ofRight left right idxRight ih =>
    -- Analyze whether the right child of idxRight exists
    cases hchild : idxRight.rightChild with
    | none =>
      simp [SkeletonNodeIndex.rightChild, Option.bind, hchild]
    | some child =>
      have hc : parent child = some idxRight := by
        simpa [SkeletonNodeIndex.rightChild, Option.bind, hchild] using ih
      cases child with
      | ofLeaf => cases hc
      | ofInternal => cases hc
      | ofLeft _ =>
        simp [SkeletonNodeIndex.rightChild, SkeletonNodeIndex.parent, Option.bind, hchild, hc]
      | ofRight _ =>
        simp [SkeletonNodeIndex.rightChild, SkeletonNodeIndex.parent, Option.bind, hchild, hc]

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


instance {s} : LawfulFunctor (fun α => LeafData α s) := by
  classical
  refine
    { map_const := rfl
      id_map := ?_
      comp_map := ?_ }
  · intro α x
    induction x with
    | leaf value => simp [Functor.map, LeafData.map]
    | @internal left right tl tr ihL ihR =>
      simp_all [Functor.map, LeafData.map]
  · intro α β γ g h x
    induction x with
    | leaf value => simp [Functor.map, LeafData.map]
    | @internal left right ihL ihR =>
      simp_all [Functor.map, LeafData.map]

instance {s} : LawfulFunctor (fun α => InternalData α s) := by
  classical
  refine
    { map_const := rfl
      id_map := ?_
      comp_map := ?_ }
  · intro α x
    induction x with
    | leaf => simp [Functor.map, InternalData.map]
    | @internal value tL tR ihL ihR =>
      simp_all [Functor.map, InternalData.map]
  · intro α β γ g h x
    induction x with
    | leaf => simp [Functor.map, InternalData.map]
    | @internal value tL tR ihL ihR =>
      simp_all [Functor.map, InternalData.map]

instance {s} : LawfulFunctor (fun α => FullData α s) := by
  classical
  refine
    { map_const := rfl
      id_map := ?_
      comp_map := ?_ }
  · intro α x
    induction x with
    | leaf value => simp [Functor.map, FullData.map]
    | @internal value tL tR ihL ihR =>
      simp_all [Functor.map, FullData.map]
  · intro α β γ g h x
    induction x with
    | leaf value => simp [Functor.map, FullData.map]
    | @internal value tL tR ihL ihR =>
      simp_all [Functor.map, FullData.map]

end Navigation

end BinaryTree
