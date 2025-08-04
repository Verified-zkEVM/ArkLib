

-- theorem of_mem_singleHash_support {α : Type} [DecidableEq α] [SelectableType α]
--     (left right out : α) (preexisting_cache resulting_cache : (spec α).QueryCache)
--     (h :
--       (out, resulting_cache) ∈
--         ((simulateQ randomOracle (singleHash α left right)).run
--             preexisting_cache).support) :
--     QueryCache.toSet () resulting_cache
--     = QueryCache.toSet () preexisting_cache ∪ {((left, right), out)} := by
--   unfold singleHash at h
--   simp at h
--   set pre_out := preexisting_cache () (left, right) with h_mem_pre_out
--   clear_value pre_out

--   cases pre_out with
--   | none =>
--     simp_all only []
--     simp at h
--     subst h
--     rw [QueryCache.toSet_cacheQuery_eq_insert_of_none _ _ _ _ h_mem_pre_out.symm]
--   | some u =>
--     simp_all only []
--     simp at h
--     rcases h with ⟨rfl, rfl⟩
--     simp only [domain_def, range_def, Set.union_singleton]
--     symm
--     simp
--     simp [QueryCache.toSet, h_mem_pre_out]






-- @[simp]
-- theorem mem_singleHash_support_iff {α : Type} [DecidableEq α] [SelectableType α]
--     (left right out : α) (preexisting_cache resulting_cache : (spec α).QueryCache) :
--     ((out, resulting_cache)
--       ∈ ((simulateQ randomOracle (singleHash α left right)).run preexisting_cache).support)
--     ↔
--     QueryCache.toSet () resulting_cache
--     = QueryCache.toSet () preexisting_cache ∪ {((left, right), out)} := by
--   constructor
--   · intro h
--     exact of_mem_singleHash_support left right out preexisting_cache resulting_cache h
--   · intro h
--     unfold singleHash
--     simp only [simulateQ_bind, StateT.run_bind]
--     simp

--     set pre_out := preexisting_cache () (left, right) with h_mem_pre_out
--     clear_value pre_out
--     cases pre_out with
--     | none =>
--       simp_all [QueryCache.cacheQuery]
--       apply @QueryCache.ext _ (spec α)
--       intro i

--       simp
--       ext d r
--       simp [Function.update_apply]
--       revert r
--       simp only [Option.eq_of_forall_eq]
--       by_cases h_eq : d = (left, right)
--       · simp [h_eq]

--         sorry
--       · simp [h_eq]
--         sorry

--     | some u =>
--       simp only [StateT.run_pure]
--       simp at h
--       sorry







  -- constructor
  -- · intro h
  --   sorry
  -- · intro h
  --   unfold singleHash
  --   simp only [simulateQ_bind, StateT.run_bind]
  --   simp

  --   set pre_out := preexisting_cache () (left, right) with h_mem_pre_out
  --   clear_value pre_out
  --   cases pre_out with
  --   | none =>
  --     simp_all [QueryCache.cacheQuery]
  --     apply @QueryCache.ext _ (spec α)
  --     intro i

  --     simp
  --     ext d r
  --     simp [Function.update_apply]
  --     revert r
  --     simp only [Option.eq_of_forall_eq]
  --     by_cases h_eq : d = (left, right)
  --     · simp [h_eq]

  --       sorry
  --     · simp [h_eq]
  --       sorry

  --   | some u =>
  --     simp only [StateT.run_pure]
  --     simp at h
  --     sorry



-- /--
-- A theorem that characterizes the support of the `buildMerkleTree` computation.
-- This is used to prove completeness of the Merkle tree construction.

-- TODO backwards direction
-- (requires also stating that the merkle_tree_cache is consistent with the
--   leaf_data_tree, i.e. that the corresponding leaf values are the same)
-- -/
-- theorem of_mem_buildMerkleTree_support {α : Type} [DecidableEq α] [SelectableType α]
--    {s : Skeleton}
--     (leaf_data_tree : LeafDataTree α s)
--     (merkle_tree_cache) (preexisting_cache resulting_cache : (spec α).QueryCache)
--     (h :
--      ((merkle_tree_cache, resulting_cache)
--         ∈ ((simulateQ randomOracle
--           (buildMerkleTree leaf_data_tree)).run preexisting_cache).support)
--     )
--     :
--     (
--       QueryCache.toSet () resulting_cache
--       = QueryCache.toSet () preexisting_cache ∪ merkle_tree_cache.toQueryCacheSet
--     ) := by
--   induction s generalizing preexisting_cache resulting_cache with
--   | leaf =>
--     cases leaf_data_tree with
--     | leaf a =>
--       unfold buildMerkleTree at h
--       rcases h
--       simp [QueryCache.toSet]
--   | internal left_skeleton right_skeleton left_ih right_ih =>
--     cases leaf_data_tree with
--     | internal leftData rightData =>
--       unfold buildMerkleTree at h
--       simp only [bind_pure_comp, simulateQ_bind, StateT.run_bind, Function.comp_apply,
--         simulateQ_map, StateT.run_map, support_bind, support_map, Set.mem_iUnion, Set.mem_image,
--         Prod.mk.injEq, Prod.exists, exists_eq_right_right, exists_prop] at h
--       rcases h with ⟨merkle_tree_cache_left, query_cache_left, h_left,
--         merkle_tree_cache_right, query_cache_right, h_right,
--         merkle_tree_cache_final, h_final, h_eq⟩
--       rw [← h_eq]
--       rw [FullDataTree.internal_toQueryCacheSet]
--       specialize left_ih _ _ _ _ h_left
--       specialize right_ih _ _ _ _ h_right
--       have final_of_mem_singleHash_support := of_mem_singleHash_support _ _ _ _ _ h_final
--       simp_rw [←Set.union_assoc]
--       rw [<-left_ih, <-right_ih, <- final_of_mem_singleHash_support]

-- theorem InductiveMerkleTree.mem_buildMerkleTree_support_iff.extracted_1_1 {α : Type}
--     [inst : DecidableEq α] [inst_1 : SelectableType α] {s : Skeleton}
--     (leaf_data_tree : LeafDataTree α s) (merkle_tree_cache : FullDataTree α s)
--     (preexisting_cache resulting_cache : (spec α).QueryCache)
--     (h :
--       (merkle_tree_cache, resulting_cache) ∈
--         ((simulateQ randomOracle
--           (buildMerkleTree leaf_data_tree)).run preexisting_cache).support) :
--     leaf_data_tree = merkle_tree_cache.toLeafDataTree := by
--   induction s generalizing preexisting_cache resulting_cache with
--   | leaf =>
--     cases leaf_data_tree with
--     | leaf a =>
--       unfold buildMerkleTree at h
--       rcases h
--       simp
--   | internal left_skeleton right_skeleton left_ih right_ih =>
--     cases leaf_data_tree with
--     | internal leftData rightData =>
--       unfold buildMerkleTree at h
--       simp at h
--       rcases h with ⟨merkle_tree_cache_left, query_cache_left, h_left,
--         merkle_tree_cache_right, query_cache_right, h_right,
--         merkle_tree_cache_final, h_final, h_eq⟩
--       specialize left_ih leftData
--       specialize right_ih rightData

--       sorry


-- theorem mem_buildMerkleTree_support_iff {α : Type} [DecidableEq α] [SelectableType α]
--     {s : Skeleton}
--     (leaf_data_tree : LeafDataTree α s)
--     (merkle_tree_cache : FullDataTree α s)
--     (preexisting_cache resulting_cache : (spec α).QueryCache) :
--     ((merkle_tree_cache, resulting_cache)
--       ∈ ((simulateQ randomOracle
--             (buildMerkleTree leaf_data_tree)).run preexisting_cache).support)
--     ↔
--     QueryCache.toSet () resulting_cache
--     = QueryCache.toSet () preexisting_cache ∪ merkle_tree_cache.toQueryCacheSet
--     ∧
--     -- the merkle_tree_cache is consistent with the leaf_data_tree
--     leaf_data_tree = merkle_tree_cache.toLeafDataTree
--      := by
--   constructor
--   · intro h
--     constructor
--     · exact of_mem_buildMerkleTree_support leaf_data_tree merkle_tree_cache preexisting_cache
--         resulting_cache h
--     · exact?
--       -- sorry -- TODO: prove that the merkle_tree_cache is consistent with the leaf_data_tree
--   · intro h
--     induction s generalizing preexisting_cache resulting_cache with
--     | leaf =>
--       cases leaf_data_tree with
--       | leaf a =>
--         unfold buildMerkleTree

--         simp only [simulateQ_pure, StateT.run_pure, neverFails_pure]
--         simp
--         simp at h
--         rw [QueryCache.toSet_eq_iff] at h
--         rcases h with ⟨h1, h2⟩
--         constructor
--         · exact FullDataTree.toLeafDataTree_eq_leaf a merkle_tree_cache h2
--         · exact h1
--     | internal left_skeleton right_skeleton left_ih right_ih =>
--       cases leaf_data_tree with
--       | internal leftData rightData =>
--         unfold buildMerkleTree
--         sorry

-- theorem FullDataTree.internal_toQueryCacheSet {α : Type} [inst : DecidableEq α]
--   [inst_1 : SelectableType α] (left_skeleton right_skeleton : Skeleton)
--   (left_tree : FullDataTree α left_skeleton)
--   (right_tree : FullDataTree α right_skeleton) (root : α)
--    :
--    (FullDataTree.internal root left_tree right_tree).toQueryCacheSet =
--   insert ((left_tree.getRootValue, right_tree.getRootValue), root)
--       (left_tree.toQueryCacheSet ∪ right_tree.toQueryCacheSet)
--      := by
--   rw [toQueryCacheSet_internal]
--   sorry
