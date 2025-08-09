
import VCVio
import ArkLib.Data.Math.Basic
import ArkLib.CommitmentScheme.Basic
import Mathlib.Data.Vector.Snoc

/--
Returns, for a particular oracle's cache, and a particular oracle index `i`,
the set of all (query, response) pairs that have been made to the oracle `i`.
-/
def QueryCache.toSet {ι : Type} {spec : OracleSpec ι} (i : ι) (cache : spec.QueryCache) :
    Set (spec.domain i × spec.range i) :=
  { (q, r) : spec.domain i × spec.range i | cache i q = some r }

@[simp]
lemma QueryCache.toSet_cacheQuery_eq_insert_of_none {ι : Type} {spec : OracleSpec ι}
    [spec.DecidableEq] [DecidableEq ι]
    (i : ι) (cache : spec.QueryCache) (q : spec.domain i) (r : spec.range i)
    (h : cache i q = none) :
    QueryCache.toSet i (cache.cacheQuery i q r) =
      QueryCache.toSet i cache ∪ {(q, r)} := by
  simp only [QueryCache.toSet, OracleSpec.QueryCache.cacheQuery]
  simp
  ext ⟨q', r'⟩
  simp
  rw [Function.update_apply]
  split_ifs with h' <;> simp_all
  exact eq_comm


/-- If the QueryCache.toSet are equal, the underlying caches are equal -/
@[simp]
theorem QueryCache.toSet_eq_iff {ι : Type} [Subsingleton ι] {spec : OracleSpec ι}
    (i : ι) (cache1 cache2 : spec.QueryCache) :
    QueryCache.toSet i cache1 = QueryCache.toSet i cache2 ↔ cache1 = cache2 := by
  constructor
  · intro h
    
    sorry
    -- ext i' d r
    -- unfold QueryCache.toSet at *
    -- simp at h
    -- have : i' = i := by
    --   -- exact?
    --   apply Subsingleton.elim
    -- subst this
    -- have := congr_fun h (d, r)
    -- simp at this
    -- convert this using 1

  · intro h_eq
    subst h_eq
    rfl
