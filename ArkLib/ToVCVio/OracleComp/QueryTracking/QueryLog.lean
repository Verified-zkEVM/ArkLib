/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michele Orrù
-/

import VCVio.OracleComp.Coercions.SubSpec
import VCVio.OracleComp.QueryTracking.LoggingOracle

/-!
# Additions to VCV-io's `QueryLog` and logging oracle

Upstream candidates for `VCVio.OracleComp.QueryTracking.{Structures, LoggingOracle}`:

- `QueryLog.lookup?` — first-match lookup of a query's logged answer (computable, unlike a
  `Classical.dec`-based scan), with `cons`/`append` evaluation lemmas.
- `simp` lemmas relating the sum-spec projections `QueryLog.{fst, snd}` to
  `{(· ++ ·), QueryLog.inl, QueryLog.inr}`.
- `OracleComp.withQueryLog_liftComp_inl` — logging a computation lifted from the left summand
  of a sum spec records the `Sum.inl`-embedded log of the base computation.
-/

universe u

namespace OracleSpec

namespace QueryLog

section lookup

variable {ι : Type u} {spec : OracleSpec ι} [spec.DecidableEq]

/-- First-match lookup of the answer to a query `t` in a query log, if any.

Note that a log may answer the same query several times (e.g. when it records a randomness
oracle rather than a function); `lookup?` returns the *earliest* entry. When the log is
function-like (at most one entry per query, as for the canonical transcript-derivation log),
this is the unique answer. -/
def lookup? (log : QueryLog spec) (t : spec.Domain) : Option (spec.Range t) :=
  match log with
  | [] => none
  | ⟨t', u⟩ :: rest => if ht : t' = t then some (ht ▸ u) else lookup? rest t

@[simp]
lemma lookup?_nil (t : spec.Domain) : lookup? ([] : QueryLog spec) t = none := rfl

lemma lookup?_cons (t' : spec.Domain) (u : spec.Range t') (rest : QueryLog spec)
    (t : spec.Domain) :
    lookup? (⟨t', u⟩ :: rest) t
      = if ht : t' = t then some (ht ▸ u) else lookup? rest t := rfl

/-- `lookup?` scans left-to-right through an append: the second log answers only the
queries the first leaves unanswered. -/
lemma lookup?_append (l₁ l₂ : QueryLog spec) (t : spec.Domain) :
    lookup? (l₁ ++ l₂) t
      = ((lookup? l₁ t).rec (lookup? l₂ t) (fun u => some u) : Option (spec.Range t)) := by
  induction l₁ with
  | nil => rfl
  | cons e rest ihe =>
    obtain ⟨t', u⟩ := e
    rw [show (⟨t', u⟩ :: rest) ++ l₂ = ⟨t', u⟩ :: (rest ++ l₂) from rfl,
      lookup?_cons, lookup?_cons]
    by_cases ht : t' = t
    · rw [dif_pos ht, dif_pos ht]
    · rw [dif_neg ht, dif_neg ht, ihe]

end lookup

section sumProjections

variable {ι₁ ι₂ : Type u} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}

/-- `QueryLog.fst` distributes over append. -/
@[simp]
lemma fst_append (l₁ l₂ : QueryLog (spec₁ + spec₂)) :
    (l₁ ++ l₂).fst = l₁.fst ++ l₂.fst :=
  List.filterMap_append

/-- `QueryLog.snd` distributes over append. -/
@[simp]
lemma snd_append (l₁ l₂ : QueryLog (spec₁ + spec₂)) :
    (l₁ ++ l₂).snd = l₁.snd ++ l₂.snd :=
  List.filterMap_append

/-- The left projection of a left-embedded log is the log itself. -/
@[simp]
lemma fst_inl (l : QueryLog spec₁) : (QueryLog.inl (spec₂ := spec₂) l).fst = l := by
  simp [QueryLog.inl, QueryLog.fst]

/-- The right projection of a left-embedded log is empty. -/
@[simp]
lemma snd_inl (l : QueryLog spec₁) : (QueryLog.inl (spec₂ := spec₂) l).snd = [] := by
  simp [QueryLog.inl, QueryLog.snd]

/-- The left projection of a right-embedded log is empty. -/
@[simp]
lemma fst_inr (l : QueryLog spec₂) : (QueryLog.inr (spec₁ := spec₁) l).fst = [] := by
  simp [QueryLog.inr, QueryLog.fst]

/-- The right projection of a right-embedded log is the log itself. -/
@[simp]
lemma snd_inr (l : QueryLog spec₂) : (QueryLog.inr (spec₁ := spec₁) l).snd = l := by
  simp [QueryLog.inr, QueryLog.snd]

end sumProjections

end QueryLog

end OracleSpec

namespace OracleComp

open OracleSpec

/-- Logging a computation lifted from the left summand of a sum spec records the
`Sum.inl`-embedded log: the lifted computation's queries are exactly the base queries,
re-indexed.

The `MonadLiftT` instance is a *free* implicit argument (not instance-bound), so this applies
whatever (possibly non-canonical) instance route appears in the goal; the query-agreement
hypothesis `hq` is typically closed by `rfl`. -/
lemma withQueryLog_liftComp_inl {ι₁ ι₂ : Type} {oSpec : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {α : Type} {i₁ : MonadLiftT (OracleQuery oSpec) (OracleQuery (oSpec + spec₂))}
    (hq : ∀ (t : oSpec.Domain),
      (liftComp ((oSpec.query t : OracleQuery oSpec _) : OracleComp oSpec _) (oSpec + spec₂)
          (h := i₁))
        = (show OracleComp (oSpec + spec₂) (oSpec.Range t) from
            query (spec := oSpec + spec₂) (Sum.inl t)))
    (X : OracleComp oSpec α) :
    (simulateQ loggingOracle (liftComp X (oSpec + spec₂) (h := i₁))).run
      = (liftComp ((simulateQ loggingOracle X).run) (oSpec + spec₂) (h := i₁)) >>= fun p =>
          pure (p.1, QueryLog.inl p.2) := by
  induction X using OracleComp.inductionOn with
  | pure x =>
    simp only [liftComp_pure, simulateQ_pure, WriterT.run_pure, pure_bind, QueryLog.inl]
    rfl
  | query_bind t k ih =>
    rw [liftComp_bind]
    refine Eq.trans (OracleComp.withQueryLog_bind _ _) ?_
    rw [show (liftComp ((liftM (OracleSpec.query t) : OracleComp oSpec _)) (oSpec + spec₂)
        (h := i₁)) = (show OracleComp (oSpec + spec₂) (oSpec.Range t) from
          query (spec := oSpec + spec₂) (Sum.inl t)) from hq t]
    rw [show ((show OracleComp (oSpec + spec₂) (oSpec.Range t) from
          query (spec := oSpec + spec₂) (Sum.inl t))).withQueryLog
      = (show OracleComp (oSpec + spec₂) (oSpec.Range t) from
          query (spec := oSpec + spec₂) (Sum.inl t)) >>= fun u =>
          pure (u, [⟨Sum.inl t, u⟩])
      from OracleComp.withQueryLog_query (Sum.inl t)]
    conv_rhs =>
      rw [show ((simulateQ loggingOracle ((liftM (OracleSpec.query t) : OracleComp oSpec _)
          >>= k)).run)
        = (liftM (OracleSpec.query t) : OracleComp oSpec _) >>= fun u =>
            (fun p : α × QueryLog oSpec => (p.1, ⟨t, u⟩ :: p.2)) <$>
              (simulateQ loggingOracle (k u)).run
        from OracleComp.run_simulateQ_loggingOracle_query_bind t k]
    rw [liftComp_bind]
    rw [show (liftComp ((liftM (OracleSpec.query t) : OracleComp oSpec _)) (oSpec + spec₂)
        (h := i₁)) = (show OracleComp (oSpec + spec₂) (oSpec.Range t) from
          query (spec := oSpec + spec₂) (Sum.inl t)) from hq t]
    simp only [bind_assoc, pure_bind]
    refine bind_congr fun u => ?_
    rw [show (((k u).liftComp (oSpec + spec₂) (h := i₁))).withQueryLog
      = (liftComp ((simulateQ loggingOracle (k u)).run) (oSpec + spec₂) (h := i₁)) >>= fun p =>
          pure (p.1, QueryLog.inl p.2) from ih u]
    simp only [liftComp_map, map_bind, map_pure]
    rw [bind_map_left]
    refine bind_congr fun p => ?_
    simp only [Prod.map, QueryLog.inl, List.map_cons, id]
    rfl

end OracleComp
