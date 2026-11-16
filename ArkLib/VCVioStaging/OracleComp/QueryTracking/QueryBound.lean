/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import VCVio.OracleComp.Coercions.SubSpec
public import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# Query-bound transfer through `liftComp` / sub-spec lifting

Upstream candidates for `VCVio.OracleComp.QueryTracking.QueryBound`:

Lifting a computation into a larger oracle spec (`liftComp`, or `liftM` through a
`SubSpec`-derived `MonadLiftT (OracleQuery spec₁) (OracleQuery spec₂)`) maps each source
query to exactly one target query, so query bounds transfer:

- `isTotalQueryBound_liftM_query'` / `isQueryBoundP_liftM_query'` — a single embedded
  `OracleQuery` value (arbitrary continuation) counts as one query.
- `liftedIndex` — the `spec₂`-index a `spec₁`-query lands on after lifting.
- `IsTotalQueryBound.liftComp'` — total bounds transfer verbatim.
- `isQueryBoundP_liftComp_of_isTotalQueryBound` — a total bound on the source bounds any
  predicated count of the lifted computation.
- `isQueryBoundP_liftComp_of_forall_not` — if no lifted query index satisfies `p`, the
  lifted computation makes zero `p`-queries (no bound needed on the source).
- `IsQueryBoundP.liftComp_of_iff` — predicated bounds transfer along a predicate
  correspondence `p₂ ∘ liftedIndex ↔ p₁`.

These are stated for an arbitrary `MonadLiftT (OracleQuery spec₁) (OracleQuery spec₂)`
(not just a single `MonadLift`), so they apply to composite instance chains as resolved
at `liftComp` call sites.
-/

@[expose] public section

universe u

open OracleSpec

namespace OracleComp

variable {ι₁ ι₂ : Type u} {spec₁ : OracleSpec.{u, u} ι₁} {spec₂ : OracleSpec.{u, u} ι₂}
  {α β : Type u}

/-- A single (embedded) oracle query makes exactly one query, regardless of its
continuation. -/
lemma isTotalQueryBound_liftM_query' (q : OracleQuery spec₁ α) :
    IsTotalQueryBound (liftM q : OracleComp spec₁ α) 1 := by
  obtain ⟨t, cont⟩ := q
  change IsTotalQueryBound (liftM (spec₁.query t) >>= fun u => pure (cont u)) 1
  exact isTotalQueryBound_query_bind_iff.mpr ⟨one_pos, fun u => trivial⟩

/-- A single (embedded) oracle query is `p`-bounded by any `n` with `p q.input → 0 < n`. -/
lemma isQueryBoundP_liftM_query' {p : ι₁ → Prop} [DecidablePred p]
    (q : OracleQuery spec₁ α) {n : ℕ} (h : p q.input → 0 < n) :
    IsQueryBoundP (liftM q : OracleComp spec₁ α) p n := by
  obtain ⟨t, cont⟩ := q
  change IsQueryBoundP (liftM (spec₁.query t) >>= fun u => pure (cont u)) p n
  refine (isQueryBoundP_query_bind_iff p t _ n).mpr ⟨?_, fun u => by simp⟩
  by_cases hp : p t
  · exact Or.inr (h hp)
  · exact Or.inl hp

/-- The `spec₂`-index a `spec₁`-query lands on after lifting through a query-level
`MonadLiftT` (e.g. a `SubSpec` inclusion chain). -/
def liftedIndex [inst : MonadLiftT (OracleQuery spec₁) (OracleQuery spec₂)]
    (t : spec₁.Domain) : spec₂.Domain :=
  (liftM (spec₁.query t) : OracleQuery spec₂ (spec₁.Range t)).input

variable [inst : MonadLiftT (OracleQuery spec₁) (OracleQuery spec₂)]

/-- Total-query-bound transfer through `liftComp`: each source query maps to exactly one
query in the larger spec. -/
lemma IsTotalQueryBound.liftComp' {oa : OracleComp spec₁ α} {n : ℕ}
    (h : IsTotalQueryBound oa n) :
    IsTotalQueryBound (liftComp oa spec₂) n := by
  rw [liftComp_def]
  exact h.simulateQ_of_step fun t =>
    isTotalQueryBound_liftM_query' (liftM (spec₁.query t) : OracleQuery spec₂ _)

/-- Predicated-bound transfer through `liftComp` from a total bound on the source: any
`p`-count of the lifted computation is at most the source's total count. -/
lemma isQueryBoundP_liftComp_of_isTotalQueryBound
    {p : ι₂ → Prop} [DecidablePred p] {oa : OracleComp spec₁ α} {n : ℕ}
    (h : IsTotalQueryBound oa n) :
    IsQueryBoundP (liftComp oa spec₂) p n := by
  exact h.liftComp'.isQueryBoundP

/-- If no lifted source query lands on a `p`-index, the lifted computation makes **zero**
`p`-queries — with no total bound needed on the source. -/
lemma isQueryBoundP_liftComp_of_forall_not
    {p : ι₂ → Prop} [DecidablePred p]
    (hp : ∀ t : spec₁.Domain, ¬ p (liftedIndex (spec₁ := spec₁) (spec₂ := spec₂) t))
    (oa : OracleComp spec₁ α) :
    IsQueryBoundP (liftComp oa spec₂) p 0 := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t mx ih =>
      rw [liftComp_def, simulateQ_query_bind]
      exact isQueryBoundP_bind
        (isQueryBoundP_liftM_query' _ (fun hcon => absurd hcon (hp t)))
        (fun u _ => ih _) |>.mono (le_refl 0)

/-- Predicated-bound transfer through `liftComp` along a predicate correspondence: if `p₂`
holds at a lifted index exactly when `p₁` held at the source index, `p₁`-bounds transfer
to `p₂`-bounds verbatim. -/
lemma IsQueryBoundP.liftComp_of_iff
    {p₁ : ι₁ → Prop} [DecidablePred p₁] {p₂ : ι₂ → Prop} [DecidablePred p₂]
    (hp : ∀ t : spec₁.Domain,
      p₂ (liftedIndex (spec₁ := spec₁) (spec₂ := spec₂) t) ↔ p₁ t)
    {oa : OracleComp spec₁ α} {n : ℕ} (h : IsQueryBoundP oa p₁ n) :
    IsQueryBoundP (liftComp oa spec₂) p₂ n := by
  rw [liftComp_def]
  refine h.simulateQ_of_step (fun t _ => ?_) (fun t ht => ?_)
  · exact isQueryBoundP_liftM_query' _ (fun _ => one_pos)
  · exact isQueryBoundP_liftM_query' _ (fun hq => absurd ((hp t).mp hq) ht)

/-! ### Per-step transfer through `StateT`/`OptionT` towers

`IsQueryBoundP.simulateQ_run_StateT_of_step` covers implementations landing in
`StateT σ (OracleComp spec')`.  The DSFS `D2SQuery` pipelines land in
`StateT σ (OptionT (OracleComp spec'))` (one mutable state plus an abort layer) and
`StateT σ₁ (StateT σ₂ (OptionT (OracleComp spec')))` (query state, memo state, abort).
The two lemmas below extend the per-step transfer to those towers: an aborting run makes
no further queries, so the same budget accounting applies verbatim. -/

section OptionTTower

variable {ι : Type u} {spec : OracleSpec.{u, u} ι} {ι' : Type u}
  {spec' : OracleSpec.{u, u} ι'}

/-- Per-step query-bound transfer through `simulateQ` into `StateT σ (OptionT (OracleComp _))`:
if the handler for query index `t` makes at most one `q`-query when `p t` holds and none
otherwise (at every state), a `p`-bound on the source computation becomes a `q`-bound on the
fully-run simulation.  `OptionT` aborts short-circuit the continuation and cost nothing. -/
theorem IsQueryBoundP.simulateQ_run_optionT_of_step
    {σ : Type u} {α : Type u}
    {p : ι → Prop} [DecidablePred p]
    {q : ι' → Prop} [DecidablePred q]
    {impl : QueryImpl spec (StateT σ (OptionT (OracleComp spec')))}
    {oa : OracleComp spec α} {n : ℕ}
    (h : IsQueryBoundP oa p n)
    (hstep : ∀ t s, IsQueryBoundP (((impl t).run s).run) q (if p t then 1 else 0))
    (s : σ) :
    IsQueryBoundP (((simulateQ impl oa).run s).run) q n := by
  induction oa using OracleComp.inductionOn generalizing n s with
  | pure x =>
      simp [simulateQ_pure]
  | query_bind t mx ih =>
      rw [isQueryBoundP_query_bind_iff] at h
      rw [simulateQ_query_bind, StateT.run_bind, OptionT.run_bind]
      have hrest : ∀ x? ∈ support (((impl t).run s).run),
          IsQueryBoundP
            (Option.elim x? (pure none)
              (fun x => ((simulateQ impl (mx x.1)).run x.2).run))
            q (if p t then n - 1 else n) := by
        intro x? _
        cases x? with
        | none => simp
        | some x => exact ih x.1 (h.2 x.1) x.2
      have hbind := isQueryBoundP_bind (hstep t s) hrest
      refine hbind.mono ?_
      by_cases ht : p t
      · rcases h.1 with hnot | hpos
        · exact absurd ht hnot
        · simp only [ite_eq_left ht]
          omega
      · simp only [ite_eq_right ht]
        omega

/-- Per-step query-bound transfer through `simulateQ` into
`StateT σ₁ (StateT σ₂ (OptionT (OracleComp _)))` — the `d2fRaw` tower (D2SQuery state, inner
memo, abort layer).  Same accounting as `simulateQ_run_optionT_of_step` with one more state
layer. -/
theorem IsQueryBoundP.simulateQ_run_run_optionT_of_step
    {σ₁ σ₂ : Type u} {α : Type u}
    {p : ι → Prop} [DecidablePred p]
    {q : ι' → Prop} [DecidablePred q]
    {impl : QueryImpl spec (StateT σ₁ (StateT σ₂ (OptionT (OracleComp spec'))))}
    {oa : OracleComp spec α} {n : ℕ}
    (h : IsQueryBoundP oa p n)
    (hstep : ∀ t s₁ s₂, IsQueryBoundP ((((impl t).run s₁).run s₂).run) q
      (if p t then 1 else 0))
    (s₁ : σ₁) (s₂ : σ₂) :
    IsQueryBoundP ((((simulateQ impl oa).run s₁).run s₂).run) q n := by
  have hflat := h.simulateQ_run_optionT_of_step
    (impl := impl.flattenStateT) (fun t s => by
      simpa only [QueryImpl.flattenStateT, StateT.run_mk, OptionT.run_map,
        isQueryBoundP_map_iff] using hstep t s.1 s.2) (s₁, s₂)
  simpa only [simulateQ_flattenStateT_run, bind_pure_comp, OptionT.run_map,
    isQueryBoundP_map_iff] using hflat

/-- `isQueryBoundP_bind` at the `StateT σ (OptionT (OracleComp _))` run level: compose a
budget for the head with a state-uniform budget for the continuation.  The `OptionT` abort
branch costs nothing. -/
lemma isQueryBoundP_stateT_optionT_run_bind
    {σ : Type u} {α β : Type u}
    {q : ι' → Prop} [DecidablePred q]
    {mx : StateT σ (OptionT (OracleComp spec')) α}
    {f : α → StateT σ (OptionT (OracleComp spec')) β}
    {s : σ} {n m : ℕ}
    (h : IsQueryBoundP ((mx.run s).run) q n)
    (hf : ∀ a s', IsQueryBoundP (((f a).run s').run) q m) :
    IsQueryBoundP (((mx >>= f).run s).run) q (n + m) := by
  rw [StateT.run_bind, OptionT.run_bind]
  refine isQueryBoundP_bind h fun x? _ => ?_
  cases x? with
  | none => exact (isQueryBoundP_pure q _ 0).mono (Nat.zero_le m)
  | some x => exact hf x.1 x.2

end OptionTTower

end OracleComp
