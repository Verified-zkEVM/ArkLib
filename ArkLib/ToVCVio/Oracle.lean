/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.OracleComp.QueryTracking.CachingOracle

/-!
  # Helper Definitions and Lemmas to be ported to VCVio
-/

open OracleSpec OracleComp

universe u v

variable {ι : Type} {α β γ : Type}

/-- A function that implements the oracle interface specified by `spec`, and queries no further
  oracles.
-/
def OracleSpec.FunctionType (spec : OracleSpec ι) := (i : ι) → spec.domain i → spec.range i

namespace OracleSpec

variable {ι : Type} {spec : OracleSpec ι}

-- def QueryLog.getQueriesFromIdx (log : QueryLog spec) (i : ι) :
--     List (spec.domain i × spec.range i) :=
--   log i

end OracleSpec

namespace OracleComp

variable {ι : Type} {spec : OracleSpec ι} {α σ : Type}

/-- Run an oracle computation `OracleComp spec α` with an oracle coming from
  a (deterministic) function `f` that queries no further oracles.

  TODO: add state for `f`
-/
def runWithOracle (f : spec.FunctionType) : OracleComp spec α → Option α :=
  OracleComp.construct' (spec := spec) (C := fun _ => Option α)
    -- For a pure value, return that value successfully
    (fun x => some x)
    -- When a query bind is made, run the oracle function `f` and compute on the result
    (fun i q _ g => g (f i q))
    -- If the computation fails, return `none`
    (none)

@[simp]
theorem runWithOracle_pure (f : spec.FunctionType) (a : α) :
    runWithOracle f (pure a) = some a := by
  unfold runWithOracle OracleComp.construct'
  simp only [construct_pure]

@[simp]
theorem runWithOracle_freeMonad_pure_some (f : spec.FunctionType) (a : α) :
    runWithOracle f (FreeMonad.pure (a : Option α)) = a := by
  exact rfl

@[simp]
theorem runWithOracle_freeMonad_pure_none (f : spec.FunctionType) :
    runWithOracle f (FreeMonad.pure (none : Option α)) = none := by
  exact rfl

@[simp]
theorem runWithOracle_freeMonad_pure (f : spec.FunctionType) (a : Option α) :
    runWithOracle f (FreeMonad.pure a) = a := by
  cases a with
  | none => simp only [runWithOracle_freeMonad_pure_none]
  | some val => simp only [runWithOracle_freeMonad_pure_some]

@[simp]
theorem runWithOracle_freeMonad_query_roll (f : spec.FunctionType)
    (i : ι) (t : spec.domain i)
    (r : (spec.range i) → FreeMonad (spec.OracleQuery) (Option α)) :
    runWithOracle f (FreeMonad.roll (query i t) r) = runWithOracle f (r (f i t)) := by
  rfl

@[simp]
theorem runWithOracle_bind (f : spec.FunctionType)
    (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    runWithOracle f (oa >>= ob) =
    (runWithOracle f oa) >>=
    (fun x => runWithOracle f (ob x)) := by
  induction oa generalizing β f ob with
  | pure x =>
    cases x with
    | some a => rfl
    | none => rfl
  | roll x r ih =>
    cases x with
    | query i t =>
      simp only [runWithOracle_freeMonad_query_roll, Option.bind_eq_bind]
      simp only [Option.bind_eq_bind] at ih
      specialize ih (f i t) f ob
      rw [<-ih]
      rfl

@[simp]
theorem runWithOracle_failure (f : spec.FunctionType) :
    runWithOracle f (failure : OracleComp spec α) = none := by
  unfold runWithOracle OracleComp.construct'
  simp only [construct_failure]

-- Oracle with bounded use; returns `default` if the oracle is used more than `bound` times.
-- We could then have the range be an `Option` type, so that `default` is `none`.
-- def boundedUseOracle {ι : Type} [DecidableEq ι] {spec : OracleSpec ι} (bound : ι → ℕ) :
--     spec →[ι → ℕ]ₛₒ spec := fun i query queryCount =>
--   if queryCount i > bound i then
--     return ⟨default, queryCount⟩
--   else
--     countingOracle i query queryCount

-- Single use oracle
-- @[reducible]
-- def singleUseOracle {ι : Type} [DecidableEq ι] {spec : OracleSpec ι} :
--     spec →[ι → ℕ]ₛₒ spec :=
--   boundedUseOracle (fun _ ↦ 1)

@[simp]
theorem OracleSpec.append_range_left {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    (i : ι₁) : (spec₁ ++ₒ spec₂).range (Sum.inl i) = spec₁.range i := by
  simp [append, OracleSpec.range]

@[simp]
theorem OracleSpec.append_range_right {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    (i : ι₂) : (spec₁ ++ₒ spec₂).range (Sum.inr i) = spec₂.range i := by
  simp [append, OracleSpec.range]

-- set_option linter.unusedVariables false in
-- /-- `SatisfiesM` for `OracleComp` -/
-- @[simp]
-- theorem SatisfiesM_OracleComp_eq {p : α → Prop} {x : OracleComp spec α} :
--     SatisfiesM (m := OracleComp spec) p x ↔
--       (∀ a, x = liftM (pure a) → p a) ∧
--         (∀ i q oa, x = queryBind' i q _ oa →
--           ∀ a, SatisfiesM (m := OracleComp spec) p (oa a)) where
--   mp h := by
--     obtain ⟨ x', hx' ⟩ := h
--     constructor
--     · intro a h'
--       simp_all
--       match x' with
--       | pure' _ ⟨ _, h'' ⟩ => simp_all; exact hx' ▸ h''
--     · intro i q oa h' a
--       simp_all
--       match x' with
--       | queryBind' i' q' _ oa' =>
--         simp [map_bind] at hx'
--         obtain ⟨ hi, hq, hoa ⟩ := hx'
--         subst hi hoa hq h'
--         refine ⟨ oa' a, by simp ⟩
--   -- For some reason `h` is marked as unused variable
--   -- Probably due to `simp_all`
--   mpr := fun h => match x with
--     | pure' _ a => by
--       simp_all
--       exact ⟨ pure' _ ⟨a , h⟩, by simp ⟩
--     | queryBind' i q _ oa => by
--       simp_all
--       have hBind' := h i q rfl
--       simp at hBind'
--       have h' := fun a => Classical.choose_spec (hBind' a)
--       exact ⟨ queryBind' i q _ (fun a =>Classical.choose (hBind' a)), by simp [map_bind, h'] ⟩
--     | failure' _ => by sorry

/-- True if every non-`none` element of the cache has that same value in the oracle -/
def Oracle.containsCache {ι : Type} {spec : OracleSpec ι}
    (f : spec.FunctionType) (cache : spec.QueryCache) :
    Prop :=
  ∀ i q r, cache i q = some r → f i q = r

/-- For any cache, there is a function to contain it -/
lemma Oracle.containsCache_of_cache {ι : Type} {spec : OracleSpec ι}
    [(i : ι) → Inhabited (OracleSpec.range spec i)]
    (cache : spec.QueryCache) :
    ∃ (f : spec.FunctionType), Oracle.containsCache f cache := by
  use fun i q =>
    match cache i q with
    | none => default
    | some r => r
  unfold Oracle.containsCache
  intro i q r h
  cases cache i q with
  | none => simp_all
  | some val => simp_all

/--
For a particular cache, the oracle never fails on that cache
iff it never fails when run with any oracle function that is compatible with the cache.
-/
theorem randomOracle_cache_neverFails_iff_runWithOracle_neverFails {β}
    [DecidableEq ι] [spec.DecidableEq] [(i : ι) → SelectableType (OracleSpec.range spec i)]
    (oa : OracleComp (spec) β) (preexisting_cache : spec.QueryCache)
    :
    ((oa.simulateQ randomOracle).run preexisting_cache).neverFails
    ↔
    (∀ (f : spec.FunctionType),
      Oracle.containsCache f preexisting_cache →
      (runWithOracle f oa).isSome) := by
  haveI : (i : ι) → Inhabited (OracleSpec.range spec i) := by
    sorry
  -- todo
  -- ((oa.simulateQ randomOracle).run preexisting_cache).neverFails ↔ never fails for any supercache
  induction oa using OracleComp.inductionOn with
  | pure x =>
    simp_all
  | query_bind i t oa ih =>
    simp_all
    set pre := preexisting_cache i t with pre_eq
    clear_value pre
    cases pre with
    | none =>
      simp_all only [StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_pure_comp,
        StateT.run_modifyGet, Functor.map_map, neverFails_map_iff, neverFails_uniformOfFintype,
        support_map, support_uniformOfFintype, Set.image_univ, Set.mem_range, Prod.mk.injEq,
        exists_eq_left, forall_eq', true_and]
      constructor
      · intro h f hf
        sorry
      · sorry
    | some val => sorry
  | failure =>
    simp_all
    exact Oracle.containsCache_of_cache preexisting_cache

/--
For a particular oracle function, the computation succeeds with that oracle function
iff it succeeds when initialized with a cache that contains all of data from that oracle function.
-/
theorem runWithOracle_succeeds_iff_simulateQ_randomOracle_neverFails
     {β}
    [DecidableEq ι] [spec.DecidableEq] [(i : ι) → SelectableType (OracleSpec.range spec i)]
    (oa : OracleComp (spec) β) (f : spec.FunctionType) :
    (runWithOracle f oa).isSome ↔
    ((oa.simulateQ randomOracle).run (fun i q => some (f i q))).neverFails := by
  sorry

/--
The oracle never fails on any cache
iff it never fails when run with any oracle function.
-/
theorem randomOracle_neverFails_iff_runWithOracle_neverFails {β}
    [DecidableEq ι] [spec.DecidableEq] [(i : ι) → SelectableType (OracleSpec.range spec i)]
    (oa : OracleComp (spec) β)
    :
    (∀ (preexisting_cache : spec.QueryCache),
      ((oa.simulateQ randomOracle).run preexisting_cache).neverFails)
    ↔
    (∀ (f : spec.FunctionType),
      (runWithOracle f oa).isSome) := by
  constructor
  · intro h f
    rw [runWithOracle_succeeds_iff_simulateQ_randomOracle_neverFails]
    exact h fun i q ↦ some (f i q)
  · intro h preexisting_cache
    sorry

end OracleComp

variable {m : Type u → Type v} [Monad m] [LawfulMonad m]
    {m' : Type u → Type v} [Monad m'] [LawfulMonad m']

namespace QueryImpl

variable {ι : Type u} [DecidableEq ι] {spec : OracleSpec ι} [spec.DecidableEq] {m : Type u → Type v}
  [Monad m]

/-- Compose a query implementation from `spec` to some monad `m`, with a further monad homomorphism
  from `m` to `m'`. -/
def composeM {m' : Type u → Type v} [Monad m'] (hom : m →ᵐ m') (so : QueryImpl spec m) :
    QueryImpl spec m' where
  impl | query i t => hom (so.impl (query i t))

end QueryImpl

section SelectableTypeInstances

/-- A type equivalent to a `SelectableType` is also `SelectableType`. -/
def SelectableType.ofEquiv {α β : Type} [DecidableEq α] [DecidableEq β] [SelectableType α]
    (e : α ≃ β) : SelectableType β where
  selectElem := e <$> SelectableType.selectElem (β := α)
  mem_support_selectElem := fun x => by
    -- support (e <$> selectElem) = e '' support selectElem
    simp only [OracleComp.support_map]
    -- Since e is an equivalence, x ∈ e '' S ↔ e.symm x ∈ S
    rw [Set.mem_image_equiv]
    exact SelectableType.mem_support_selectElem (e.symm x)
  probOutput_selectElem_eq := fun x y => by
    simp only [probOutput_map_eq_tsum, OracleComp.probOutput_pure, mul_ite, mul_one, mul_zero]
    let reduce_sum (z : β) :
      (∑' a, if z = e a then [= a | SelectableType.selectElem (β := α)] else 0)
      = [= e.symm z | SelectableType.selectElem (β := α)] := by
      convert tsum_eq_single (e.symm z) _
      · simp only [Equiv.apply_symm_apply, ↓reduceIte]
      · intro b hb
        split_ifs with h
        · have h_eq: e.symm z = b := by rw [h, Equiv.symm_apply_apply]
          rw [←h_eq]; simp only [probOutput_eq_zero_iff']
          exact fun a ↦ hb (id (Eq.symm h_eq))
        · rfl
    rw [reduce_sum x, reduce_sum y]
    apply SelectableType.probOutput_selectElem_eq
  probFailure_selectElem := by
    simp only [probFailure_map, SelectableType.probFailure_selectElem]

/-- A function from `Fin n` to a `SelectableType` is also `SelectableType`. -/
instance instSelectableTypeFinFunc {n : ℕ} {α : Type} [SelectableType α] [DecidableEq α] :
    SelectableType (Fin n → α) := by
  letI instVectorFinFuncEquiv: (_root_.Vector α n) ≃ (Fin n → α) :=
    { toFun := fun v i => v.get i
      invFun := _root_.Vector.ofFn
      left_inv := fun v => by
        ext i
        simp only [Vector.ofFn, Vector.get, Fin.coe_cast, Vector.getElem_toArray, Vector.getElem_mk,
          Array.getElem_ofFn]
      right_inv := fun f => by
        funext i
        simp only [Vector.get, Vector.ofFn, Fin.coe_cast, Array.getElem_ofFn, Fin.eta] }
  exact SelectableType.ofEquiv (instVectorFinFuncEquiv)

end SelectableTypeInstances
