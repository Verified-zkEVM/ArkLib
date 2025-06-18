/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio
import Batteries.Data.Array.Monadic

/-!
  # Helper Definitions and Lemmas to be ported to VCVio
-/

open OracleSpec OracleComp

variable {ι : Type} {α β γ : Type}

/--
  A function that implements the oracle interface specified by `spec`, and queries no further
  oracles.
-/
def Oracle (spec : OracleSpec ι) := (i : ι) → spec.domain i → spec.range i


variable [DecidableEq α] [DecidableEq β] [Inhabited β] [Fintype β] [Inhabited γ] [Fintype γ]

namespace OracleSpec

variable {ι : Type} {spec : OracleSpec ι}

-- def QueryLog.getQueriesFromIdx (log : QueryLog spec) (i : ι) :
--     List (spec.domain i × spec.range i) :=
--   log i

end OracleSpec

namespace OracleComp

variable {ι : Type} {spec : OracleSpec ι} {α σ : Type}

/--
  Run an oracle computation `OracleComp spec α` with an oracle coming from
  a (deterministic) function `f` that queries no further oracles.

  TODO: add state for `f`
-/
def runWithOracle (f : Oracle spec) : OracleComp spec α → Option α :=
  OracleComp.construct' (spec := spec) (C := fun _ => Option α) (fun x => some x)
    (fun i q _ g => g (f i q)) (none)

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



/-!
# ROM equivalent to implementation with a random function
-/


/--
An oracle implementation that implements `MerkleTree.spec`
by simply applying a provided function `hash` to the input.

TODO:
The random oracle model is usually defined by assuming that the hash function is randomly selected
from the space of all functions from `α × α` to `α`.
This is in contrast to the actual `randomOracle` implementation in VCVio,
which works by sampling random outputs when a query is made, and then caching the result.
Clearly the latter is the sensible way to implement things,
but the former seems like a more natural definition for proofs, since it's stateless.
Perhaps both should be provided, with theorems establishing equivalence.
Either way, this feels like it should be generalized
and moved to VCVio,
~~not sure if its already there somewhwere~~ seems like it's similar to the above `runWithOracle`, though this is monadic

-/
def implement_with_function (hash : α × α -> α) :
    QueryImpl (spec α) (StateT Unit (OracleComp (emptySpec))) where
  impl q := match q with
    | ⟨_, ⟨left, right⟩⟩ =>
        do
          let out := hash (left, right)
          return out

lemma implement_with_function_impl_eq {hash : α × α -> α} (q : OracleQuery (spec α) α) :
    (implement_with_function α hash).impl q = match q with
      | ⟨_, ⟨left, right⟩⟩ => do
          let out := hash (left, right)
          return out := by
  cases q with
  | query i t => rfl

theorem randomOracle_neverFails_of_implement_with_function_neverFails {β} [SelectableType α]
    (oa : OracleComp (spec α) β) (preexisting_cache : (spec α).QueryCache)
    :
    (∀ hash : α × α -> α,
      ((oa.simulateQ (implement_with_function α hash)).run ()).neverFails)
    -- This is also fine. We are not in danger of queries to the same hash returning different values because now we are on the empty spec []ₒ (i.e., there are no oracles, no queries are made)
    →
    ((oa.simulateQ (randomOracle)).run preexisting_cache).neverFails
    -- I think this is the right way to write it, we are not in danger of queries to the same hash returning different values because the lifting to randomOracle ensures each value is queried at most once
      := by
  intro h_impl

  induction oa using OracleComp.inductionOn generalizing preexisting_cache with
  | pure x => simp only [simulateQ_pure, StateT.run_pure, neverFails_pure]
  | failure =>
    simp at h_impl
  | query_bind q t r ih =>
    simp only [range_def, simulateQ_bind, simulateQ_query, QueryImpl.withCaching_apply,
      unifOracle.apply_eq, LawfulMonad.bind_assoc, StateT.run_bind, StateT.run_get,
      Function.comp_apply, pure_bind, neverFails_bind_iff, Prod.forall]
    simp at h_impl
    cases preexisting_cache q t with
    | none =>
      -- If the query is not in the cache, we can just use the implementation with a function
      simp
      intro a
      apply ih
      intros hash
      specialize h_impl hash -- does this need to be modified?
      rcases h_impl with ⟨h_impl1, h_impl2⟩
      apply h_impl2
      clear h_impl2
      -- simp [support, supportWhen]
      -- simp [neverFails, neverFailsWhen, allWhen] at h_impl1
      -- set query_q_t := query (spec := spec α) q t
      simp [implement_with_function_impl_eq] at h_impl1
      cases query q t with
      | query i t' =>
        -- We can use the implementation with a function, since it never fails
        simp only [implement_with_function_impl_eq, Prod.mk.eta, StateT.run_pure, support_pure,
          Set.mem_singleton_iff, Prod.mk.injEq, and_true]

        -- simp [implement_with_function_impl_eq] at h_impl1

        -- We can use the implementation with a function, since it never fails
        -- exact h_impl1
        sorry


end OracleComp
