/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
import VCVio.OracleComp.SimSemantics.StateT.Basic
import VCVio.OracleComp.SimSemantics.OptionT.Basic

/-! Compatibility import for additions that now live in VCVio.

`simulateQ_randomOracle_map_uniformFin` now lives in
`VCVio/OracleComp/QueryTracking/RandomOracle/Simulation.lean`, which this file imports so the name
keeps resolving for downstream consumers.

Worth knowing when deduplicating against VCVio: the local copy was identical in statement and proof,
yet no "already declared" error ever fired, because the two sat at root scope in *different* modules
— nothing imported both at once. A green build therefore does not certify the absence of duplicates;
names must also be checked against the dependency's sources directly. -/

open OracleComp

/-- `simulateQ` fixes `OptionT` `pure` values: the simulated pure computation is pure.
Complements VCVio's `simulateQ_optionT_bind`/`simulateQ_optionT_bind_run` family
(`VCVio/OracleComp/SimSemantics/OptionT/Basic.lean`); upstream candidate. -/
lemma simulateQ_optionT_pure {ι : Type}
    {oSpec : OracleSpec ι} {M : Type → Type}
    [Monad M] [LawfulMonad M] (impl : QueryImpl oSpec M) {X : Type} (x : X) :
    simulateQ impl (pure x : OptionT (OracleComp oSpec) X) =
      (pure x : OptionT M X) := by
  apply OptionT.ext
  change simulateQ impl (pure (some x)) = pure (some x)
  exact simulateQ_pure impl (some x)

/-- A simulated finite guarded loop succeeds exactly when all its conditions hold.
This packages the success and failure lemmas from VCVio without changing short-circuiting. -/
lemma simulateQ_optionT_finRange_forIn {ι : Type} {spec : OracleSpec ι}
    {M : Type → Type} [Monad M] [LawfulMonad M] (impl : QueryImpl spec M)
    {β : Type} {m : ℕ} (init : β)
    (body : Fin m → β → OptionT (OracleComp spec) (ForInStep β))
    (cond : Fin m → Prop) [DecidablePred cond]
    (hbody : ∀ a, simulateQ impl (body a init).run =
      pure (if cond a then some (ForInStep.yield init) else none)) :
    simulateQ impl ((forIn (List.finRange m) init body :
      OptionT (OracleComp spec) β).run) =
      pure (if ∀ a, cond a then some init else none) := by
  classical
  by_cases hall : ∀ a, cond a
  · rw [if_pos hall]
    apply simulateQ_optionT_forIn_yield_pure_some
    intro a
    exact (hbody a).trans (congrArg pure (if_pos (hall a)))
  · rw [if_neg hall]
    apply simulateQ_optionT_forIn_yield_pure_none impl _ _ body cond hbody
    simpa using hall
