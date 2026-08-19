/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import VCVio.OracleComp.EvalDist

/-!
# Query implementations with `ExceptT` base monads

This is the `ExceptT` counterpart of VCVio's `QueryImpl.mapStateTBase`: interpreting the
base-oracle computations of an exception-valued handler commutes with simulating the handler.
The result is useful for lossless, structured-abort simulations, where erasing an exception into
`OptionT` would lose the reason needed by a first-bad-event proof.
-/

universe u v

open OracleComp OracleSpec

namespace QueryImpl

/-- Running a computation lifted through `ExceptT` and then `StateT` preserves its result and
threads the supplied state.  This elementary transformer law is useful when comparing a direct
oracle handler with one obtained by pushing an outer simulation through a lossless stack. -/
theorem run_stateT_lift_exceptT_lift {m : Type u → Type v}
    [Monad m] [LawfulMonad m] {σ ε α : Type u}
    (oa : m α) (s : σ) :
    ExceptT.run ((StateT.lift (ExceptT.lift oa) : StateT σ (ExceptT ε m) α).run s) =
      (fun a => Except.ok (a, s)) <$> oa := by
  rw [StateT.run_lift, ExceptT.run_bind, ExceptT.run_lift]
  rw [bind_map_left]
  rw [map_eq_pure_bind]
  apply bind_congr
  intro a
  rfl

/-- Lift an oracle implementation through the `StateT σ (ExceptT ε ·)` stack without changing
any query. -/
noncomputable def liftStateTExceptTBase {ι : Type _} {spec : OracleSpec ι}
    {m : Type u → Type v} [Monad m] {σ ε : Type u}
    (inner : QueryImpl spec m) : QueryImpl spec (StateT σ (ExceptT ε m)) := fun query =>
  StateT.lift (ExceptT.lift (inner query))

/-- Running a fully lifted handler is exactly the base simulation, with the input state paired
with its result and no exception. -/
theorem simulateQ_liftStateTExceptTBase_run {ι : Type _} {spec : OracleSpec ι}
    {m : Type u → Type v} [Monad m] [LawfulMonad m] {σ ε : Type u}
    (inner : QueryImpl spec m) {α : Type u} (oa : OracleComp spec α) (state : σ) :
    ExceptT.run ((simulateQ (liftStateTExceptTBase (ε := ε) inner) oa).run state) =
      (fun value => Except.ok (value, state)) <$> simulateQ inner oa := by
  induction oa using OracleComp.inductionOn generalizing state with
  | pure value => simp
  | query_bind query continuation ih =>
      simp only [simulateQ_bind, StateT.run_bind, ExceptT.run_bind]
      rw [simulateQ_spec_query]
      simp only [liftStateTExceptTBase, simulateQ_spec_query]
      rw [StateT.run_lift, ExceptT.run_bind, ExceptT.run_lift]
      rw [bind_map_left]
      rw [map_bind]
      simp only [ExceptT.run_pure]
      simp only [bind_pure_comp]
      rw [bind_map_left]
      apply bind_congr
      intro answer
      exact ih answer state

/-- Push an outer oracle interpretation through the base oracle computation of an
`ExceptT`-valued query implementation. -/
noncomputable def mapExceptTBase {ι₀ ι₁ : Type _}
    {spec₀ : OracleSpec ι₀} {spec₁ : OracleSpec ι₁}
    {m : Type u → Type v} [Monad m] {ε : Type _}
    (outer : QueryImpl spec₁ m)
    (inner : QueryImpl spec₀ (ExceptT ε (OracleComp spec₁))) :
    QueryImpl spec₀ (ExceptT ε m) := fun t =>
  ExceptT.mk (simulateQ outer (inner t).run)

/-- Running an `ExceptT` handler and then interpreting its base oracle computations is the same
as first mapping the handler's base through the outer interpreter. -/
theorem simulateQ_mapExceptTBase_run {ι₀ ι₁ : Type _}
    {spec₀ : OracleSpec ι₀} {spec₁ : OracleSpec ι₁}
    {m : Type u → Type v} [Monad m] [LawfulMonad m] {ε : Type _}
    (outer : QueryImpl spec₁ m)
    (inner : QueryImpl spec₀ (ExceptT ε (OracleComp spec₁)))
    {α : Type u} (oa : OracleComp spec₀ α) :
    simulateQ outer (ExceptT.run (simulateQ inner oa)) =
      ExceptT.run (simulateQ (outer.mapExceptTBase inner) oa) := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
      simp only [simulateQ_bind, ExceptT.run_bind]
      rw [simulateQ_spec_query]
      simp only [mapExceptTBase, simulateQ_spec_query]
      apply bind_congr
      intro result
      cases result with
      | error e => rfl
      | ok value => exact ih value

/-- Push an outer oracle interpretation through a stateful `ExceptT` handler. -/
noncomputable def mapStateTExceptTBase {ι₀ ι₁ : Type _}
    {spec₀ : OracleSpec ι₀} {spec₁ : OracleSpec ι₁}
    {m : Type u → Type v} [Monad m] {σ ε : Type _}
    (outer : QueryImpl spec₁ m)
    (inner : QueryImpl spec₀ (StateT σ (ExceptT ε (OracleComp spec₁)))) :
    QueryImpl spec₀ (StateT σ (ExceptT ε m)) := fun t =>
  StateT.mk fun s => ExceptT.mk (simulateQ outer ((inner t).run s).run)

/-- Simulating the base oracle computation of a stateful lossless handler commutes with
interpreting the handler after mapping its base through the same outer interpreter. -/
theorem simulateQ_mapStateTExceptTBase_run {ι₀ ι₁ : Type _}
    {spec₀ : OracleSpec ι₀} {spec₁ : OracleSpec ι₁}
    {m : Type u → Type v} [Monad m] [LawfulMonad m] {σ ε : Type _}
    (outer : QueryImpl spec₁ m)
    (inner : QueryImpl spec₀ (StateT σ (ExceptT ε (OracleComp spec₁))))
    {α : Type u} (oa : OracleComp spec₀ α) (s : σ) :
    simulateQ outer (ExceptT.run ((simulateQ inner oa).run s)) =
      ExceptT.run ((simulateQ (outer.mapStateTExceptTBase inner) oa).run s) := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp
  | query_bind t k ih =>
      simp only [simulateQ_bind, StateT.run_bind, ExceptT.run_bind]
      rw [simulateQ_spec_query]
      simp only [mapStateTExceptTBase, simulateQ_spec_query]
      apply bind_congr
      intro result
      cases result with
      | error e => rfl
      | ok result => exact ih result.1 result.2

/-- If an `ExceptT`-valued stateful oracle computation is followed by a pure state-dependent
postprocessing step, interpreting its base oracle calls commutes with that whole bind.  This is
the naturality law used by a lossless D2F handler: first run one D2S step, then classify its
result as either a continuing state or a structured stop. -/
theorem simulateQ_mapStateTExceptTBase_bind_pure_run {ι₀ ι₁ : Type _}
    {spec₀ : OracleSpec ι₀} {spec₁ : OracleSpec ι₁}
    {m : Type u → Type v} [Monad m] [LawfulMonad m] {σ ε α β : Type u}
    (outer : QueryImpl spec₁ m)
    (inner : QueryImpl spec₀ (StateT σ (ExceptT ε (OracleComp spec₁))))
    (oa : OracleComp spec₀ α) (state : σ)
    (post : α → σ → Except ε (β × σ)) :
    simulateQ outer
      (ExceptT.run ((do
        let value ← simulateQ inner oa
        StateT.mk fun current => ExceptT.mk (pure (post value current))).run state)) =
      ExceptT.run ((do
        let value ← simulateQ (outer.mapStateTExceptTBase inner) oa
        StateT.mk fun current => ExceptT.mk (pure (post value current))).run state) := by
  simp only [StateT.run_bind, ExceptT.run_bind]
  rw [simulateQ_bind]
  rw [simulateQ_mapStateTExceptTBase_run]
  rw [bind_congr]
  intro result
  cases result <;> rfl

/-- The preceding naturality law in the fully unwrapped `ExceptT` form used by handlers with an
explicit `StateT` run.  Keeping this form available avoids fragile reassociation of `.run` when
the handler is itself embedded in a larger state transformer. -/
theorem simulateQ_mapStateTExceptTBase_bind_pure_run_unwrapped {ι₀ ι₁ : Type _}
    {spec₀ : OracleSpec ι₀} {spec₁ : OracleSpec ι₁}
    {m : Type u → Type v} [Monad m] [LawfulMonad m] {σ ε α β : Type u}
    (outer : QueryImpl spec₁ m)
    (inner : QueryImpl spec₀ (StateT σ (ExceptT ε (OracleComp spec₁))))
    (oa : OracleComp spec₀ α) (state : σ)
    (post : α → σ → Except ε (β × σ)) :
    ExceptT.run (simulateQ outer
      (((do
        let value ← simulateQ inner oa
        StateT.mk fun current => ExceptT.mk (pure (post value current))).run state).run)) =
      ((do
        let value ← simulateQ (outer.mapStateTExceptTBase inner) oa
        StateT.mk fun current => ExceptT.mk (pure (post value current))).run state).run :=
  simulateQ_mapStateTExceptTBase_bind_pure_run outer inner oa state post

/-- Push an outer oracle interpretation through the exact
`StateT σ (StateT τ (ExceptT ε ·))` stack used by lossless stateful simulations. -/
noncomputable def mapStateTStateTExceptTBase {ι₀ ι₁ : Type _}
    {spec₀ : OracleSpec ι₀} {spec₁ : OracleSpec ι₁}
    {m : Type u → Type v} [Monad m] {σ τ ε : Type _}
    (outer : QueryImpl spec₁ m)
    (inner : QueryImpl spec₀ (StateT σ (StateT τ (ExceptT ε (OracleComp spec₁))))) :
    QueryImpl spec₀ (StateT σ (StateT τ (ExceptT ε m))) := fun t =>
  StateT.mk fun s => StateT.mk fun q =>
    ExceptT.mk (simulateQ outer (((inner t).run s).run q).run)

/-- Simulating the base oracle computation of a two-state lossless handler commutes with
interpreting the handler after its base has been mapped through the same outer interpreter. -/
theorem simulateQ_mapStateTStateTExceptTBase_run {ι₀ ι₁ : Type _}
    {spec₀ : OracleSpec ι₀} {spec₁ : OracleSpec ι₁}
    {m : Type u → Type v} [Monad m] [LawfulMonad m] {σ τ ε : Type _}
    (outer : QueryImpl spec₁ m)
    (inner : QueryImpl spec₀ (StateT σ (StateT τ (ExceptT ε (OracleComp spec₁)))))
    {α : Type u} (oa : OracleComp spec₀ α) (s : σ) (q : τ) :
    simulateQ outer (ExceptT.run (((simulateQ inner oa).run s).run q)) =
      ExceptT.run (((simulateQ (outer.mapStateTStateTExceptTBase inner) oa).run s).run q) := by
  induction oa using OracleComp.inductionOn generalizing s q with
  | pure x => simp
  | query_bind t k ih =>
      simp only [simulateQ_bind, StateT.run_bind, ExceptT.run_bind]
      rw [simulateQ_spec_query]
      simp only [mapStateTStateTExceptTBase, simulateQ_spec_query]
      apply bind_congr
      intro result
      cases result with
      | error e => rfl
      | ok result => exact ih result.1.1 result.1.2 result.2

end QueryImpl
