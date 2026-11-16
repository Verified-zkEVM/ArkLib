/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# Zero-budget predicate query bounds through `OptionT` / `StateT` layers

`IsQueryBoundP oa p 0` ("`oa` makes no `p`-queries") is stated for bare `OracleComp`
computations.  Structured simulators (e.g. the DSFS `D2SQuery` step) live in towers
`StateT σ (OptionT (OracleComp spec))`; establishing the zero bound for `((x.run s).run)`
by distributing the `run`s through every `do`-bind is brittle and quadratic.

This file provides a compositional interface instead: `AbortZeroBoundP` (through `OptionT`)
and `StateTAbortZeroBoundP` (through `StateT` over `OptionT`), with introduction rules for
`pure` / `bind` / `failure` / `get` / `set` / `modifyGet` / lifts.  A structural walk over a
`do`-block then applies the rules leaf-by-leaf without ever normalizing the monad stack.

Upstreaming candidate for `VCVio.OracleComp.QueryTracking.QueryBound`.
-/

@[expose] public section

open OracleComp

namespace OracleComp

variable {ι : Type} {spec : OracleSpec ι} {α β σ : Type}
  (p : ι → Prop) [DecidablePred p]

/-- Zero-budget `p`-query bound through the `OptionT` abort layer. -/
def AbortZeroBoundP (x : OptionT (OracleComp spec) α) : Prop :=
  IsQueryBoundP x.run p 0

/-- Zero-budget `p`-query bound through `StateT` over the `OptionT` abort layer, for every
initial state. -/
def StateTAbortZeroBoundP (x : StateT σ (OptionT (OracleComp spec)) α) : Prop :=
  ∀ s : σ, AbortZeroBoundP p (x.run s)

variable {p}

/-! ### `OptionT` layer rules -/

lemma AbortZeroBoundP.pure (a : α) :
    AbortZeroBoundP p (pure a : OptionT (OracleComp spec) α) := by
  unfold AbortZeroBoundP
  rw [OptionT.run_pure]
  exact isQueryBoundP_pure p _ 0

lemma AbortZeroBoundP.failure :
    AbortZeroBoundP p (failure : OptionT (OracleComp spec) α) := by
  unfold AbortZeroBoundP
  rw [OptionT.run_failure]
  exact isQueryBoundP_pure p _ 0

lemma AbortZeroBoundP.bind {x : OptionT (OracleComp spec) α}
    {f : α → OptionT (OracleComp spec) β}
    (hx : AbortZeroBoundP p x) (hf : ∀ a, AbortZeroBoundP p (f a)) :
    AbortZeroBoundP p (x >>= f) := by
  unfold AbortZeroBoundP at *
  rw [OptionT.run_bind]
  unfold Option.elimM
  refine (isQueryBoundP_bind hx (fun o _ => ?_) : IsQueryBoundP _ p (0 + 0))
  cases o with
  | none => exact isQueryBoundP_pure p _ 0
  | some a => exact hf a

lemma AbortZeroBoundP.lift {c : OracleComp spec α} (hc : IsQueryBoundP c p 0) :
    AbortZeroBoundP p (OptionT.lift c) := by
  unfold AbortZeroBoundP
  rw [OptionT.run_lift]
  exact (isQueryBoundP_bind hc (fun a _ => isQueryBoundP_pure p _ 0) :
    IsQueryBoundP _ p (0 + 0))

/-! ### `StateT` layer rules -/

lemma StateTAbortZeroBoundP.pure (a : α) :
    StateTAbortZeroBoundP p (pure a : StateT σ (OptionT (OracleComp spec)) α) := by
  intro s
  rw [StateT.run_pure]
  exact AbortZeroBoundP.pure _

lemma StateTAbortZeroBoundP.bind {x : StateT σ (OptionT (OracleComp spec)) α}
    {f : α → StateT σ (OptionT (OracleComp spec)) β}
    (hx : StateTAbortZeroBoundP p x) (hf : ∀ a, StateTAbortZeroBoundP p (f a)) :
    StateTAbortZeroBoundP p (x >>= f) := by
  intro s
  rw [StateT.run_bind]
  exact AbortZeroBoundP.bind (hx s) (fun pr => hf pr.1 pr.2)

/-- Mapping the returned value does not add oracle queries. -/
lemma StateTAbortZeroBoundP.map {x : StateT σ (OptionT (OracleComp spec)) α}
    (hx : StateTAbortZeroBoundP p x) (f : α → β) :
    StateTAbortZeroBoundP p (f <$> x) := by
  rw [map_eq_bind_pure_comp]
  exact StateTAbortZeroBoundP.bind hx (fun _ => StateTAbortZeroBoundP.pure _)

lemma StateTAbortZeroBoundP.get :
    StateTAbortZeroBoundP p (get : StateT σ (OptionT (OracleComp spec)) σ) := by
  intro s
  rw [StateT.run_get]
  exact AbortZeroBoundP.pure _

lemma StateTAbortZeroBoundP.set (s' : σ) :
    StateTAbortZeroBoundP p (set s' : StateT σ (OptionT (OracleComp spec)) PUnit) := by
  intro s
  rw [StateT.run_set]
  exact AbortZeroBoundP.pure _

lemma StateTAbortZeroBoundP.liftAbort {c : OptionT (OracleComp spec) α}
    (hc : AbortZeroBoundP p c) :
    StateTAbortZeroBoundP p (StateT.lift c : StateT σ (OptionT (OracleComp spec)) α) := by
  intro s
  rw [StateT.run_lift]
  exact AbortZeroBoundP.bind hc (fun a => AbortZeroBoundP.pure _)

lemma StateTAbortZeroBoundP.liftComp {c : OracleComp spec α} (hc : IsQueryBoundP c p 0) :
    StateTAbortZeroBoundP p
      (StateT.lift (OptionT.lift c) : StateT σ (OptionT (OracleComp spec)) α) :=
  StateTAbortZeroBoundP.liftAbort (AbortZeroBoundP.lift hc)

end OracleComp
