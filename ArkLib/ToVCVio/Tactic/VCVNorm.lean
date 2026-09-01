/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import VCVio.OracleComp.Coercions.SubSpec
import VCVio.OracleComp.QueryTracking.LoggingOracle
import VCVio.OracleComp.SimSemantics.Append
import VCVio.OracleComp.SimSemantics.OptionT.Basic
import VCVio.OracleComp.SimSemantics.StateT.Basic
import VCVio.OracleComp.SimSemantics.WriterT.Basic

/-!
# `vcv_norm` : a normalization tactic for VCVio monad goals

When one unfolds the `OracleReduction` security notions (soundness, knowledge soundness, their
adaptive and coin-bearing variants, completeness) to prove a *game-distribution =
experiment-distribution* equality, the goal is dominated by generic monad plumbing over
`OracleComp` / `simulateQ` / `StateT` / `OptionT` / `WriterT` / `loggingOracle` / `liftComp`.
This file packages that plumbing so the user is left only with the genuinely
construction-specific congruence leaves.

## Surface

- `vcv_norm` — the workhorse `simp only` normalizer: pushes `simulateQ` to the leaves through
  every transformer `run`, flattens `addLift` towers, turns `liftComp` over an `addLift` into the
  inner `simulateQ`, reduces `OptionT`/`StateT`/`WriterT` `run`s to canonical form, and *strips
  `loggingOracle` value-marginals* (via the `loggingStrip` simproc) whenever the log is unused.
- `vcv_strip_log` — just the `loggingStrip` simproc, for when only log-stripping is wanted.
- `vcv_init_peel` — peels a shared `do let s ← init; (simulateQ … ).run' s` prelude, reducing a
  distribution equality to the underlying `simulateQ … = simulateQ …` body equality.
- `vcv_congr` — drives the body equality through `bind_congr` / `simulateQ_bind_congr`, closing
  `rfl` leaves and leaving genuine handler-identity goals for the user.
- `vcv` — umbrella: `vcv_norm` then `vcv_congr`.
- `vcv_event [hev, hdist]` — the generic `Pr`-level closing chain shared by every recipe.

## The logging strip

`loggingOracle.run_simulateQ_bind_fst : (simulateQ loggingOracle oa).run >>= (fun x => ob x.1)
= oa >>= ob` is `@[simp]`, but it does **not** fire automatically: `?ob x.1` is not a
higher-order *pattern* (the argument `x.1 = Prod.fst x` is not a bound variable), so neither `simp`
nor `rw` can synthesize `?ob`.  The `loggingStrip` simproc synthesizes it by `kabstract`-ing the
`Prod.fst x` occurrences in the continuation body — and *refuses* to strip when the log component
`x.2` is genuinely used (which would be unsound).  Because it is a simproc it descends under
binders, so nested logs (the `prover → verifier → extractor` chains) strip at any depth, subsuming
the hand-written `logging_strip₂` / `logging_strip₃`.
-/

open Lean Lean.Meta Lean.Elab.Tactic OracleComp OracleSpec

namespace ToVCVio.VCVNorm

universe u v

/-! ## Generic `OptionT` shape facts (formerly inlined as local `hgetM`/`helim`) -/

/-- `OptionT.run` of `Option.getM` is `pure` — the canonical de-abort of an already-resolved
`Option`.  Generic; previously appeared as a local `hgetM` `have` in every DSFS game proof. -/
@[simp]
theorem optionT_run_getM {m : Type u → Type v} [Monad m] {α : Type u} (o : Option α) :
    (OptionT.run o.getM : m (Option α)) = pure o := by
  cases o <;> rfl

/-- A pure `Option.elim` into `pure none`/`pure (some (g ·))` collapses to `pure (o.map g)`.
Generic; previously appeared as a local `helim` `have`. -/
@[simp]
theorem optionT_elim_pure_map {m : Type u → Type v} [Monad m] {α γ : Type u}
    (g : α → γ) (o : Option α) :
    (o.elim (pure none) (fun s => pure (some (g s))) : m (Option γ)) = pure (o.map g) := by
  cases o <;> rfl

/-! ## `simulateQ` / `OptionT` bridge (formerly the local `hsm` `have`) -/

/-- `OptionT.mk` is the identity coercion `m (Option α) → OptionT m α`, so it disappears under
`simulateQ`.  Lets `simulateQ`-pushing reach a `liftComp`/handler that an `OptionT.mk` wrapper
would otherwise hide. -/
theorem simulateQ_optionT_mk {ι : Type} {spec : OracleSpec ι} {n : Type → Type v} [Monad n]
    {α : Type} (impl : QueryImpl spec n) (x : OracleComp spec (Option α)) :
    simulateQ impl (OptionT.mk x) = simulateQ impl x := rfl

/-- `simulateQ` commutes with the `OptionT` functor map as the `Option.map` of its image.
Bridges an `OptionT`-functor `f <$> m` to the `Option.map f` of the simulated computation. -/
theorem simulateQ_optionT_map {ι : Type} {spec : OracleSpec ι} {n : Type → Type v}
    [Monad n] [LawfulMonad n] (impl : QueryImpl spec n) {β γ : Type}
    (f : β → γ) (m : OptionT (OracleComp spec) β) :
    simulateQ impl ((f <$> m : OptionT (OracleComp spec) γ))
      = Option.map f <$> simulateQ impl m := by
  rw [← simulateQ_map]; congr 1; apply OptionT.ext; rw [OptionT.run_map]; rfl

/-! ## Generic `simulateQ` bind congruence and `loggingOracle` value-marginal strips -/

/-- Congruence for `simulateQ` over a bind: equate the heads and, pointwise, the simulated tails. -/
theorem simulateQ_bind_congr {ι : Type} {spec : OracleSpec ι} {n : Type → Type v}
    [Monad n] [LawfulMonad n] {impl : QueryImpl spec n} {α β : Type}
    (x y : OracleComp spec α) (f g : α → OracleComp spec β)
    (h1 : x = y) (h2 : ∀ a, simulateQ impl (f a) = simulateQ impl (g a)) :
    simulateQ impl (x >>= f) = simulateQ impl (y >>= g) := by
  subst h1; simp only [simulateQ_bind]; exact bind_congr h2

/-- The `OptionT` `monadLift` (`liftM`) is `OptionT.lift` — a syntactic bridge so that
`simulateQ_optionT_lift` (keyed on `OptionT.lift`) fires on goals phrased with `liftM`.  Kept out of
the default simp set / `vcv_norm` (it perturbs otherwise-`rfl` forms); supply it explicitly. -/
theorem optionT_liftM_eq_lift {m : Type u → Type v} [Monad m] {α : Type u} (comp : m α) :
    (liftM comp : OptionT m α) = OptionT.lift comp := rfl

/-- Depth-2 `loggingOracle` value-marginal strip: two nested logged runs feeding a read-out that
uses only their values drop both logs.  (The `loggingStrip` simproc subsumes this; kept as a named
lemma for explicit `rw` use.) -/
theorem logging_strip₂ {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β γ : Type}
    (oa : OracleComp spec α) (ob : α → OracleComp spec β) (k : α → β → γ) :
    ((simulateQ loggingOracle oa).run >>= fun p =>
      (simulateQ loggingOracle (ob p.1)).run >>= fun q => pure (k p.1 q.1))
      = oa >>= fun a => ob a >>= fun b => pure (k a b) := by
  rw [loggingOracle.run_simulateQ_bind_fst (oa := oa)
      (ob := fun a => (simulateQ loggingOracle (ob a)).run >>= fun q => pure (k a q.1))]
  refine bind_congr fun a => ?_
  rw [loggingOracle.run_simulateQ_bind_fst (oa := ob a) (ob := fun b => pure (k a b))]

/-- Depth-3 `loggingOracle` value-marginal strip (the `prover → verifier → extractor` chain of the
KS games).  (Subsumed by the `loggingStrip` simproc; kept as a named lemma.) -/
theorem logging_strip₃ {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β γ δ : Type}
    (oa : OracleComp spec α) (ob : α → OracleComp spec β) (oc : α → β → OracleComp spec γ)
    (k : α → β → γ → δ) :
    ((simulateQ loggingOracle oa).run >>= fun p =>
      (simulateQ loggingOracle (ob p.1)).run >>= fun q =>
        (simulateQ loggingOracle (oc p.1 q.1)).run >>= fun r => pure (k p.1 q.1 r.1))
      = oa >>= fun a => ob a >>= fun b => oc a b >>= fun c => pure (k a b c) := by
  rw [loggingOracle.run_simulateQ_bind_fst (oa := oa)
      (ob := fun a => (simulateQ loggingOracle (ob a)).run >>= fun q =>
        (simulateQ loggingOracle (oc a q.1)).run >>= fun r => pure (k a q.1 r.1))]
  refine bind_congr fun a => ?_
  rw [loggingOracle.run_simulateQ_bind_fst (oa := ob a)
      (ob := fun b => (simulateQ loggingOracle (oc a b)).run >>= fun r => pure (k a b r.1))]
  refine bind_congr fun b => ?_
  rw [loggingOracle.run_simulateQ_bind_fst (oa := oc a b) (ob := fun c => pure (k a b c))]

/-! ## The `loggingStrip` simproc -/

/-- View `e` as a logging bind `(simulateQ loggingOracle oa).run >>= cont` (a monadic `Bind.bind`
whose lhs contains `simulateQ loggingOracle oa`); return `(oa, cont)`. -/
def matchLogBind (e : Expr) : MetaM (Option (Expr × Expr)) := do
  unless e.isAppOf ``Bind.bind && e.getAppNumArgs == 6 do return none
  let args := e.getAppArgs
  let lhs := args[4]!
  let cont := args[5]!
  let some sq := lhs.find? (fun s =>
    s.isAppOf ``simulateQ &&
      s.getAppArgs.any (fun a => a.getAppFn.constName? == some ``OracleSpec.loggingOracle)) |
    return none
  let sqArgs := sq.getAppArgs
  return some (sqArgs[sqArgs.size - 1]!, cont)

/-- Build `(rhs, proof : e = rhs)` stripping a `loggingOracle` value-marginal, or `none` if the log
component is actually used (so the strip would be unsound). -/
def mkStripEq (e oa cont : Expr) : MetaM (Option (Expr × Expr)) := do
  lambdaTelescope cont fun xs body => do
    unless xs.size == 1 do return none
    let x := xs[0]!
    let xTy ← whnf (← inferType x)
    let .app (.app prodC pα) pω := xTy | return none
    unless prodC.isAppOf ``Prod do return none
    let fstApp := mkApp3 (mkConst ``Prod.fst [(← getLevel pα), (← getLevel pω)]) pα pω x
    let bodyAbs ← kabstract body fstApp
    if bodyAbs.containsFVar x.fvarId! then return none
    let ob := Expr.lam `a pα bodyAbs BinderInfo.default
    let proof ← mkAppM ``loggingOracle.run_simulateQ_bind_fst #[oa, ob]
    let some (_, _, rhs) := (← inferType proof).eq? | return none
    return some (rhs, ← mkExpectedTypeHint proof (← mkEq e rhs))

/-- Strip a `loggingOracle` value-marginal whenever the log is unused.  Fires under binders and on
nested logs, since `simp` re-descends into the produced term. -/
simproc_decl loggingStrip (Bind.bind _ _) := fun e => do
  let some (oa, cont) ← matchLogBind e | return .continue
  let some (rhs, proof) ← mkStripEq e oa cont | return .continue
  return .visit { expr := rhs, proof? := proof }

end ToVCVio.VCVNorm

open ToVCVio.VCVNorm in
/-! ## The tactics -/

open Lean.Parser.Tactic in
/-- Push `simulateQ` to the leaves through every transformer `run`, flatten `addLift`, collapse
`liftComp`-over-`addLift`, reduce `OptionT`/`StateT`/`WriterT` `run`s, and strip unused
`loggingOracle` value-marginals.  Supports a location: `vcv_norm at h`.  For extra lemmas, follow
with an ordinary `simp only [...]`. -/
macro (name := vcvNorm) "vcv_norm" loc:(location)? : tactic =>
    `(tactic| simp only [
        -- simulateQ push-in (NB: simulateQ_spec_query, not simulateQ_query)
        simulateQ_pure, simulateQ_bind, simulateQ_map, simulateQ_spec_query,
        simulateQ_seq, simulateQ_seqLeft, simulateQ_seqRight, simulateQ_ite, simulateQ_id',
        simulateQ_query_bind, simulateQ_list_mapM, simulateQ_list_forM, simulateQ_list_forIn,
        simulateQ_option_elim, simulateQ_optionT_lift, simulateQ_optionT_bind,
        -- handler algebra
        QueryImpl.simulateQ_compose, QueryImpl.addLift_def,
        QueryImpl.liftTarget_self, QueryImpl.liftTarget_apply,
        QueryImpl.simulateQ_add_liftComp_left, QueryImpl.simulateQ_add_liftComp_right,
        -- liftComp / monadLift
        OracleComp.liftComp_pure, OracleComp.liftComp_bind, OracleComp.liftComp_map,
        OracleComp.liftComp_self, monadLift_eq_self,
        -- OptionT run-level normal form
        OptionT.run_bind, OptionT.run_pure, OptionT.run_map, OptionT.run_mk,
        OptionT.run_monadLift, Option.elimM, Option.elim_some,
        ToVCVio.VCVNorm.optionT_run_getM, ToVCVio.VCVNorm.optionT_elim_pure_map,
        -- StateT / WriterT run' normal form
        StateT.run'_map', StateT.run'_bind', StateT.run'_pure', WriterT.run_map',
        -- generic monad glue
        pure_bind, bind_map_left, map_bind, map_pure, Option.map_map, Function.comp_def,
        -- logging value-marginal strip
        ToVCVio.VCVNorm.loggingStrip] $(loc)?)

open Lean.Parser.Tactic in
/-- Strip all unused `loggingOracle` value-marginals reachable in the goal. -/
macro "vcv_strip_log" loc:(location)? : tactic =>
  `(tactic| simp only [ToVCVio.VCVNorm.loggingStrip] $(loc)?)

/-- Peel a shared `do let s ← init; (simulateQ … ).run' s` prelude from a distribution equality,
reducing it to the underlying `simulateQ … = simulateQ …` body equality (under `bind_congr`). -/
macro "vcv_init_peel" : tactic =>
  `(tactic|
    (rw [map_bind];
     refine bind_congr fun s => ?_;
     rw [← StateT.run'_map', ← simulateQ_map]))

/-- Drive a `simulateQ … = simulateQ …` body equality through `bind_congr` /
`simulateQ_bind_congr`, closing `rfl` leaves and leaving genuine handler-identity goals. -/
macro "vcv_congr" : tactic =>
  `(tactic|
    (repeat' first
      | rfl
      | refine ToVCVio.VCVNorm.simulateQ_bind_congr _ _ _ _ rfl (fun a => ?_)
      | refine bind_congr (fun a => ?_)))

/-- Umbrella: normalize, then drive congruence. -/
macro "vcv" : tactic => `(tactic| (vcv_norm; vcv_congr))

/-- **Compatibility plumbing** — the lean drop-in for hand-tuned proofs that were written against a
specific normalization shape.  Same lemma set as a minimal `simulateQ`/`OptionT` push, but with the
formerly-local `hgetM`/`helim` `have`s replaced by the global `optionT_run_getM` /
`optionT_elim_pure_map`, so no local scaffolding is required.  Prefer `vcv_norm` for new proofs (it
also flattens `addLift`, collapses `liftComp`, and strips `loggingOracle` value-marginals). -/
macro "vcv_simp" : tactic =>
  `(tactic| simp only [
      OptionT.run_bind, Option.elimM, OptionT.run_monadLift, monadLift_eq_self,
      OptionT.run_mk, OptionT.run_pure, pure_bind, bind_map_left, map_bind,
      Option.elim_some, ToVCVio.VCVNorm.optionT_run_getM,
      ToVCVio.VCVNorm.optionT_elim_pure_map, map_pure, Option.map_map, Function.comp_def,
      simulateQ_bind, simulateQ_pure, simulateQ_map, QueryImpl.simulateQ_compose])

/-- The generic `Pr`-level closing chain of a recipe: rewrite by the distribution equality
`hdist`, push the event through the functor `map` (`probEvent_map`), then rewrite the event
identity `hev`. -/
macro "vcv_event" "[" hev:term "," hdist:term "]" : tactic =>
  `(tactic| (rw [$hdist:term, probEvent_map, $hev:term]))
