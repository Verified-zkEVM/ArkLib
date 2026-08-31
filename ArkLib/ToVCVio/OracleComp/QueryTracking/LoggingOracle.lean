/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import VCVio

/-!
# Additions to VCV-io's `loggingOracle`

Two `loggingOracle` lemmas used by knowledge-soundness reductions: one collapses a `pure`
`OptionT` computation under logging, the other discards a query log beneath a continuation that
only reads the run result (e.g. an extractor).

Both are upstreaming candidates: they mention nothing outside VCV-io, and
`map_fst_run_simulateQ` is a strict generalisation of VCV-io's own
`loggingOracle.fst_map_run_simulateQ` (which is the `h = id` case, and whose `@[simp]` form cannot
fire on the factored spelling).
-/

open OracleComp OracleSpec

namespace loggingOracle

/-- Logging a `pure` `OptionT` computation (e.g. an always-accepting or already-collapsed
verifier `verify`) produces the same value with an empty query log. Stated over the
`OptionT`-coerced `pure` so it rewrites knowledge-soundness game terms directly. -/
lemma run_simulateQ_optionT_pure
    {ιs : Type} {spec : OracleSpec ιs} {α : Type} (a : α) :
    (simulateQ loggingOracle
        ((pure a : OptionT (OracleComp spec) α) : OracleComp spec (Option α))).run
      = (pure (some a, ∅) : OracleComp spec (Option α × QueryLog spec)) := by
  rw [show ((pure a : OptionT (OracleComp spec) α) : OracleComp spec (Option α))
      = (pure (some a) : OracleComp spec (Option α)) from rfl, simulateQ_pure]
  rfl

/-- Discard a query log under a continuation that only uses the run result (e.g. an extractor
that ignores the logs): mapping a `Prod.fst`-factoring function over a logged run is mapping it
over the bare run. Map-shaped companion of `loggingOracle.run_simulateQ_bind_fst`; apply by
`Eq.trans` (definitional unification — the factored spelling is not `rw`-matchable). -/
lemma map_fst_run_simulateQ {ιs : Type} {spec : OracleSpec.{0, 0} ιs}
    {α β : Type} (oa : OracleComp spec α) (h : α → β) :
    (fun x ↦ h x.1) <$> (simulateQ loggingOracle oa).run = h <$> oa := by
  refine Eq.trans
    (Eq.symm (Functor.map_map Prod.fst h ((simulateQ loggingOracle oa).run))) ?_
  rw [loggingOracle.fst_map_run_simulateQ]

end loggingOracle
