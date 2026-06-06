/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VCVio.EvalDist.Instances.OptionT
import VCVio.EvalDist.Monad.Map
import VCVio.OracleComp.ProbComp

/-!
# Additions to VCV-io's `EvalDist.Instances.OptionT`
-/

/-- Bridge lemma: when two `OptionT ProbComp` computations have underlying `run`s related by
    an `Option.map` of a function `f`, their probability events of `P` and `P ∘ f` agree. -/
lemma OptionT.probEvent_eq_of_run_map_eq {α β : Type}
    (mx : OptionT ProbComp α) (my : OptionT ProbComp β) (f : β → α) (P : α → Prop)
    (h : mx.run = (Option.map f) <$> my.run) :
    Pr[P | mx] = Pr[P ∘ f | my] := by
  have hmx : mx = f <$> my := by
    change mx.run = (f <$> my).run
    rw [OptionT.run_map]; exact h
  rw [hmx, probEvent_map]
