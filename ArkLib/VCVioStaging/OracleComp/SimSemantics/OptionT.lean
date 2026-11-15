/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/
module

public import VCVio.OracleComp.SimSemantics.OptionT.Basic

/-!
# Simulation of optional values

Interpreting a lifted optional value preserves it without making oracle queries.
-/

@[expose] public section

namespace OracleComp

/-- Interpreting an optional value retains both success and failure unchanged. -/
theorem simulateQ_getM_run {ι α : Type} {spec : OracleSpec ι}
    {m : Type → Type*} [Monad m] (impl : QueryImpl spec m) (x : Option α) :
    simulateQ impl (x.getM : OptionT (OracleComp spec) α).run = pure x := by
  cases x <;> rfl

end OracleComp
