/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import VCVio.EvalDist.Instances.OptionT
/-! Event probabilities for optional computations. -/

namespace OptionT

universe u v

variable {m : Type u → Type v} [Monad m] [MonadLiftT m SPMF]
  [LawfulMonadLiftT m SPMF] {α : Type u}

/-- An event in an optional computation is the corresponding event on successful results
of its underlying computation; `none` contributes no mass. -/
theorem probEvent_eq_run (mx : OptionT m α) (P : α → Prop) :
    Pr[ P | mx] = Pr[ fun x ↦ x.elim False P | mx.run] := by
  classical
  rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite, tsum_option _ ENNReal.summable]
  simp only [Option.elim_none, Option.elim_some, if_false, zero_add, probOutput_eq]
  rfl

end OptionT
