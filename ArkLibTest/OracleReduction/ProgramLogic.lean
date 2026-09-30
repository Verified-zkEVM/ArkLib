/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

import ArkLib.OracleReduction.ProgramLogic

/-!
# `prvcgen` on reduction executions

`prvcgen` walks a verifier challenge with `ProtocolSpec.Qualitative.Spec.getChallenge`, also when
the challenge is lifted into a reduction's oracle world `oSpec + [pSpec.Challenge]ₒ`. The
completeness proofs converted to `prvcgen` (for example
`CoordinateWise.CommittedScalar.reduction_run_support`) exercise `Reduction.run_run_eq`.
-/

open OracleComp OracleSpec ProtocolSpec

namespace ProgramLogicRegression

/-- One verifier challenge in `Fin 4`. -/
abbrev protocol : ProtocolSpec 1 := ⟨fun _ => .V_to_P, fun _ => Fin 4⟩

/-- A challenge may be any value, so a draw paired with itself is a diagonal pair. -/
example : ∀ x ∈ support (do
      let c ← protocol.getChallenge ⟨0, rfl⟩
      pure (c, c)), x.1 = x.2 := by
  prvcgen

/-- The same draw lifted into a reduction's oracle world `oSpec + [pSpec.Challenge]ₒ`. -/
example {ι : Type} (oSpec : OracleSpec ι) :
    ∀ x ∈ support (do
      let c ← (liftM (protocol.getChallenge ⟨0, rfl⟩) :
        OracleComp (oSpec + [protocol.Challenge]ₒ'challengeOracleInterface) _)
      pure (c.val < 4)), x = true := by
  prvcgen
  exact decide_eq_true (Fin.isLt _)

end ProgramLogicRegression
