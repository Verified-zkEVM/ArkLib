/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

import ArkLib.OracleReduction.ProgramLogic

/-!
# `prvcgen` on reduction executions

`prvcgen` walks a verifier challenge with `ProtocolSpec.Necessary.Spec.getChallenge`, also when
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

/-- An opaque initial draw is read through its support in the upper reading: once the
`OptionT` event is stated on the underlying run, an output outside the language has
probability zero. -/
example {σ : Type} (init : ProbComp σ) (lang : Set ℕ) (h : 7 ∉ lang) :
    Pr{let stmtOut ← (OptionT.mk (do
      let _ ← init
      pure (some 7)) : OptionT ProbComp ℕ)}[stmtOut ∈ lang] = 0 := by
  simp only [OptionT.prEvent_mk]
  prvcgen [OracleComp.Upper.Spec.ofSupport init]
  exact (propInd_eq_zero_iff.mpr h).le

/-- A simulated opaque program is read through its support, with the state it runs from left
to unification. -/
example {ι σ : Type} (oSpec : OracleSpec ι) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (init : ProbComp σ) (oa : OracleComp oSpec ℕ) (lang : Set ℕ) (h : ∀ n, n ∉ lang) :
    Pr{let s ← init; let x ← (simulateQ impl oa).run s}[x.1 ∈ lang] = 0 := by
  prvcgen [OracleComp.Upper.Spec.ofSupport init,
    OracleComp.Upper.Spec.ofSupport ((simulateQ impl oa).run _)]
  simp [h]

end ProgramLogicRegression
