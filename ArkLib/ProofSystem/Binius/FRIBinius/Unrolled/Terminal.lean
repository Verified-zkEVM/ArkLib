/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.ProofSystem.Binius.BinaryBasefold.Spec
public import ArkLib.OracleReduction.Security.GuardedRoundByRound

/-!
# Terminal check of the fused sumcheck and folding loop

The prover sends the final folded constant. The verifier checks the final sum-check target
against the public multiplier evaluated at the folding challenges times that constant. In
particular it never divides by the multiplier, and it forwards the received constant unchanged
when the multiplier vanishes. The output retains the oracle family for the query phase.

The multiplier evaluator and output-context projection are explicit parameters. FRI-Binius
instantiates them with the ring-switching multiplier and the original query's suffix.
-/

@[expose] public section

namespace Binius.FRIBinius.Unrolled.Terminal

open Binius.BinaryBasefold OracleSpec OracleComp ProtocolSpec

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L]
variable (K : Type) [Field K] [Fintype K] [DecidableEq K]
  [Fact (Fintype.card K = 2)] [Algebra K L]
local instance [Finite K] : Fact (Nat.Prime (ringChar K)) := ⟨CharP.prime_ringChar K⟩
variable (β : Fin r → L) [Fact (LinearIndependent K β)]
variable {ℓ R ϑ : ℕ} [NeZero ℓ] [NeZero R] [NeZero ϑ]
  {h_rate : ℓ + R < r} [Fact (ϑ ∣ ℓ)]
variable {Context : Type}
variable (evaluateMultiplier : Context → (Fin ℓ → L) → L)
variable (outputContext : Context → SumcheckBaseContext L ℓ)

/-- The closing equation uses the received scalar, including at a zero multiplier. -/
def check (s : Statement (L := L) Context (Fin.last ℓ)) (c : L) : Prop :=
  s.sumcheck_target = evaluateMultiplier s.ctx s.challenges * c

/-- Preserve challenges, target and final scalar, projecting only the unused query context. -/
def output (s : Statement (L := L) Context (Fin.last ℓ)) (c : L) :
    FinalSumcheckStatementOut (L := L) (ℓ := ℓ) where
  ctx := outputContext s.ctx
  challenges := s.challenges
  sumcheck_target := s.sumcheck_target
  finalConstant := c

/-- Read the final scalar, abort on a failed multiplier check, and forward every oracle. -/
def verifier : OracleVerifier []ₒ
    (Statement (L := L) Context (Fin.last ℓ))
    (OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) (Fin.last ℓ))
    (FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) (Fin.last ℓ))
    (pSpecFinalSumcheckStep (L := L)) where
  verify s _ := do
    let c : L ← query (spec := [(pSpecFinalSumcheckStep (L := L)).Message]ₒ) ⟨⟨0, rfl⟩, ()⟩
    guard (s.sumcheck_target = evaluateMultiplier s.ctx s.challenges * c)
    pure (output outputContext s c)
  outputOracle := .inl {
    embed := Function.Embedding.inl
    hEq := fun _ => rfl
    outputInterface_heq := fun _ => HEq.rfl }

/-- The terminal verifier is guarded by exactly the closing multiplier equation. -/
def guardedForm :
    (verifier K β evaluateMultiplier outputContext (ϑ := ϑ)
      (h_rate := h_rate)).toVerifier.GuardedForm :=
  Verifier.GuardedForm.ofQueryGuard _ ⟨⟨0, rfl⟩, ()⟩
    (fun s c _ => check evaluateMultiplier s c)
    (hcheck := fun _ _ _ => by dsimp only [check]; infer_instance)
    (fun s c _ => output outputContext s c)
    (fun _ _ => rfl)

omit [DecidableEq K] [Fact (Fintype.card K = 2)] [NeZero R] [Fact (ϑ ∣ ℓ)] in
/-- The guarded form forwards the input oracles without changing their contents. -/
theorem guardedForm_out
    (s : Statement (L := L) Context (Fin.last ℓ) ×
      ∀ j, OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) (Fin.last ℓ) j)
    (tr : (pSpecFinalSumcheckStep (L := L)).FullTranscript) :
    (guardedForm K β evaluateMultiplier outputContext (ϑ := ϑ) (h_rate := h_rate)).out s tr =
      (output outputContext s.1 (tr.messages ⟨0, rfl⟩), s.2) := rfl

omit [Fintype L] [DecidableEq L] [NeZero ℓ] in
/-- Zero multiplier does not constrain the received scalar, but still requires a zero target. -/
theorem check_of_multiplier_zero (s : Statement (L := L) Context (Fin.last ℓ)) (c : L)
    (h : evaluateMultiplier s.ctx s.challenges = 0) :
    check evaluateMultiplier s c ↔ s.sumcheck_target = 0 := by
  simp [check, h]

omit [Field L] [Fintype L] [DecidableEq L] [NeZero ℓ] in
/-- The query phase always receives the scalar that was actually sent. -/
theorem output_finalConstant (s : Statement (L := L) Context (Fin.last ℓ)) (c : L) :
    (output outputContext s c).finalConstant = c := rfl

end Binius.FRIBinius.Unrolled.Terminal
