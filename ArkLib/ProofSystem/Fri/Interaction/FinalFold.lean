/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Fri.Interaction.Core
import ArkLib.Interaction.Oracle.Execution

open Interaction.TwoParty

/-!
# FRI Interaction: Final Fold

This module packages the terminal FRI fold round as an
`Interaction.Oracle.Reduction`.
-/

open Interaction CompPoly CPoly OracleComp OracleSpec

namespace Fri

namespace OracleLayer

section

variable {F : Type} [BEq F] [LawfulBEq F] [DecidableEq F] [NonBinaryField F] [Finite F]
variable (D : Subgroup Fˣ) {n : ℕ}
variable [DIsCyclicC : IsCyclicWithGen D] [DSmooth : SmoothPowerOfTwo n D]
variable (x : Fˣ)
variable {k : ℕ} (s : Fin (k + 1) → ℕ+) (d : ℕ)

/-- Reduction for the terminal FRI fold round. The incoming local
statement only needs to expose the collected non-final challenges. -/
def finalFoldReduction {SharedIn : Type} {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {StatementIn : SharedIn → Type}
    (toFoldChallenges :
      (shared : SharedIn) → StatementIn shared → FoldChallenges (F := F) (k := k))
    (sampleChallenge : SharedIn → OracleComp oSpec F) :
    Interaction.Oracle.Reduction (ι := ι) oSpec SharedIn
      (fun _ => finalFoldSpec (F := F) (d := d))
      (fun _ => finalFoldRoles (F := F) (d := d))
      (fun _ => finalFoldOD (F := F) (d := d))
      StatementIn
      (ιₛᵢ := fun _ => Unit)
      (fun _ => FoldCodewordTraceOracleFamily (F := F) (n := n) D x s)
      (fun _ => HonestPoly (F := F) s d k)
      (fun _ _ => FinalStatement (F := F) (k := k) (d := d))
      (ιₛₒ := fun _ _ => Unit)
      (fun _ _ => FoldCodewordTraceOracleFamily (F := F) (n := n) D x s)
      (fun _ _ => PUnit) where
  prover shared sWithOracles witness := do
    let proverStep :
        Interaction.Spec.StrategyOver (pairedSyntax (OracleComp oSpec)) Interaction.TwoParty.Participant.focal
          (finalFoldSpec (F := F) (d := d)).toInteractionSpec
          ((finalFoldSpec (F := F) (d := d)).toSpecRoles
            (finalFoldRoles (F := F) (d := d)))
          (fun _ =>
            HonestProverOutput
              (StatementWithOracles
                (fun _ => FinalStatement (F := F) (k := k) (d := d))
                (fun _ => FoldCodewordTraceOracleFamily (F := F) (n := n) D x s)
                shared)
              PUnit) := by
      intro α
      let finalPoly : CDegreeLE F d :=
        honestFinalPolynomial (F := F) (s := s) (d := d) witness α
      let stmtOut : FinalStatement (F := F) (k := k) (d := d) :=
        ⟨toFoldChallenges shared sWithOracles.stmt, α, finalPoly⟩
      let nextOutput :
          HonestProverOutput
            (StatementWithOracles
              (fun _ => FinalStatement (F := F) (k := k) (d := d))
              (fun _ => FoldCodewordTraceOracleFamily (F := F) (n := n) D x s)
              shared)
            PUnit :=
        ⟨⟨stmtOut, sWithOracles.oracleStmt⟩, PUnit.unit⟩
      simpa [Spec.StrategyOver, pairedSyntax, TwoParty.Participant.focal] using
        (pure <|
          (pure <|
              (show (finalPoly : CDegreeLE F d) ×
                HonestProverOutput
                  (StatementWithOracles
                    (fun _ => FinalStatement (F := F) (k := k) (d := d))
                    (fun _ => FoldCodewordTraceOracleFamily (F := F) (n := n) D x s)
                    shared)
                  PUnit from
              ⟨finalPoly, nextOutput⟩)) :
          OracleComp oSpec
            (OracleComp oSpec
              ((finalPoly : CDegreeLE F d) ×
                HonestProverOutput
                  (StatementWithOracles
                    (fun _ => FinalStatement (F := F) (k := k) (d := d))
                    (fun _ => FoldCodewordTraceOracleFamily (F := F) (n := n) D x s)
                    shared)
                  PUnit)))
    pure <|
      Interaction.TwoParty.Focal.toConstantMonads
        (finalFoldSpec (F := F) (d := d)).toInteractionSpec
        ((finalFoldSpec (F := F) (d := d)).toSpecRoles
          (finalFoldRoles (F := F) (d := d)))
        proverStep
  verifier := {
    toFun := fun shared stmt => do
      let α ← sampleChallenge shared
      pure ⟨α, fun finalPoly => ⟨toFoldChallenges shared stmt, α, finalPoly⟩⟩
    simulate := fun _ _ q =>
      liftM <| ([FoldCodewordTraceOracleFamily (F := F) (n := n) D x s]ₒ).query q
  }

end

end OracleLayer

end Fri

