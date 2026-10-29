/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.OracleReduction.Security.RoundByRound

/-!
  # A classification of all (oracle) reductions with no interaction between the prover and verifier

  This file contains the general form of all (oracle) reductions with no interaction between the
  prover and verifier. In this setting, there are many specializations, and we can use these to
  derive simpler conditions for completeness & soundness.
-/

@[expose] public section

open OracleComp OracleInterface ProtocolSpec Function NNReal ENNReal

namespace NoInteraction

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
  {WitIn : Type}
  {StmtOut : Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} [Oₛₒ : ∀ i, OracleInterface (OStmtOut i)]
  {WitOut : Type}

section Reduction

variable (mapStmt : StmtIn → StmtOut)
  (mapWit : StmtIn → WitIn → OracleComp oSpec WitOut)

/-- Collect the functions `mapStmt` and `mapWit` into a single function `mapCtx` -/
@[reducible]
def combineMap : StmtIn × WitIn → OracleComp oSpec (StmtOut × WitOut) :=
  fun ⟨stmt, wit⟩ => do return (mapStmt stmt, ← mapWit stmt wit)

/-- The prover in a no-interaction reduction can be specified by a tuple of functions:
- `mapStmt : StmtIn → StmtOut` maps the input statement to an output statement
- `mapWit : StmtIn → WitIn → OracleComp oSpec WitOut` maps the input witness to an output witness,
  depending on the input statement
-/
@[reducible]
def prover : Prover oSpec StmtIn WitIn StmtOut WitOut !p[] where
  PrvState | 0 => StmtIn × WitIn
  input := id
  sendMessage := fun i => nomatch i
  receiveChallenge := fun i => nomatch i
  output := combineMap mapStmt mapWit

/-- The verifier in a no-interaction reduction takes an empty transcript, and hence reduces to a
  function `mapStmt : StmtIn → StmtOut`.
  The statement map is pure because the verifier must recompute the prover's statement. -/
@[reducible]
def verifier : Verifier oSpec StmtIn StmtOut !p[] where
  verify := fun stmt _ => pure (mapStmt stmt)

/-- The no-interaction verifier deterministically recomputes the output statement. -/
instance instIsPure : (verifier (oSpec := oSpec) mapStmt).IsPure :=
  ⟨fun stmt _ => mapStmt stmt, fun _ _ => rfl⟩

/-- The no-interaction reduction can be specified by a tuple of functions:
- `mapStmt : StmtIn → StmtOut` maps the input statement to an output statement
- `mapWit : StmtIn → WitIn → OracleComp oSpec WitOut` maps the input witness to an output witness,
  depending on the input statement
-/
@[reducible]
def reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut !p[] where
  prover := prover mapStmt mapWit
  verifier := verifier mapStmt

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}

theorem reduction_completeness {ε : ℝ≥0}
    (hRel : ∀ stmtIn witIn, (stmtIn, witIn) ∈ relIn →
      Pr{let witOut ← do
        (simulateQ impl (mapWit stmtIn witIn)).run' (← init)}[(mapStmt stmtIn, witOut) ∈ relOut]
        ≥ 1 - ε) :
    Reduction.completeness init impl relIn relOut (reduction mapStmt mapWit) ε := by
  intro stmtIn witIn hIn
  let : ∀ i, OracleInterface ((!p[]).Challenge i) := challengeOracleInterface
  have hrun : ((reduction mapStmt mapWit).run stmtIn witIn).run =
      (fun w => some (((default : (!p[]).FullTranscript), mapStmt stmtIn, w), mapStmt stmtIn)) <$>
        (liftM (mapWit stmtIn witIn) : OracleComp (oSpec + [(!p[]).Challenge]ₒ) WitOut) := by
    simp [Reduction.run, Prover.run, prover, reduction, combineMap, verifier,
      Verifier.run, Prover.runToRound_zero_of_prover_first,
      ← monadLift_liftM_OptionT, OptionT.run_monadLift]
    rfl
  change 1 - (ε : ℝ≥0∞) ≤ _
  rw [hrun, OptionT.prEvent_mk]
  simpa [QueryImpl.addLift_def, QueryImpl.simulateQ_add_liftM_left,
    StateT.run'_eq, OptionT.prEvent_mk] using hRel stmtIn witIn hIn

end Reduction

section OracleReduction



end OracleReduction

end NoInteraction
