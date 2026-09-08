/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Security.RoundByRound

/-!
  # A classification of all (oracle) reductions with no interaction between the prover and verifier

  This file contains the general form of all (oracle) reductions with no interaction between the
  prover and verifier. In this setting, there are many specializations, and we can use these to
  derive simpler conditions for completeness & soundness.
-/

open OracleComp OracleInterface ProtocolSpec Function NNReal ENNReal

namespace NoInteraction

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
  {WitIn : Type}
  {StmtOut : Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} [Oₛₒ : ∀ i, OracleInterface (OStmtOut i)]
  {WitOut : Type}

section Reduction

variable (mapStmt : StmtIn → OracleComp oSpec StmtOut)
  (mapWit : StmtIn → WitIn → OracleComp oSpec WitOut)

/-- Collect the functions `mapStmt` and `mapWit` into a single function `mapCtx` -/
@[reducible]
def combineMap : StmtIn × WitIn → OracleComp oSpec (StmtOut × WitOut) :=
  fun ⟨stmt, wit⟩ => do return (← mapStmt stmt, ← mapWit stmt wit)

/-- The prover in a no-interaction reduction can be specified by a tuple of functions:
- `mapStmt : StmtIn → OracleComp oSpec StmtOut` maps the input statement to an output statement
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

/- **No `Prover.OutputIsPure` instance.** Unlike the other components, this prover's `output` runs
`mapStmt` and `mapWit`, which are arbitrary `OracleComp`s, so it is not of the form `pure ∘ f` and
the class genuinely does not hold. It is therefore the in-tree witness that `Prover.append_run`'s
purity hypothesis is not vacuous: appending this prover on the left of a protocol that opens with a
challenge round reorders the queries. A caller who instantiates `mapStmt` / `mapWit` at `pure`
functions can supply the instance at that instantiation. -/

/-- The verifier in a no-interaction reduction takes an empty transcript, and hence reduce to a
  function `mapStmt : StmtIn → OracleComp oSpec StmtOut` -/
@[reducible]
def verifier : Verifier oSpec StmtIn StmtOut !p[] where
  verify := fun stmt _ => mapStmt stmt

/-- The no-interaction reduction can be specified by a tuple of functions:
- `mapStmt : StmtIn → OracleComp oSpec StmtOut` maps the input statement to an output statement
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
      Pr[ fun ⟨stmtOut, witOut⟩ => (stmtOut, witOut) ∈ relOut | do
        (simulateQ impl <| combineMap mapStmt mapWit ⟨stmtIn, witIn⟩).run' (← init)] ≥ 1 - ε) :
    Reduction.completeness init impl relIn relOut (reduction mapStmt mapWit) ε := by
  classical
  simp only [Reduction.completeness, ChallengeIdx, Challenge, QueryImpl.addLift_def,
    PFunctor.Handler.liftTarget_self, Reduction.run, Prover.run, Fin.reduceLast, prover,
    Nat.reduceAdd, Fin.isValue, MessageIdx, Message, Prover.runToRound_zero_of_prover_first,
    id_eq, liftM_bind, bind_pure_comp, liftM_map, map_bind, Functor.map_map, pure_bind,
    monadLift_liftM_OptionT, Verifier.run, OptionT.run_monadLift, monadLift_self,
    bind_map_left, Option.getM_some, map_pure, bind_assoc, OptionT.run_bind,
    OptionT.run_map, StateT.run'_eq, OptionT.mk_bind, ge_iff_le]
  intro stmtIn witIn hStmtIn
  refine ge_trans ?_ (hRel stmtIn witIn hStmtIn)
  sorry

end Reduction

section OracleReduction



end OracleReduction

end NoInteraction
