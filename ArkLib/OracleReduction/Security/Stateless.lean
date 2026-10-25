/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/
module

public import ArkLib.OracleReduction.Security.RoundByRound

/-!
# Stateless interpretations of ambient oracles

An arbitrary oracle specification can be interpreted by a stateless probabilistic handler.
Lifting that handler to a singleton state preserves its complete distribution, including failure
mass. Randomized queries remain fresh samples, not a memoized random oracle.

The terminal bridges below connect the existing fresh-initial-state RBR obligations to the
verifier's actual continuation. They do not require guarded verifiers or lossless handlers.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ProbabilityTheory

namespace QueryImpl

variable {ι : Type} {oSpec : OracleSpec ι}

/-- Interpret a stateless handler in the framework's stateful security interfaces. -/
abbrev statelessLift (impl : QueryImpl oSpec ProbComp) :
    QueryImpl oSpec (StateT PUnit ProbComp) := impl.liftTarget _

/-- Adding another stateless handler commutes with lifting to the singleton carrier. -/
@[simp] theorem statelessLift_addLift {κ : Type} {otherSpec : OracleSpec κ}
    (impl : QueryImpl oSpec ProbComp) (other : QueryImpl otherSpec ProbComp) :
    (impl.statelessLift.addLift other : QueryImpl (oSpec + otherSpec) (StateT PUnit ProbComp)) =
      (impl + other).statelessLift := by
  funext query
  cases query <;> rfl

/-- Erasing the singleton carrier leaves the original simulation distribution unchanged. -/
@[simp] theorem simulateQ_statelessLift_run' (impl : QueryImpl oSpec ProbComp)
    {α : Type} (comp : OracleComp oSpec α) (state : PUnit) :
    (simulateQ impl.statelessLift comp).run' state = simulateQ impl comp := by
  simp [statelessLift, simulateQ_liftTarget]

end QueryImpl

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n} {impl : QueryImpl oSpec ProbComp}
  {verifier : Verifier oSpec StmtIn StmtOut pSpec}

/-- A supported related output under a stateless handler satisfies the final knowledge state. -/
theorem KnowledgeStateFunction.stateless_terminal
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {WitMid : Fin (n + 1) → Type}
    {extractor : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid}
    (kSF : verifier.KnowledgeStateFunction (pure PUnit.unit) impl.statelessLift
      relIn relOut extractor)
    (stmtIn : StmtIn) (transcript : FullTranscript pSpec) (witOut : WitOut)
    (stmtOut : StmtOut)
    (hsupport : some stmtOut ∈ support (simulateQ impl (verifier.run stmtIn transcript).run))
    (hrel : (stmtOut, witOut) ∈ relOut) :
    kSF (.last n) stmtIn transcript (extractor.extractOut stmtIn transcript witOut) := by
  apply kSF.toFun_full stmtIn transcript witOut
  simp only [Fin.val_last, gt_iff_lt, OptionT.prEvent_mk_pos_iff]
  refine ⟨stmtOut, ?_, hrel⟩
  simpa only [pure_bind, QueryImpl.simulateQ_statelessLift_run', OptionT.run] using hsupport

/-- A supported output in the output language satisfies the final ordinary state. -/
theorem StateFunction.stateless_terminal
    {langIn : Set StmtIn} {langOut : Set StmtOut}
    (sF : verifier.StateFunction (pure PUnit.unit) impl.statelessLift langIn langOut)
    (stmtIn : StmtIn) (transcript : FullTranscript pSpec) (stmtOut : StmtOut)
    (hsupport : some stmtOut ∈ support (simulateQ impl (verifier.run stmtIn transcript).run))
    (hmem : stmtOut ∈ langOut) : sF (.last n) stmtIn transcript := by
  by_contra hfalse
  have hzero := sF.toFun_full stmtIn transcript hfalse
  simp only [Fin.val_last, OptionT.prEvent_mk_eq_zero_iff] at hzero
  exact hzero stmtOut
    (by simpa only [pure_bind, QueryImpl.simulateQ_statelessLift_run', OptionT.run]
      using hsupport) hmem

end Verifier
