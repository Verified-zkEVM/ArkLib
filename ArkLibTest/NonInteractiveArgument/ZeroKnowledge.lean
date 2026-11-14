/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuxi Zheng, Chung Thai Nguyen, Michele Orrù
-/
import ArkLib.NonInteractiveArgument.ZeroKnowledge
import VCVio.OracleComp.RunIO

/-!
# Zero-knowledge clients

The first client changes oracle indices, answers, realization spaces, NARG strings, and
programming data with the public parameters. Its single simulator family works at every
query budget.
-/

open OracleComp OracleSpec Reduction

namespace ZeroKnowledgeTest

def publicSpec (securityParameter sizeBound : ℕ) : OracleSpec (Fin (sizeBound + 1)) :=
  Fin (sizeBound + 1) →ₒ Fin (securityParameter + sizeBound + 1)

def sampleOracle (securityParameter sizeBound : ℕ) :
    ProbComp (Fin (securityParameter + sizeBound + 1)) :=
  sampleUniform (Fin (securityParameter + sizeBound + 1))

def oracleImpl (securityParameter sizeBound : ℕ)
    (realization : Fin (securityParameter + sizeBound + 1)) :
    QueryImpl (publicSpec securityParameter sizeBound) ProbComp :=
  fun _ => pure realization

def programImpl (securityParameter sizeBound : ℕ)
    (realization : Fin (securityParameter + sizeBound + 1)) (_program : Fin (sizeBound + 1)) :
    QueryImpl (publicSpec securityParameter sizeBound) ProbComp :=
  oracleImpl securityParameter sizeBound realization

def prover (securityParameter sizeBound : ℕ) :
    NARGZKProver (publicSpec securityParameter sizeBound) ℕ Unit (Fin (securityParameter + 1)) :=
  fun _ _ => pure 0

def simulator (securityParameter sizeBound : ℕ) :
    NARGZKSimulator (publicSpec securityParameter sizeBound) ℕ
      (Fin (securityParameter + 1)) (Fin (sizeBound + 1)) :=
  fun _ => pure (0, 0)

-- Arbitrary adversaries observe the same NARG string and oracle in both experiments.
-- Both public parameters are chosen after the simulator family, as are all query budgets.
example : adaptiveNARGZeroKnowledge
    publicSpec sampleOracle oracleImpl programImpl prover Set.univ id
    (fun _ _ _ => 0) := by
  refine ⟨simulator, ?_⟩
  intro securityParameter sizeBound t Output adversary _hQueries
  simp [adaptiveNARGZKRealExp, adaptiveNARGZKSimExp, prover, simulator, programImpl]

def emptyStringAdversary :
    NARGZKAdversary (Unit →ₒ Unit) Unit Unit Empty Unit (fun _ _ => True) where
  State := Unit
  choose := do
    let _ ← ((Unit →ₒ Unit) + unifSpec).query (Sum.inl ())
    pure (⟨((), ()), trivial⟩, ())
  distinguish _ proof := nomatch proof

-- An empty NARG-string type makes the continuation condition vacuous, but one public
-- query in the initial call still violates budget zero.
example : ¬ emptyStringAdversary.HasAggregateQueryBound (fun _ => True) 0 := by
  simp [NARGZKAdversary.HasAggregateQueryBound, emptyStringAdversary,
    isQueryBoundP_query_bind_iff, publicQuerySelector]

end ZeroKnowledgeTest

namespace NARGPrivateCoinsTest

namespace ZKOrdering
abbrev publicSpec := Unit →ₒ Fin 7

def publicQuery : OracleComp (publicSpec + unifSpec)
    ((publicSpec + unifSpec).Range (.inl ())) :=
  liftM ((publicSpec + unifSpec).query (.inl ()))

def adversary : Reduction.NARGZKAdversary publicSpec Unit Unit Unit (Fin 7)
    (fun _ _ => True) where
  State := Fin 7
  choose := do
    let coin ← samplePrivateUniform (Fin 7)
    pure (⟨((), ()), trivial⟩, coin)
  distinguish := fun _ _ => publicQuery

example : adversary.HasAggregateQueryBound (fun _ => True) 1 := by
  apply adversary.hasAggregateQueryBound_of_stage_bounds (fun _ => True)
    (chooseBudget := 0) (distinguishBudget := 1) (by omega)
  · exact isQueryBoundP_bind
      (isQueryBoundP_samplePrivateUniform (publicSpec := publicSpec) (Fin 7) (fun _ => True))
      (fun _ _ => isQueryBoundP_pure _ _ 0)
  · intro state proof
    change publicQuery.IsQueryBoundP _ 1
    rw [publicQuery, isQueryBoundP_query_iff]
    simp [publicQuerySelector]

example : ¬ publicQuery.IsQueryBoundP (publicQuerySelector fun _ => True) 0 := by
  rw [publicQuery, isQueryBoundP_query_iff]
  simp [publicQuerySelector]
end ZKOrdering

/-- Execute both adversarial stages and check their public/private routing. -/
def checkRuntime : IO Unit := do
  let zkImpl : QueryImpl (ZKOrdering.publicSpec + unifSpec) ProbComp :=
    (fun _ => pure (5 : Fin 7) : QueryImpl ZKOrdering.publicSpec ProbComp) +
      QueryImpl.id' unifSpec
  let (choice, chooseLog) ← OracleComp.runIO <|
    simulateQ zkImpl ZKOrdering.adversary.choose.withQueryLog
  let (answer, distinguishLog) ← OracleComp.runIO <|
    simulateQ zkImpl (ZKOrdering.adversary.distinguish choice.2 ()).withQueryLog
  unless chooseLog.publicQueries.isEmpty && chooseLog.snd.length == 1 &&
      answer == 5 && distinguishLog.publicQueries.length == 1 && distinguishLog.snd.isEmpty do
    throw (IO.userError "ZK public queries or private draws reached the wrong oracle slot")
  let legacy : OracleComp (unifSpec + ZKOrdering.publicSpec) (Fin 7) := do
    let _ ← liftM ((unifSpec + ZKOrdering.publicSpec).query (.inl 6))
    liftM ((unifSpec + ZKOrdering.publicSpec).query (.inr ()))
  let (swappedAnswer, swappedLog) ← OracleComp.runIO <|
    simulateQ zkImpl legacy.swapOracles.withQueryLog
  unless swappedAnswer == 5 && swappedLog.publicQueries.length == 1 && swappedLog.snd.length == 1 do
    throw (IO.userError "oracle reordering changed answers or public/private routing")

end NARGPrivateCoinsTest

/-- Run with `lake env lean --run ArkLibTest/NonInteractiveArgument/ZeroKnowledge.lean`. -/
def main : IO Unit := NARGPrivateCoinsTest.checkRuntime
