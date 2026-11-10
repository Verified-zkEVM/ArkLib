/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuxi Zheng, Chung Thai Nguyen, Michele Orrù
-/
import ArkLib.OracleReduction.Security.ZeroKnowledge

/-!
# Zero-knowledge clients

The first client changes oracle indices, answers, realization spaces, NARG strings, and
programming data with the public parameters. Its single simulator family works at every
query budget.
-/

open OracleComp OracleSpec ProtocolSpec Reduction

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
