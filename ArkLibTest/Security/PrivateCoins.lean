/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/
import ArkLib.Security.PrivateCoins
import VCVio.OracleComp.RunIO

/-!
# Private sampling: routing, transcripts, budgets, and execution
-/

open OracleComp OracleSpec

namespace PrivateCoinsTest
-- Nested lifts normalize without protocol-specific lemmas, preserving the stateful handler.
example {ι κ ν α σ : Type} {a : OracleSpec ι} {b : OracleSpec κ} {c : OracleSpec ν}
    (ha : QueryImpl a (StateT σ ProbComp)) (hb : QueryImpl b ProbComp)
    (hc : QueryImpl c ProbComp) (p : OracleComp a α) :
    simulateQ ((ha.addLift hb : QueryImpl _ (StateT σ ProbComp)).addLift hc :
      QueryImpl _ (StateT σ ProbComp)) (liftComp p ((a + b) + c)) = simulateQ ha p := by
  simp only [QueryImpl.addLift_def, QueryImpl.liftTarget_self, simulateQ_add_add_liftComp_left]

example {ι κ ν α σ : Type} {a : OracleSpec ι} {b : OracleSpec κ} {c : OracleSpec ν}
    (hab : QueryImpl (a + b) (StateT σ ProbComp)) (hc : QueryImpl c ProbComp)
    (p : OracleComp (a + b) α) :
    simulateQ (hab.addLift hc : QueryImpl _ (StateT σ ProbComp))
      (liftComp p ((a + b) + c)) = simulateQ hab p := by
  simp only [QueryImpl.addLift_def, QueryImpl.liftTarget_self, simulateQ_add_liftComp_sum_left]

-- Identical slot types must not make the normalizer identify distinct handlers.
example {ι α : Type} {spec : OracleSpec ι}
    (h₁ h₂ h₃ : QueryImpl spec ProbComp) (p : OracleComp spec α) :
    simulateQ ((h₁ + h₂) + h₃) (liftComp p ((spec + spec) + spec)) =
      simulateQ h₃ p := by
  simp only [QueryImpl.simulateQ_add_liftComp_right]

-- Merging slots works for stateful handlers, including when all slot types coincide.
-- Only the two slots interpreted by h₂ are merged; h₁ and h₃ stay distinct.
example {ι α σ : Type} {spec : OracleSpec ι}
    (h₁ h₂ h₃ : QueryImpl spec (StateT σ ProbComp))
    (p : OracleComp (((spec + spec) + spec) + spec) α) :
    simulateQ ((h₁ + h₃) + h₂) p.mergeRight =
      simulateQ (((h₁ + h₂) + h₃) + h₂) p := by
  simp only [simulateQ_mergeRight]

-- The budget excludes the private slot, even when the public slot has the same type.
example : (samplePrivateUniform (publicSpec := unifSpec) (Fin 7)).IsQueryBoundP
    (publicQuerySelector fun _ => True) 0 :=
  isQueryBoundP_samplePrivateUniform _ _

-- Logging does not reveal the sample to the public transcript.
example : (fun r => r.2.publicQueries) <$>
    (samplePrivateUniform (publicSpec := unifSpec) (Fin 7)).withQueryLog =
    (fun _ => ([] : QueryLog unifSpec)) <$>
      samplePrivateUniform (publicSpec := unifSpec) (Fin 7) := by
  have h := publicQueries_withQueryLog_samplePrivateUniform (publicSpec := unifSpec) (Fin 7)
  simpa only [Functor.map_map] using congrArg (Functor.map Prod.snd) h

/-- A private request implemented using two uniform samples. -/
def twoDraws : QueryImpl (Unit →ₒ Fin 7) ProbComp := fun _ => do
  let a ← sampleUniform (Fin 7)
  let b ← sampleUniform (Fin 7)
  return a + b

/-- A client of the sampling capability through a monad transformer. -/
def sampleInState : StateT ℕ ProbComp (Fin 7) := do
  modify (· + 1)
  sampleUniform (Fin 7)

/-- The public request is logged once; the private request expands to two private draws. -/
def mixed : OracleComp (unifSpec + (Unit →ₒ Fin 7)) (Fin 7) := do
  let _ ← liftM ((unifSpec + (Unit →ₒ Fin 7)).query (.inl 0))
  liftM ((unifSpec + (Unit →ₒ Fin 7)).query (.inr ()))

/-- Execute the regression checks for observable oracle routing. -/
def checkRuntime : IO Unit := do
  let ((_, tr), _) ← OracleComp.runIO <|
    (simulateQ ((QueryImpl.id' unifSpec).addLift (QueryImpl.id' unifSpec) :
      QueryImpl (unifSpec + unifSpec) (StateT Unit ProbComp))
      (normalizePrivateCoins twoDraws mixed).withQueryLog).run ()
  unless tr.publicQueries.length == 1 && tr.snd.length == 2 do
    throw (IO.userError "private-sampler normalization changed query routing")
  let (_, trPrivate) ← OracleComp.runIO <|
    simulateQ ((QueryImpl.id' unifSpec) + (QueryImpl.id' unifSpec))
      (samplePrivateUniform (publicSpec := unifSpec) (Fin 7)).withQueryLog
  unless trPrivate.publicQueries.isEmpty && trPrivate.snd.length == 1 do
    throw (IO.userError "private sample was exposed as a public query")
  let (_, state) ← OracleComp.runIO (sampleInState.run 4)
  unless state == 5 do
    throw (IO.userError "sampling capability lost transformer state")

end PrivateCoinsTest

/-- Run with `lake env lean --run ArkLibTest/Security/PrivateCoins.lean`. -/
def main : IO Unit := PrivateCoinsTest.checkRuntime
