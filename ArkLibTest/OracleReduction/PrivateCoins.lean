/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/
import ArkLib.OracleReduction.Security.PrivateCoins
import ArkLib.OracleReduction.Security.ZeroKnowledge
import VCVio.OracleComp.RunIO

/-!
# Private sampling: routing, transcripts, budgets, and execution

The public oracle specification deliberately contains `unifSpec` too. A private draw must use
the other slot, even in this ambiguous case. A custom private request expands to two draws;
normalizing it preserves the public transcript and state, without charging either draw.
-/

open OracleComp OracleSpec ProtocolSpec

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

/-- A legacy prover over the public interface still embeds without private sampling. -/
def legacySRProver : OracleComp ([]ₒ + srChallengeOracle (Unit × Unit) (default : ProtocolSpec 0))
    ((Unit × Unit) × (default : ProtocolSpec 0).Messages) := pure (((), ()), default)

def embeddedSRProver : Prover.StateRestoration.Soundness []ₒ unifSpec Unit
    (default : ProtocolSpec 0) (Salt := Unit) := liftComp legacySRProver _

/-- The extractor has private randomness without acquiring the SR challenge interface. -/
def randomizedSRExtractor : Extractor.StateRestoration []ₒ Unit (Fin 7) Unit
    (default : ProtocolSpec 0) (Salt := Unit) := fun _ _ _ _ tr trV => do
  if tr.isEmpty && trV.isEmpty then
    liftM (samplePrivateUniform (publicSpec := []ₒ) (Fin 7))
  else failure

def emptySRImpl : QueryImpl ([]ₒ + srChallengeOracle (Unit × Unit) (default : ProtocolSpec 0))
    ProbComp := fun
  | .inl q => nomatch q
  | .inr ⟨i, _⟩ => nomatch i.val

def emptyImpl : QueryImpl []ₒ ProbComp := fun q => nomatch q

namespace SRBudget

abbrev pSpec : ProtocolSpec 1 := ⟨!v[.V_to_P], !v[Fin 7]⟩
abbrev publicSpec := []ₒ + srChallengeOracle (Unit × Unit) pSpec

abbrev firstMove : (srChallengeOracle (Unit × Unit) pSpec).Domain :=
  ⟨⟨0, rfl⟩, ((), ()), fun i => Fin.elim0 i.val⟩

def request : OracleComp (publicSpec + unifSpec)
    ((publicSpec + unifSpec).Range (.inl (.inr firstMove))) :=
  liftM ((publicSpec + unifSpec).query (.inl (.inr firstMove)))

-- A genuine SR move consumes one unit, so it cannot fit a zero move budget.
example : request.IsQueryBoundP
    (publicQuerySelector (Verifier.StateRestoration.isSrChallengeMove (Salt := Unit)
      (oSpec := []ₒ))) 1 := by
  rw [request, isQueryBoundP_query_iff]
  simp [publicQuerySelector, Verifier.StateRestoration.isSrChallengeMove]

example : ¬ request.IsQueryBoundP
    (publicQuerySelector (Verifier.StateRestoration.isSrChallengeMove (Salt := Unit)
      (oSpec := []ₒ))) 0 := by
  rw [request, isQueryBoundP_query_iff]
  simp [publicQuerySelector, Verifier.StateRestoration.isSrChallengeMove]

end SRBudget

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

namespace AdaptiveAccess

abbrev publicSpec := Unit →ₒ Fin 7

def publicImpl : QueryImpl publicSpec (StateT ℕ ProbComp) := fun _ => do
  modify (· + 1)
  return Fin.ofNat 7 (← get)

def prover : OracleComp (publicSpec + unifSpec) (Unit × Unit) := do
  let _ ← samplePrivateUniform (publicSpec := publicSpec) (Fin 7)
  let _ ← liftM ((publicSpec + unifSpec).query (.inl ()))
  return ((), ())

def verifier : NonInteractiveVerifier Unit publicSpec Unit Unit where
  verify _ _ := do
    let _ ← liftM (publicSpec.query ())
    return ()

-- The standalone extractor's type grants sampling only, independently of the prover's access.
def standalone : Unit → Unit → QueryLog publicSpec → QueryLog publicSpec →
    OptionT ProbComp (Fin 7) := fun _ _ trP trV =>
  if trP.length == 1 && trV.length == 1 then pure 1 else failure

-- Public query access is a separate, explicit choice of extractor interface and handler.
def shared : Unit → Unit → QueryLog publicSpec → QueryLog publicSpec →
    OptionT (OracleComp (publicSpec + unifSpec)) (Fin 7) := fun _ _ trP trV => do
  if trP.length == 1 && trV.length == 1 then
    liftM ((publicSpec + unifSpec).query (.inl ()))
  else failure

end AdaptiveAccess

/-- Execute the named sampler and normalization, checking their observable routing. -/
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
  let (_, legacyLog) ← OracleComp.runIO <|
    simulateQ (emptySRImpl + QueryImpl.id' unifSpec)
      embeddedSRProver.withQueryLog
  unless legacyLog.isEmpty do
    throw (IO.userError "embedding a coin-free SR prover added oracle calls")
  let (wit, extractorLog) ← OracleComp.runIO <|
    simulateQ (emptyImpl + QueryImpl.id' unifSpec)
      ((randomizedSRExtractor () () () default [] []).run.withQueryLog)
  unless wit.isSome && extractorLog.publicQueries.isEmpty && extractorLog.snd.length == 1 do
    throw (IO.userError "SR extractor sampling changed its public permissions")
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
  let (_, witness, accepted) ← OracleComp.runIO <|
    adaptiveNARGKnowledgeSoundnessExp (pure 0) AdaptiveAccess.publicImpl
      (QueryImpl.id' unifSpec) ((QueryImpl.id' unifSpec).liftTarget (StateT ℕ ProbComp))
      AdaptiveAccess.verifier AdaptiveAccess.standalone AdaptiveAccess.prover
  unless witness == some 1 && accepted == some () do
    throw (IO.userError "adaptive KS exposed private draws in the extractor's public logs")
  let (_, witness, _) ← OracleComp.runIO <|
    adaptiveNARGKnowledgeSoundnessExp (pure 0) AdaptiveAccess.publicImpl
      (QueryImpl.id' unifSpec) (AdaptiveAccess.publicImpl.addLift (QueryImpl.id' unifSpec))
      AdaptiveAccess.verifier AdaptiveAccess.shared AdaptiveAccess.prover
  unless witness == some 3 do
    throw (IO.userError "explicit shared-oracle extraction did not continue the verifier state")
  let (_, state) ← OracleComp.runIO (sampleInState.run 4)
  unless state == 5 do
    throw (IO.userError "sampling capability lost transformer state")

end PrivateCoinsTest

/-- Run with `lake env lean --run ArkLibTest/OracleReduction/PrivateCoins.lean`. -/
def main : IO Unit := PrivateCoinsTest.checkRuntime
