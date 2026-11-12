/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/
import ArkLib.InteractiveProof.StateRestorationSoundness
import VCVio.OracleComp.RunIO

/-!
# State-restoration private-coin and move-budget boundaries
-/

open OracleComp OracleSpec ProtocolSpec

namespace StateRestorationCoinsTest
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

/-- Execute the regression checks for observable oracle routing. -/
def checkRuntime : IO Unit := do
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

end StateRestorationCoinsTest

namespace SRSpecializationTest

abbrev pSpec : ProtocolSpec 1 := ⟨!v[.V_to_P], !v[Fin 7]⟩
abbrev ambient := Unit →ₒ ℕ
abbrev publicSpec := ambient + srChallengeOracle (Unit × Bool) pSpec

local instance : ∀ i, DecidableEq (pSpec.Message i) := fun i => isEmptyElim i

local instance : ∀ i, Inhabited (pSpec.Challenge i) := fun i => by
  have hi : i = ⟨0, rfl⟩ := Subtype.ext (Fin.eq_zero _)
  subst i
  exact inferInstanceAs (Inhabited (Fin 7))

-- The final salt changes the reconstructed challenge. It is not passed to the IP verifier.
def table : QueryImpl (srChallengeOracle (Unit × Bool) pSpec) Id := fun q => by
  obtain ⟨i, x, messages⟩ := q
  have hi : i = ⟨0, rfl⟩ := Subtype.ext (Fin.eq_zero _)
  subst i
  change Fin 7
  exact if x.2 then 5 else 2

def impl : QueryImpl ambient (StateT (QueryImpl (srChallengeOracle (Unit × Bool) pSpec) Id)
    ProbComp) := fun _ => pure 9

def verifier : Verifier ambient Unit ℕ pSpec where
  verify _ tr := do
    let value ← liftM (ambient.query ())
    let challenge : Fin 7 := tr 0
    if challenge == 5 then pure value else failure

def prover : Prover.StateRestoration.KnowledgeSoundness ambient unifSpec Unit ℕ pSpec
    (Salt := Bool) := do
  let _ ← samplePrivateUniform (publicSpec := publicSpec) (Fin 7)
  return (((), true), fun i => isEmptyElim i, 11)

-- The reconstruction challenge must be visible in the transcript, but absent from both logs.
-- The extractor is also allowed to query the original ambient oracle.
def extractor : Extractor.StateRestoration ambient Unit ℕ ℕ pSpec (Salt := Bool) :=
  fun _ salt w tr logP logV => do
    let value ← liftM ((ambient + unifSpec).query (.inl ()))
    let challenge : Fin 7 := tr 0
    if salt && w == 11 && challenge == 5 && logP.isEmpty && logV.length == 1 then
      pure value
    else failure

/-- Check reconstruction, salt, output witnesses, private-log hiding, and extractor access. -/
def checkRuntime : IO Unit := do
  let (_, originalWitness, originalOut, outputWitness) ← OracleComp.runIO <|
    Verifier.StateRestoration.knowledgeSoundnessExperiment (pure table) impl
      (QueryImpl.id' unifSpec) extractor verifier prover
  let (statement, witness, out) ← OracleComp.runIO <|
    adaptiveNARGKnowledgeSoundnessExp (pure table)
      (impl + srChallengeQueryImpl' (Statement := Unit × Bool) (pSpec := pSpec))
      (QueryImpl.id' unifSpec) (impl.addLift (QueryImpl.id' unifSpec))
      (Verifier.StateRestoration.toNARGKnowledgeVerifier verifier)
      (Verifier.StateRestoration.toNARGExtractor extractor) prover
  unless originalWitness == some 9 && originalOut == some 9 && outputWitness == 11 &&
      statement == ((), true) && witness == some 9 && out == some (9, 11) do
    throw (IO.userError "SR specialization changed reconstruction, logs, or extractor permissions")

end SRSpecializationTest

/-- Run with `lake env lean --run ArkLibTest/InteractiveProof/StateRestorationSoundness.lean`. -/
def main : IO Unit := do
  StateRestorationCoinsTest.checkRuntime
  SRSpecializationTest.checkRuntime
