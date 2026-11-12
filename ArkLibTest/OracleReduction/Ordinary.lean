/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuxi Zheng, Chung Thai Nguyen, Michele Orrù
-/
import ArkLib.OracleReduction.Security.Ordinary
import VCVio.OracleComp.RunIO

/-!
# Ordinary security boundaries

A verifier can draw private coins despite an empty public oracle interface. Neither its draws
nor the prover's private draws enter the extractor's logs. Rejection and missing extraction
remain distinct outcomes.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ProbabilityTheory

namespace OrdinarySecurityTest

def coinProver : NARG.Prover []ₒ Unit Unit :=
  (do
    let _ ← samplePrivateUniform (publicSpec := []ₒ) Bool
    pure ((), ()) : OracleComp ([]ₒ + unifSpec) (Unit × Unit))

def coinVerifier : NARG.Verifier []ₒ Unit Unit where
  verify _ _ := do
    let accepted ← liftM (samplePrivateUniform (publicSpec := []ₒ) Bool)
    pure accepted

def checkHiddenCoins : NARG.Extractor []ₒ Unit Unit Unit := fun _ _ logP logV =>
  if logP.isEmpty && logV.isEmpty then pure () else failure

-- Both parties sample a real private coin; the extractor still receives two empty logs.
example :
    NARG.knowledgeSoundnessExperiment (pure ()) PublicCoinIP.emptyImpl
      coinVerifier checkHiddenCoins coinProver = (do
        let _ ← sampleUniform Bool
        let accepted ← sampleUniform Bool
        pure ((), some (), some accepted)) := by
  have hE : checkHiddenCoins = fun _ _ _ _ => pure () := by
    funext x π logP logV
    cases logP with
    | cons entry _ => nomatch entry.1
    | nil =>
      cases logV with
      | cons entry _ => nomatch entry.1
      | nil => rfl
  rw [hE]
  simp only [NARG.knowledgeSoundnessExperiment_eq, coinProver, coinVerifier]
  simp only [QueryImpl.addLift_def, QueryImpl.liftTarget_self, OptionT.liftM_def,
    OptionT.run_lift, simulateQ_bind, simulateQ_pure, OptionT.run_pure, bind_assoc, pure_bind,
    StateT.run'_bind', StateT.run'_pure']
  rfl

-- Verifier rejection never creates a knowledge failure, even with no extracted witness.
example : ¬ NARG.knowledgeSoundnessFailureEvent (∅ : Set (Unit × Unit))
    ((), none, some false) := by
  simp [NARG.knowledgeSoundnessFailureEvent, nargKSFailEvent]

-- Adding the dummy witness changes neither the move count nor the private-coin convention.
example {Statement Salt : Type} {n : ℕ} {pSpec : ProtocolSpec n}
    (P : PublicCoinIP.SRProver Statement pSpec (Salt := Salt)) (t : ℕ) :
    P.toReduction.IsQueryBoundP
      (publicQuerySelector (Verifier.StateRestoration.isSrChallengeMove (Salt := Salt)
        (oSpec := []ₒ))) t ↔
    P.IsQueryBoundP
      (publicQuerySelector (Verifier.StateRestoration.isSrChallengeMove (Salt := Salt)
        (oSpec := []ₒ))) t := by
  simp [PublicCoinIP.SRProver.toReduction]

/-- Execute both parties' private sampling and check that extraction sees neither coin log. -/
def checkRuntime : IO Unit := do
  let (_, witness, accepted) ← OracleComp.runIO <|
    NARG.knowledgeSoundnessExperiment (pure ()) PublicCoinIP.emptyImpl
      coinVerifier checkHiddenCoins coinProver
  unless witness == some () && accepted.isSome do
    throw (IO.userError "ordinary NARG execution exposed private draws or lost the verifier result")

end OrdinarySecurityTest

namespace OrdinaryParameterizedSecurityTest

-- The upper boundary is included, whereas the immediately larger false statement is excluded.
example : NARG.soundnessFailureEventSizeBounded id 3 (∅ : Set ℕ) (some (3, true)) := by
  simp [NARG.soundnessFailureEventSizeBounded, NARG.soundnessFailureEvent, nargSoundFailEvent]

example : ¬ NARG.soundnessFailureEventSizeBounded id 3 (∅ : Set ℕ) (some (4, true)) := by
  simp [NARG.soundnessFailureEventSizeBounded]

-- Neither rejection nor a missing verifier result becomes a false-acceptance event.
example : ¬ NARG.soundnessFailureEventSizeBounded id 3 (∅ : Set ℕ) (some (3, false)) := by
  simp [NARG.soundnessFailureEventSizeBounded, NARG.soundnessFailureEvent, nargSoundFailEvent]

example : ¬ NARG.soundnessFailureEventSizeBounded id 3 (∅ : Set ℕ) none := by
  simp [NARG.soundnessFailureEventSizeBounded]

-- Making oversized pairs valid would miss this case: the whole event must be excluded even
-- when extraction returns no witness.
example : ¬ NARG.knowledgeSoundnessFailureEventSizeBounded id 3 (Set.univ : Set (ℕ × Unit))
    (4, none, some true) := by
  simp [NARG.knowledgeSoundnessFailureEventSizeBounded]

example : NARG.knowledgeSoundnessFailureEventSizeBounded id 3 (Set.univ : Set (ℕ × Unit))
    (3, none, some true) := by
  simp [NARG.knowledgeSoundnessFailureEventSizeBounded]

example : ¬ NARG.knowledgeSoundnessFailureEventSizeBounded id 3 (∅ : Set (ℕ × Unit))
    (3, none, some false) := by
  simp [NARG.knowledgeSoundnessFailureEventSizeBounded,
    NARG.knowledgeSoundnessFailureEvent, nargKSFailEvent]

example : ¬ NARG.knowledgeSoundnessFailureEventSizeBounded id 3 (∅ : Set (ℕ × Unit))
    (3, none, none) := by simp [NARG.knowledgeSoundnessFailureEventSizeBounded]

-- Query indices depend on the security parameter; answers and stored state depend on n.
def publicSpec (securityParam instanceBound : ℕ) : OracleSpec (Fin (securityParam + 1)) :=
  Fin (securityParam + 1) →ₒ Fin (instanceBound + 1)

def sampleOracle (securityParam instanceBound : ℕ) : ProbComp (Fin (instanceBound + 1)) :=
  pure ⟨securityParam % (instanceBound + 1), Nat.mod_lt _ (Nat.zero_lt_succ _)⟩

def oracleImpl (securityParam instanceBound : ℕ) :
    QueryImpl (publicSpec securityParam instanceBound)
      (StateT (Fin (instanceBound + 1)) ProbComp) := fun _ => get

-- The NARG-string type also varies with both public parameters.
def verifier (securityParam instanceBound : ℕ) :
    NARG.Verifier (publicSpec securityParam instanceBound) ℕ
      (Fin (securityParam + instanceBound + 1)) where
  verify _ _ := pure false

def extractor (securityParam instanceBound : ℕ) :
    NARG.Extractor (publicSpec securityParam instanceBound) ℕ Unit
      (Fin (securityParam + instanceBound + 1)) := fun _ _ _ _ => pure ()

-- A fixed-configuration probability bound supplies the whole parameterized definition.
example (language : Set ℕ) (error : ℕ → ℕ → ℕ → ENNReal)
    (h : ∀ sec n t (P : NARG.Prover (publicSpec sec n) ℕ (Fin (sec + n + 1))),
      P.IsQueryBoundP (publicQuerySelector fun _ => True) t →
      Pr{let out ← (NARG.soundnessExperiment (sampleOracle sec n) (oracleImpl sec n)
        (verifier sec n) P)}[NARG.soundnessFailureEvent language out] ≤ error sec n t) :
    NARG.adaptiveSoundness publicSpec sampleOracle oracleImpl verifier language id error := by
  intro sec n t P hP
  refine (prEvent_mono _ _ _ ?_).trans (h sec n t P hP)
  intro out hout
  cases out with
  | none => exact False.elim hout
  | some out => exact hout.2

-- The named extractor is one family, fixed before all budgets and adversaries.
example (relation : Set (ℕ × Unit)) (error : ℕ → ℕ → ℕ → ENNReal)
    (h : ∀ sec n t (P : NARG.Prover (publicSpec sec n) ℕ (Fin (sec + n + 1))),
      P.IsQueryBoundP (publicQuerySelector fun _ => True) t →
      Pr{let out ←
        (NARG.knowledgeSoundnessExperiment (sampleOracle sec n) (oracleImpl sec n)
          (verifier sec n) (extractor sec n) P)}[NARG.knowledgeSoundnessFailureEvent relation out] ≤
        error sec n t) :
    NARG.adaptiveKnowledgeSoundness publicSpec sampleOracle oracleImpl verifier
      relation id error := by
  refine ⟨extractor, ?_⟩
  intro sec n t P hP
  exact (prEvent_mono _ _ _ fun _ hout => hout.2).trans (h sec n t P hP)

end OrdinaryParameterizedSecurityTest

/-- Run with `lake env lean --run ArkLibTest/OracleReduction/Ordinary.lean`. -/
def main : IO Unit := OrdinarySecurityTest.checkRuntime
