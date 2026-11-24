/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuxi Zheng, Chung Thai Nguyen, Michele Orrù
-/
import ArkLib.InteractiveProof.Soundness
import VCVio.OracleComp.RunIO

/-!
# NARG security boundaries

The prover and the extractor can draw private coins despite an empty public oracle interface.
The prover's draws do not enter the extractor's logs. Rejection and missing extraction remain
distinct outcomes. A statement-size bound is part of the failure event, and a family statement
quantifies over its parameters itself.
-/

open OracleComp OracleSpec
open scoped NNReal ProbabilityTheory

namespace NARGSecurityTest

def emptyImpl {σ : Type} : QueryImpl []ₒ (StateT σ ProbComp) := fun q => nomatch q

def coinProver : NARG.Prover []ₒ Unit Unit :=
  (do
    let _ ← samplePrivateUniform (publicSpec := []ₒ) Bool
    pure ((), ()) : OracleComp ([]ₒ + unifSpec) (Unit × Unit))

def acceptingVerifier : NonInteractiveVerifier Unit []ₒ Unit Bool where
  verify _ _ := pure true

-- The extractor samples its own coin and succeeds only on two empty logs.
def checkHiddenCoins : NARG.Extractor []ₒ Unit Unit Unit := fun _ _ logP logV =>
  if logP.isEmpty && logV.isEmpty then do
    let _ ← OptionT.lift (samplePrivateUniform (publicSpec := []ₒ) Bool)
    pure ()
  else failure

-- Verifier rejection never creates a knowledge failure, even with no extracted witness.
example : ¬ nargKSFailEvent (∅ : Set (Unit × Unit)) {true} ((), none, some false) := by
  simp [nargKSFailEvent]

/-- Execute the prover's and extractor's private sampling and check that extraction sees no
prover coin in its logs. -/
def checkRuntime : IO Unit := do
  let (_, witness, accepted) ← OracleComp.runIO <|
    adaptiveNARGKnowledgeSoundnessExp (pure ()) emptyImpl
      acceptingVerifier checkHiddenCoins coinProver
  unless witness == some () && accepted == some true do
    throw (IO.userError "NARG execution exposed private draws or lost the verifier result")

end NARGSecurityTest

namespace NARGParameterizedSecurityTest

-- A size bound `size x ≤ n` enters the event through the input language: the upper boundary is
-- included, whereas the immediately larger false statement is excluded.
example : nargSoundFailEvent {x : ℕ | x ≤ 3 → x ∈ (∅ : Set ℕ)} {true} (some (3, true)) := by
  simp [nargSoundFailEvent]

example : ¬ nargSoundFailEvent {x : ℕ | x ≤ 3 → x ∈ (∅ : Set ℕ)} {true} (some (4, true)) := by
  simp [nargSoundFailEvent]

-- Neither rejection nor a missing verifier result becomes a false-acceptance event.
example : ¬ nargSoundFailEvent {x : ℕ | x ≤ 3 → x ∈ (∅ : Set ℕ)} {true} (some (3, false)) := by
  simp [nargSoundFailEvent]

example : ¬ nargSoundFailEvent {x : ℕ | x ≤ 3 → x ∈ (∅ : Set ℕ)} {true} none := by
  simp [nargSoundFailEvent]

-- For knowledge soundness, the size-restricted verifier rejects an oversized statement, so the
-- event is excluded even when extraction returns no witness.
example : ¬ nargKSFailEvent (Set.univ : Set (ℕ × Unit)) {true} (4, none, some false) := by
  simp [nargKSFailEvent]

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
    NonInteractiveVerifier (Fin (securityParam + instanceBound + 1))
      (publicSpec securityParam instanceBound) ℕ Bool where
  verify _ _ := pure false

def extractor (securityParam instanceBound : ℕ) :
    NARG.Extractor (publicSpec securityParam instanceBound) ℕ Unit
      (Fin (securityParam + instanceBound + 1)) := fun _ _ _ _ => pure ()

-- A family statement quantifies over the parameters and the budget itself. A fixed-configuration
-- probability bound on the experiment supplies each instance of the predicate.
example (language : Set ℕ) (error : ℕ → ℕ → ℕ → ENNReal)
    (h : ∀ sec n t (P : NARG.Prover (publicSpec sec n) ℕ (Fin (sec + n + 1))),
      P.IsQueryBoundP (publicQuerySelector fun _ => True) t →
      Pr{let out ← (adaptiveNARGSoundnessExp (sampleOracle sec n) (oracleImpl sec n)
        (verifier sec n) P)}[nargSoundFailEvent {x | x ≤ n → x ∈ language} {true} out] ≤
        error sec n t) :
    ∀ sec n t, (verifier sec n).adaptiveNARGSoundnessQueryBounded (sampleOracle sec n)
      (oracleImpl sec n) {x | x ≤ n → x ∈ language} {true} (fun _ => True) t (error sec n t) :=
  fun sec n t => (Verifier.adaptiveNARGSoundnessQueryBounded_iff ..).2 (h sec n t)

-- The named extractor family is fixed before all budgets and adversaries.
example (relation : Set (ℕ × Unit)) (error : ℕ → ℕ → ℕ → ENNReal)
    (h : ∀ sec n t (P : NARG.Prover (publicSpec sec n) ℕ (Fin (sec + n + 1))),
      P.IsQueryBoundP (publicQuerySelector fun _ => True) t →
      Pr{let out ← (adaptiveNARGKnowledgeSoundnessExp (sampleOracle sec n) (oracleImpl sec n)
        (verifier sec n) (extractor sec n) P)}[nargKSFailEvent relation {true} out] ≤
        error sec n t) :
    ∃ E : ∀ sec n, NARG.Extractor (publicSpec sec n) ℕ Unit (Fin (sec + n + 1)),
      ∀ sec n t, (verifier sec n).adaptiveNARGKnowledgeSoundnessQueryBoundedWithExtractor
        (sampleOracle sec n) (oracleImpl sec n) relation {true} (E sec n) (fun _ => True) t
        (error sec n t) :=
  ⟨extractor, fun sec n t =>
    (Verifier.adaptiveNARGKnowledgeSoundnessQueryBoundedWithExtractor_iff ..).2 (h sec n t)⟩

end NARGParameterizedSecurityTest

/-- Run with `lake env lean --run ArkLibTest/NonInteractiveArgument/NARG.lean`. -/
def main : IO Unit := NARGSecurityTest.checkRuntime
