/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.LiftContext.OracleReduction
import ArkLibTest.OracleReduction.GuardedLens

/-!
# Round-by-round context lifting

The lifted extractor carries the outer output witness through every intermediate round.
This remains valid when that witness type is empty, and guarded statement lenses retain
round-by-round soundness bounds.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace LiftContextRoundByRoundRegression

abbrev oracle : OracleSpec Empty := Empty →ₒ Unit
abbrev challengeRound : ProtocolSpec 1 := ⟨!v[.V_to_P], fun _ => Bool⟩

instance : ∀ i, SampleableType (challengeRound.Challenge i) :=
  fun _ => inferInstanceAs (SampleableType Bool)

def impl : QueryImpl oracle (StateT Unit ProbComp) := fun q => nomatch q

def verifier : Verifier oracle Unit Unit challengeRound := ⟨fun _ _ => pure ()⟩

/-- The input witness changes from Nat to Bool, while no outer output witness exists. -/
def emptyOutputLens : Extractor.Lens Unit Unit Unit Unit Bool Empty Nat Unit where
  stmt := ⟨id, fun _ => id⟩
  wit := ⟨(fun p => nomatch p.2), fun _ w => decide (w = 0)⟩

/-- The inner extractor retains a natural-number witness through the challenge. -/
def extractor : Extractor.RoundByRound oracle Unit Nat Unit challengeRound (fun _ => Nat) where
  extractIn := fun _ w => w
  extractMid := fun _ _ _ w => w
  extractOut := fun _ _ _ => 0

/-- A saved outer Boolean determines the reconstructed input witness. -/
def savedWitnessLens : Extractor.Lens Unit Unit Unit Unit Bool Bool Nat Unit where
  stmt := ⟨id, fun _ => id⟩
  wit := ⟨fun _ => (), fun p w => p.2 && decide (w = 0)⟩

/-- Execute final, intermediate and input extraction through the lifted witness lens. -/
def runSavedWitnessExtractor (saved : Bool) : Bool :=
  let lifted := extractor.liftContext savedWitnessLens
  lifted.extractIn ()
    (lifted.extractMid 0 () (fun _ => false)
      (lifted.extractOut () (fun _ => false) saved))

/-- info: (true, false) -/
#guard_msgs in
#eval (runSavedWitnessExtractor true, runSavedWitnessExtractor false)

/-- Each lifted intermediate witness saves the outer output witness. -/
example : Extractor.RoundByRound oracle Unit Bool Empty challengeRound
    (fun _ => Empty × Nat) :=
  extractor.liftContext emptyOutputLens

/-- An empty outer output type yields empty intermediate witness types. -/
example : IsEmpty (Empty × Nat) := inferInstance

instance : Extractor.Lens.IsKnowledgeSound (∅ : Set (Unit × Bool))
    (Set.univ : Set (Unit × Nat)) (∅ : Set (Unit × Empty))
    (Set.univ : Set (Unit × Unit))
    (verifier.compatStatement emptyOutputLens.stmt) (fun _ _ => True)
    ⟨emptyOutputLens.stmt, emptyOutputLens.wit⟩ where
  proj_knowledgeSound := fun _ _ w => nomatch w
  lift_knowledgeSound := fun _ w => nomatch w

/-- The inner knowledge state accepts every residual witness. -/
def knowledgeState : verifier.KnowledgeStateFunction (pure ()) impl
    (Set.univ : Set (Unit × Nat)) (Set.univ : Set (Unit × Unit)) extractor where
  toFun := fun _ _ _ _ => True
  toFun_empty := fun _ _ _ => Set.mem_univ _
  toFun_next := fun _ _ _ _ _ _ _ => trivial
  toFun_full := fun _ _ _ _ => trivial

theorem innerKnowledge : verifier.rbrKnowledgeSoundness (pure ()) impl
    (Set.univ : Set (Unit × Nat)) (Set.univ : Set (Unit × Unit)) (fun _ => 0) := by
  refine ⟨(fun _ => Nat), extractor, knowledgeState, ?_⟩
  intro stmt i tr
  simp [knowledgeState]

/-- Lifting does not require an inhabitant of the outer output witness type. -/
example : (verifier.liftContext emptyOutputLens.stmt).rbrKnowledgeSoundness
    (pure ()) impl (∅ : Set (Unit × Bool)) (∅ : Set (Unit × Empty)) (fun _ => 0) :=
  verifier.liftContext_rbrKnowledgeSoundness innerKnowledge
    (stmtLens := emptyOutputLens.stmt) (witLens := emptyOutputLens.wit)

section GuardedStatement

variable {ι σ CIn COut Flag : Type} {oSpec : OracleSpec ι}
    {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
    {init : ProbComp σ} {queryImpl : QueryImpl oSpec (StateT σ ProbComp)}
    (V : Verifier oSpec CIn COut pSpec)
    (langIn : Set CIn) (langOut : Set COut) (extra : Set Flag)
    {err : pSpec.ChallengeIdx → ℝ≥0}

local instance : Statement.Lens.IsSound
    (GuardedLensRegression.orLanguage langIn extra)
    (GuardedLensRegression.orLanguage langOut extra)
    langIn langOut (V.compatStatement GuardedLensRegression.orLens)
    GuardedLensRegression.orLens where
  proj_sound := (GuardedLensRegression.orLens_sound langIn langOut extra).proj_sound
  lift_sound := fun stmt stmtOut hOuter _ hInner =>
    (GuardedLensRegression.orLens_sound langIn langOut extra).lift_sound
      stmt stmtOut hOuter trivial hInner

/-- The auxiliary disjunct is retained in the soundness lift. -/
example (h : V.rbrSoundness init queryImpl langIn langOut err) :
    (V.liftContext GuardedLensRegression.orLens).rbrSoundness init queryImpl
      (GuardedLensRegression.orLanguage langIn extra)
      (GuardedLensRegression.orLanguage langOut extra) err :=
  V.liftContext_rbrSoundness h

end GuardedStatement

end LiftContextRoundByRoundRegression

/--
info: 'Verifier.liftContext_rbrSoundness' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.liftContext_rbrSoundness

/--
info: 'Verifier.liftContext_rbrKnowledgeSoundness' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.liftContext_rbrKnowledgeSoundness

/--
info: 'OracleVerifier.liftContext_rbrSoundness' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms OracleVerifier.liftContext_rbrSoundness

/--
info: 'OracleVerifier.liftContext_rbrKnowledgeSoundness' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms OracleVerifier.liftContext_rbrKnowledgeSoundness
