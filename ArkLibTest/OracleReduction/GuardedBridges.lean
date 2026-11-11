/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.Security.GuardedBridges
import ArkLib.OracleReduction.Security.GuardedSoundness

/-!
# Concrete guarded bridge regression tests

A mixed protocol retains the actual output witness through backward extraction, even when the
prover writes shared Boolean oracle state. Further examples cover rejection, zero rounds, and an
auxiliary prover input whose type differs from the empty input-relation witness type.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace GuardedBridgesRegression

abbrev oracle : OracleSpec Bool := Bool →ₒ Bool

/-- Queries can toggle the ambient bit, and return its current value. -/
def impl : QueryImpl oracle (StateT Bool ProbComp) := fun write => do
  if write then modify (!·)
  get

abbrev mixed : ProtocolSpec 2 := ⟨!v[.P_to_V, .V_to_P], fun _ => Bool⟩

instance : ∀ i, SampleableType (mixed.Challenge i) :=
  fun _ => inferInstanceAs (SampleableType Bool)

/-- Only true input statements are accepted. -/
def verifier : Verifier oracle Bool Bool mixed :=
  ⟨fun stmt _ => if stmt then pure stmt else failure⟩

def guarded : verifier.GuardedForm :=
  ⟨fun stmt _ => stmt, fun stmt _ => stmt, fun _ _ => rfl⟩

abbrev relIn : Set (Bool × Bool) := {p | p.1 = true ∧ p.2 = true}
abbrev relOut : Set (Bool × Bool) := {p | p.2 = true}

/-- Every backward step preserves the actual output witness. -/
def extractor : Extractor.RoundByRound oracle Bool Bool Bool mixed (fun _ => Bool) where
  extractIn := fun _ w => w
  extractMid := fun _ _ _ w => w
  extractOut := fun _ _ w => w

noncomputable def knowledgeState : verifier.KnowledgeStateFunction (pure false) impl
    relIn relOut extractor where
  toFun := fun _ stmt _ w => stmt = true ∧ w = true
  toFun_empty := fun _ _ h => h
  toFun_next := fun _ _ _ _ _ _ h => h
  toFun_full := fun stmt tr w hp => by
    exact guarded.check_and_of_prEvent_pos hp

theorem fixedKnowledge : verifier.rbrKnowledgeSoundnessWith (pure false) impl
    relIn relOut (fun _ => Bool) extractor knowledgeState (fun _ => 0) := by
  intro stmt i tr
  simp [knowledgeState, extractor]

/-- The mixed-schedule knowledge certificate yields ordinary knowledge soundness. -/
theorem mixedKnowledge : verifier.knowledgeSoundnessWith (pure false) impl relIn relOut
    extractor.foldExtractor 0 := by
  simpa using guarded.knowledgeSoundnessWith_of_rbrKnowledgeSoundnessWith
    knowledgeState fixedKnowledge

/-- Project the same certificate, then apply the ordinary soundness bridge. -/
theorem mixedSoundness : verifier.soundness (pure false) impl relIn.language relOut.language 0 := by
  have h := Verifier.rbrSoundness_of_rbrKnowledgeSoundnessWith fixedKnowledge
  simpa using guarded.soundness_of_rbrSoundness h

/-- This prover changes ambient state while sending its message. Its auxiliary input is Unit. -/
def effectfulProver : Prover oracle Bool Unit Bool Bool mixed where
  PrvState := fun _ => Bool
  input := fun input => input.1
  sendMessage := fun _ st => do
    let bit ← (query (spec := oracle) true : OracleComp oracle Bool)
    pure (bit, st)
  receiveChallenge := fun _ st => pure (fun _ => st)
  output := fun st => do
    let bit ← (query (spec := oracle) true : OracleComp oracle Bool)
    pure (st, bit)

/-- The prover's message really changes the shared state from false to true. -/
example : (simulateQ impl (effectfulProver.sendMessage ⟨0, rfl⟩ false)).run false =
    pure ((true, false), true) := by
  simp [effectfulProver, impl]

/-- The actual output step also changes ambient state and returns its resulting bit as witness. -/
example : (simulateQ impl (effectfulProver.output true)).run true =
    pure ((true, false), false) := by
  simp [effectfulProver, impl]

/-- Instantiate the soundness bridge against that effectful prover and a rejected statement. -/
example := mixedSoundness Unit Bool () effectfulProver false (by simp [relIn, Set.language])

/-- Instantiate the knowledge bridge against the same prover and an accepted statement. -/
example := mixedKnowledge Unit true () effectfulProver

/-- The folded extractor uses the supplied output witness in both cases. -/
example (stmt : Bool) (tr : mixed.FullTranscript) :
    (extractor.foldExtractor stmt true tr default default).run = pure (some true) := by
  rfl

example (stmt : Bool) (tr : mixed.FullTranscript) :
    (extractor.foldExtractor stmt false tr default default).run = pure (some false) := by
  rfl

/-- Noncommuting steps read their own prefix endpoint, so skipping or reversing a step changes
this concrete fold's result. -/
def orderedExtractor : Extractor.RoundByRound oracle Bool Nat Nat mixed (fun _ => Nat) where
  extractIn := fun _ w => w
  extractMid := fun i _ tr w =>
    if i.val = 0 then w + (cond (tr (Fin.last i.val)) 1 2)
    else 2 * w + (cond (tr (Fin.last i.val)) 3 4)
  extractOut := fun _ _ w => w + 5

example : (orderedExtractor.foldExtractor true 7 !v[true, false] default default).run =
    pure (some 29) := by rfl

run_cmd do
  let result := orderedExtractor.foldPrefix true (Fin.last 2) !v[true, false]
    (orderedExtractor.extractOut true !v[true, false] 7)
  unless result == 29 do throwError "Backward fold returned the wrong witness"

abbrev zero : ProtocolSpec 0 := !p[]

/-- Initial extraction can read the statement even when its witness type is different. -/
def statementExtractor : Extractor.RoundByRound oracle Bool Bool Unit zero (fun _ => Unit) where
  extractIn := fun stmt _ => stmt
  extractMid := fun i => Fin.elim0 i
  extractOut := fun _ _ w => w

example : statementExtractor.foldPrefix true 0 default () = true := rfl

example : statementExtractor.foldPrefix false 0 default () = false := rfl

example (stmt : Bool) :
    (statementExtractor.foldExtractor stmt () default default default).run =
      pure (some stmt) := rfl

run_cmd do
  unless statementExtractor.foldPrefix true 0 default () do
    throwError "Initial extraction lost the true statement"
  if statementExtractor.foldPrefix false 0 default () then
    throwError "Initial extraction lost the false statement"

def rejecting : Verifier oracle Unit Unit zero := ⟨fun _ _ => failure⟩

def rejectingGuard : rejecting.GuardedForm :=
  ⟨fun _ _ => false, fun _ _ => (), fun _ _ => rfl⟩

noncomputable def rejectingState : rejecting.StateFunction (pure false) impl ∅ Set.univ where
  toFun := fun _ _ _ => False
  toFun_empty := fun _ h => h
  toFun_next := fun i => Fin.elim0 i
  toFun_full := fun _ _ _ => by
    apply le_antisymm _ zero_le
    apply le_of_not_gt
    intro hp
    exact Bool.false_ne_true (rejectingGuard.check_and_of_prEvent_pos hp).1

/-- A true input language need not make the initial state true. -/
example : rejecting.StateFunction (pure false) impl Set.univ Set.univ where
  toFun := fun _ _ _ => False
  toFun_empty := fun _ _ => Set.mem_univ _
  toFun_next := fun i => Fin.elim0 i
  toFun_full := rejectingState.toFun_full

/-- Zero rounds and a rejecting guard give zero ordinary soundness error. -/
example : rejecting.soundness (pure false) impl ∅ Set.univ 0 := by
  have h : rejecting.rbrSoundness (pure false) impl ∅ Set.univ (fun _ => 0) := by
    apply Verifier.rbrSoundness_of_badEvents ∅ (fun _ _ _ => False)
      (pure false) impl Set.univ rejecting
    · intro stmt tr _ _
      exact rejectingState.toFun_full stmt tr id
    · intro _ _ i
      exact Fin.elim0 i.1
  simpa using rejectingGuard.soundness_of_rbrSoundness h

/-- A concrete zero-round prover has Unit auxiliary data and an actual output witness. -/
def zeroProver : Prover oracle Unit Unit Unit Unit zero where
  PrvState := fun _ => Unit
  input := fun _ => ()
  sendMessage := fun i => Fin.elim0 i.1
  receiveChallenge := fun i => Fin.elim0 i.1
  output := fun _ => do
    let _ ← (query (spec := oracle) true : OracleComp oracle Bool)
    pure ((), ())

/-- Rejection allows an optional extractor with empty input witness type, while the malicious
prover still has Unit auxiliary input and Unit output witnesses. -/
theorem emptyWitnessKnowledge : rejecting.knowledgeSoundnessWith (pure false) impl
    (∅ : Set (Unit × Empty)) (Set.univ : Set (Unit × Unit))
    (Extractor.Straightline.ofTranscriptAndOutput (fun _ _ _ => none)) 0 := by
  apply rejectingGuard.knowledgeSoundnessWith_of_output_transcript_event
    (pure false) impl ∅ Set.univ (fun _ _ _ => none) 0 (fun _ _ => False)
  · intro stmt tr wit hc
    cases hc
  · intro Aux stmt wit P os
    simp

example := emptyWitnessKnowledge Unit () () zeroProver

/-- A total fold with empty input witnesses necessarily also has empty output witnesses for a
zero-round protocol with inhabited statements. The optional adapter above exercises the concrete
malicious-prover boundary independently. -/
def emptyExtractor : Extractor.RoundByRound oracle Unit Empty Empty zero (fun _ => Empty) where
  extractIn := fun _ w => w
  extractMid := fun i => Fin.elim0 i
  extractOut := fun _ _ w => w

noncomputable def emptyKnowledgeState : rejecting.KnowledgeStateFunction (pure false) impl
    (∅ : Set (Unit × Empty)) (∅ : Set (Unit × Empty)) emptyExtractor where
  toFun := fun _ _ _ w => nomatch w
  toFun_empty := fun _ w => nomatch w
  toFun_next := fun i => Fin.elim0 i
  toFun_full := fun _ _ w => nomatch w

example : rejecting.knowledgeSoundnessWith (pure false) impl
    (∅ : Set (Unit × Empty)) (∅ : Set (Unit × Empty)) emptyExtractor.foldExtractor 0 := by
  have h : rejecting.rbrKnowledgeSoundnessWith (pure false) impl
      (∅ : Set (Unit × Empty)) (∅ : Set (Unit × Empty)) (fun _ => Empty)
      emptyExtractor emptyKnowledgeState (fun _ => 0) := fun _ i => Fin.elim0 i.1
  simpa using rejectingGuard.knowledgeSoundnessWith_of_rbrKnowledgeSoundnessWith
    emptyKnowledgeState h

end GuardedBridgesRegression
