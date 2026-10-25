/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.Security.StatelessImplications

/-! # Stateless implication regressions

The specification is nonempty. Both deterministic and freshly randomized handlers instantiate
the implications; the adversarial prover is still allowed to query this ambient specification.
The zero-round protocol preserves a nontrivial relation, not the universal relation.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ProbabilityTheory

namespace StatelessImplicationTests

abbrev spec : OracleSpec Bool := Bool →ₒ Bool

def deterministic : QueryImpl spec ProbComp := fun bit => pure bit

def randomized : QueryImpl spec ProbComp := fun _ => $ᵗ Bool

example : simulateQ deterministic (query (spec := spec) true : OracleComp spec Bool) =
    pure true := by simp [deterministic]

example : simulateQ randomized (do
    let first ← (query (spec := spec) true : OracleComp spec Bool)
    let second ← (query (spec := spec) true : OracleComp spec Bool)
    pure (first, second)) = (do
      let first ← $ᵗ Bool
      let second ← $ᵗ Bool
      pure (first, second)) := by
  simp [randomized]

def verifier : Verifier spec Bool Bool !p[] := ⟨fun stmt _ => pure stmt⟩

def relation : Set (Bool × Unit) := { ⟨stmt, _⟩ | stmt = true }

example : (true, ()) ∈ relation ∧ (false, ()) ∉ relation := by simp [relation]

def extractor : Extractor.RoundByRound spec Bool Unit Unit !p[] (fun _ => Unit) where
  eqIn := rfl
  extractMid := fun m => nomatch m
  extractOut := fun _ _ witOut => witOut

def knowledgeState (handler : QueryImpl spec ProbComp) :
    verifier.KnowledgeStateFunction (pure PUnit.unit) handler.statelessLift
      relation relation extractor where
  toFun := fun _ stmt _ _ => stmt = true
  toFun_empty := by intros; rfl
  toFun_next := fun m => nomatch m
  toFun_full := by
    intro stmt tr wit h
    simp only [Fin.val_last, gt_iff_lt, OptionT.prEvent_mk_pos_iff] at h
    obtain ⟨out, hout, hrel⟩ := h
    simp only [pure_bind, QueryImpl.simulateQ_statelessLift_run'] at hout
    change some out ∈ support (simulateQ handler (pure (some stmt))) at hout
    have heq : out = stmt := by simpa using hout
    exact heq.symm.trans hrel

theorem rbr (handler : QueryImpl spec ProbComp) :
    verifier.rbrKnowledgeSoundness (pure PUnit.unit) handler.statelessLift relation relation
      (fun _ => 0) := by
  refine ⟨fun _ => Unit, extractor, knowledgeState handler, ?_⟩
  intro stmt wit prover i
  exact Fin.elim0 i.1

theorem deterministic_knowledge_soundness :
    verifier.knowledgeSoundness (pure PUnit.unit) deterministic.statelessLift
      relation relation 0 := by
  simpa using Verifier.rbrKnowledgeSoundness_implies_knowledgeSoundness deterministic
    relation relation verifier (fun _ => 0) (rbr deterministic)

theorem randomized_knowledge_soundness :
    verifier.knowledgeSoundness (pure PUnit.unit) randomized.statelessLift
      relation relation 0 := by
  simpa using Verifier.rbrKnowledgeSoundness_implies_knowledgeSoundness randomized
    relation relation verifier (fun _ => 0) (rbr randomized)

example (stmt : Bool) (wit : Unit) (tr : FullTranscript !p[]) :
    (extractor.toStraightline stmt wit tr [] []).run = pure (some wit) := rfl

def oneProverRound : ProtocolSpec 1 := ⟨!v[.P_to_V], !v[Unit]⟩

def backwardStep : Extractor.RoundByRound spec Unit Bool Bool oneProverRound
    (fun _ => Bool) where
  eqIn := rfl
  extractMid := fun _ _ _ wit => !wit
  extractOut := fun _ _ wit => wit

/-- info: false -/
#guard_msgs in
#eval backwardStep.extractPrefix () (Fin.last 1) (fun | ⟨0, _⟩ => ()) true

example : (backwardStep.toStraightline () true (fun | ⟨0, _⟩ => ()) [] []).run =
    pure (some false) := rfl

end StatelessImplicationTests

/-- info: 'Verifier.rbrSoundness_implies_soundness' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.rbrSoundness_implies_soundness

/-- info: 'Verifier.rbrKnowledgeSoundnessWith_implies_knowledgeSoundnessWith' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.rbrKnowledgeSoundnessWith_implies_knowledgeSoundnessWith

/-- info: 'Verifier.rbrKnowledgeSoundness_implies_knowledgeSoundness' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.rbrKnowledgeSoundness_implies_knowledgeSoundness

/-- info: 'StatelessImplicationTests.randomized_knowledge_soundness' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StatelessImplicationTests.randomized_knowledge_soundness
