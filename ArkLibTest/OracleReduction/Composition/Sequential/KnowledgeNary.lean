/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.Composition.Sequential.KnowledgeNary
import ArkLibTest.OracleReduction.Composition.Sequential.GuardedKnowledge

/-!
# Finite guarded knowledge composition acceptance cases

The sequence preserves the actual equality relation between a Boolean statement and witness.
Every component checks its Boolean challenge. The empty sequence, singleton, and longer sequence
exercise the exact recursive knowledge objects and actual verifier execution.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace KnowledgeNaryRegression

open GuardedKnowledgeRegression
open Verifier.KnowledgeSeqCompose

/-- A finite sequence of actual guarded challenge verifiers. -/
def sequence (m : ℕ) :
    Verifier oracle Bool Bool (ProtocolSpec.seqCompose (fun _ : Fin m => challenge)) :=
  Verifier.seqCompose (fun _ => Bool) (fun _ => verifier challenge (fun tr => tr 0))

/-- The recursive extractor retains all component extraction seams. -/
def sequenceExtractor (m : ℕ) :=
  Verifier.KnowledgeSeqCompose.extractor (fun _ : Fin (m + 1) => Bool) (fun _ => Bool)
    (fun _ => verifier challenge (fun tr => tr 0)) (fun _ => form challenge (fun tr => tr 0))
    (fun _ _ => Bool) (fun _ => GuardedKnowledgeRegression.extractor challenge)

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oracle (StateT σ ProbComp))

/-- The exact knowledge state generated from non-universal component equality predicates. -/
def sequenceState (m : ℕ) :=
  state (fun _ : Fin (m + 1) => Bool) (fun _ => Bool) init impl (fun _ => relation)
    (fun _ => verifier challenge (fun tr => tr 0)) (fun _ => form challenge (fun tr => tr 0))
    (fun _ _ => Bool) (fun _ => GuardedKnowledgeRegression.extractor challenge)
    (fun _ => kstate init impl challenge (fun tr => tr 0))

/-- Every finite fixture sequence uses the exposed exact extractor and state in the WC contract. -/
theorem sequence_sound (m : ℕ) :
    (sequence m).rbrKnowledgeSoundnessWorstCaseWith init impl relation relation
      (Witness (fun _ : Fin (m + 1) => Bool) (fun _ _ => Bool)) (sequenceExtractor m)
      (sequenceState init impl m) (error (fun _ : Fin m => (0 : challenge.ChallengeIdx → ℝ≥0))) :=
  Verifier.seqCompose_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_verifiers
    (fun _ => Bool) (fun _ => Bool) init impl (fun _ => relation)
    (fun _ => verifier challenge (fun tr => tr 0)) (fun _ => form challenge (fun tr => tr 0))
    (fun _ _ => Bool) (fun _ => GuardedKnowledgeRegression.extractor challenge)
    (fun _ => kstate init impl challenge (fun tr => tr 0)) (fun _ => 0)
    (fun _ => sound init impl challenge (fun tr => tr 0))

/-- The zero-component contract is inhabited by the actual identity extractor and state. -/
theorem empty_sound :
    (sequence 0).rbrKnowledgeSoundnessWorstCaseWith init impl relation relation
      (Witness (fun _ : Fin 1 => Bool) (fun _ _ => Bool)) (sequenceExtractor 0)
      (sequenceState init impl 0) (error (fun _ : Fin 0 => (0 : challenge.ChallengeIdx → ℝ≥0))) :=
  sequence_sound init impl 0

/-- The singleton keeps the terminal identity seam in the exact recursive extractor. -/
theorem singleton_sound :
    (sequence 1).rbrKnowledgeSoundnessWorstCaseWith init impl relation relation
      (Witness (fun _ : Fin 2 => Bool) (fun _ _ => Bool)) (sequenceExtractor 1)
      (sequenceState init impl 1) (error (fun _ : Fin 1 => (0 : challenge.ChallengeIdx → ℝ≥0))) :=
  sequence_sound init impl 1

/-- A three-component client checks repeated composition rather than only one binary seam. -/
theorem three_sound :
    (sequence 3).rbrKnowledgeSoundnessWorstCaseWith init impl relation relation
      (Witness (fun _ : Fin 4 => Bool) (fun _ _ => Bool)) (sequenceExtractor 3)
      (sequenceState init impl 3) (error (fun _ : Fin 3 => (0 : challenge.ChallengeIdx → ℝ≥0))) :=
  sequence_sound init impl 3

omit init impl in
/-- The empty sequence really executes the identity verifier. -/
theorem empty_run (s : Bool) : (sequence 0).run s (fun i => i.elim0) = pure s := rfl

/-- At its only cutoff, the empty recursive knowledge state is the actual input relation. -/
theorem empty_state (s w : Bool) :
    sequenceState init impl 0 0 s (fun i => i.elim0) w ↔ s = w := Iff.rfl

/-- The singleton's final cutoff still uses its component knowledge state through the seam. -/
theorem singleton_state (s w : Bool) :
    sequenceState init impl 1 (Fin.last 1) s
      (FullTranscript.append (pSpec₁ := challenge) (pSpec₂ := !p[])
        (fun _ => true) default) w ↔ s = w := by
  rfl

omit init impl in
/-- A rejected singleton transcript aborts the actual composed verifier. -/
theorem singleton_rejects (s : Bool) :
    (sequence 1).run s
      (FullTranscript.append (pSpec₁ := challenge) (pSpec₂ := !p[])
        (fun _ => false) default) = failure := by
  change ((verifier challenge (fun tr => tr 0)).append Verifier.id).run s _ = failure
  rw [Verifier.KnowledgeAppend.run_guarded (form challenge (fun tr => tr 0))]
  simp [form]

omit init impl in
/-- The first and last components pass, while the middle component rejects. -/
def mixedTranscript : (ProtocolSpec.seqCompose (fun _ : Fin 3 => challenge)).FullTranscript :=
  FullTranscript.append (pSpec₁ := challenge) (pSpec₂ := challenge ++ₚ (challenge ++ₚ !p[]))
    (fun _ => true)
    (FullTranscript.append (pSpec₁ := challenge) (pSpec₂ := challenge ++ₚ !p[])
      (fun _ => false)
      (FullTranscript.append (pSpec₁ := challenge) (pSpec₂ := !p[])
        (fun _ => true) default))

omit init impl in
/-- A rejected middle component stays rejected when the first and last components pass. -/
theorem middle_rejects (s : Bool) : (sequence 3).run s mixedTranscript = failure := by
  unfold mixedTranscript
  change ((verifier challenge (fun tr => tr 0)).append
    ((verifier challenge (fun tr => tr 0)).append
      ((verifier challenge (fun tr => tr 0)).append Verifier.id))).run s _ = failure
  rw [Verifier.KnowledgeAppend.run_guarded (form challenge (fun tr => tr 0))]
  simp only [FullTranscript.append_fst, FullTranscript.append_snd, form, ↓reduceIte]
  rw [Verifier.KnowledgeAppend.run_guarded (form challenge (fun tr => tr 0))]
  simp [form]

omit init impl in
/-- The actual recursive terminal extractor returns the same equality witness. -/
theorem terminal_extraction (s w : Bool) :
    (sequenceExtractor 3).extractOut s mixedTranscript w = w := rfl

omit init impl in
/-- Extraction at the first challenge after a component seam uses the actual recursive extractor. -/
theorem second_challenge_extraction (s w : Bool)
    (tr : (ProtocolSpec.seqCompose (fun _ : Fin 3 => challenge)).Transcript
      (Fin.succ (1 : Fin 3))) :
    (sequenceExtractor 3).extractMid (1 : Fin 3) s tr w = w := rfl

/-- Once the rejected middle component is behind a seam, no final knowledge witness survives. -/
theorem middle_knowledge_rejects (s w : Bool) :
    ¬ sequenceState init impl 3 (Fin.last 3) s mixedTranscript w := by
  change ¬ (Verifier.KnowledgeStateFunction.appendGuarded
    (form challenge (fun tr => tr 0)) (kstate init impl challenge (fun tr => tr 0))
    (sequenceState init impl 2)) (Fin.last 3) s mixedTranscript w
  simp only [Verifier.KnowledgeStateFunction.appendGuarded]
  erw [Verifier.KnowledgeAppend.state_right _ _ _ (k := Fin.last (1 + 2))
    (Fin.last 2) (by simp) (by simp)]
  intro h
  have ht := h.2
  change (Verifier.KnowledgeStateFunction.appendGuarded
    (form challenge (fun tr => tr 0)) (kstate init impl challenge (fun tr => tr 0))
    (sequenceState init impl 1)) (Fin.last 2) s
      (FullTranscript.append (pSpec₁ := challenge) (pSpec₂ := challenge ++ₚ !p[])
        (fun _ => false)
        (FullTranscript.append (pSpec₁ := challenge) (pSpec₂ := !p[])
          (fun _ => true) default)) w at ht
  simp only [Verifier.KnowledgeStateFunction.appendGuarded] at ht
  erw [Verifier.KnowledgeAppend.state_right _ _ _ (k := Fin.last (1 + 1))
    (Fin.last 1) (by simp) (by simp)] at ht
  have hbad := ht.1
  change false = true at hbad
  cases hbad

omit init impl in
/-- Decoding a later component challenge returns its actual, distinct component error. -/
theorem third_error :
    error (fun i : Fin 3 => fun _ : challenge.ChallengeIdx => (i.val + 1 : ℝ≥0))
      (sigmaChallengeIdxToSeqCompose (pSpec := fun _ : Fin 3 => challenge)
        2 ⟨0, rfl⟩) = 3 := by
  rw [error_component]
  norm_num

omit init impl in
/-- The public sigma decoder selects the same third-component error, rather than the first. -/
theorem third_decoded_error :
    (let ij := seqComposeChallengeIdxToSigma
      (sigmaChallengeIdxToSeqCompose (pSpec := fun _ : Fin 3 => challenge) 2 ⟨0, rfl⟩)
     (ij.1.val + 1 : ℝ≥0)) = 3 := by
  rw [← congrFun (error_eq_sigma
    (fun i : Fin 3 => fun _ : challenge.ChallengeIdx => (i.val + 1 : ℝ≥0)))
    (sigmaChallengeIdxToSeqCompose (pSpec := fun _ : Fin 3 => challenge) 2 ⟨0, rfl⟩)]
  exact third_error

end KnowledgeNaryRegression
