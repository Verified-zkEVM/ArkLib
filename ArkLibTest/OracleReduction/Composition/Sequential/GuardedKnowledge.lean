/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.Composition.Sequential.Append.Knowledge

/-!
# Guarded knowledge composition at zero-round and challenge seams

The fixtures retain the actual equality relation between a Boolean statement and witness. Their
runtime guards may reject. Both directions of the empty-component boundary, a final left challenge,
a first right challenge, and a first right prover message exercise the exact append extractor.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace GuardedKnowledgeRegression

abbrev oracle : OracleSpec Unit := fun _ => Bool

abbrev challenge : ProtocolSpec 1 := ⟨fun _ => .V_to_P, fun _ => Bool⟩
abbrev message : ProtocolSpec 1 := ⟨fun _ => .P_to_V, fun _ => Bool⟩

instance : ∀ i, SampleableType (challenge.Challenge i) := fun _ =>
  inferInstanceAs (SampleableType Bool)

instance : ∀ i, SampleableType (message.Challenge i) := fun i =>
  False.elim (by have hi := i.2; simp at hi)

local instance : ∀ i, SampleableType ((challenge ++ₚ challenge).Challenge i) :=
  ProtocolSpec.instSampleableTypeChallengeAppend (pSpec₁ := challenge) (pSpec₂ := challenge)

local instance : ∀ i, SampleableType ((challenge ++ₚ message).Challenge i) :=
  ProtocolSpec.instSampleableTypeChallengeAppend (pSpec₁ := challenge) (pSpec₂ := message)

local instance : ∀ i, SampleableType ((!p[] ++ₚ challenge).Challenge i) :=
  ProtocolSpec.instSampleableTypeChallengeAppend (pSpec₁ := !p[]) (pSpec₂ := challenge)

local instance : ∀ i, SampleableType ((challenge ++ₚ !p[]).Challenge i) :=
  ProtocolSpec.instSampleableTypeChallengeAppend (pSpec₁ := challenge) (pSpec₂ := !p[])

local instance : ∀ i, SampleableType ((!p[] ++ₚ !p[]).Challenge i) :=
  ProtocolSpec.instSampleableTypeChallengeAppend (pSpec₁ := !p[]) (pSpec₂ := !p[])

abbrev relation : Set (Bool × Bool) := {p | p.1 = p.2}

/-- The fixture checks its transcript and preserves its Boolean statement. -/
def verifier {n : ℕ} (p : ProtocolSpec n) (check : p.FullTranscript → Bool) :
    Verifier oracle Bool Bool p :=
  ⟨fun s tr => if check tr then pure s else failure⟩

def form {n : ℕ} (p : ProtocolSpec n) (check : p.FullTranscript → Bool) :
    (verifier p check).GuardedForm := ⟨fun _ tr => check tr, fun s _ => s, fun _ _ => rfl⟩

def extractor {n : ℕ} (p : ProtocolSpec n) :
    Extractor.RoundByRound oracle Bool Bool Bool p (fun _ => Bool) where
  eqIn := rfl
  extractMid := fun _ _ _ w => w
  extractOut := fun _ _ w => w

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oracle (StateT σ ProbComp))

/-- The knowledge predicate is the actual equality relation, including at round zero. -/
def kstate {n : ℕ} (p : ProtocolSpec n) (check : p.FullTranscript → Bool) :
    (verifier p check).KnowledgeStateFunction init impl relation relation (extractor p) where
  toFun := fun _ s _ w => s = w
  toFun_empty := fun _ _ => Iff.rfl
  toFun_next := fun _ _ _ _ _ _ hw => hw
  toFun_full := by
    intro s tr w hp
    rw [gt_iff_lt, probEvent_pos_iff] at hp
    obtain ⟨out, hout, hrel⟩ := hp
    have ho := (Verifier.mem_outputs_iff init impl (verifier p check) s tr out).mpr hout
    have he := Verifier.outputs_guarded_subsingleton init impl (verifier p check)
      (form p check).check (form p check).out (form p check).verify_eq s tr ho
    change out = s at he
    exact he ▸ hrel

/-- Each component has zero bad-transition probability for the exposed extractor and state. -/
theorem sound {n : ℕ} (p : ProtocolSpec n) [∀ i, SampleableType (p.Challenge i)]
    (check : p.FullTranscript → Bool) :
    (verifier p check).rbrKnowledgeSoundnessWorstCaseWith init impl relation relation
      (fun _ => Bool) (extractor p) (kstate init impl p check) 0 := by
  intro s i tr
  change Pr[fun _ : p.Challenge i => ∃ w : Bool, ¬ s = w ∧ s = w | $ᵗ (p.Challenge i)] ≤ 0
  simp

private theorem sound_exists {n : ℕ} (p : ProtocolSpec n)
    [∀ i, SampleableType (p.Challenge i)] (check : p.FullTranscript → Bool) :
    (verifier p check).rbrKnowledgeSoundnessWorstCase init impl relation relation 0 :=
  ⟨(fun _ => Bool), extractor p, kstate init impl p check, sound init impl p check⟩

/-- A last left challenge followed immediately by a first right challenge uses the exact objects. -/
theorem challenge_seam :
    ((verifier challenge (fun tr => tr 0)).append
      (verifier challenge (fun tr => tr 0))).rbrKnowledgeSoundnessWorstCaseWith
      init impl relation relation
      (Verifier.KnowledgeAppend.Witness (fun _ : Fin 2 => Bool) (fun _ : Fin 2 => Bool))
      ((extractor challenge).append (extractor challenge) (form challenge (fun tr => tr 0)).out)
      (Verifier.KnowledgeStateFunction.appendGuarded (form challenge (fun tr => tr 0))
        (kstate init impl challenge (fun tr => tr 0))
        (kstate init impl challenge (fun tr => tr 0)))
      (Sum.elim 0 0 ∘ ChallengeIdx.sumEquiv.symm) :=
  Verifier.append_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_first
    (form challenge (fun tr => tr 0)) _ _ (sound init impl _ _) (sound init impl _ _)

/-- The first right prover message is checked with the same seam extraction. -/
theorem message_seam :
    ((verifier challenge (fun tr => tr 0)).append
      (verifier message (fun tr => tr 0))).rbrKnowledgeSoundnessWorstCase
      init impl relation relation
      (Sum.elim 0 0 ∘ ChallengeIdx.sumEquiv.symm) := by
  apply Verifier.append_rbrKnowledgeSoundnessWorstCase_of_guarded_first (R₂ := relation) _ _
    (form challenge (fun tr => tr 0))
  · exact sound_exists init impl _ _
  · exact sound_exists init impl _ _

/-- An empty left component still invokes the left extractor at the first right challenge. -/
theorem empty_left :
    ((verifier !p[] (fun _ => true)).append
      (verifier challenge (fun tr => tr 0))).rbrKnowledgeSoundnessWorstCase
      init impl relation relation
      (Sum.elim 0 0 ∘ ChallengeIdx.sumEquiv.symm) := by
  apply Verifier.append_rbrKnowledgeSoundnessWorstCase_of_guarded_first (R₂ := relation) _ _
    (form !p[] (fun _ => true))
  · exact sound_exists init impl _ _
  · exact sound_exists init impl _ _

/-- An empty right component invokes both output extractors in the terminal state. -/
theorem empty_right :
    ((verifier challenge (fun tr => tr 0)).append
      (verifier !p[] (fun _ => true))).rbrKnowledgeSoundnessWorstCase init impl relation relation
      (Sum.elim 0 0 ∘ ChallengeIdx.sumEquiv.symm) := by
  apply Verifier.append_rbrKnowledgeSoundnessWorstCase_of_guarded_first (R₂ := relation) _ _
    (form challenge (fun tr => tr 0))
  · exact sound_exists init impl _ _
  · exact sound_exists init impl _ _

/-- Two empty components preserve a non-universal relation as well. -/
theorem both_empty :
    ((verifier !p[] (fun _ => true)).append
      (verifier !p[] (fun _ => true))).rbrKnowledgeSoundnessWorstCase init impl relation relation
      (Sum.elim 0 0 ∘ ChallengeIdx.sumEquiv.symm) := by
  apply Verifier.append_rbrKnowledgeSoundnessWorstCase_of_guarded_first (R₂ := relation) _ _
    (form !p[] (fun _ => true))
  · exact sound_exists init impl _ _
  · exact sound_exists init impl _ _

omit init impl in
/-- Runtime rejection by the left persists even when the right transcript passes. -/
theorem rejection_persists (s : Bool) :
    ((verifier challenge (fun tr => tr 0)).append
      (verifier challenge (fun tr => tr 0))).run s
      (FullTranscript.append (pSpec₁ := challenge) (pSpec₂ := challenge)
        (fun _ => false) (fun _ => true)) = failure := by
  rw [Verifier.KnowledgeAppend.run_guarded (form challenge (fun tr => tr 0))]
  simp [form]

/-- The right leaf really queries and changes a shared oracle state. -/
def toggle : QueryImpl oracle (StateT Bool ProbComp) := fun _ => do
  let b ← get
  set (!b)
  pure b

def effectful : Verifier oracle Bool Bool !p[] := ⟨fun s _ => do
  let _ ← (query (spec := oracle) () : OracleComp oracle Bool)
  pure s⟩

omit init impl in
/-- The right query is executed and its state change is retained. -/
theorem effectful_run (s : Bool) (tr : (!p[]).FullTranscript) :
    (simulateQ toggle (effectful.run s tr)).run false = pure (some s, true) := by
  change (simulateQ toggle ((fun _ : Bool => some s) <$>
    (query (spec := oracle) () : OracleComp oracle Bool))).run false = _
  simp [simulateQ_map, toggle]

omit init impl in
private def effectful_state : effectful.KnowledgeStateFunction (pure false) toggle
    relation relation (extractor !p[]) where
  toFun := fun _ s _ w => s = w
  toFun_empty := fun _ _ => Iff.rfl
  toFun_next := fun i => Fin.elim0 i
  toFun_full := by
    intro s tr w hp
    change Pr[fun t => t = w | OptionT.mk do
      (simulateQ toggle (effectful.run s tr)).run' (← pure false)] > 0 at hp
    simp only [pure_bind, StateT.run'_eq] at hp
    erw [effectful_run] at hp
    have he : w = s := by simpa using hp
    exact he.symm

omit init impl in
/-- An actual effectful suffix satisfies the same guarded-left composition theorem. -/
theorem effectful_suffix :
    ((verifier challenge (fun tr => tr 0)).append effectful).rbrKnowledgeSoundnessWorstCase
      (pure false) toggle relation relation (Sum.elim 0 0 ∘ ChallengeIdx.sumEquiv.symm) := by
  apply Verifier.append_rbrKnowledgeSoundnessWorstCase_of_guarded_first (R₂ := relation) _ _
    (form challenge (fun tr => tr 0))
  · exact sound_exists (pure false) toggle _ _
  · exact ⟨(fun _ => Bool), extractor !p[], effectful_state, fun _ i => Fin.elim0 i.1⟩

omit init impl in
/-- A passing left guard preserves the effectful right leaf's observable state change. -/
theorem effectful_append_run (s : Bool) :
    (simulateQ toggle (((verifier challenge (fun tr => tr 0)).append effectful).run s
      ((fun _ => true) ++ₜ default))).run false = pure (some s, true) := by
  rw [Verifier.KnowledgeAppend.run_guarded (form challenge (fun tr => tr 0))]
  simp only [FullTranscript.append_fst, FullTranscript.append_snd, form, ↓reduceIte]
  exact effectful_run s _

/-- A rejected left transcript also makes every post-seam knowledge witness invalid. -/
theorem rejected_knowledge (s : Bool)
    (w : Verifier.KnowledgeAppend.Witness (fun _ : Fin 2 => Bool)
      (fun _ : Fin 2 => Bool) (Fin.last 2)) :
    ¬ (Verifier.KnowledgeStateFunction.appendGuarded (form challenge (fun tr => tr 0))
      (kstate init impl challenge (fun tr => tr 0))
      (kstate init impl challenge (fun tr => tr 0))) (Fin.last 2) s
        (FullTranscript.append (pSpec₁ := challenge) (pSpec₂ := challenge)
        (fun _ => false) (fun _ => true)) w := by
  simp only [Verifier.KnowledgeStateFunction.appendGuarded]
  erw [Verifier.KnowledgeAppend.state_right _ _ _ (k := Fin.last (1 + 1))
    (Fin.last 1) (by simp) (by simp)]
  erw [Verifier.KnowledgeAppend.left_full]
  simp [form]

end GuardedKnowledgeRegression

/--
info: 'Verifier.append_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_first'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.append_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_first

/--
info: 'Verifier.KnowledgeStateFunction.appendGuarded'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.KnowledgeStateFunction.appendGuarded
