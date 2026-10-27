/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Composition.Sequential.Append.SoundnessEmpty
import ArkLib.OracleReduction.Composition.Sequential.General

/-!
# Ordinary soundness and knowledge-soundness composition API regressions

Two one-challenge verifiers preserve the input statement and reject complementary challenges.
Their zero-error soundness bounds hold against arbitrary provers, including arbitrary auxiliary
input and output types. The examples exercise binary, plain-model and finite-chain interfaces.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace OrdinaryCompositionRegression

abbrev protocol : ProtocolSpec 1 := ⟨fun _ => .V_to_P, fun _ => Bool⟩

instance : ∀ i, SampleableType (protocol.Challenge i) :=
  fun _ => inferInstanceAs (SampleableType Bool)

local instance : ∀ i, SampleableType ((protocol ++ₚ protocol).Challenge i) :=
  ProtocolSpec.instSampleableTypeChallengeAppend (pSpec₁ := protocol) (pSpec₂ := protocol)

/-- Each component really rejects one of its two possible challenges. -/
def stage (expected : Bool) : Verifier emptySpec.{0, 0} Bool Bool protocol :=
  ⟨fun stmt tr => if tr 0 == expected then pure stmt else failure⟩

def guarded (expected : Bool) : (stage expected).GuardedForm :=
  ⟨fun _ tr => tr 0 == expected, fun stmt _ => stmt, fun _ _ => rfl⟩

instance (expected : Bool) : (stage expected).IsGuarded := (guarded expected).isGuarded

abbrev language : Set Bool := {true}

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl emptySpec.{0, 0} (StateT σ ProbComp))

/-- A successful component leaves the statement unchanged, so it cannot produce a valid
statement from an invalid one, for any prover or initial state. -/
theorem stage_soundness (expected : Bool) :
    (stage expected).soundness init impl language language 0 := by
  rw [(guarded expected).soundness_iff]
  intro Aux Out wit P stmt hstmt
  simp only [guarded, hstmt, and_false, prEvent_false, ENNReal.coe_zero, le_refl]

/-- The binary interface accepts a first-stage bound at the chosen initialization and a
second-stage bound uniform over deterministic initial states. -/
theorem binary : ((stage true).append (stage false)).soundness init impl language language 0 := by
  simpa using Verifier.append_soundness (stage true) (stage false)
    (stage_soundness init impl true) (fun s => stage_soundness (pure s) impl false)

/-- The plain-model interface needs only the two component bounds at the same initialization. -/
theorem plain : ((stage true).append (stage false)).soundness init impl language language 0 := by
  simpa using Verifier.append_soundness_of_empty (stage true) (stage false) id
    (stage_soundness init impl true) (stage_soundness init impl false)

/-- The finite-chain API accepts guarded forms as data and per-state component bounds. -/
theorem chain :
    (Verifier.seqCompose (fun _ : Fin 3 => Bool) (fun _ : Fin 2 => stage true)).soundness
      init impl language language 0 := by
  simpa using Verifier.seqCompose_soundness (fun _ : Fin 3 => language)
    (fun _ : Fin 2 => stage true) (fun _ => 0) (fun _ => guarded true)
    (fun _ s => stage_soundness (pure s) impl true) (init := init)

example : (stage true).run false (fun _ => false) = failure := rfl
example : (stage false).run false (fun _ => false) = pure false := rfl

/-- A directly defined two-round adversary, with both challenges in its private state. -/
def adversary : Prover emptySpec.{0, 0} Bool Unit Bool Unit (protocol ++ₚ protocol) where
  PrvState := fun _ => Bool × Bool
  input := fun _ => (false, false)
  sendMessage := fun ⟨i, hi⟩ _ => False.elim (by fin_cases i <;> cases hi)
  receiveChallenge := fun ⟨i, _⟩ st => pure fun c =>
    let c : Bool := cast (by fin_cases i <;> rfl) c
    if i.val = 0 then (c, st.2) else (st.1, c)
  output := fun st => pure (Bool.xor st.1 st.2, ())

/- Executing the restrictions retains the first challenge through the seam and the original
output step. This checks the computational definitions independently of the proof API. -/
run_cmd do
  let firstProver := adversary.appendPrefix (fun tr => tr 0)
  let before := firstProver.input (false, ())
  let after := (firstProver.receiveChallenge ⟨0, rfl⟩ before).runEmpty true
  let seam := (firstProver.output after).runEmpty
  let suffix := adversary.appendSuffix (Stmt₂ := Bool)
  let last := (suffix.receiveChallenge ⟨0, rfl⟩ (suffix.input seam)).runEmpty false
  let result := (suffix.output last).runEmpty
  unless seam.1 == true && result.1 == true do
    throwError "Prover restrictions did not retain the challenge at the seam"

/-- The recovered witness is the actual final output witness, independent of the auxiliary input. -/
def outputExtractor : Bool → Bool → protocol.FullTranscript → Option Bool :=
  fun _ w _ => some w

abbrev relation : Set (Bool × Bool) := {sw | sw.1 = sw.2}

/-- Accepted output witnesses are retained by the named extractor. -/
theorem stage_knowledgeSoundness (expected : Bool) :
    (stage expected).knowledgeSoundnessWith init impl relation relation
      (Extractor.Straightline.ofTranscriptAndOutput outputExtractor) 0 := by
  rw [(guarded expected).knowledgeSoundnessWith_iff]
  intro Aux stmt aux P
  rw [ENNReal.coe_zero, le_zero_iff]
  apply prEvent_eq_zero_of_forall_not
  rintro z ⟨_, hf, hr⟩
  exact hf z.1.2.2 rfl hr

/-- Named binary composition preserves the output-dependent extractor contract. -/
theorem binary_knowledgeWith :
    ((stage true).append (stage false)).knowledgeSoundnessWith init impl relation relation
      (Extractor.Straightline.ofTranscriptAndOutput
        ((guarded true).appendExtract outputExtractor outputExtractor)) 0 := by
  simpa using Verifier.append_knowledgeSoundnessWith (guarded true)
    outputExtractor outputExtractor (stage_knowledgeSoundness init impl true)
    (fun s => stage_knowledgeSoundness (pure s) impl false)

/-- Plain-model composition accepts both component certificates at the same initialization. -/
theorem plain_knowledge :
    ((stage true).append (stage false)).knowledgeSoundness init impl relation relation 0 := by
  simpa using Verifier.append_knowledgeSoundness_of_empty (stage true) (stage false) id
    ⟨outputExtractor, stage_knowledgeSoundness init impl true⟩
    ⟨outputExtractor, stage_knowledgeSoundness init impl false⟩

/-- The named finite-chain API exposes its executable folded extractor. -/
theorem chain_knowledgeWith :
    (Verifier.seqCompose (fun _ : Fin 3 => Bool)
      (fun _ : Fin 2 => stage true)).knowledgeSoundnessWith
      init impl relation relation
      (Extractor.Straightline.ofTranscriptAndOutput
        (Verifier.seqComposeExtract (fun _ : Fin 3 => Bool) (fun _ => Bool)
          (fun _ : Fin 2 => stage true) (fun _ => guarded true) (fun _ => outputExtractor))) 0 := by
  simpa using Verifier.seqCompose_knowledgeSoundnessWith (fun _ : Fin 3 => relation)
    (fun _ : Fin 2 => stage true) (fun _ => 0) (fun _ => guarded true)
    (fun _ => outputExtractor) (fun _ s => stage_knowledgeSoundness (pure s) impl true)
    (init := init)

/-- A rejecting suffix makes composition meaningful even when intermediate witnesses are empty. -/
def reject : Verifier emptySpec.{0, 0} Bool Bool protocol := ⟨fun _ _ => failure⟩

def rejectGuarded : reject.GuardedForm :=
  ⟨fun _ _ => false, fun x _ => x, fun _ _ => rfl⟩

/-- Regression against accidental `Nonempty` assumptions on the intermediate witness type. -/
theorem empty_intermediate :
    ((stage true).append reject).knowledgeSoundnessWith init impl relation relation
      (Extractor.Straightline.ofTranscriptAndOutput
        ((guarded true).appendExtract (fun _ (w : Empty) _ => nomatch w)
          (fun _ (_ : Bool) _ => (none : Option Empty)))) 0 := by
  have h₁ : (stage true).knowledgeSoundnessWith init impl relation (∅ : Set (Bool × Empty))
      (Extractor.Straightline.ofTranscriptAndOutput (fun _ (w : Empty) _ => nomatch w)) 0 := by
    rw [(guarded true).knowledgeSoundnessWith_iff]
    intro Aux stmt aux P
    simp only [Set.mem_empty_iff_false, and_false, prEvent_false, ENNReal.coe_zero, le_refl]
  have h₂ (s : σ) : reject.knowledgeSoundnessWith (pure s) impl
      (∅ : Set (Bool × Empty)) relation
      (Extractor.Straightline.ofTranscriptAndOutput (fun _ (_ : Bool) _ => (none : Option Empty)))
      0 := by
    rw [rejectGuarded.knowledgeSoundnessWith_iff]
    intro Aux stmt aux P
    simp only [rejectGuarded, Bool.false_eq_true, false_and, prEvent_false,
      ENNReal.coe_zero, le_refl]
  simpa using Verifier.append_knowledgeSoundnessWith (guarded true) _ _ h₁ h₂

/- Run the prefix adversary's output: the suffix's challenge affects extraction while the
prefix transcript remains available. Also execute binary and n-ary extractors and failure
propagation. -/
run_cmd do
  let extract := fun (y : Bool) (_ : Unit) (tr : protocol.FullTranscript) =>
    if tr 0 then none else some y
  let pref := adversary.appendPrefixExtract (fun tr => tr 0) extract (fun _ => false) false
  let st := (pref.receiveChallenge ⟨0, rfl⟩ (pref.input (false, ()))).runEmpty true
  unless (pref.output st).runEmpty == (true, true) do
    throwError "Suffix extraction did not use the retained prefix and fixed challenge"
  let failing := adversary.appendPrefixExtract (fun tr => tr 0) extract (fun _ => true) false
  let st' := (failing.receiveChallenge ⟨0, rfl⟩ (failing.input (false, ()))).runEmpty true
  unless (failing.output st').runEmpty == (true, false) do
    throwError "Suffix extraction fallback was not returned"
  let e := fun (x w : Bool) (tr : protocol.FullTranscript) =>
    if tr 0 == x then some (!w) else none
  let t : protocol.FullTranscript := fun _ => true
  let f : protocol.FullTranscript := fun _ => false
  unless (guarded true).appendExtract e e true false (t ++ₜ t) == some false do
    throwError "Binary extraction order is incorrect"
  unless (guarded true).appendExtract e e true false (t ++ₜ f) == none do
    throwError "Binary extraction did not propagate None"
  let chainExtract := Verifier.seqComposeExtract (fun _ : Fin 3 => Bool) (fun _ => Bool)
    (fun _ : Fin 2 => stage true) (fun _ => guarded true) (fun _ => e)
  let emptyTranscript : (!p[]).FullTranscript := fun i => Fin.elim0 i
  unless chainExtract true false (t ++ₜ (t ++ₜ emptyTranscript)) == some false do
    throwError "Folded extraction failed"
  unless chainExtract true false (t ++ₜ (f ++ₜ emptyTranscript)) == none do
    throwError "Folded extraction did not propagate None"
  let emptyExtract := Verifier.seqComposeExtract (oSpec := emptySpec.{0, 0})
    (fun _ : Fin 1 => Bool) (fun _ => Bool)
    (n := fun i => Fin.elim0 i) (pSpec := fun i => Fin.elim0 i)
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  unless emptyExtract false true emptyTranscript == some true do
    throwError "Empty folded extraction did not return its output witness"

#print axioms binary_knowledgeWith
#print axioms plain_knowledge
#print axioms chain_knowledgeWith
#print axioms empty_intermediate

#print axioms binary
#print axioms plain
#print axioms chain

end OrdinaryCompositionRegression
