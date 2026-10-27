/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Composition.Sequential.Append.SoundnessEmpty
import ArkLib.OracleReduction.Composition.Sequential.General

/-!
# Ordinary soundness composition API regressions

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

#print axioms binary
#print axioms plain
#print axioms chain

end OrdinaryCompositionRegression
