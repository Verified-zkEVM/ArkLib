/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.LiftContext.Purity
import ArkLib.OracleReduction.Composition.Sequential.GuardedRoundByRound
import ArkLib.OracleReduction.Composition.Sequential.GuardedNary
import ArkLib.OracleReduction.Security.GuardedBridges

/-!
# Named guarded certificates through context lifting and composition

A one-challenge Boolean check lifts to a context carrying an additional Boolean. The outer
relation also requires its witness to equal that saved Boolean, which the inner check never sees.
A two-component family combines the lifted named certificate with a rejecting suffix. Its named
sequential certificate retains the component extractors and gives ordinary knowledge soundness
through the guarded bridge.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace GuardedLiftContextRegression

abbrev oracle : OracleSpec Empty := Empty →ₒ Unit
abbrev protocol : ProtocolSpec 1 := ⟨!v[.V_to_P], fun _ => Bool⟩

instance : ∀ i, SampleableType (protocol.Challenge i) :=
  fun _ => inferInstanceAs (SampleableType Bool)

def impl : QueryImpl oracle (StateT Unit ProbComp) := fun q => nomatch q

def inner : Verifier oracle Bool Bool protocol :=
  ⟨fun stmt _ => if stmt then pure stmt else failure⟩

def innerGuard : inner.GuardedForm :=
  ⟨fun stmt _ => stmt, fun stmt _ => stmt, fun _ _ => rfl⟩

abbrev innerRel : Set (Bool × Unit) := {p | p.1 = true}

def innerExtractor : Extractor.RoundByRound oracle Bool Unit Unit protocol (fun _ => Unit) where
  extractIn := fun _ w => w
  extractMid := fun _ _ _ w => w
  extractOut := fun _ _ w => w

def innerState : inner.KnowledgeStateFunction (pure ()) impl innerRel innerRel
    innerExtractor where
  toFun := fun _ stmt _ _ => stmt = true
  toFun_empty := fun _ _ h => h
  toFun_next := fun _ _ _ _ _ _ h => h
  toFun_full := fun _ _ _ hp => (innerGuard.check_and_of_prEvent_pos hp).1

theorem innerCertificate : inner.rbrKnowledgeSoundnessWith (pure ()) impl
    innerRel innerRel (fun _ => Unit) innerExtractor innerState (fun _ => 0) := by
  intro stmt i tr
  simp [innerState, innerExtractor]

abbrev outerRel : Set ((Bool × Bool) × Bool) :=
  {p | p.1.1 = true ∧ p.2 = p.1.2}

/-- Statement projection forgets the saved Boolean; output lifting restores it. -/
abbrev lens : Extractor.Lens (Bool × Bool) (Bool × Bool) Bool Bool Bool Bool Unit Unit where
  stmt := ⟨Prod.fst, fun stmt out => (out, stmt.2)⟩
  wit := ⟨fun _ => (), fun p _ => p.1.2⟩

instance : Extractor.Lens.IsKnowledgeSound outerRel innerRel outerRel innerRel
    (inner.compatStatement lens.stmt) (fun _ _ => True) ⟨lens.stmt, lens.wit⟩ where
  proj_knowledgeSound := fun _ _ _ _ h => Or.inl h.1
  lift_knowledgeSound := fun _ _ _ _ h => ⟨h, rfl⟩

abbrev lifted := inner.liftContext lens.stmt
abbrev liftedExtractor := innerExtractor.liftContext lens

def liftedState : lifted.KnowledgeStateFunction (pure ()) impl outerRel outerRel
    liftedExtractor :=
  innerState.liftContext lens inner outerRel innerRel outerRel innerRel innerExtractor

def liftedGuard : lifted.GuardedForm := innerGuard.liftContext lens.stmt inner

/-- The transported certificate names both the lifted extractor and lifted knowledge state. -/
theorem liftedCertificate : lifted.rbrKnowledgeSoundnessWith (pure ()) impl
    outerRel outerRel (fun _ => Bool × Unit) liftedExtractor liftedState (fun _ => 0) :=
  inner.liftContext_rbrKnowledgeSoundnessWith innerExtractor innerState innerCertificate

/-- The extra conjunct is present at both ends of the lifted component. -/
example : ((true, false), false) ∈ outerRel ∧ ((true, false), true) ∉ outerRel := by
  decide

example (stmt : Bool × Bool) (tr : protocol.FullTranscript) :
    liftedGuard.check stmt tr = innerGuard.check stmt.1 tr := rfl

example (stmt : Bool × Bool) (tr : protocol.FullTranscript) :
    (liftedGuard.out stmt tr).2 = stmt.2 := rfl

def rejecting : Verifier oracle (Bool × Bool) (Bool × Bool) protocol :=
  ⟨fun _ _ => failure⟩

def rejectingGuard : rejecting.GuardedForm :=
  ⟨fun _ _ => false, fun stmt _ => stmt, fun _ _ => rfl⟩

def rejectingExtractor : Extractor.RoundByRound oracle (Bool × Bool) Bool Bool protocol
    (fun _ => Bool) where
  extractIn := fun _ w => w
  extractMid := fun _ _ _ w => w
  extractOut := fun _ _ w => w

def rejectingState : rejecting.KnowledgeStateFunction (pure ()) impl outerRel outerRel
    rejectingExtractor where
  toFun := fun _ _ _ _ => False
  toFun_empty := fun _ _ h => h.elim
  toFun_next := fun _ _ _ _ _ _ h => h
  toFun_full := fun _ _ _ hp =>
    Bool.false_ne_true (rejectingGuard.check_and_of_prEvent_pos hp).1

theorem rejectingCertificate : rejecting.rbrKnowledgeSoundnessWith (pure ()) impl
    outerRel outerRel (fun _ => Bool) rejectingExtractor rejectingState (fun _ => 0) := by
  intro stmt i tr
  simp [rejectingState]

abbrev componentStmt : Fin 3 → Type := fun _ => Bool × Bool
abbrev componentWit : Fin 3 → Type := fun _ => Bool
abbrev componentRounds : Fin 2 → ℕ := fun _ => 1
abbrev componentProtocol : (i : Fin 2) → ProtocolSpec (componentRounds i) := fun _ => protocol
abbrev componentRel : (i : Fin 3) → Set (componentStmt i × componentWit i) :=
  fun _ => outerRel

abbrev componentVerifier : (i : Fin 2) →
    Verifier oracle (componentStmt i.castSucc) (componentStmt i.succ) (componentProtocol i) :=
  Fin.cases lifted (fun _ => rejecting)

def componentGuard : (i : Fin 2) → (componentVerifier i).GuardedForm :=
  Fin.cases liftedGuard (fun _ => rejectingGuard)

abbrev componentWitMid : (i : Fin 2) → Fin (componentRounds i + 1) → Type :=
  Fin.cases (fun _ => Bool × Unit) (fun _ _ => Bool)

def componentExtractor : (i : Fin 2) → Extractor.RoundByRound oracle
    (componentStmt i.castSucc) (componentWit i.castSucc) (componentWit i.succ)
    (componentProtocol i) (componentWitMid i) :=
  Fin.cases liftedExtractor (fun _ => rejectingExtractor)

def componentState : (i : Fin 2) → (componentVerifier i).KnowledgeStateFunction
    (pure ()) impl (componentRel i.castSucc) (componentRel i.succ) (componentExtractor i) :=
  Fin.cases liftedState (fun _ => rejectingState)

theorem componentCertificate (i : Fin 2) :
    (componentVerifier i).rbrKnowledgeSoundnessWith (pure ()) impl
      (componentRel i.castSucc) (componentRel i.succ) (componentWitMid i)
      (componentExtractor i) (componentState i) (fun _ => 0) := by
  refine Fin.cases liftedCertificate (fun j => ?_) i
  fin_cases j
  exact rejectingCertificate

abbrev composed := Verifier.seqCompose componentStmt componentVerifier
abbrev composedExtractor := Extractor.RoundByRound.seqCompose componentStmt componentWit
  componentVerifier componentGuard componentExtractor

def composedState : composed.KnowledgeStateFunction (pure ()) impl outerRel outerRel
    composedExtractor :=
  Verifier.KnowledgeStateFunction.seqComposeGuarded componentStmt componentWit componentRel
    componentVerifier componentGuard componentExtractor componentState

def composedGuard : composed.GuardedForm :=
  Verifier.GuardedForm.seqCompose componentStmt componentVerifier componentGuard

abbrev composedError (ε : (i : Fin 2) → (componentProtocol i).ChallengeIdx → ℝ≥0)
    (idx : (ProtocolSpec.seqCompose componentProtocol).ChallengeIdx) : ℝ≥0 :=
  let ij := seqComposeChallengeIdxToSigma idx
  ε ij.1 ij.2

/-- The named finite-chain certificate retains the lifted component's extractor and state. -/
theorem composedCertificate : composed.rbrKnowledgeSoundnessWith (pure ()) impl
    outerRel outerRel _ composedExtractor composedState (fun _ => 0) := by
  exact Verifier.seqCompose_rbrKnowledgeSoundnessWith_of_guarded
    componentStmt componentWit componentRel componentVerifier componentGuard
    componentExtractor componentState (fun _ _ => 0) componentCertificate

/-- The named composed extractor also supplies the ordinary knowledge certificate. -/
theorem composedKnowledge : composed.knowledgeSoundnessWith (pure ()) impl outerRel outerRel
    composedExtractor.foldExtractor 0 := by
  simpa using composedGuard.knowledgeSoundnessWith_of_rbrKnowledgeSoundnessWith
    composedState composedCertificate

/-- Component bounds are transported through the dependent challenge-index decoding. -/
theorem composedCertificateWith
    (ε : (i : Fin 2) → (componentProtocol i).ChallengeIdx → ℝ≥0) :
    composed.rbrKnowledgeSoundnessWith (pure ()) impl outerRel outerRel _
      composedExtractor composedState (composedError ε) := by
  apply Verifier.seqCompose_rbrKnowledgeSoundnessWith_of_guarded
    componentStmt componentWit componentRel componentVerifier componentGuard
    componentExtractor componentState ε
  intro i stmt j tr
  exact (componentCertificate i stmt j tr).trans (by simp)

theorem composedError_transport
    (ε : (i : Fin 2) → (componentProtocol i).ChallengeIdx → ℝ≥0)
    (i : Fin 2) (j : (componentProtocol i).ChallengeIdx) :
    composedError ε (sigmaChallengeIdxToSeqCompose i j) = ε i j :=
  ProtocolSpec.apply_seqComposeChallengeIdxToSigma ε _ i j (Fin.splitSum_embedSum i j.1)

abbrev taggedError : (i : Fin 2) → (componentProtocol i).ChallengeIdx → ℝ≥0 :=
  fun i _ => i.val + 1

example (j : protocol.ChallengeIdx) :
    composedError taggedError (sigmaChallengeIdxToSeqCompose 0 j) = 1 := by
  rw [composedError_transport]
  norm_num [taggedError]

example (j : protocol.ChallengeIdx) :
    composedError taggedError (sigmaChallengeIdxToSeqCompose 1 j) = 2 := by
  rw [composedError_transport]
  norm_num [taggedError]

example : composed.rbrKnowledgeSoundnessWith (pure ()) impl outerRel outerRel _
    composedExtractor composedState (composedError taggedError) :=
  composedCertificateWith taggedError

/-- The final component's rejecting guard remains in the finite composition. -/
theorem composedGuard_rejects (stmt : Bool × Bool)
    (tr : (ProtocolSpec.seqCompose componentProtocol).FullTranscript) :
    composedGuard.check stmt tr = false := by
  change (liftedGuard.check stmt tr.fst && (false && true)) = false
  simp

example (stmt : Bool × Bool)
    (tr : (ProtocolSpec.seqCompose componentProtocol).FullTranscript) :
    composed.verify stmt tr = failure := by
  rw [composedGuard.verify_eq]
  simp [composedGuard_rejects]

/-- Execute the complete backward fold, recovering the extra Boolean saved by the lift. -/
def runComposedExtractor (saved : Bool) : Bool :=
  let stmt := (true, saved)
  let tr := FullTranscript.seqCompose (pSpec := componentProtocol) (fun _ _ => false)
  composedExtractor.foldPrefix stmt (Fin.last _) tr (composedExtractor.extractOut stmt tr true)

/-- info: (true, false) -/
#guard_msgs in
#eval (runComposedExtractor true, runComposedExtractor false)

end GuardedLiftContextRegression
