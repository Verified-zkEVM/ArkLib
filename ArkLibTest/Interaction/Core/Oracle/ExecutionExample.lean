/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Core.Oracle.Routing

/-!
# Oracle execution with a passive verifier

The prover announces a `Bool`, sends a pair oracle, receives a sampled challenge, and sends a
second pair oracle. Only the first coordinate of each pair is observable. The passive decision
reads the input, both sent oracles and the challenge, after every prover effect. A stateful logger
distinguishes the exact effect schedule from reordered or duplicated execution.

The composition section checks verdicts, seam effects and rejection of appended oracle verifiers,
and the typing facts that keep payloads and later oracles out of a decision's reach.
-/

open PFunctor PFunctor.FreeM Interaction.Core Interaction.Oracle Interaction.TwoParty.Lens
  OracleComp

namespace Interaction.Core.ExecutionExampleTests

/-- Ambient operations are tagged; the logger records each tag and answers with it. -/
abbrev ambient : OracleSpec Nat := Nat →ₒ Nat

/-- One scalar input slot. -/
@[instance_reducible] def inputs : OracleFamily Unit (fun _ => Nat) :=
  ⟨fun _ => OracleInterface.instDefault⟩

/-- The input data: the single slot holds 7. -/
def seven : ∀ _ : Unit, Nat := fun _ => 7

/-- No output oracles. -/
@[instance_reducible] def noOutputs : OracleFamily PEmpty (fun i => i.elim) := ⟨fun i => i.elim⟩

/-- The output map into no oracles. -/
def noOutputMap {I : Type} {A : I → Type} (In : OracleFamily I A) : OracleMap In noOutputs where
  f _ i := i.elim
  impl q := q.1.elim
  law _ q := q.1.elim

/-- Only the first coordinate of a sent pair is observable. -/
@[reducible] def firstInterface : OracleInterface (Nat × Nat) where
  Query := Unit
  toOC.spec := fun _ => Nat
  toOC.impl _ := do return (← read).1

/-- The final part: one pair oracle, then the leaf. -/
@[instance_reducible] def opaqueProtocol : OracleProtocol :=
  .liftBind (.oracle (Nat × Nat) firstInterface) (fun _ => .pure ⟨⟩)

/-- A public `Bool`, a pair oracle, a challenge, and a final pair oracle. -/
@[instance_reducible] def protocol : OracleProtocol :=
  .liftBind (.message Bool) (fun _ =>
    .liftBind (.oracle (Nat × Nat) firstInterface) (fun _ =>
      .liftBind (.challenge Nat) (fun _ => opaqueProtocol)))

/-- The decision resources on a path of `protocol`. -/
abbrev resources (announced : Bool) :=
  sumFamily inputs (pathFamily protocol ⟨announced, ⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩⟩)

/-- The decision records 0 and 5, reads the first sent oracle, records 2, reads the input, records
3, and reads the final sent oracle. It accepts the latest answer plus the challenge if the
challenge is the input plus the first answer and the prover announced `true`, and decides 0 on
`false`. -/
def verifier : OracleVerifier ambient protocol Unit Nat inputs noOutputs where
  decide _ p v := by
    rcases p with ⟨announced, ⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩⟩
    exact OptionT.mk do
      let _ ← liftM ((ambient + (resources announced).spec).query (.inl 0))
      let _ ← liftM ((ambient + (resources announced).spec).query (.inl 5))
      let sent : Nat ← liftM ((ambient + (resources announced).spec).query
        (.inr ⟨.inr (.inl ⟨⟩), ()⟩))
      let _ ← liftM ((ambient + (resources announced).spec).query (.inl 2))
      let old : Nat ← liftM ((ambient + (resources announced).spec).query (.inr ⟨.inl (), ()⟩))
      let _ ← liftM ((ambient + (resources announced).spec).query (.inl 3))
      let latest : Nat ← liftM ((ambient + (resources announced).spec).query
        (.inr ⟨.inr (.inr (.inl ⟨⟩)), ()⟩))
      let challenge : Nat := v.val.2.2.1
      pure (if challenge = old + sent then
        some (if show Bool from announced then latest + challenge else 0) else none)
  outputMap _ p _ := noOutputMap (sumFamily inputs (pathFamily protocol p))

/-- The prover announces `true`, records 1, sends `(11, hidden)`, receives the challenge, records
4, sends `(challenge + 1, 99)`, and keeps `(777, hidden)` as private output. -/
def prover (hidden : Nat) : Prover oracleSig ambient protocol (fun _ => Nat × Nat) :=
  pure ⟨true, do
    let _ ← liftM (ambient.query 1)
    pure ⟨(11, hidden), pure fun (challenge : Nat) => do
      let _ ← liftM (ambient.query 4)
      pure ⟨(challenge + 1, 99), pure (777, hidden)⟩⟩⟩

/-- Record each ambient tag and answer it with itself; answer the only challenge with `draw`. -/
def logger (draw : Nat) : QueryImpl (ambient + challengeSpec oracleSig protocol)
    (StateM (List Nat))
  | .inl tag => do modify (· ++ [tag]); pure tag
  | .inr ⟨.inl _, h⟩ => nomatch h
  | .inr ⟨.inr ⟨_, .inl _⟩, h⟩ => nomatch h
  | .inr ⟨.inr ⟨_, .inr ⟨_, .inl _⟩⟩, _⟩ => pure (draw : Nat)
  | .inr ⟨.inr ⟨_, .inr ⟨_, .inr ⟨_, .inl _⟩⟩⟩, h⟩ => nomatch h
  | .inr ⟨.inr ⟨_, .inr ⟨_, .inr ⟨_, .inr ⟨_, n⟩⟩⟩⟩, _⟩ => n.elim

/-- The run under the logger, with the challenge drawn as 18. -/
def observed (hidden : Nat) :=
  (simulateQ (logger 18) (verifier.run () seven (prover hidden))).run []

/-- The verifier's view of the run's transcript, with the verdict. -/
def publicResult (hidden : Nat) : PathAlong viewSig protocol × Option Nat :=
  ((toView protocol (observed hidden).1.1).val, (observed hidden).1.2.2.map Prod.fst)

-- ExecutionExample 1, restated: the frozen verifier computes its challenge 7 + 11 by querying.
-- Challenges are sampled (Dec12), so the sampler draws 18; the decision checks it against the
-- queried input and first message and returns the final message 19 plus 18. For every hidden value.
example (hidden : Nat) : (observed hidden).1.2.2.map Prod.fst = some 37 := rfl

-- ExecutionExample 2, restated: the frozen schedule interleaves verifier effects between the
-- prover's. The verifier is passive (Dec2, Dec12): the prover's events 1 and 4, then the decision's
-- events 0, 5, 2 and 3, each once, for every hidden value.
example (hidden : Nat) : (observed hidden).2 = [1, 4, 0, 5, 2, 3] := rfl

-- ExecutionExample 3: the private output survives unchanged and differs from the verdict.
example (hidden : Nat) : (observed hidden).1.2.1 = (777, hidden) := rfl

-- ExecutionExample 4, restated: the verifier's view keeps the announced choice and the
-- challenge, and erases both payloads.
example (hidden : Nat) : (publicResult hidden).1 = ⟨true, ⟨⟩, (18 : Nat), ⟨⟩, ⟨⟩⟩ := rfl

-- ExecutionExample 5, restated: the same view with the verdict 37.
theorem publicResult_eq (hidden : Nat) :
    publicResult hidden = (⟨true, ⟨⟩, (18 : Nat), ⟨⟩, ⟨⟩⟩, some 37) := rfl

-- ExecutionExample 6, restated: the hidden coordinates do not change the view or the verdict.
example (hidden₁ hidden₂ : Nat) : publicResult hidden₁ = publicResult hidden₂ := by
  rw [publicResult_eq, publicResult_eq]

-- ExecutionExample 7, restated: the decision of an oracle node receives a view, whose oracle move
-- is `PUnit`, so a decision reading the payload's hidden coordinate does not elaborate.
example : True := by
  fail_if_success
    have _ : OracleVerifier ambient opaqueProtocol Unit Nat inputs noOutputs :=
      { decide := fun _ _ v => pure (show Nat × Nat from v.val.1).2
        outputMap := fun _ p _ => noOutputMap (sumFamily inputs (pathFamily opaqueProtocol p)) }
  trivial

-- ExecutionExample 8, restated: its positive counterpart reaches the payload only through the
-- query interface, which answers the observable coordinate.
example : OracleVerifier ambient opaqueProtocol Unit Nat inputs noOutputs where
  decide _ p _ := by
    rcases p with ⟨⟨⟩, ⟨⟩⟩
    exact liftM ((ambient + (sumFamily inputs (pathFamily opaqueProtocol ⟨⟨⟩, ⟨⟩⟩)).spec).query
      (.inr ⟨.inr (.inl ⟨⟩), ()⟩))
  outputMap _ p _ := noOutputMap (sumFamily inputs (pathFamily opaqueProtocol p))

-- ExecutionExample 10, restated: the frozen row erases the oracle executor to an ordinary paired
-- run through tree conversions, which are retired (Dec5). The oracle verifier's run of these
-- strategies is, by definition, the paired run against the sampler followed by the decision with
-- its resource queries answered from the input and this run's payloads.
example (hidden : Nat) :
    verifier.run () seven (prover hidden) = (do
      let ⟨tr, out, _⟩ ← TwoParty.Lens.run protocol
        ((prover hidden).simulate
          (fun q => liftM ((ambient + challengeSpec oracleSig protocol).query (.inl q))))
        (sampler oracleSig protocol (fun c =>
          liftM ((ambient + challengeSpec oracleSig protocol).query (.inr c))))
      let p := projectPathAlong oracleSig protocol tr
      let verdict ← simulateQ
        (QueryImpl.addLift
          ((fun q => liftM ((ambient + challengeSpec oracleSig protocol).query (.inl q))) :
            QueryImpl ambient (OracleComp (ambient + challengeSpec oracleSig protocol)))
          ((sumFamily inputs (pathFamily protocol p)).behaviorOfRealizations
            (sumData seven (payloads protocol tr))))
        (verifier.decide () p (toView protocol tr)).run
      pure ⟨tr, out, verdict.map fun t => (t,
        (verifier.outputMap () p (toView protocol tr)).f
          (sumData seven (payloads protocol tr)))⟩) :=
  rfl

run_cmd do
  for hidden in [0, 1000] do
    unless (observed hidden).2 == [1, 4, 0, 5, 2, 3] do
      throwError "the effect schedule is wrong: {(observed hidden).2}"
    unless (observed hidden).1.2.2.map Prod.fst == some 37 do
      throwError "the verdict is wrong"

end Interaction.Core.ExecutionExampleTests

namespace Interaction.Core.ExecutionExampleTests.Append

open Interaction.Core.ExecutionExampleTests

/-! ## Appended oracle verifiers

The prefix sends one pair oracle and samples a challenge; the suffix always sends a second pair
oracle. The challenge preserves the shape and changes the suffix verdict. -/

/-- One pair oracle, then a challenge. -/
@[instance_reducible] def firstProtocol : OracleProtocol :=
  .liftBind (.oracle (Nat × Nat) firstInterface) (fun _ =>
    .liftBind (.challenge Nat) (fun _ => .pure ⟨⟩))

abbrev combined : OracleProtocol := firstProtocol.append (fun _ => opaqueProtocol)

/-- The prefix resources on its only shape path. -/
abbrev prefixResources := sumFamily inputs (pathFamily firstProtocol ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩)

/-- The suffix resources on its only shape path. -/
abbrev suffixResources := sumFamily inputs (pathFamily opaqueProtocol ⟨⟨⟩, ⟨⟩⟩)

/-- The prefix decision records 11, reads its sent oracle, records 12, reads the input, and passes
the sent answer on, or rejects. Its output map forwards the input. -/
def firstVerifier (proceed : Bool) :
    OracleVerifier ambient firstProtocol Unit Nat inputs inputs where
  decide _ p _ := by
    rcases p with ⟨⟨⟩, ⟨⟩, ⟨⟩⟩
    exact OptionT.mk do
      let _ ← liftM ((ambient + prefixResources.spec).query (.inl 11))
      let sent : Nat ← liftM ((ambient + prefixResources.spec).query (.inr ⟨.inr (.inl ⟨⟩), ()⟩))
      let _ ← liftM ((ambient + prefixResources.spec).query (.inl 12))
      let _ ← liftM ((ambient + prefixResources.spec).query (.inr ⟨.inl (), ()⟩))
      pure (if proceed then some sent else none)
  outputMap _ p _ := (OracleMap.embedding (sumFamily inputs (pathFamily firstProtocol p))
    (fun _ => .inl ()) : OracleMap _ inputs)

/-- The suffix decision records 16 and 17, reads its sent oracle, and adds the prefix value. -/
def secondVerifier : OracleVerifier ambient opaqueProtocol Nat Nat inputs noOutputs where
  decide mid p _ := by
    rcases p with ⟨⟨⟩, ⟨⟩⟩
    exact do
      let _ ← liftM ((ambient + suffixResources.spec).query (.inl 16))
      let _ ← liftM ((ambient + suffixResources.spec).query (.inl 17))
      let latest : Nat ← liftM ((ambient + suffixResources.spec).query
        (.inr ⟨.inr (.inl ⟨⟩), ()⟩))
      pure (latest + mid)
  outputMap _ p _ := noOutputMap (sumFamily inputs (pathFamily opaqueProtocol p))

def compatible (proceed : Bool) :
    OracleVerifier.OutputCompatibility (firstVerifier proceed) (fun _ => secondVerifier) where
  outputMap stmt p v :=
    (secondVerifier.outputMap 0 (Path.split firstProtocol (fun _ => opaqueProtocol) p).2
      (View.split firstProtocol (fun _ => opaqueProtocol) p v).2).comp
      (OracleVerifier.suffixRoute (firstVerifier proceed) stmt p v)
  agrees _ _ _ _ _ _ := rfl

def verifier (proceed : Bool) :=
  (firstVerifier proceed).append (fun _ => secondVerifier) (compatible proceed)

/-- The prefix prover records 10, sends `(11, hidden)`, receives the challenge, records 14, and
passes on the challenge and `hidden` plus the answer. -/
def firstProver (hidden : Nat) : Prover oracleSig ambient firstProtocol (fun _ => Nat × Nat) := do
  let _ ← liftM (ambient.query 10)
  pure ⟨(11, hidden), pure fun (challenge : Nat) => do
    let response : Nat ← liftM (ambient.query 14)
    pure (challenge, hidden + response)⟩

/-- The suffix prover records 15 and sends `(challenge + 1, memory)`, keeping `memory`. -/
def secondProver (mid : Nat × Nat) : Prover oracleSig ambient opaqueProtocol (fun _ => Nat) := do
  let _ ← liftM (ambient.query 15)
  pure ⟨(mid.1 + 1, mid.2), pure mid.2⟩

def prover (hidden : Nat) : Prover oracleSig ambient combined (fun _ => Nat) :=
  Prover.append (firstProver hidden) (fun _ mid => pure (secondProver mid))

/-- Record each ambient tag and answer it with itself; answer the only challenge with `draw`. -/
def logger (draw : Nat) : QueryImpl (ambient + challengeSpec oracleSig combined)
    (StateM (List Nat))
  | .inl tag => do modify (· ++ [tag]); pure tag
  | .inr ⟨.inl _, h⟩ => nomatch h
  | .inr ⟨.inr ⟨_, .inl _⟩, _⟩ => pure (draw : Nat)
  | .inr ⟨.inr ⟨_, .inr ⟨_, .inl _⟩⟩, h⟩ => nomatch h
  | .inr ⟨.inr ⟨_, .inr ⟨_, .inr ⟨_, n⟩⟩⟩, _⟩ => n.elim

def observed (proceed : Bool) (draw hidden : Nat) :=
  (simulateQ (logger draw) ((verifier proceed).run () seven (prover hidden))).run []

/-- The shape path, the verdict, the private output and the history of one run. -/
def summary (proceed : Bool) (draw hidden : Nat) :
    Path combined × Option Nat × Nat × List Nat :=
  let z := observed proceed draw hidden
  (projectPathAlong oracleSig combined z.1.1, z.1.2.2.map Prod.fst, z.1.2.1, z.2)

-- ExecutionExample 19, restated: the frozen prefix ends with an `Option Nat` challenge that
-- selects the suffix shape. Here the prefix challenge preserves the shape, the suffix always sends
-- its oracle, and the suffix decision returns its latest answer plus the prefix value 11. With the
-- challenge drawn as 18 the verdict is `19 + 11 = 30`, for every hidden value; the history is the
-- prover's events, then the decisions', and the private output keeps the ambient answer 14 read
-- after the challenge.
example (hidden : Nat) :
    summary true 18 hidden =
      (⟨⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩⟩, some 30, hidden + 14, [10, 14, 15, 11, 12, 16, 17]) := by
  unfold summary observed verifier
  rw [OracleVerifier.run_append]
  rfl

-- Companion to ExecutionExample 19: for every challenge the shape path is the same, while the
-- verdict, carried by the prover's second message, changes with the challenge.
example (draw hidden : Nat) :
    summary true draw hidden =
      (⟨⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩⟩, some (draw + 1 + 11), hidden + 14, [10, 14, 15, 11, 12, 16, 17]) := by
  unfold summary observed verifier
  rw [OracleVerifier.run_append]
  rfl

-- ExecutionExample 22, restated: the frozen abort comes from an `Option` challenge. Here the
-- prefix decision rejects at the end (Dec2, Dec11, D5): the verdict is `none`, the suffix
-- interaction still runs (event 15), and the suffix decision's events 16 and 17 are skipped.
example (draw hidden : Nat) :
    summary false draw hidden = (⟨⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩⟩, none, hidden + 14, [10, 14, 15, 11, 12]) := by
  unfold summary observed verifier
  rw [OracleVerifier.run_append]
  rfl

-- ExecutionExample 9, restated: the frozen row checks that a verifier node before the second send
-- cannot query the second oracle. A decision's resources are fixed by its own shape path (D6): the
-- composed decision can name the second sent oracle, the prefix decision cannot.
example : OracleComp (ambient +
    (sumFamily inputs (pathFamily combined ⟨⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩⟩)).spec) Nat :=
  liftM ((ambient + (sumFamily inputs (pathFamily combined ⟨⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩⟩)).spec).query
    (.inr ⟨.inr (.inr (.inl ⟨⟩)), ()⟩))

example : True := by
  fail_if_success
    have _ : OracleComp (ambient + prefixResources.spec) Nat :=
      liftM ((ambient + prefixResources.spec).query (.inr ⟨.inr (.inr (.inl ⟨⟩)), ()⟩))
  trivial

/-! ### A completed prefix decision is not moved before the next prover send

Run separately, a completed prefix decision's effect precedes the next prover's. Appended, it is
an end decision and follows the suffix prover. The two orders differ. -/

abbrev done : OracleProtocol := .pure ⟨⟩

/-- The completed decision records 40 and forwards the input. -/
def completedVerifier : OracleVerifier ambient done Unit Unit inputs inputs where
  decide _ p _ := do
    let _ ← liftM ((ambient + (sumFamily inputs (pathFamily done p)).spec).query (.inl 40))
  outputMap _ p _ := (OracleMap.embedding (sumFamily inputs (pathFamily done p))
    (fun _ => .inl ()) : OracleMap _ inputs)

/-- A decision without effects. -/
def quietVerifier : OracleVerifier ambient opaqueProtocol Unit Unit inputs noOutputs where
  decide _ _ _ := pure ()
  outputMap _ p _ := noOutputMap (sumFamily inputs (pathFamily opaqueProtocol p))

/-- The next prover records 41 and sends `(11, 0)`. -/
def nextProver : Prover oracleSig ambient opaqueProtocol (fun _ => Unit) := do
  let _ ← liftM (ambient.query 41)
  pure ⟨(11, 0), pure ()⟩

def movedCompatible :
    OracleVerifier.OutputCompatibility completedVerifier (fun _ => quietVerifier) where
  outputMap stmt p v :=
    (quietVerifier.outputMap () (Path.split done (fun _ => opaqueProtocol) p).2
      (View.split done (fun _ => opaqueProtocol) p v).2).comp
      (OracleVerifier.suffixRoute completedVerifier stmt p v)
  agrees _ _ _ _ _ _ := rfl

/-- The completed decision appended before the next interaction. -/
def movedVerifier := completedVerifier.append (fun _ => quietVerifier) movedCompatible

theorem noChallengeDone : ChallengeNode oracleSig done → False := fun c => c.val.elim

theorem noChallengeOpaque : ChallengeNode oracleSig opaqueProtocol → False := by
  rintro ⟨_ | ⟨_, n⟩, h⟩
  · exact nomatch h
  · exact n.elim

/-- Interpret a run without challenges in the ambient oracle. -/
def ambientOnly {s : OracleProtocol} (none : ChallengeNode oracleSig s → False) {α : Type}
    (program : OracleComp (ambient + challengeSpec oracleSig s) α) : OracleComp ambient α :=
  simulateQ (fun
      | .inl q => liftM (ambient.query q)
      | .inr c => (none c).elim :
    QueryImpl (ambient + challengeSpec oracleSig s) (OracleComp ambient)) program

/-- The prover of the completed part has no effects. -/
def idleProver : Prover oracleSig ambient done (fun _ => Unit) :=
  (pure () : OracleComp ambient Unit)

/-- The completed decision's run, then the next interaction's run. -/
def completedThen : OracleComp ambient Unit := do
  let _ ← ambientOnly noChallengeDone
    (completedVerifier.run () seven idleProver)
  let _ ← ambientOnly noChallengeOpaque (quietVerifier.run () seven nextProver)

/-- The appended run of the same decisions and the next prover. -/
def movedThen : OracleComp ambient Unit := do
  let _ ← ambientOnly noChallengeOpaque (movedVerifier.run () seven nextProver)

def tagLogger : QueryImpl ambient (StateM (List Nat)) := fun tag => do
  modify (· ++ [tag])
  pure tag

-- ExecutionExample 25, restated: run in sequence, the completed decision's effect 40 precedes the
-- next prover's effect 41.
example : ((simulateQ tagLogger completedThen).run []).2 = [40, 41] := rfl

-- ExecutionExample 26, restated: appended, the completed decision is an end decision and its
-- effect follows the suffix prover's.
example : ((simulateQ tagLogger movedThen).run []).2 = [41, 40] := rfl

-- ExecutionExample 27: the two orders differ, so effects are not reordered silently.
example : ((simulateQ tagLogger completedThen).run []).2 ≠
    ((simulateQ tagLogger movedThen).run []).2 := by
  change [40, 41] ≠ [41, 40]
  decide

/-! ### A sampled first suffix move follows the prefix and precedes the prover response -/

/-- The prefix sends a public `Unit`. -/
@[instance_reducible] def firstPublic : OracleProtocol :=
  .liftBind (.message Unit) (fun _ => .pure ⟨⟩)

/-- The suffix samples one challenge. -/
@[instance_reducible] def secondPublic : OracleProtocol :=
  .liftBind (.challenge Nat) (fun _ => .pure ⟨⟩)

abbrev combinedPublic : OracleProtocol := firstPublic.append (fun _ => secondPublic)

/-- The prefix decision records 49 and decides 9. -/
def firstPublicVerifier : OracleVerifier ambient firstPublic Unit Nat inputs inputs where
  decide _ p _ := do
    let _ ← liftM ((ambient + (sumFamily inputs (pathFamily firstPublic p)).spec).query (.inl 49))
    pure 9
  outputMap _ p _ := (OracleMap.embedding (sumFamily inputs (pathFamily firstPublic p))
    (fun _ => .inl ()) : OracleMap _ inputs)

/-- The suffix decision reads answer 50, records 52, and accepts the sampled challenge if it is
that answer plus the prefix value. -/
def secondPublicVerifier : OracleVerifier ambient secondPublic Nat Nat inputs noOutputs where
  decide mid p v := OptionT.mk do
    let answer : Nat ← liftM ((ambient + (sumFamily inputs (pathFamily secondPublic p)).spec).query
      (.inl 50))
    let _ ← liftM ((ambient + (sumFamily inputs (pathFamily secondPublic p)).spec).query (.inl 52))
    let challenge : Nat := v.val.1
    pure (if challenge = answer + mid then some challenge else none)
  outputMap _ p _ := noOutputMap (sumFamily inputs (pathFamily secondPublic p))

def publicCompatible :
    OracleVerifier.OutputCompatibility firstPublicVerifier (fun _ => secondPublicVerifier) where
  outputMap stmt p v :=
    (secondPublicVerifier.outputMap 0 (Path.split firstPublic (fun _ => secondPublic) p).2
      (View.split firstPublic (fun _ => secondPublic) p v).2).comp
      (OracleVerifier.suffixRoute firstPublicVerifier stmt p v)
  agrees _ _ _ _ _ _ := rfl

def publicVerifier :=
  firstPublicVerifier.append (fun _ => secondPublicVerifier) publicCompatible

/-- The prefix prover records 48, sends `()` and keeps `hidden`. -/
def firstPublicProver (hidden : Nat) : Prover oracleSig ambient firstPublic (fun _ => Nat) := do
  let _ ← liftM (ambient.query 48)
  pure ⟨(), pure hidden⟩

/-- After the challenge the suffix prover records 51 and keeps `memory + challenge + response`. -/
def secondPublicProver (memory : Nat) : Prover oracleSig ambient secondPublic (fun _ => Nat) :=
  pure fun (challenge : Nat) => do
    let response : Nat ← liftM (ambient.query 51)
    pure (memory + challenge + response)

def publicProver (hidden : Nat) : Prover oracleSig ambient combinedPublic (fun _ => Nat) :=
  Prover.append (firstPublicProver hidden) (fun _ memory => pure (secondPublicProver memory))

/-- Record each ambient tag; record the challenge draw as its value. -/
def publicLogger (draw : Nat) : QueryImpl (ambient + challengeSpec oracleSig combinedPublic)
    (StateM (List Nat))
  | .inl tag => do modify (· ++ [tag]); pure tag
  | .inr ⟨.inl _, h⟩ => nomatch h
  | .inr ⟨.inr ⟨_, .inl _⟩, _⟩ => do modify (· ++ [draw]); pure (draw : Nat)
  | .inr ⟨.inr ⟨_, .inr ⟨_, n⟩⟩, _⟩ => n.elim

def observedPublic (hidden : Nat) :=
  (simulateQ (publicLogger 59) (publicVerifier.run () seven (publicProver hidden))).run []

-- ExecutionExample 28, restated: the frozen suffix verifier computes its challenge from an
-- ambient answer at the seam. The challenge is sampled (Dec12): the draw (logged as its value 59)
-- follows the prover's event 48 and precedes its response 51; the decisions' events 49, 50 and 52
-- follow, for every hidden value.
example (hidden : Nat) : (observedPublic hidden).2 = [48, 59, 51, 49, 50, 52] := by
  unfold observedPublic publicVerifier
  rw [OracleVerifier.run_append]
  rfl

-- ExecutionExample 29, restated: the prover's response sees the sampled challenge 59.
example (hidden : Nat) : (observedPublic hidden).1.2.1 = hidden + 59 + 51 := by
  unfold observedPublic publicVerifier
  rw [OracleVerifier.run_append]
  rfl

-- ExecutionExample 30, restated: the suffix decision reads the challenge from its view and checks
-- it against its answer 50 plus the prefix value 9.
example (hidden : Nat) : (observedPublic hidden).1.2.2.map Prod.fst = some 59 := by
  unfold observedPublic publicVerifier
  rw [OracleVerifier.run_append]
  rfl

end Interaction.Core.ExecutionExampleTests.Append

-- ExecutionExample 16 and 18: the oracle execution and composition laws stay axiom-clean.
run_cmd do
  for decl in [``Interaction.Core.OracleVerifier.run, ``Interaction.Core.Reduction.run,
      ``Interaction.Core.OracleVerifier.run_append, ``Interaction.Core.run_splitSampler,
      ``Interaction.Core.run_appendSampler] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected axiom {ax} in {decl}"
