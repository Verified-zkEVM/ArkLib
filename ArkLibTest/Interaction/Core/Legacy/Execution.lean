/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Core.Legacy.Execution

/-! Acceptance examples for the execution correspondence: the finalized interaction-layer run
of an embedded legacy reduction against the legacy run, on protocols with every direction, zero
rounds and consecutive rounds of one owner; with an accepting and a rejecting run; and with
shared-oracle queries at the terminal boundary of the empty protocol. -/

open PFunctor PFunctor.FreeM OracleComp OracleSpec Interaction.Core Interaction.TwoParty.Lens
  ProtocolSpec

namespace Interaction.Core.Legacy.ExecutionTests

/-! ### A message, a challenge and a message -/

/-- A message, a challenge, then a second message. -/
def twoWay : ProtocolSpec 3 := ⟨!v[.P_to_V, .V_to_P, .P_to_V], !v[Nat, Bool, Nat]⟩

/-- A legacy prover with a counter state. Its outputs differ from the verifier's. -/
def counterProver : _root_.Prover []ₒ Nat Nat Nat Nat twoWay where
  PrvState _ := Nat
  input sw := sw.1 + sw.2
  sendMessage
    | ⟨0, _⟩ => fun st => pure (st, st + 1)
    | ⟨1, h⟩ => nomatch h
    | ⟨2, _⟩ => fun st => pure (st * 10, st)
  receiveChallenge
    | ⟨0, h⟩ => nomatch h
    | ⟨1, _⟩ => fun st => pure (fun b => bif (show Bool from b) then st else 0)
    | ⟨2, h⟩ => nomatch h
  output st := pure (st, st + 100)

/-- A legacy verifier that accepts when the challenge is `true` and adds the last message. -/
def lastIfTrue : _root_.Verifier []ₒ Nat Nat twoWay where
  verify stmt tr := bif (show Bool from tr 1) then pure (stmt + show Nat from tr 2) else failure

def counterReduction : _root_.Reduction []ₒ Nat Nat Nat Nat twoWay :=
  ⟨counterProver, lastIfTrue⟩

/-- Constant legacy challenges. -/
def constChallenge (b : Bool) : (i : twoWay.ChallengeIdx) → twoWay.Challenge i
  | ⟨⟨0, _⟩, h⟩ => nomatch h
  | ⟨⟨1, _⟩, _⟩ => show Bool from b
  | ⟨⟨2, _⟩, h⟩ => nomatch h

/-- Answer legacy challenge queries with a constant, in `Id`. -/
def legacyAnswers (b : Bool) : QueryImpl ([]ₒ + [twoWay.Challenge]ₒ) Id :=
  QueryImpl.add (fun q => q.elim) (fun q => constChallenge b q.1)

/-- The program equality in the counterpart-first schedule. -/
example (stmt wit : Nat) :
    finalize <$> observeWith .counterpartFirst (embedVerifier lastIfTrue) stmt
        (embedProver counterProver stmt wit) = (counterReduction.run stmt wit).run :=
  finalize_observeWith_counterpartFirst counterReduction stmt wit

/-- `receiveChallenge` has no effect, so the default schedule gives the same program. -/
theorem counter_pure : PureChallengeSlots counterProver
  | ⟨⟨0, _⟩, h⟩, _ => nomatch h
  | ⟨⟨1, _⟩, _⟩, _ => ⟨_, rfl⟩
  | ⟨⟨2, _⟩, h⟩, _ => nomatch h

example (stmt wit : Nat) :
    simulateQ (challengeReindex []ₒ twoWay)
        (finalize <$> (embedReduction counterReduction).observe stmt wit) =
      (counterReduction.run stmt wit).run :=
  simulateQ_finalize_observe counterReduction counter_pure stmt wit

/-- The outputs of a run: the last message, the prover's output and the verifier's output. -/
def outputs (r : LegacyResult twoWay Nat Nat) : Option (Nat × (Nat × Nat) × Nat) :=
  r.map fun x => (show Nat from x.1.1 2, x.1.2, x.2)

/-- An accepting run keeps the prover's output `(6, 106)` and the verifier's output `2 + 60`. -/
example : outputs (simulateQ (legacyAnswers true) (counterReduction.run 2 3).run) =
    some (60, (6, 106), 62) := by
  decide

/-- A rejecting run is the outcome `none`. -/
example : outputs (simulateQ (legacyAnswers false) (counterReduction.run 2 3).run) = none := by
  decide

/-- The interaction-layer challenge oracle answered by the same constants, through the
reindexing of challenge nodes. -/
def coreAnswers (b : Bool) :
    QueryImpl ([]ₒ + challengeSpec plainSig (protocol twoWay)) Id :=
  QueryImpl.add (fun q => q.elim) fun c =>
    (challengeMove 0 3 (Nat.zero_add 3) c).symm
      (constChallenge b (challengeRound 0 3 (Nat.zero_add 3) c))

/-- The interaction-layer execution under the default schedule computes the same outputs. -/
example : outputs (simulateQ (coreAnswers true)
    (finalize <$> (embedReduction counterReduction).observe 2 3)) = some (60, (6, 106), 62) := by
  decide

example : outputs (simulateQ (coreAnswers false)
    (finalize <$> (embedReduction counterReduction).observe 2 3)) = none := by
  decide

/-! ### The empty protocol with terminal queries -/

/-- One shared oracle from `Unit` to `Nat`. -/
abbrev counterSpec : OracleSpec Unit := Unit →ₒ Nat

/-- With no rounds, the prover's only action is `output`, which queries the shared oracle. -/
def terminalProver : _root_.Prover counterSpec Nat Nat Nat Nat (n := 0) !p[] where
  PrvState _ := Nat
  input sw := sw.1 + sw.2
  sendMessage i := i.1.elim0
  receiveChallenge i := i.1.elim0
  output st := do
    let x ← query (spec := counterSpec) ()
    pure (st + x, x)

/-- The verifier also queries the shared oracle, and rejects when it answers zero. -/
def terminalVerifier : _root_.Verifier counterSpec Nat Nat (n := 0) !p[] where
  verify stmt _ := do
    let x ← query (spec := counterSpec) ()
    if x = 0 then failure else pure (stmt * x)

def terminalReduction : _root_.Reduction counterSpec Nat Nat Nat Nat (n := 0) !p[] :=
  ⟨terminalProver, terminalVerifier⟩

/-- Answer the shared oracle with `a`. There are no challenges. -/
def terminalAnswers (a : Nat) :
    QueryImpl (counterSpec + challengeSpec plainSig (protocol (n := 0) !p[])) Id :=
  QueryImpl.add (fun _ => a) (fun c => c.val.elim)

def terminalOutputs (r : LegacyResult (n := 0) !p[] Nat Nat) : Option ((Nat × Nat) × Nat) :=
  r.map fun x => (x.1.2, x.2)

example : terminalOutputs (simulateQ (terminalAnswers 7)
    (finalize <$> (embedReduction terminalReduction).observe 2 3)) = some ((12, 7), 14) := by
  decide

example : terminalOutputs (simulateQ (terminalAnswers 0)
    (finalize <$> (embedReduction terminalReduction).observe 2 3)) = none := by
  decide

theorem terminal_pure : PureChallengeSlots terminalProver := fun i => i.1.elim0

example (stmt wit : Nat) :
    simulateQ (challengeReindex counterSpec (n := 0) !p[])
        (finalize <$> (embedReduction terminalReduction).observe stmt wit) =
      (terminalReduction.run stmt wit).run :=
  simulateQ_finalize_observe terminalReduction terminal_pure stmt wit

/-! ### Every direction, with consecutive rounds of one owner -/

/-- Two prover messages, two challenges, then one more message. -/
def mixed : ProtocolSpec 5 := ⟨!v[.P_to_V, .P_to_V, .V_to_P, .V_to_P, .P_to_V],
  !v[Nat, Bool, Bool, Nat, Nat]⟩

/-- A prover whose challenge slots query the shared oracle before the challenge arrives, so
only the distributional correspondence applies to it. -/
def mixedProver : _root_.Prover counterSpec Nat Unit Nat Nat mixed where
  PrvState _ := Nat
  input sw := sw.1
  sendMessage
    | ⟨0, _⟩ => fun st => pure (st, st)
    | ⟨1, _⟩ => fun st => pure (true, st + 1)
    | ⟨2, h⟩ => nomatch h
    | ⟨3, h⟩ => nomatch h
    | ⟨4, _⟩ => fun st => pure (st, st)
  receiveChallenge
    | ⟨0, h⟩ => nomatch h
    | ⟨1, h⟩ => nomatch h
    | ⟨2, _⟩ => fun st => do
      let x ← query (spec := counterSpec) ()
      pure fun b => bif (show Bool from b) then st + x else st
    | ⟨3, _⟩ => fun st => pure fun c => st + show Nat from c
    | ⟨4, h⟩ => nomatch h
  output st := pure (st, st)

def mixedVerifier : _root_.Verifier counterSpec Nat Nat mixed where
  verify _ tr := pure (show Nat from tr 4)

def mixedReduction : _root_.Reduction counterSpec Nat Unit Nat Nat mixed :=
  ⟨mixedProver, mixedVerifier⟩

example (stmt : Nat) :
    finalize <$> observeWith .counterpartFirst (embedVerifier mixedVerifier) stmt
        (embedProver mixedProver stmt ()) = (mixedReduction.run stmt ()).run :=
  finalize_observeWith_counterpartFirst mixedReduction stmt ()

/-- The distributional correspondence, for any stateful shared oracle and challenge
implementation, and the output measures in any measurable structure. -/
example {σ : Type} (init : ProbComp σ) (impl : QueryImpl counterSpec (StateT σ ProbComp))
    (chImpl : QueryImpl [mixed.Challenge]ₒ ProbComp) (stmt : Nat) :
    experiment init impl (plainChallengeImpl chImpl)
        (finalize <$> (embedReduction mixedReduction).observe stmt ()) =ᵈ
      experiment init impl chImpl (mixedReduction.run stmt ()).run :=
  experiment_finalize_observe_evalDistEq init impl chImpl mixedReduction stmt ()

example {σ : Type} [MeasurableSpace (LegacyResult mixed Nat Nat)] (init : ProbComp σ)
    (impl : QueryImpl counterSpec (StateT σ ProbComp))
    (chImpl : QueryImpl [mixed.Challenge]ₒ ProbComp) (stmt : Nat) :
    𝒟[experiment init impl (plainChallengeImpl chImpl)
        (finalize <$> (embedReduction mixedReduction).observe stmt ())] =
      𝒟[experiment init impl chImpl (mixedReduction.run stmt ()).run] :=
  evalDist_experiment_finalize_observe init impl chImpl mixedReduction stmt ()

end Interaction.Core.Legacy.ExecutionTests
