/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Core.Legacy.OracleSecurity

/-! Acceptance examples for the execution correspondence of embedded legacy oracle reductions:
the finalized run of the embedded oracle verifier against the embedded oracle prover, on the
oracle tree, against the legacy oracle reduction's run. The verifier reads the input oracle and a
message through its oracle interface. The examples cover an accepting and a rejecting run,
prover and verifier outputs that differ, and both legacy output-oracle representations. -/

open PFunctor PFunctor.FreeM OracleComp OracleSpec Interaction.Core Interaction.TwoParty.Lens
  ProtocolSpec

namespace Interaction.Core.Legacy.OracleExecutionTests

/-- A message, a challenge, then a second message. -/
def twoWay : ProtocolSpec 3 := ⟨!v[.P_to_V, .V_to_P, .P_to_V], !v[Nat, Bool, Nat]⟩

instance twoWayOracles : ∀ i, OracleInterface.{0, 0} (twoWay.Message i) :=
  fun _ => OracleInterface.instDefault

/-- One input oracle statement. -/
abbrev InStmt : Unit → Type := fun _ => Nat

instance : ∀ i, OracleInterface.{0, 0} (InStmt i) := fun _ => OracleInterface.instDefault

/-- One virtual output oracle. -/
abbrev OutSum : Unit → Type := fun _ => Nat

instance : ∀ i, OracleInterface.{0, 0} (OutSum i) := fun _ => OracleInterface.instDefault

/-- Two forwarded output oracles: the input oracle (`true`) and the first message (`false`). -/
abbrev OutCopy : Bool → Type := fun _ => Nat

instance : ∀ i, OracleInterface.{0, 0} (OutCopy i) := fun _ => OracleInterface.instDefault

instance : ∀ t, Inhabited (([]ₒ : OracleSpec PEmpty).Range t) := fun t => t.elim

/-- The legacy decision: read the input oracle and the last message, and accept with their sum
plus the statement when the challenge is `true`. -/
def decide (stmt : Nat) (ch : twoWay.Challenges) :
    OptionT (OracleComp ([]ₒ + ([InStmt]ₒ + [twoWay.Message]ₒ))) Nat := do
  let a ← OptionT.lift
    (query (spec := []ₒ + ([InStmt]ₒ + [twoWay.Message]ₒ)) (.inr (.inl ⟨(), ()⟩)))
  let b ← OptionT.lift
    (query (spec := []ₒ + ([InStmt]ₒ + [twoWay.Message]ₒ)) (.inr (.inr ⟨⟨2, rfl⟩, ()⟩)))
  bif (show Bool from ch ⟨1, rfl⟩) then pure (stmt + (show Nat from a) + (show Nat from b))
    else failure

/-- The output oracle is simulated: input oracle plus both messages. -/
def sumVerifier : _root_.OracleVerifier []ₒ Nat InStmt Nat OutSum twoWay where
  verify := decide
  outputOracle := .inr {
    materializeOutput _ o msgs _ :=
      (show Nat from o ()) + (show Nat from msgs ⟨0, rfl⟩) + (show Nat from msgs ⟨2, rfl⟩)
    simulateOutputQuery _ _ := do
      let a ← query (spec := []ₒ + ([InStmt]ₒ + [twoWay.Message]ₒ)) (.inr (.inl ⟨(), ()⟩))
      let b ← query (spec := []ₒ + ([InStmt]ₒ + [twoWay.Message]ₒ))
        (.inr (.inr ⟨⟨0, rfl⟩, ()⟩))
      let c ← query (spec := []ₒ + ([InStmt]ₒ + [twoWay.Message]ₒ))
        (.inr (.inr ⟨⟨2, rfl⟩, ()⟩))
      pure ((show Nat from a) + (show Nat from b) + (show Nat from c))
    simulateOutputQuery_eq _ _ _ _ := rfl }

/-- The output oracles are forwarded: the input oracle and the first message. -/
def copyVerifier : _root_.OracleVerifier []ₒ Nat InStmt Nat OutCopy twoWay where
  verify := decide
  outputOracle := .inl {
    embed := ⟨fun b => bif b then .inl () else .inr ⟨0, rfl⟩, by
      intro a b h; cases a <;> cases b <;> simp_all⟩
    hEq := fun b => by cases b <;> rfl
    outputInterface_heq := fun b => by cases b <;> rfl }

/-- A legacy oracle prover with a counter state. Its output statement, oracle data and witness
differ from the verifier's outputs. -/
def counterProver {ιₛₒ : Type} (OStmtOut : ιₛₒ → Type)
    [∀ i, OracleInterface.{0, 0} (OStmtOut i)] (out : Nat → ∀ i, OStmtOut i) :
    OracleProver []ₒ Nat InStmt Nat Nat OStmtOut Nat twoWay where
  PrvState _ := Nat
  input sw := sw.1.1 + (show Nat from sw.1.2 ()) + sw.2
  sendMessage
    | ⟨0, _⟩ => fun st => pure (st, st + 1)
    | ⟨1, h⟩ => nomatch h
    | ⟨2, _⟩ => fun st => pure (st * 10, st)
  receiveChallenge
    | ⟨0, h⟩ => nomatch h
    | ⟨1, _⟩ => fun st => pure (fun b => bif (show Bool from b) then st else 0)
    | ⟨2, h⟩ => nomatch h
  output st := pure ((st, out st), st + 100)

def sumReduction :
    _root_.OracleReduction []ₒ Nat InStmt Nat Nat OutSum Nat twoWay :=
  ⟨counterProver OutSum (fun st _ => st + 1), sumVerifier⟩

def copyReduction :
    _root_.OracleReduction []ₒ Nat InStmt Nat Nat OutCopy Nat twoWay :=
  ⟨counterProver OutCopy (fun st b => bif b then st else st + 1), copyVerifier⟩

theorem counter_pure {ιₛₒ : Type} (OStmtOut : ιₛₒ → Type)
    [∀ i, OracleInterface.{0, 0} (OStmtOut i)] (out : Nat → ∀ i, OStmtOut i) :
    PureChallengeSlots (counterProver OStmtOut out)
  | ⟨⟨0, _⟩, h⟩, _ => nomatch h
  | ⟨⟨1, _⟩, _⟩, _ => ⟨_, rfl⟩
  | ⟨⟨2, _⟩, h⟩, _ => nomatch h

/-- The input oracle holds `5`. -/
def five : ∀ i, InStmt i := fun _ => (5 : Nat)

/-! ### Program equality -/

/-- The counterpart-first oracle observation, finalized, is the legacy run. -/
example (stmt wit : Nat) (oStmt : ∀ i, InStmt i) :
    oracleFinalize <$> oracleObserveWith .counterpartFirst (embedOracleVerifier sumVerifier) stmt
        oStmt (embedOracleProver sumReduction.prover stmt oStmt wit) =
      (sumReduction.run stmt oStmt wit).run :=
  oracleFinalize_observeWith_counterpartFirst sumReduction stmt oStmt wit

/-- With pure challenge slots, the default schedule gives the same program. -/
example (stmt wit : Nat) (oStmt : ∀ i, InStmt i) :
    simulateQ (oracleChallengeReindex []ₒ twoWay)
        (oracleFinalize <$> (embedOracleVerifier copyVerifier).run stmt oStmt
          (embedOracleProver copyReduction.prover stmt oStmt wit)) =
      (copyReduction.run stmt oStmt wit).run :=
  simulateQ_oracleFinalize_run copyReduction (counter_pure _ _) stmt oStmt wit

/-- The distributional form, for any stateful shared oracle and challenge implementation. -/
example {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (chImpl : QueryImpl [twoWay.Challenge]ₒ ProbComp) (stmt wit : Nat) :
    experiment init impl (oracleChallengeImpl chImpl)
        (oracleFinalize <$> (embedOracleVerifier sumVerifier).run stmt five
          (embedOracleProver sumReduction.prover stmt five wit)) =ᵈ
      experiment init impl chImpl (sumReduction.run stmt five wit).run :=
  experiment_oracleFinalize_run_evalDistEq init impl chImpl sumReduction stmt five wit

/-! ### Concrete runs -/

/-- Constant legacy challenges. -/
def constChallenge (b : Bool) : (i : twoWay.ChallengeIdx) → twoWay.Challenge i
  | ⟨⟨0, _⟩, h⟩ => nomatch h
  | ⟨⟨1, _⟩, _⟩ => show Bool from b
  | ⟨⟨2, _⟩, h⟩ => nomatch h

/-- Answer legacy challenge queries with a constant, in `Id`. -/
def legacyAnswers (b : Bool) : QueryImpl ([]ₒ + [twoWay.Challenge]ₒ) Id :=
  QueryImpl.add (fun q => q.elim) (fun q => constChallenge b q.1)

/-- The oracle tree's challenge oracle, answered by the same constants. -/
def oracleAnswers (b : Bool) :
    QueryImpl ([]ₒ + challengeSpec oracleSig (oracleProtocol twoWay)) Id :=
  QueryImpl.add (fun q => q.elim) fun c =>
    (oracleChallengeMove 0 3 (Nat.zero_add 3) c).symm
      (constChallenge b (oracleChallengeRound 0 3 (Nat.zero_add 3) c))

/-- The outputs of a run with a virtual output oracle: the last message, the prover's output
statement, oracle data and witness, and the verifier's output statement and oracle data. -/
def sumOutputs (r : LegacyResult twoWay (Nat × ∀ i, OutSum i) Nat) :
    Option (Nat × Nat × Nat × Nat × Nat × Nat) :=
  r.map fun x => (show Nat from x.1.1 2, x.1.2.1.1, x.1.2.1.2 (), x.1.2.2, x.2.1, x.2.2 ())

/-- The same outputs with forwarded output oracles, read at both indices. -/
def copyOutputs (r : LegacyResult twoWay (Nat × ∀ i, OutCopy i) Nat) :
    Option (Nat × (Nat × Nat) × Nat × Nat × (Nat × Nat)) :=
  r.map fun x => (x.1.2.1.1, (x.1.2.1.2 true, x.1.2.1.2 false), x.1.2.2, x.2.1,
    (x.2.2 true, x.2.2 false))

/-- Statement `2`, input oracle `5`, witness `3`: the prover starts at `10`, sends `10`, then
`110`, and outputs statement `11`, data `12` and witness `111`. The verifier accepts with
`2 + 5 + 110` and the virtual output `5 + 10 + 110`. -/
example : sumOutputs (simulateQ (legacyAnswers true) (sumReduction.run 2 five 3).run) =
    some (110, 11, 12, 111, 117, 125) := by
  decide

example : sumOutputs (simulateQ (legacyAnswers false) (sumReduction.run 2 five 3).run) = none := by
  decide

/-- The oracle-tree run computes the same outputs, accepting and rejecting. -/
example : sumOutputs (simulateQ (oracleAnswers true)
    (oracleFinalize <$> (embedOracleVerifier sumVerifier).run 2 five
      (embedOracleProver sumReduction.prover 2 five 3))) =
    some (110, 11, 12, 111, 117, 125) := by
  decide

example : sumOutputs (simulateQ (oracleAnswers false)
    (oracleFinalize <$> (embedOracleVerifier sumVerifier).run 2 five
      (embedOracleProver sumReduction.prover 2 five 3))) = none := by
  decide

/-- Forwarded output oracles: the verifier's outputs are the input oracle `5` and the first
message `10`; the prover's are its own `(11, 12)`. -/
example : copyOutputs (simulateQ (oracleAnswers true)
    (oracleFinalize <$> (embedOracleVerifier copyVerifier).run 2 five
      (embedOracleProver copyReduction.prover 2 five 3))) =
    some (11, (11, 12), 111, 117, (5, 10)) := by
  decide

example : copyOutputs (simulateQ (oracleAnswers false)
    (oracleFinalize <$> (embedOracleVerifier copyVerifier).run 2 five
      (embedOracleProver copyReduction.prover 2 five 3))) = none := by
  decide

example : copyOutputs (simulateQ (legacyAnswers true) (copyReduction.run 2 five 3).run) =
    some (11, (11, 12), 111, 117, (5, 10)) := by
  decide

/-! ### Security transfers on the oracle tree -/

example {σ : Type} [∀ i, SampleableType (twoWay.Challenge i)] (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) (langIn : Set (Nat × ∀ i, InStmt i))
    (langOut : Set (Nat × ∀ i, OutSum i)) (ε : NNReal)
    (h : sumVerifier.soundness init impl langIn langOut ε)
    (Out : PathAlong oracleSig (oracleProtocol twoWay) → Type) :
    letI : MeasurableSpace (Observation oracleSig (oracleProtocol twoWay) Out
      (fun _ => Nat × ∀ i, OutSum i)) := ⊤
    Core.soundness ((embedOracleVerifier sumVerifier).classicalModel (Out := Out) init impl
        (oracleChallengeImpl ProtocolSpec.challengeQueryImpl))
      (langProblem langIn) (langProblem langOut)
      (fun obs => projectPathAlong oracleSig _ obs.1) (fun obs => obs.2.2) ε :=
  (oracleSoundness_iff init impl sumVerifier langIn langOut ε).mpr h Out

example [∀ i, SampleableType (twoWay.Challenge i)] (init : ProbComp Unit)
    (impl : QueryImpl []ₒ (StateT Unit ProbComp)) (langIn : Set (Nat × ∀ i, InStmt i))
    (langOut : Set (Nat × ∀ i, OutSum i)) (ε : twoWay.ChallengeIdx → NNReal)
    (h : sumVerifier.rbrSoundness init impl langIn langOut ε)
    (hinit : ∀ st, st ∈ support init) :
    (embedOracleVerifier sumVerifier).rbrSoundness impl (langProblem langIn)
      (langProblem langOut) (oracleChallengeImpl ProtocolSpec.challengeQueryImpl)
      (fun c => ε (oracleChallengeRound 0 3 (Nat.zero_add 3) c)) :=
  embedOracleVerifier_rbrSoundness init impl sumVerifier langIn langOut ε
    (StateTerminalCertificate.of_support_init hinit) h

end Interaction.Core.Legacy.OracleExecutionTests
