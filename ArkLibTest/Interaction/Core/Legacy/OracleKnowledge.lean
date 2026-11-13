/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Core.Legacy.OracleKnowledge

/-! Acceptance examples for the straight-line knowledge-soundness transfer of embedded legacy
oracle verifiers. The prover and the decision both query a shared oracle; the decision also reads
the input oracle and a message through its oracle interface. The extractor reads both
shared-oracle logs, so its witness records which queries each log holds. -/

open PFunctor PFunctor.FreeM OracleComp OracleSpec Interaction.Core Interaction.TwoParty.Lens
  ProtocolSpec

namespace Interaction.Core.Legacy.OracleKnowledgeTests

/-- A message, a challenge, then a second message. -/
def twoWay : ProtocolSpec 3 := ⟨!v[.P_to_V, .V_to_P, .P_to_V], !v[Nat, Bool, Nat]⟩

instance twoWayOracles : ∀ i, OracleInterface.{0, 0} (twoWay.Message i) :=
  fun _ => OracleInterface.instDefault

/-- One input oracle statement. -/
abbrev InStmt : Unit → Type := fun _ => Nat

instance : ∀ i, OracleInterface.{0, 0} (InStmt i) := fun _ => OracleInterface.instDefault

/-- Two forwarded output oracles: the input oracle (`true`) and the first message (`false`). -/
abbrev OutCopy : Bool → Type := fun _ => Nat

instance : ∀ i, OracleInterface.{0, 0} (OutCopy i) := fun _ => OracleInterface.instDefault

/-- A shared oracle answering natural numbers. -/
abbrev shared : OracleSpec Unit := Unit →ₒ Nat

instance : ∀ t, Inhabited (shared.Range t) := fun _ => ⟨(0 : Nat)⟩

/-- The legacy decision's oracles: the shared oracle, the input oracle and the messages. -/
abbrev DecisionSpec := shared + ([InStmt]ₒ + [twoWay.Message]ₒ)

/-- The legacy decision: query the shared oracle, the input oracle and the last message, and
accept with their sum plus the statement when the challenge is `true`. -/
def decide (stmt : Nat) (ch : twoWay.Challenges) : OptionT (OracleComp DecisionSpec) Nat := do
  let s ← OptionT.lift (query (spec := DecisionSpec) (.inl ()))
  let a ← OptionT.lift (query (spec := DecisionSpec) (.inr (.inl ⟨(), ()⟩)))
  let b ← OptionT.lift (query (spec := DecisionSpec) (.inr (.inr ⟨⟨2, rfl⟩, ()⟩)))
  bif (show Bool from ch ⟨1, rfl⟩)
    then pure (stmt + (show Nat from s) + (show Nat from a) + (show Nat from b))
    else failure

/-- The legacy oracle verifier; its output oracles forward the input oracle and the first
message. -/
def sharedVerifier : _root_.OracleVerifier shared Nat InStmt Nat OutCopy twoWay where
  verify := decide
  outputOracle := .inl {
    embed := ⟨fun b => bif b then .inl () else .inr ⟨0, rfl⟩, by
      intro a b h; cases a <;> cases b <;> simp_all⟩
    hEq := fun b => by cases b <;> rfl
    outputInterface_heq := fun b => by cases b <;> rfl }

/-- A legacy oracle prover that adds a shared-oracle answer to its first message. -/
def sharedProver : OracleProver shared Nat InStmt Nat Nat OutCopy Nat twoWay where
  PrvState _ := Nat
  input sw := sw.1.1 + (show Nat from sw.1.2 ()) + sw.2
  sendMessage
    | ⟨0, _⟩ => fun st => do
      let x ← query (spec := shared) ()
      pure (st + (show Nat from x), st + 1)
    | ⟨1, h⟩ => nomatch h
    | ⟨2, _⟩ => fun st => pure (st * 10, st)
  receiveChallenge
    | ⟨0, h⟩ => nomatch h
    | ⟨1, _⟩ => fun st => pure (fun b => bif (show Bool from b) then st else 0)
    | ⟨2, h⟩ => nomatch h
  output st := pure ((st, fun b => bif b then st else st + 1), st + 100)

/-- The sum of the shared-oracle answers in a log. -/
def logSum (log : QueryLog shared) : Nat := (log.map fun e => (show Nat from e.2)).sum

/-- A legacy straight-line extractor that reads both shared-oracle logs: the prover's answers,
`100` times the decision's answers, and `1000` times the number of decision entries. -/
def logExtractor :
    _root_.Extractor.Straightline shared (Nat × ∀ i, InStmt i) Nat Nat twoWay :=
  fun _ _ _ proveLog verifyLog =>
    pure (logSum proveLog + 100 * logSum verifyLog + 1000 * verifyLog.length)

/-- The input oracle holds `5`. -/
def five : ∀ i, InStmt i := fun _ => (5 : Nat)

/-! ### The transfers -/

example {σ : Type} [∀ i, SampleableType (twoWay.Challenge i)] (init : ProbComp σ)
    (impl : QueryImpl shared (StateT σ ProbComp))
    (relIn : Set ((Nat × ∀ i, InStmt i) × Nat)) (relOut : Set ((Nat × ∀ i, OutCopy i) × Nat))
    (ε : NNReal) :
    letI : MeasurableSpace (Observation oracleSig (oracleProtocol twoWay)
      (fun _ => (Nat × (∀ i, OutCopy i)) × Nat) (Nat × (∀ i, OutCopy i))) := ⊤
    letI : MeasurableSpace Nat := ⊤
    knowledgeSoundnessWith
        ((embedOracleVerifier sharedVerifier).classicalModel init impl
          (oracleChallengeImpl ProtocolSpec.challengeQueryImpl))
        (relProblem relIn) (relProblem relOut) (oracleKnowledgeJudgement relOut)
        ((embedOracleVerifier sharedVerifier).classicalStraightline (fun _ => Nat) init impl
          (oracleChallengeImpl ProtocolSpec.challengeQueryImpl) (fun _ o => o.2))
        (liftOracleExtractor logExtractor) ε ↔
      sharedVerifier.knowledgeSoundnessWith init impl relIn relOut logExtractor ε :=
  oracleKnowledgeSoundnessWith_iff init impl sharedVerifier relIn relOut logExtractor ε

example {σ : Type} [∀ i, SampleableType (twoWay.Challenge i)] (init : ProbComp σ)
    (impl : QueryImpl shared (StateT σ ProbComp))
    (relIn : Set ((Nat × ∀ i, InStmt i) × Nat)) (relOut : Set ((Nat × ∀ i, OutCopy i) × Nat))
    (ε : NNReal) :
    letI : MeasurableSpace (Observation oracleSig (oracleProtocol twoWay)
      (fun _ => (Nat × (∀ i, OutCopy i)) × Nat) (Nat × (∀ i, OutCopy i))) := ⊤
    letI : MeasurableSpace Nat := ⊤
    knowledgeSoundness
        ((embedOracleVerifier sharedVerifier).classicalModel init impl
          (oracleChallengeImpl ProtocolSpec.challengeQueryImpl))
        (relProblem relIn) (relProblem relOut) (oracleKnowledgeJudgement relOut)
        ((embedOracleVerifier sharedVerifier).classicalStraightline (fun _ => Nat) init impl
          (oracleChallengeImpl ProtocolSpec.challengeQueryImpl) (fun _ o => o.2)) ε ↔
      sharedVerifier.knowledgeSoundness init impl relIn relOut ε :=
  oracleKnowledgeSoundness_iff init impl sharedVerifier relIn relOut ε

/-- The lifted extractor reads the decoded transcript: lowering it gives back the legacy
extractor's results. -/
example : liftOracleExtractor (lowerOracleExtractor (liftOracleExtractor logExtractor)) =
    liftOracleExtractor (pSpec := twoWay) logExtractor :=
  liftOracleExtractor_lowerOracleExtractor _

/-! ### Concrete extraction games

The shared oracle answers `7`. Statement `2`, input oracle `5`, witness `3`: the prover starts
at `10`, queries the shared oracle, sends `17`, then `110`, and outputs statement `11` and
witness `111`. The decision queries the shared oracle, the input oracle and the last message,
and accepts with `2 + 7 + 5 + 110 = 124`; its output oracles are `5` and `17`. The extractor sees
one prover answer `7` and one decision entry `7`, the decision's input-oracle and message queries
removed: `7 + 700 + 1000 = 1707`. -/

/-- Constant legacy challenges. -/
def constChallenge (b : Bool) : (i : twoWay.ChallengeIdx) → twoWay.Challenge i
  | ⟨⟨0, _⟩, h⟩ => nomatch h
  | ⟨⟨1, _⟩, _⟩ => show Bool from b
  | ⟨⟨2, _⟩, h⟩ => nomatch h

/-- Shared answers `7` and constant challenges, on the oracle tree. -/
def oracleAnswers (b : Bool) :
    QueryImpl (shared + challengeSpec oracleSig (oracleProtocol twoWay)) Id :=
  QueryImpl.add (fun _ => (7 : Nat)) fun c =>
    (oracleChallengeMove 0 3 (Nat.zero_add 3) c).symm
      (constChallenge b (oracleChallengeRound 0 3 (Nat.zero_add 3) c))

/-- Shared answers `7` and constant challenges, for the legacy challenge oracle. -/
def legacyAnswers (b : Bool) : QueryImpl (shared + [twoWay.Challenge]ₒ) Id :=
  QueryImpl.add (fun _ => (7 : Nat)) (fun q => constChallenge b q.1)

/-- The verdict, the verifier's output oracles, and the extracted witness of an oracle
extraction game. -/
def gameOutputs (z : Observation oracleSig (oracleProtocol twoWay)
    (fun _ => (Nat × (∀ i, OutCopy i)) × Nat) (Nat × (∀ i, OutCopy i)) × Option Nat) :
    Option (Nat × Nat × Nat) × Option Nat :=
  (z.1.2.2.map fun t => (t.1, t.2 true, t.2 false), z.2)

/-- The same outputs, read off the legacy knowledge program. -/
def legacyOutputs
    (r : Option ((Nat × ∀ i, InStmt i) × Option Nat × (Nat × ∀ i, OutCopy i) × Nat)) :
    Option (Option Nat × Nat × Nat × Nat × Nat) :=
  r.map fun x => (x.2.1, x.2.2.1.1, x.2.2.1.2 true, x.2.2.1.2 false, x.2.2.2)

/-- The oracle extraction game: the extractor reads both shared-oracle logs. -/
example : gameOutputs (simulateQ (oracleAnswers true)
    ((embedOracleVerifier sharedVerifier).extractionGame (fun _ o => o.2)
      (liftOracleExtractor logExtractor) (2, five) (embedOracleProver sharedProver 2 five 3))) =
    (some (124, 5, 17), some 1707) := by
  decide

/-- A rejected run extracts nothing. -/
example : gameOutputs (simulateQ (oracleAnswers false)
    ((embedOracleVerifier sharedVerifier).extractionGame (fun _ o => o.2)
      (liftOracleExtractor logExtractor) (2, five) (embedOracleProver sharedProver 2 five 3))) =
    (none, none) := by
  decide

/-- The legacy knowledge program computes the same witness and outputs. -/
example : legacyOutputs (simulateQ (legacyAnswers true)
    (ambientLogged (sharedProver.run (2, five) 3) >>=
      knowledgeTail [twoWay.Challenge]ₒ sharedVerifier.toVerifier logExtractor (2, five))) =
    some (some 1707, 124, 5, 17, 111) := by
  decide

example : legacyOutputs (simulateQ (legacyAnswers false)
    (ambientLogged (sharedProver.run (2, five) 3) >>=
      knowledgeTail [twoWay.Challenge]ₒ sharedVerifier.toVerifier logExtractor (2, five))) =
    none := by
  decide

end Interaction.Core.Legacy.OracleKnowledgeTests
