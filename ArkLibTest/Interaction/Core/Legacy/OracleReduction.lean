import ArkLib.Interaction.Core.Legacy.OracleReduction

/-! Acceptance examples for the embedded legacy oracle verifier: both legacy output-oracle
representations, an embedding and a simulation, become one interaction-layer oracle map whose
data map is the legacy materialization and whose queries agree with it. -/

open PFunctor PFunctor.FreeM OracleComp OracleSpec Interaction.Core Interaction.TwoParty.Lens
  ProtocolSpec

namespace Interaction.Core.Legacy.Tests

/-- An oracle message followed by a challenge, both natural numbers. -/
def msgChal : ProtocolSpec 2 := ⟨!v[.P_to_V, .V_to_P], fun _ => Nat⟩

instance msgChalOracles : ∀ i, OracleInterface.{0, 0} (msgChal.Message i) :=
  fun _ => OracleInterface.instDefault

/-- One input oracle statement. -/
abbrev InStmt : Unit → Type := fun _ => Nat

instance : ∀ i, OracleInterface.{0, 0} (InStmt i) := fun _ => OracleInterface.instDefault

/-- Two output oracles: a copy of the input oracle and a copy of the message. -/
abbrev OutCopy : Bool → Type := fun _ => Nat

instance : ∀ i, OracleInterface.{0, 0} (OutCopy i) := fun _ => OracleInterface.instDefault

/-- One virtual output oracle. -/
abbrev OutSum : Unit → Type := fun _ => Nat

instance : ∀ i, OracleInterface.{0, 0} (OutSum i) := fun _ => OracleInterface.instDefault

instance : ∀ t, Inhabited (([]ₒ : OracleSpec PEmpty).Range t) := fun t => t.elim

/-- A legacy verifier whose outputs embed the input oracle (`true`) and the message (`false`). -/
def copyVerifier : _root_.OracleVerifier []ₒ Unit InStmt Unit OutCopy msgChal where
  verify _ _ := pure ()
  outputOracle := .inl {
    embed := ⟨fun b => bif b then .inl () else .inr ⟨0, rfl⟩, by
      intro a b h; cases a <;> cases b <;> simp_all⟩
    hEq := fun b => by cases b <;> rfl
    outputInterface_heq := fun b => by cases b <;> rfl }

/-- A legacy verifier with one virtual output: input oracle plus message plus challenge. -/
def sumVerifier : _root_.OracleVerifier []ₒ Unit InStmt Unit OutSum msgChal where
  verify _ _ := pure ()
  outputOracle := .inr {
    materializeOutput ch o msgs _ :=
      (show Nat from o ()) + (show Nat from msgs ⟨0, rfl⟩) + (show Nat from ch ⟨1, rfl⟩)
    simulateOutputQuery ch _ := do
      let a ← query (spec := []ₒ + ([InStmt]ₒ + [msgChal.Message]ₒ)) (.inr (.inl ⟨(), ()⟩))
      let b ← query (spec := []ₒ + ([InStmt]ₒ + [msgChal.Message]ₒ))
        (.inr (.inr ⟨⟨0, rfl⟩, ()⟩))
      pure ((show Nat from a) + (show Nat from b) + (show Nat from ch ⟨1, rfl⟩))
    simulateOutputQuery_eq _ _ _ _ := rfl }

/-- A run: message `4`, challenge `9`. -/
def msgChalRun : PathAlong oracleSig (oracleProtocol msgChal) := ⟨(4 : Nat), ⟨(9 : Nat), ⟨⟩⟩⟩

/-- The shape path of the run. -/
abbrev msgChalPath : Path (oracleProtocol msgChal) :=
  projectPathAlong oracleSig _ msgChalRun

/-- Input oracle `5` beside the run's message. -/
def msgChalData : ∀ o, Sum.elim InStmt (OracleData (oracleProtocol msgChal) msgChalPath) o :=
  sumData (fun _ => (5 : Nat)) (payloads _ msgChalRun)

def nineChallenges : msgChal.Challenges := fun _ => (9 : Nat)

/-- The embedding case: the data map copies the input oracle and the message. -/
example : (legacyOutputMap copyVerifier nineChallenges msgChalPath).f msgChalData true =
    (5 : Nat) := rfl
example : (legacyOutputMap copyVerifier nineChallenges msgChalPath).f msgChalData false =
    (4 : Nat) := rfl

/-- The simulation case: the data map is the legacy materialization. -/
example : (legacyOutputMap sumVerifier nineChallenges msgChalPath).f msgChalData () =
    (18 : Nat) := rfl

/-- Queries agree with the materialized data in both cases. -/
example : simulateQ ((sumFamily (family InStmt) (pathFamily _ msgChalPath)).behaviorOfRealizations
      msgChalData) ((legacyOutputMap sumVerifier nineChallenges msgChalPath).impl ⟨(), ()⟩) =
    (18 : Nat) :=
  (legacyOutputMap sumVerifier nineChallenges msgChalPath).law msgChalData ⟨(), ()⟩
example : simulateQ ((sumFamily (family InStmt) (pathFamily _ msgChalPath)).behaviorOfRealizations
      msgChalData) ((legacyOutputMap copyVerifier nineChallenges msgChalPath).impl ⟨false, ()⟩) =
    (4 : Nat) :=
  (legacyOutputMap copyVerifier nineChallenges msgChalPath).law msgChalData ⟨false, ()⟩

/-- The embedded oracle verifier reads the challenges from its view. -/
example : viewChallenges (pSpec := msgChal) ⟨⟨⟩, ⟨(9 : Nat), ⟨⟩⟩⟩ ⟨1, rfl⟩ = (9 : Nat) := rfl

example (stmt : Unit) (view : View (oracleProtocol msgChal) msgChalPath) :
    (embedOracleVerifier sumVerifier).outputMap stmt msgChalPath view =
      legacyOutputMap sumVerifier (viewChallenges view.val) msgChalPath := rfl

end Interaction.Core.Legacy.Tests
