/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Core.Security.StateRestoration
import ArkLibTest.Interaction.Core.Oracle

/-! A one-round state-restoration client: the prover sends an oracle in `Fin 8`, the verifier draws
a `Bool`. On challenge `true` the verifier reads the sent payload and returns it as the claim, with
the payload as its output oracle; on `false` it rejects. The input domain is `Nat`. -/

open PFunctor PFunctor.FreeM Interaction.Core Interaction.Oracle Interaction.TwoParty.Lens
  OracleComp OracleSpec
open Interaction.Core.StateRestoration
open Interaction.Core.OracleTests (emptyFamily)

namespace Interaction.Core.StateRestorationTests

/-- A sent `Fin 8` answers its single query with itself. -/
@[instance_reducible] def messageInterface : OracleInterface (Fin 8) where
  Query := Unit
  toOC := { spec := fun _ => Fin 8, impl := fun _ => do return (← read) }

/-- One round: a `Fin 8` oracle message, then a uniform `Bool` challenge. -/
@[implicit_reducible] def round : Round where
  Message := Fin 8
  Challenge := Bool
  interface := messageInterface
  sampleChallenge := inferInstance

@[implicit_reducible] def rounds : List Round := [round]

/-- The output is one `Fin 8` oracle. -/
@[instance_reducible] def outputFamily : OracleFamily PUnit (fun _ => Fin 8) :=
  singletonFamily messageInterface

/-- The input statement: a number with no input oracles. -/
abbrev Stmt : Type := Nat × (∀ i : PEmpty.{1}, (PEmpty.elim i : Type))

/-- The statement `z` with no input oracles. -/
def stmt (z : Nat) : Stmt := (z, fun i => PEmpty.elim i)

/-- Statements are equal when their numbers are; there are no input oracles. -/
instance : DecidableEq Stmt := fun a b =>
  decidable_of_iff (a.1 = b.1) ⟨fun h => Prod.ext h (funext fun i => i.elim), congrArg Prod.fst⟩

instance : DecidableEq (Key Stmt Unit rounds) :=
  inferInstanceAs (DecidableEq ((Stmt × Fin 8 × Unit) ⊕ (Fin 8 × Unit × Empty)))

/-- On challenge `true` read the payload and return it, on `false` reject. The output oracle is
the sent payload. -/
def verifier : OracleVerifier []ₒ (protocol rounds) Nat (Fin 8) emptyFamily outputFamily where
  decide _ p v := by
    rcases p with ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩
    exact if (show Bool from v.1.2.1) then
      liftM (([]ₒ + (sumFamily emptyFamily
        (pathFamily (protocol rounds) ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩)).spec).query (.inr ⟨.inr (.inl ⟨⟩), ()⟩))
    else failure
  outputMap _ p _ := by
    rcases p with ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩
    exact OracleMap.embedding (sumFamily emptyFamily (pathFamily (protocol rounds)
      ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩)) (fun _ => .inr (.inl ⟨⟩))

/-- The transcript with message `m` and challenge `c`. -/
def path (m : Fin 8) (c : Bool) : PathAlong oracleSig (protocol rounds) := ⟨m, ⟨c, ⟨⟩⟩⟩

/-- The adversary selects input 0, message 7, salt `()` and witness 6 without querying. -/
def messages : Messages Unit rounds := ⟨(7 : Fin 8), (), PUnit.unit⟩

def adversary : OracleComp (oracleSpec Stmt Unit rounds) (Stmt × Messages Unit rounds × Nat) :=
  pure ⟨stmt 0, messages, 6⟩

/-- The single first-round key of the adversary's selection. -/
def key : Key Stmt Unit rounds := Key.here (stmt 0) (7 : Fin 8) ()

-- Row 7 (StateRestoration L150, uniformVerifier_fresh): the game's challenge draw at a key's
-- receiver prefix is the uniform sample of that round's alphabet.
example : sampleAt oracleSig (uniformDraw rounds) (keySpine key) rfl = ($ᵗ Bool) :=
  sampleAt_keySpine key

-- Row 13 (StateRestoration L215, oracleObservation_true): on `true` the closed observation returns
-- the message as the claim and as its output oracle.
theorem oracleObservation_true (z : Nat) (m : Fin 8) :
    closedTerminalObservation verifier (stmt z) (path m true) = some (m, fun _ => m) := rfl

-- Row 14 (StateRestoration L219, oracleObservation_false): on `false` the closed observation is
-- `none`.
theorem oracleObservation_false (z : Nat) (m : Fin 8) :
    closedTerminalObservation verifier (stmt z) (path m false) = none := rfl

-- Row 17 (StateRestoration L258): the `false` branch returns no claim in the fixed `Option`
-- output, so no output relation can hold there.
example (z : Nat) (m : Fin 8) (rel : Fin 8 × (PUnit → Fin 8) → Prop) :
    ¬ ∃ claim, closedTerminalObservation verifier (stmt z) (path m false) = some claim ∧
      rel claim := by
  rw [oracleObservation_false]
  simp

-- Row 9 (StateRestoration L175, nativeResult_eq): against any answer table, the game completes
-- the adversary's selection with the table's challenge, and the verifier decides on that path.
theorem game_eval (table : Table Stmt Unit rounds) :
    evalWithAnswerFn (QueryImpl.ofFn table) (closedVerificationGame verifier adversary) =
      (stmt 0, path 7 (table key), closedTerminalObservation verifier (stmt 0) (path 7 (table key)),
        6) := by
  rw [closedVerificationGame_eq, evalWithAnswerFn_map, restoredExecution_eval]
  rfl

/-- The game's output against the constant table `c`, as plain numbers. -/
def gameResult (c : Bool) : Nat × Bool × Option (Nat × Nat) × Nat :=
  let table : Table Stmt Unit rounds
    | .inl _ => c
    | .inr (_, _, key) => key.elim
  let r := evalWithAnswerFn (QueryImpl.ofFn table) (closedVerificationGame verifier adversary)
  (r.1.1, r.2.1.2.1, r.2.2.1.map (fun claim => ((claim.1 : Nat), (claim.2 ⟨⟩ : Nat))), r.2.2.2)

-- Row 10 (StateRestoration L182): the game run on challenge `true`.
/-- info: (0, true, some (7, 7), 6) -/
#guard_msgs in
#eval gameResult true

-- Row 11 (StateRestoration L183): the game run on challenge `false`.
/-- info: (0, false, none, 6) -/
#guard_msgs in
#eval gameResult false

-- Row 18 (StateRestoration L264): the closed observation on the `true` branch.
/-- info: some (7, 7) -/
#guard_msgs in
#eval (closedTerminalObservation verifier (stmt 0) (path 7 true)).map
  (fun claim => ((claim.1 : Nat), (claim.2 ⟨⟩ : Nat)))

-- Row 19 (StateRestoration L266): the closed observation on the `false` branch.
/-- info: none -/
#guard_msgs in
#eval (closedTerminalObservation verifier (stmt 0) (path 7 false)).map
  (fun claim => ((claim.1 : Nat), (claim.2 ⟨⟩ : Nat)))

/-- The adversary's private coin selects one of two selections. -/
def coinAdversary (coin : Bool) :
    OracleComp (oracleSpec Stmt Unit rounds) (Stmt × Messages Unit rounds × Nat) :=
  if coin then adversary else pure ⟨stmt 0, ⟨(3 : Fin 8), (), PUnit.unit⟩, 2⟩

-- Row 21 (StateRestoration L291): coins that fail give the game probability 0.
example : Pr{let _result ← ((failure : OptionT ProbComp Bool) >>= fun coin => OptionT.lift
    ((simulateQ randomOracle (closedVerificationGame verifier (coinAdversary coin))).run' ∅))}[
      True] = 0 := by
  simp [failure_bind]

end Interaction.Core.StateRestorationTests
