/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Prover.Storage
import Mathlib.Data.Rat.Defs
import Lean.Compiler.IR

/-! # Actual retained states, transcripts, typed provider payloads and frontend inventories -/

open Interaction.Oracle OracleComp OracleSpec CompPoly Logup.Interaction
open Logup.Prover Logup.Prover.Honest.Accounting Logup.Prover.Storage
open Lean Elab Command
namespace LogupStorageTest

abbrev ambient : OracleSpec Unit := Unit →ₒ Rat
def handler : QueryImpl ambient Id := fun _ => 0
def groups : Vector (List (Fin 2)) 2 := #v[[0], [1]]
theorem group_bound : ∀ k, (groups.get k).length ≤ 1 := by decide

def prepared (n : Nat) (zero : Bool) : Prepared Rat 2 2 n :=
  { denominator := Vector.replicate 2 (Vector.replicate (2 ^ n) 2)
    weight := Vector.replicate 2 (Vector.replicate (2 ^ n) (if zero then 0 else 1))
    helper := Vector.replicate 2 (Vector.replicate (2 ^ n) (if zero then 0 else 3)) }
def state (n : Nat) (zero : Bool) : Logup.Prover.State Rat 2 2 n :=
  { toPrepared := prepared n zero
    kernel := Vector.ofFn fun i => (i.val + 1 : Nat)
    lambda := #v[1, 0] }
def choices (n code : Nat) : Vector (Option Rat) n := Vector.ofFn fun i =>
  match code / 3 ^ i.val % 3 with | 0 => none | 1 => some 0 | _ => some 5

def recorded (n code : Nat) (zero : Bool) := observeNative ambient handler n
  (nativeWith (callInterpreter (B := Rat)) call_erases (· ++ ·) ambient groups group_bound
    n (state n zero) []) (choices n code)
def ordinary (n code : Nat) (zero : Bool) := observeNative ambient handler n
  (nativeWith (unitInterpreter (B := Rat)) unit_erases (fun _ _ => ()) ambient groups group_bound
    n (state n zero) ()) (choices n code)

def sentLevels (n code : Nat) : List Nat :=
  (List.range n).takeWhile (fun i => (List.range i).all fun j => code / 3 ^ j % 3 != 0)

example {B E : Type} [CommRing B] [CommRing E] [Inv E] [DecidableEq E]
    {n T K ell : Nat} {ι : Type} (ambient : OracleSpec ι) (handler : QueryImpl ambient Id)
    (groups : Vector (List (Fin T)) K) (hgroups : ∀ k, (groups.get k).length ≤ ell)
    (sourceCells : Nat) (prepared : Prepared E T K n)
    (helper : Vector (CMlPolynomialEval E n) K) (state : Logup.Prover.State E T K n)
    (history : Vector (Option E) n) :
    let actual := observeNative ambient handler n
      (nativeWith (callInterpreter (B := B)) call_erases (· ++ ·) ambient groups hgroups
        n state []) history
    retainedScalarCells sourceCells prepared helper actual.2 actual.1 ≤
      sourceCells + (2 * T + 2 * K) * 2 ^ n + (2 * T + K + 1) * positiveRows n +
        n * K + n * (ell + 3) :=
  observed_retainedScalarCells_le ambient handler groups hgroups sourceCells prepared helper
    state history

namespace Prefix

def first : Sumcheck.Spec.StatementRound Int 2 0 := ⟨7, Fin.elim0⟩
def second : Sumcheck.Spec.StatementRound Int 2 1 := ⟨11, ![5]⟩
def third : Sumcheck.Spec.StatementRound Int 2 2 := ⟨13, ![5, 9]⟩
def actual : Fin 3 → Nat := ![statementCells first, statementCells second, statementCells third]
def allStates : (i : Fin 3) → Sumcheck.Spec.StatementRound Int 2 i :=
  fun i => ⟨(i.val : Int), fun j => (j.val + 5 : Nat)⟩

example : statementHistoryCells allStates = 6 := by decide
example : coordinateTailCells (#v[] : Vector Int 0) = 0 := rfl
example : coordinateTailCells (#v[7] : Vector Int 1) = 1 := rfl
example : coordinateTailCells (#v[7, 11] : Vector Int 2) = 3 := rfl
end Prefix

namespace EmptyPayload
open Logup.Lookup.Tuple
/-- Five registered buses, while all three semantic key rows use only bus one. -/
def schema : TaggedTuple.Schema Int 5 0 :=
  (TaggedTuple.Schema.mk? #v[0, 0, 0, 0, 0] #v[1, 2, 3, 4, 5]).get (by decide)
def layout : ProviderLayout 5 1 := (ProviderLayout.create? 5 1 #[1]).get (by decide)
def keys : Vector (CMlPolynomialEval schema.Key 0) 3 :=
  #v[#v[⟨1, #v[]⟩], #v[⟨1, #v[]⟩], #v[⟨1, #v[]⟩]]
def provider : PreparedProvider schema layout 0 2 :=
  PreparedProvider.prepare schema layout keys (by decide)
def indices : Vector (Fin 1) 2 := #v[0, 0]
def mu : Vector (CMlPolynomialEval Int 0) 1 := Logup.Lookup.multiplicities indices

theorem valid : Logup.Lookup.ValidIndices provider.keyData indices := by
  unfold Logup.Lookup.ValidIndices
  decide
example : witnessCells indices = 2 := rfl
example : histogramCells indices = 1 := rfl
example : providerPayloadCells provider = 0 := by decide
example : providerCoefficientCells provider = 3 := by decide
example : schemaTagCells schema = 5 ∧ schemaWidthCells schema = 5 := by decide
end EmptyPayload

namespace VariablePayload
open Logup.Lookup.Tuple

def schema : TaggedTuple.Schema Int 3 3 :=
  (TaggedTuple.Schema.mk? #v[0, 2, 1] #v[7, 11, 13]).get (by decide)
def layout : ProviderLayout 3 2 := (ProviderLayout.create? 3 2 #[0, 2]).get (by decide)
def keys : Vector (CMlPolynomialEval schema.Key 1) 3 :=
  #v[#v[⟨1, #v[17, 19]⟩, ⟨2, #v[23]⟩], #v[⟨0, #v[]⟩, ⟨0, #v[]⟩],
    #v[⟨2, #v[29]⟩, ⟨2, #v[31]⟩]]
def provider : PreparedProvider schema layout 1 1 :=
  PreparedProvider.prepare schema layout keys (by decide)

example : providerPayloadCells provider = 5 := by decide
example : providerCoefficientCells provider = 24 := by decide
end VariablePayload

/-- A generic external compiled caller for census functions, with no ring requirement. -/
def genericCensus {R : Type} {n T : Nat} (tables : Vector (CMlPolynomialEval R n) T)
    (point : Vector R n) : Nat × Nat := (familyCells tables, coordinateTailCells point)

run_cmd do
  let mut cases := 0
  for n in [0, 1, 2, 3] do
    unless positiveRows n == 2 * 2 ^ n - 2 do throwError "positive level geometry changed"
    for code in List.range (3 ^ n) do
      for zero in [false, true] do
        let got := recorded n code zero
        let unit := ordinary n code zero
        unless got.1 == unit.1 do throwError "instrumentation changed the actual Unit messages"
        let levels := sentLevels n code
        let expectedTables := (levels.map fun i => 7 * 2 ^ (n - i)).sum
        unless positiveStateTables got.2 == expectedTables &&
            positiveStateLambda got.2 == levels.length * 2 do
          throwError "actual positive snapshots, abort boundary or repeated lambda census changed"
        unless got.1.length == levels.length && messageCells got.1 ≤ n * 4 do
          throwError "actual transcript size or early abort census changed"
        if zero then
          unless messageCells got.1 == 0 do
            throwError "zero canonical messages retained padded zeros"
        unless retainedScalarCells 37 (prepared n zero) (prepared n zero).helper got.2 got.1 ≤
            37 + 8 * 2 ^ n + 7 * positiveRows n + n * 2 + n * 4 do
          throwError "explicit opaque source allowance was lost from retained scalar census"
        cases := cases + 1
  unless cases == 80 do throwError "optional history grid lost a case"
  unless (List.range 3).map prefixCells == [1, 3, 6] &&
      [Prefix.actual 0, Prefix.actual 0 + Prefix.actual 1,
        Prefix.actual 0 + Prefix.actual 1 + Prefix.actual 2] == [1, 3, 6] do
    throwError "triangular formula no longer matches actual target/prefix containers"
  unless [coordinateTailCells (#v[] : Vector Int 0), coordinateTailCells (#v[5] : Vector Int 1),
      coordinateTailCells (#v[5, 9] : Vector Int 2)] == [0, 1, 3] do
    throwError "coordinate tail inventory changed"
  unless (Vector.histogram EmptyPayload.indices).toArray == #[2] &&
      EmptyPayload.mu == #v[#v[2]] && familyCells EmptyPayload.mu == 1 &&
      signedWeightCells (fun slot => EmptyPayload.provider.coefficientTable slot 0)
        EmptyPayload.mu == 3 &&
      providerBusCells EmptyPayload.provider == 3 && layoutCells EmptyPayload.layout == 1 do
    throwError "duplicate witness, natural histogram, cast mu or width zero source roles changed"
  let cache : Vector (Vector (CMlPolynomialEval Int 1) 3) 2 :=
    Vector.replicate 2 (Vector.replicate 3 #v[0, 0])
  unless eagerCacheCells (n := 1) cache == 12 && providerBusCells VariablePayload.provider == 6 &&
      providerPayloadCells VariablePayload.provider == 5 &&
      providerCoefficientCells VariablePayload.provider == 24 do
    throwError "semantic payloads, padded coefficients or eager signed cache were conflated"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``tableCells_eq, ``familyCells_eq, ``preparedCells_eq, ``stateTableCells_eq,
      ``stateLambdaCells_eq, ``positiveRows_eq, ``prefixCells_le,
      ``observed_positive_state_cells_le, ``messageCells_le, ``observed_message_length_le,
      ``observed_message_cells_le, ``witnessCells_eq, ``histogramCells_eq, ``multiplicityCells_eq,
      ``getterCells_eq, ``signedWeightCells_eq, ``eagerCacheCells_eq, ``keyPayloadCells_le,
      ``providerPayloadCells_le, ``providerBusCells_eq, ``providerCoefficientCells_eq,
      ``schemaCells_eq, ``layoutCells_eq, ``statementCells_eq, ``statementHistoryCells_eq,
      ``coordinateTailCells_prefix, ``coordinateTailCells_le, ``observed_retainedScalarCells_le,
      ``EmptyPayload.valid] do
    unless (← collectAxioms name).all allowed.contains do
      throwError "unexpected logical storage axiom: {name}"
  for name in #[``genericCensus, ``recorded, ``ordinary, ``prepared, ``state, ``sentLevels,
      ``familyCells, ``providerPayloadCells, ``providerCoefficientCells, ``eagerCacheCells,
      ``retainedScalarCells, ``statementHistoryCells, ``coordinateTailCells] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "missing executable logical storage caller IR: {name}"
  logInfo "80 actual Unit/Call histories, collapsed messages and concrete input censuses passed"

end LogupStorageTest
