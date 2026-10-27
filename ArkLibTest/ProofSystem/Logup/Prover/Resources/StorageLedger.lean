/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import ArkLib.ProofSystem.Logup.Prover.Resources.StorageLedger
import Mathlib.Algebra.Field.ZMod
import Lean.Compiler.IR

/-! # Actual scalar/tuple control, seven-category offsets and complete named storage inventories -/

open Interaction.Oracle OracleComp OracleSpec CompPoly Logup.Interaction
open Logup.Prover Logup.Prover.Honest.Accounting Logup.Prover.Storage
open Logup.Prover.Storage.Ledger
open Lean Elab Command
namespace LogupStorageLedgerTest
abbrev F := ZMod 17
instance : Fact (Nat.Prime 17) := ⟨by decide⟩
abbrev ambient : OracleSpec Empty := fun i => nomatch i
def handler : QueryImpl ambient Id := fun i => nomatch i

def cfg (n : Fin 3) : Logup.Lookup.Config F n.val 1 2 1 :=
  (Logup.Lookup.Config.create? F n.val 1 2 1 17).get (by fin_cases n <;> decide)
def data (n : Nat) : Logup.Lookup.Data F n 1 2 := fun i =>
  i.elim (fun _ => Vector.ofFn fun r => (r.val % 2 : Nat))
    (fun p => if p.val = 0 then Vector.ofFn fun r => (r.val % 2 : Nat)
      else Vector.replicate (2 ^ n) 5)
def indices (n : Nat) : Vector (Fin (2 * 2 ^ n)) (1 * 2 ^ n) :=
  Vector.ofFn fun r => finProdFinEquiv (0, (⟨r.val, by omega⟩ : Fin (2 ^ n)))
def choices (n code : Nat) : Vector (Option F) n := Vector.ofFn fun i =>
  match code / 3 ^ i.val % 3 with | 0 => none | 1 => some 0 | _ => some 5

def joint (n : Nat) : (Fin n → F) × (Fin 3 → F) :=
  (fun i => (i.val + 3 : Nat), ![4, 6, 9])
def offsets : Allowances where
  originalSource := ⟨1, 2, 3, 4, 5, 6, 7⟩
  viewsAndGetters := ⟨11, 13, 17, 19, 23, 29, 31⟩
  embeddingsAndPrimitives := ⟨37, 41, 43, 47, 53, 59, 61⟩
  callerAndRaw := ⟨67, 71, 73, 79, 83, 89, 97⟩

def scalarCensus (n : Fin 3) (alpha : F) (code : Nat) (extra : Allowances := {}) : Inventory :=
  scalar (RingHom.id F) (cfg n) (data n.val) (indices n.val) ambient handler alpha
    (joint n.val) (choices n.val code) (Vector.replicate (2 ^ n.val) 7)
    (Vector.replicate n.val 2) extra

/-- Start at the ACTUAL scalar sender, then compare retained helper and coefficient messages with
its SAME weighted control observation; neither source binding nor the histogram is postulated. -/
def scalarControlMatches (n : Fin 3) (alpha : F) (code : Nat) : Bool := Id.run do
  let sent := simulateQ handler
    (Logup.Lookup.Honest.prover (RingHom.id F) (cfg n) (data n.val) (indices n.val) ambient)
  let mu : Vector (CMlPolynomialEval F n.val) 2 := sent.1
  let unit := observeProver ambient handler sent.2 alpha (joint n.val) (choices n.val code)
  let wd := Logup.Lookup.weightedData (data n.val) mu
  let recorded := observeProver ambient handler
    (proverWith callInterpreter call_erases (· ++ ·) [] (RingHom.id F)
      (cfg n).weighted wd ambient) alpha (joint n.val) (choices n.val code)
  return mu == Logup.Lookup.multiplicities (B := F) (indices n.val) &&
    unit.1 == recorded.1 && unit.2.1.map (fun q => q.val.val) ==
      recorded.2.1.map (fun q => q.val.val)

namespace Tuple
open Logup.Lookup.Tuple
/-- Five buses for only three columns, all keys at bus one with genuinely empty payload arrays. -/
def schema : TaggedTuple.Schema F 5 0 :=
  (TaggedTuple.Schema.mk? #v[0, 0, 0, 0, 0] #v[1, 2, 3, 4, 5]).get (by decide)
def layout : ProviderLayout 5 2 := ⟨#v[1, 1]⟩
def keys (n : Nat) : Vector (CMlPolynomialEval schema.Key n) 3 :=
  Vector.replicate 3 (Vector.replicate (2 ^ n) ⟨1, #v[]⟩)
def provider (n : Nat) : PreparedProvider schema layout n 1 :=
  PreparedProvider.prepare schema layout (keys n) (by
    intro p row
    fin_cases p <;> simp [keys, layout])
def repeated (n : Nat) (piece : Fin 2) : Vector (Fin (2 * 2 ^ n)) (1 * 2 ^ n) :=
  Vector.replicate (1 * 2 ^ n) (finProdFinEquiv (piece, ⟨0, Nat.two_pow_pos n⟩))

def census (n : Fin 3) (beta alpha : F) (code : Nat) (piece : Fin 2 := 0)
    (extra : Allowances := {}) : Inventory :=
  tuple (RingHom.id F) (cfg n) (provider n.val) (repeated n.val piece) ambient handler beta alpha
    (joint n.val) (choices n.val code) (Vector.replicate (2 ^ n.val) 7)
    (Vector.replicate n.val 2) extra

def controlMatches (n : Fin 3) (beta alpha : F) (code : Nat) (piece : Fin 2) : Bool := Id.run do
  let actual := Logup.Lookup.Tuple.Honest.Accounting.observeProver ambient handler (RingHom.id F)
    (Logup.Lookup.Tuple.Honest.prover (RingHom.id F) (cfg n) (provider n.val)
      (repeated n.val piece) ambient) beta alpha (joint n.val) (choices n.val code)
  let cache := simulateQ arithmeticAnswer
    (compressedTablesProgram (RingHom.id F) (provider n.val) beta actual.1)
  let recorded := observeProver ambient handler
    (proverWith callInterpreter call_erases (· ++ ·) [] (RingHom.id F)
      (cfg n).weighted (compressedData cache) ambient) alpha (joint n.val) (choices n.val code)
  return actual.1 == Logup.Lookup.multiplicities (B := F) (repeated n.val piece) &&
    actual.2.1 == recorded.1 && actual.2.2.1.map (fun q => q.val.val) ==
      recorded.2.1.map (fun q => q.val.val)

example : providerPayloadCells (provider 0) = 0 := by decide
example : providerCoefficientCells (provider 2) = 12 := by decide
example : providerBusCells (provider 2) = 12 := by decide
example : schemaTagCells schema = 5 := by decide
example : (tupleInput (provider 0) (repeated 0 0)
    (Vector.replicate 2 (Vector.replicate 3 #v[(0 : F)]))).arrayContainers = 37 := by decide
end Tuple

namespace VariablePayload
open Logup.Lookup.Tuple

def schema : TaggedTuple.Schema F 3 3 :=
  (TaggedTuple.Schema.mk? #v[0, 2, 1] #v[7, 11, 13]).get (by decide)
def layout : ProviderLayout 3 2 := ⟨#v[1, 2]⟩
def keys : Vector (CMlPolynomialEval schema.Key 0) 3 :=
  #v[#v[⟨0, #v[]⟩], #v[⟨1, #v[4, 9]⟩], #v[⟨2, #v[5]⟩]]
def provider : PreparedProvider schema layout 0 1 :=
  PreparedProvider.prepare schema layout keys (by decide)
def cache : Vector (Vector (CMlPolynomialEval F 0) 3) 2 := simulateQ arithmeticAnswer
  (compressedTablesProgram (RingHom.id F) provider 3
    (Logup.Lookup.multiplicities (B := F) (indices 0)))
example : providerPayloadCells provider = 3 := by decide
example : providerCoefficientCells provider = 12 := by decide
example : eagerCacheCells cache = 6 := eagerCacheCells_eq cache
example : Fits (tupleInput provider (indices 0) cache)
    { baseScalars := 3 + 3 * 3 + 3 * 4 + 3 * 2
      extensionScalars := 6
      naturalCounters := 5
      finiteIndices := 6
      arrayContainers := 46
      contextHandles := 8 } := tupleInput_le provider (indices 0) cache
end VariablePayload

namespace Collapsed
/-- No queries give actual zero weights/helpers/messages, but empty coefficient arrays still have
source/path container and list roles. -/
def cfg : Logup.Lookup.Config F 2 0 1 1 :=
  (Logup.Lookup.Config.create? F 2 0 1 1 17).get (by decide)
def values : Logup.Lookup.Data F 2 0 1 := fun _ => #v[0, 1, 3, 7]
def witness : Vector (Fin 4) 0 := #v[]
def sent := simulateQ handler (Logup.Lookup.Honest.prover (RingHom.id F) cfg values witness ambient)
def observed := observeProver ambient handler sent.2 2
  ((![3, 7] : Fin 2 → F), (![4] : Fin 1 → F)) #v[some 5, some 6]
end Collapsed

/-- Generic external consumer preserves every independently supplied workspace boundary. -/
def genericCensus {B E : Type} [CommRing B] [Field E] [DecidableEq E]
    {n M P ell : Nat} (f : B →+* E) (config : Logup.Lookup.Config B n M P ell)
    (values : Logup.Lookup.Data B n M P)
    (witness : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n))
    {ι : Type} (spec : OracleSpec ι) (impl : QueryImpl spec Id) (alpha : E)
    (challenges : (Fin n → E) × (Fin ((M + P) ⌈/⌉ ell) → E))
    (history : Vector (Option E) n) (backend : CMlPolynomialEval E n)
    (point : Vector E n) (extra : Allowances) :=
  scalar f config values witness spec impl alpha challenges history backend point extra

example {B E : Type} [CommRing B] [Field E] [DecidableEq E]
    {n M P ell : Nat} (f : B →+* E) (config : Logup.Lookup.Config B n M P ell)
    (values : Logup.Lookup.Data B n M P)
    (witness : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n))
    {ι : Type} (spec : OracleSpec ι) (impl : QueryImpl spec Id) (alpha : E)
    (challenges : (Fin n → E) × (Fin ((M + P) ⌈/⌉ ell) → E))
    (history : Vector (Option E) n) (backend : CMlPolynomialEval E n)
    (point : Vector E n) (extra : Allowances) :
    Fits (genericCensus f config values witness spec impl alpha challenges history backend point
      extra)
      (scalarBound n M P ell extra) :=
  scalar_le f config values witness spec impl alpha challenges history backend point extra

run_cmd do
  for n in List.finRange 3 do
    for code in List.range (3 ^ n.val) do
      for alpha in [(0 : F), 2, 5] do
        unless scalarControlMatches n alpha code do
          throwError "ordinary scalar sender/control messages diverged"
        let base := scalarCensus n alpha code
        let enlarged := scalarCensus n alpha code offsets
        unless enlarged == combine base (allowanceCells offsets) do
          throwError "one scalar opaque boundary was dropped or merged across categories"
        unless decide (Fits enlarged (scalarBound n.val 1 2 1 offsets)) do
          throwError "complete scalar category envelope failed"
        for beta in [(0 : F), 7] do
          for piece in List.finRange 2 do
            unless Tuple.controlMatches n beta alpha code piece do
              throwError "ordinary tuple beta cache/control lost retained histogram or helpers"
            let bare := Tuple.census n beta alpha code piece
            let full := Tuple.census n beta alpha code piece offsets
            unless full == combine bare (allowanceCells offsets) do
              throwError "one tuple opaque boundary was dropped"
            unless decide (Fits full (tupleBound 5 0 n.val 1 2 1 offsets)) do
              throwError "complete tuple category envelope failed"
  unless (scalarCensus 2 2 8).extensionScalars > (scalarCensus 2 2 0).extensionScalars do
    throwError "early abort must omit later private states/messages in the actual census"
  unless Logup.Lookup.multiplicities (B := F) (Tuple.repeated 2 0) !=
      Logup.Lookup.multiplicities (B := F) (Tuple.repeated 2 1) do
    throwError "duplicate witnesses should retain different actual multiplicity messages"
  unless VariablePayload.cache[0] == #v[#v[2], #v[5], #v[16]] &&
      VariablePayload.cache[1] == #v[#v[1], #v[16], #v[0]] do
    throwError "actual direct-BASE compression lost variable payload padding or signed weights"
  unless Collapsed.observed.2.1.map (fun q => q.val.val.size) == [0, 0] do
    throwError "actual zero-query default must retain two empty coefficient arrays"
  unless coordinateTailCells (#v[] : Vector F 0) == 0 &&
      coordinateTailCells (#v[7] : Vector F 1) == 1 &&
      coordinateTailCells (#v[7, 11] : Vector F 2) == 3 do
    throwError "actual coordinate-tail container geometry changed"
  unless withRawLog {} { extensionScalars := 1000000000 } ==
      { extensionScalars := 1000000000 } do
    throwError "raw Range payloads were silently replaced by a query-count bound"
  for n in List.finRange 3 do
    let snapshots : (i : Fin (n.val + 1)) → Sumcheck.Spec.StatementRound F n.val i :=
      fun i => ⟨7, fun j => (j.val + 5 : Nat)⟩
    unless statementHistoryCells snapshots == #[1, 3, 6][n.val]! do
      throwError "actual target-plus-prefix container geometry changed"
  logInfo "actual defaults, abort, duplicate histograms and seven-category bounds passed"

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``observed_retained_cells_le, ``observed_retained_geometric_le,
      ``whole_table_and_length, ``observed_retained_le, ``retained_extension_eq,
      ``retained_le_of_bounds, ``retainedEnvelope_le, ``publicFields_le, ``grouping_eq,
      ``scalarInput_eq, ``tupleInput_le, ``workspace_le, ``fold_workspace_le,
      ``scalarPreprocessing_eq, ``multiplicityPreprocessing_eq, ``providerConstruction_eq,
      ``compressionConstruction_eq, ``scalar_offset, ``scalar_le, ``tuple_le,
      ``scalarBound_fields, ``tupleBound_fields] do
    unless (← collectAxioms name).all allowed.contains do
      throwError "unexpected complete inventory axiom: {name}"
  for name in #[``scalar, ``tuple, ``complete, ``genericCensus, ``scalarCensus, ``Tuple.census,
      ``retained, ``workspace, ``scalarInput, ``tupleInput, ``scalarBound, ``tupleBound,
      ``scalarControlMatches, ``Tuple.controlMatches, ``allowanceCells, ``withRawLog] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "missing executable complete inventory caller IR: {name}"

end LogupStorageLedgerTest
