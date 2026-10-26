/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ProofSystem.Logup.Prover.StorageBuffers
public import ArkLib.ProofSystem.Logup.Lookup.ArithmeticProver
public import ArkLib.ProofSystem.Logup.Lookup.Tuple.ArithmeticProver

/-!
# Combined logical payload inventories

The categories distinguish carrier positions, counters, finite indices and container roles. They
are a declared census of the ordinary selected control, its original inputs, retained messages and
named construction workspaces. They do not describe bytes, allocator capacity, physical sharing,
compiler closures or stack, garbage collection, or a heap peak. Different roots may name the same
value and are deliberately counted separately.

Original source representations, opaque getters/views, embeddings and primitive implementations,
and additional caller/raw contexts have separate supplied allowances. Ordinary execution returns
a paired path and retains oracle messages; both payload roles are counted. Raw query logging is a
separate execution API and its arbitrary response payload requires an additional allowance.

The call observer below identifies the actual selected preparation, positive private states and
messages, including early abort, the skipped final fold and the omitted zero-round initialization.
Its Call instrumentation is a proof device and is not included in ordinary Unit storage.
-/

@[expose] public section

open Interaction.Oracle OracleComp OracleSpec CompPoly Logup.Interaction
open Logup.Prover.Honest.Accounting
namespace Logup.Prover.Storage.Ledger

/-- Separate logical positions and containers; none of these counters is a byte count. -/
structure Inventory where
  /-- Positions occupied by original or intermediate base-carrier values. -/
  baseScalars : Nat := 0
  /-- Positions occupied by challenge-carrier values or polynomial coefficients. -/
  extensionScalars : Nat := 0
  /-- Natural-valued histogram and schema entries, irrespective of bit size. -/
  naturalCounters : Nat := 0
  /-- Finite indices such as witness selections, bus identifiers and loop entries. -/
  finiteIndices : Nat := 0
  /-- Named arrays, including empty arrays and outer arrays of arrays. -/
  arrayContainers : Nat := 0
  /-- Named list nodes, separately from their scalar or index payloads. -/
  listCells : Nat := 0
  /-- Named source, continuation and context roots, excluding their opaque internals. -/
  contextHandles : Nat := 0
  deriving Repr, DecidableEq

/-- Combine two declared inventories componentwise, without an arithmetic instance. -/
def combine (a b : Inventory) : Inventory where
  baseScalars := a.baseScalars + b.baseScalars
  extensionScalars := a.extensionScalars + b.extensionScalars
  naturalCounters := a.naturalCounters + b.naturalCounters
  finiteIndices := a.finiteIndices + b.finiteIndices
  arrayContainers := a.arrayContainers + b.arrayContainers
  listCells := a.listCells + b.listCells
  contextHandles := a.contextHandles + b.contextHandles

/-- A separate bound on every category, without combining unlike scalar types. -/
def Fits (a b : Inventory) : Prop :=
  a.baseScalars ≤ b.baseScalars ∧ a.extensionScalars ≤ b.extensionScalars ∧
    a.naturalCounters ≤ b.naturalCounters ∧ a.finiteIndices ≤ b.finiteIndices ∧
    a.arrayContainers ≤ b.arrayContainers ∧ a.listCells ≤ b.listCells ∧
    a.contextHandles ≤ b.contextHandles

/-- Category comparisons are executable natural-number comparisons. -/
instance (a b : Inventory) : Decidable (Fits a b) := by
  unfold Fits
  infer_instance

/-- Every inventory bounds itself componentwise. -/
theorem Fits.refl (a : Inventory) : Fits a a :=
  ⟨le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩

/-- Two independent category bounds compose. -/
theorem Fits.combine_bound {a a' b b' : Inventory} (ha : Fits a a') (hb : Fits b b') :
    Fits (combine a b) (combine a' b') := by
  rcases ha with ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩
  rcases hb with ⟨g₁, g₂, g₃, g₄, g₅, g₆, g₇⟩
  exact ⟨Nat.add_le_add h₁ g₁, Nat.add_le_add h₂ g₂, Nat.add_le_add h₃ g₃,
    Nat.add_le_add h₄ g₄, Nat.add_le_add h₅ g₅, Nat.add_le_add h₆ g₆,
    Nat.add_le_add h₇ g₇⟩

/-- Independent representation and workspace boundaries that finite interfaces cannot determine. -/
structure Allowances where
  /-- Original source objects in addition to explicitly enumerated concrete input fields. -/
  originalSource : Inventory := {}
  /-- Extra representations or active workspaces of original views and table getters. -/
  viewsAndGetters : Inventory := {}
  /-- Extra workspace or representation of carrier embeddings and primitive implementations. -/
  embeddingsAndPrimitives : Inventory := {}
  /-- Caller-owned raw arrays, witness validation, and other unenumerated input contexts. -/
  callerAndRaw : Inventory := {}
  deriving Repr, DecidableEq

/-- Preserve all four unrelated opaque boundaries as explicit additive offsets. -/
def allowanceCells (a : Allowances) : Inventory :=
  combine (combine a.originalSource a.viewsAndGetters)
    (combine a.embeddingsAndPrimitives a.callerAndRaw)

/-- Add an optional raw query-log payload census. Query counts alone do not bound Range values. -/
def withRawLog (ordinary rawLog : Inventory) : Inventory := combine ordinary rawLog

/-- Componentwise bounds persist after the same supplied inventory is added. -/
theorem Fits.combine_right {a b : Inventory} (h : Fits a b) (offset : Inventory) :
    Fits (combine a offset) (combine b offset) := by
  rcases h with ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩
  exact ⟨Nat.add_le_add_right h₁ _, Nat.add_le_add_right h₂ _, Nat.add_le_add_right h₃ _,
    Nat.add_le_add_right h₄ _, Nat.add_le_add_right h₅ _, Nat.add_le_add_right h₆ _,
    Nat.add_le_add_right h₇ _⟩

/-- Every coordinate count is at most the Boolean table height. -/
theorem dimension_le_rows (n : Nat) : n ≤ 2 ^ n := Nat.le_of_lt Nat.lt_two_pow_self

/-- The exact retained private-table, batching and one-transcript envelope. -/
def retainedEnvelope (n T K ell : Nat) : Nat :=
  (2 * T + 2 * K) * 2 ^ n + (2 * T + K + 1) * positiveRows n +
    n * K + n * (ell + 3)

/-- Retaining every positive level and every coefficient transcript is geometric in the rows. -/
theorem retainedEnvelope_le (n T K ell : Nat) :
    retainedEnvelope n T K ell ≤ (6 * T + 5 * K + ell + 5) * 2 ^ n := by
  have hn := dimension_le_rows n
  have hp : positiveRows n ≤ 2 * 2 ^ n := by rw [positiveRows_eq]; omega
  calc
    _ ≤ (2 * T + 2 * K) * 2 ^ n + (2 * T + K + 1) * (2 * 2 ^ n) +
        2 ^ n * K + 2 ^ n * (ell + 3) := by
      unfold retainedEnvelope
      gcongr
    _ = _ := by ring

section Control
variable {B E : Type} [CommRing B] [Field E] [DecidableEq E]

/-- The full selected control, including preparation and the actual sent helper, obeys the
retained census. The observed annotation describes actual calls and is not a stored Unit log. -/
theorem observed_retained_cells_le {n T ell : Nat} (f : B →+* E) (cfg : Config n T ell)
    (data : Fin 2 × Fin T → CMlPolynomialEval B n) {ι : Type} (ambient : OracleSpec ι)
    (handler : QueryImpl ambient Id) (alpha : E)
    (joint : (Fin n → E) × (Fin (T ⌈/⌉ ell) → E)) (history : Vector (Option E) n)
    (sourceCells : Nat) :
    let prepared := simulateQ arithmeticAnswer
      (Call.prepare n f alpha cfg.groups data).program
    let observed := observeProver ambient handler
      (proverWith callInterpreter call_erases (· ++ ·) [] f cfg data ambient)
      alpha joint history
    retainedScalarCells sourceCells prepared observed.1 observed.2.2 observed.2.1 ≤
      sourceCells + (2 * T + 2 * (T ⌈/⌉ ell)) * 2 ^ n +
        (2 * T + (T ⌈/⌉ ell) + 1) * positiveRows n + n * (T ⌈/⌉ ell) + n * (ell + 3) := by
  rw [observeProver_with]
  cases n with
  | zero =>
    have hp := Logup.Prover.Storage.preparedCells_eq (E := E) (n := 0) (T := T)
      (K := T ⌈/⌉ ell)
      (simulateQ arithmeticAnswer (State.prepareProgram f alpha cfg.groups data))
    simp only [pow_zero, Nat.mul_one] at hp
    suffices sourceCells + (2 * T + T ⌈/⌉ ell) + T ⌈/⌉ ell ≤
        sourceCells + (2 * T + 2 * (T ⌈/⌉ ell)) by
      simpa [callInterpreter, startWith, observeNative, retainedScalarCells, Call.program,
        Call.Result, familyCells_eq, positiveStateTables, positiveStateLambda, callTableCells,
        callLambdaCells, messageCells, positiveRows, hp] using this
    omega
  | succ n =>
    let prepareCall : Call B E T (T ⌈/⌉ ell) := Call.prepare (n + 1) f alpha cfg.groups data
    let prepared := simulateQ arithmeticAnswer prepareCall.program
    let startCall : Call B E T (T ⌈/⌉ ell) := Call.start (n + 1) prepared joint.1 joint.2
    let state := simulateQ arithmeticAnswer startCall.program
    let before : List (Call B E T (T ⌈/⌉ ell)) := [prepareCall, startCall]
    have hs := observed_positive_state_cells_le (B := B) ambient handler cfg.groups
      cfg.length_group_le (n + 1) state history before
    have hm := observed_message_cells_le ambient handler (n + 1)
      (nativeWith (callInterpreter (B := B)) call_erases (· ++ ·) ambient cfg.groups
        cfg.length_group_le (n + 1) state before) history
    change retainedScalarCells sourceCells prepared prepared.helper
      (observeNative ambient handler (n + 1)
        (nativeWith (callInterpreter (B := B)) call_erases (· ++ ·) ambient cfg.groups
          cfg.length_group_le (n + 1) state before) history).2
      (observeNative ambient handler (n + 1)
        (nativeWith (callInterpreter (B := B)) call_erases (· ++ ·) ambient cfg.groups
          cfg.length_group_le (n + 1) state before) history).1 ≤ _
    dsimp only at hs hm
    have ht : positiveStateTables before = 0 := by
      simp [before, positiveStateTables, callTableCells, prepareCall, startCall]
    have hl : positiveStateLambda before = 0 := by
      simp [before, positiveStateLambda, callLambdaCells, prepareCall, startCall]
    simp only [ht, hl, Nat.zero_add] at hs
    have hp := Logup.Prover.Storage.preparedCells_eq (E := E) (n := n + 1) (T := T)
      (K := T ⌈/⌉ ell) prepared
    simp only [retainedScalarCells, familyCells_eq]
    have he : (2 * T + T ⌈/⌉ ell) * 2 ^ (n + 1) +
        (T ⌈/⌉ ell) * 2 ^ (n + 1) = (2 * T + 2 * (T ⌈/⌉ ell)) * 2 ^ (n + 1) := by ring
    omega

/-- Geometric retained bound for the same complete selected control, not another equal-output
implementation. The explicit source allowance remains an additive offset. -/
theorem observed_retained_geometric_le {n T ell : Nat} (f : B →+* E)
    (cfg : Config n T ell) (data : Fin 2 × Fin T → CMlPolynomialEval B n)
    {ι : Type} (ambient : OracleSpec ι) (handler : QueryImpl ambient Id) (alpha : E)
    (joint : (Fin n → E) × (Fin (T ⌈/⌉ ell) → E)) (history : Vector (Option E) n)
    (sourceCells : Nat) :
    let prepared := simulateQ arithmeticAnswer
      (Call.prepare n f alpha cfg.groups data).program
    let observed := observeProver ambient handler
      (proverWith callInterpreter call_erases (· ++ ·) [] f cfg data ambient)
      alpha joint history
    retainedScalarCells sourceCells prepared observed.1 observed.2.2 observed.2.1 ≤
      sourceCells + (6 * T + 5 * (T ⌈/⌉ ell) + ell + 5) * 2 ^ n := by
  have h := observed_retained_cells_le f cfg data ambient handler alpha joint history sourceCells
  have hgeom := retainedEnvelope_le n T (T ⌈/⌉ ell) ell
  dsimp only at h ⊢
  unfold retainedEnvelope at hgeom
  omega
/-- Actual selected message calls and canonical message count obey the same optional history,
including preparation/start prefixes whose state-table census is zero. -/
theorem whole_table_and_length {n T ell : Nat} (f : B →+* E) (cfg : Config n T ell)
    (data : Fin 2 × Fin T → CMlPolynomialEval B n) {ι : Type} (ambient : OracleSpec ι)
    (handler : QueryImpl ambient Id) (alpha : E)
    (joint : (Fin n → E) × (Fin (T ⌈/⌉ ell) → E)) (history : Vector (Option E) n) :
    let observed := observeProver ambient handler
      (proverWith callInterpreter call_erases (· ++ ·) [] f cfg data ambient)
      alpha joint history
    positiveStateTables observed.2.2 ≤ (2 * T + (T ⌈/⌉ ell) + 1) * positiveRows n ∧
      observed.2.1.length ≤ n := by
  rw [observeProver_with]
  cases n with
  | zero =>
    simp [callInterpreter, startWith, observeNative, positiveStateTables, callTableCells,
      positiveRows]
  | succ n =>
    let prepareCall : Call B E T (T ⌈/⌉ ell) := Call.prepare (n + 1) f alpha cfg.groups data
    let prepared := simulateQ arithmeticAnswer prepareCall.program
    let startCall : Call B E T (T ⌈/⌉ ell) := Call.start (n + 1) prepared joint.1 joint.2
    let state := simulateQ arithmeticAnswer startCall.program
    let before : List (Call B E T (T ⌈/⌉ ell)) := [prepareCall, startCall]
    have hs := observed_positive_state_cells_le (B := B) ambient handler cfg.groups
      cfg.length_group_le (n + 1) state history before
    have hm := observed_message_length_le ambient handler (n + 1)
      (nativeWith (callInterpreter (B := B)) call_erases (· ++ ·) ambient cfg.groups
        cfg.length_group_le (n + 1) state before) history
    change positiveStateTables (observeNative ambient handler (n + 1)
        (nativeWith (callInterpreter (B := B)) call_erases (· ++ ·) ambient cfg.groups
          cfg.length_group_le (n + 1) state before) history).2 ≤ _ ∧
      (observeNative ambient handler (n + 1)
        (nativeWith (callInterpreter (B := B)) call_erases (· ++ ·) ambient cfg.groups
          cfg.length_group_le (n + 1) state before) history).1.length ≤ _
    dsimp only at hs hm
    have ht : positiveStateTables before = 0 := by
      simp [before, positiveStateTables, callTableCells, prepareCall, startCall]
    simpa only [ht, Nat.zero_add] using And.intro hs.1 hm
end Control

section Private
variable {B E : Type} [CommRing B] [CommRing E] {n T K ell : Nat}

/-- Arrays in the three prepared outer families and all their inner tables, including empty
families. Container roles are separate from the scalar payload positions. -/
def preparedArrays (_prepared : Prepared E T K n) : Nat := 2 * T + K + 3

/-- Arrays at one actual positive state: prepared families, kernel and lambda. -/
def stateArrays (_state : State E T K n) : Nat := 2 * T + K + 5

/-- Actual message-call arguments identify private array containers; fold calls are not counted
again, and preparation and initialization have separate census roles. -/
def callArrays : Call B E T K → Nat
  | .message _ _ state => stateArrays state
  | _ => 0

/-- Array containers in the actual positive-level message-call snapshots. -/
def positiveStateArrays (calls : List (Call B E T K)) : Nat := (calls.map callArrays).sum

/-- Empty table families still have outer containers; every state also contains a kernel cell,
so five times its scalar table census bounds all its array roles. -/
theorem callArrays_le (call : Call B E T K) : callArrays call ≤ 5 * callTableCells call := by
  cases call with
  | message r groups state =>
    have hp : 1 ≤ 2 ^ (r + 1) := Nat.one_le_pow _ _ (by decide)
    have hm := Nat.mul_le_mul_left (2 * T + K + 1) hp
    simp only [callArrays, stateArrays, callTableCells, stateTableCells_eq, Nat.mul_one] at *
    omega
  | _ => simp [callArrays, callTableCells]

/-- The same actual table-state census bounds all retained state array containers. -/
theorem positiveStateArrays_le (calls : List (Call B E T K)) :
    positiveStateArrays calls ≤ 5 * positiveStateTables calls := by
  induction calls with
  | nil => simp [positiveStateArrays, positiveStateTables]
  | cons call calls ih =>
    have h := callArrays_le call
    simp only [positiveStateArrays, positiveStateTables, List.map_cons, List.sum_cons] at *
    omega

/-- Named private and source/path message roots. Prepared data is private; original helper and
canonical coefficient messages have separate source-handler and paired-path payload roles. Their
nested context nodes are not instrumentation lists and are counted as context handles. -/
def retained (prepared : Prepared E T K n)
    (helper : Vector (CMlPolynomialEval E n) K) (calls : List (Call B E T K))
    (messages : List (Sumcheck.Impl.Representation.Message E (ell + 2))) : Inventory where
  extensionScalars := retainedScalarCells 0 prepared helper calls messages +
    familyCells helper + messageCells messages
  arrayContainers := preparedArrays prepared + positiveStateArrays calls +
    2 * (K + 1) + 2 * messages.length
  contextHandles := 2 * messages.length

/-- Doubling the transcript roles is explicit and does not assume physical sharing. -/
theorem retained_extension_eq (prepared : Prepared E T K n)
    (helper : Vector (CMlPolynomialEval E n) K) (calls : List (Call B E T K))
    (messages : List (Sumcheck.Impl.Representation.Message E (ell + 2))) :
    (retained prepared helper calls messages).extensionScalars =
      preparedCells prepared + 2 * familyCells helper + positiveStateTables calls +
        positiveStateLambda calls + 2 * messageCells messages := by
  simp only [retained, retainedScalarCells]
  omega

/-- Separate source and paired-path payload roles add one full helper family and one canonical
transcript to the retained bound. No lower bound on nonzero message size is needed. -/
theorem retained_le_of_bounds (prepared : Prepared E T K n)
    (helper : Vector (CMlPolynomialEval E n) K) (calls : List (Call B E T K))
    (messages : List (Sumcheck.Impl.Representation.Message E (ell + 2)))
    (hcore : retainedScalarCells 0 prepared helper calls messages ≤ retainedEnvelope n T K ell)
    (htables : positiveStateTables calls ≤ (2 * T + K + 1) * positiveRows n)
    (hlen : messages.length ≤ n) :
    Fits (retained prepared helper calls messages)
      { extensionScalars := (6 * T + 6 * K + 2 * ell + 8) * 2 ^ n
        arrayContainers := 2 * T + 3 * K + 5 +
          10 * (2 * T + K + 1) * 2 ^ n + 2 * 2 ^ n
        contextHandles := 2 * 2 ^ n } := by
  have hn := dimension_le_rows n
  have hc := retainedEnvelope_le n T K ell
  have hm := messageCells_le messages
  have ha := positiveStateArrays_le calls
  have hp : positiveRows n ≤ 2 * 2 ^ n := by rw [positiveRows_eq]; omega
  have ht := Nat.mul_le_mul_left (2 * T + K + 1) hp
  have hmn := Nat.mul_le_mul_right (ell + 3) (hlen.trans hn)
  have hK : K * 2 ^ n + 2 ^ n * (ell + 3) = (K + ell + 3) * 2 ^ n := by ring
  have harr : 5 * ((2 * T + K + 1) * (2 * 2 ^ n)) =
      10 * (2 * T + K + 1) * 2 ^ n := by ring
  have hsum : (6 * T + 5 * K + ell + 5) * 2 ^ n + (K + ell + 3) * 2 ^ n =
      (6 * T + 6 * K + 2 * ell + 8) * 2 ^ n := by ring
  simp only [Fits, retained, preparedArrays, familyCells_eq]
  constructor
  · exact Nat.le_refl 0
  constructor
  · omega
  constructor
  · exact Nat.le_refl 0
  constructor
  · exact Nat.le_refl 0
  constructor
  · omega
  constructor
  · exact Nat.le_refl 0
  · omega
end Private

/-- Geometric envelope for private tables and separate source/path message roots. -/
def retainedBound (n T K ell : Nat) : Inventory where
  extensionScalars := (6 * T + 6 * K + 2 * ell + 8) * 2 ^ n
  arrayContainers := 2 * T + 3 * K + 5 + 10 * (2 * T + K + 1) * 2 ^ n + 2 * 2 ^ n
  contextHandles := 2 * 2 ^ n

/-- The complete selected prover supplies the premises of the componentwise retained bound.
The Unit implementation and this observation use the same shared control and selected programs. -/
theorem observed_retained_le {B E : Type} [CommRing B] [Field E] [DecidableEq E]
    {n T ell : Nat} (f : B →+* E) (cfg : Config n T ell)
    (data : Fin 2 × Fin T → CMlPolynomialEval B n) {ι : Type} (ambient : OracleSpec ι)
    (handler : QueryImpl ambient Id) (alpha : E)
    (joint : (Fin n → E) × (Fin (T ⌈/⌉ ell) → E)) (history : Vector (Option E) n) :
    let prepared := simulateQ arithmeticAnswer
      (State.prepareProgram f alpha cfg.groups data)
    let observed := observeProver ambient handler
      (proverWith callInterpreter call_erases (· ++ ·) [] f cfg data ambient)
      alpha joint history
    Fits (retained prepared observed.1 observed.2.2 observed.2.1)
      (retainedBound n T (T ⌈/⌉ ell) ell) := by
  have hc := observed_retained_cells_le f cfg data ambient handler alpha joint history 0
  have hs := whole_table_and_length f cfg data ambient handler alpha joint history
  dsimp only at hc hs ⊢
  apply retained_le_of_bounds
  · simpa only [Call.program, Call.Result, Nat.zero_add, retainedEnvelope] using hc
  · exact hs.1
  · exact hs.2

/-- Public scalar slots in source/path alpha, joint point and batching vector, native responses,
and every verifier target/challenge prefix. The actual point and batching arrays are read. -/
def publicFields {E : Type} {n K : Nat} (z : Vector E n) (lambda : Vector E K)
    (tuple : Bool) : Inventory where
  extensionScalars := 2 * (1 + z.toArray.size + lambda.toArray.size) + n +
    prefixCells n + (if tuple then 2 else 0)
  arrayContainers := 4 + 2 * (n + 1)
  contextHandles := 4 * (n + 1) + 8

/-- Statement prefixes and separately named public roots give an explicit geometric envelope. -/
theorem publicFields_le {E : Type} {n K : Nat} (z : Vector E n) (lambda : Vector E K)
    (tuple : Bool) :
    Fits (publicFields z lambda tuple)
      { extensionScalars := 7 * 2 ^ n + 2 * K + 4
        arrayContainers := 2 * 2 ^ n + 6
        contextHandles := 4 * 2 ^ n + 12 } := by
  have hn := dimension_le_rows n
  have hp := prefixCells_le n
  simp only [Fits, publicFields, Vector.size_toArray]
  split_ifs <;> omega

/-- Actual group list cells and the fixed configuration context, distinct from field payloads. -/
def grouping {T K : Nat} (groups : Vector (List (Fin T)) K) : Inventory where
  finiteIndices := (groups.toList.map List.length).sum
  arrayContainers := 1
  listCells := (groups.toList.map List.length).sum
  contextHandles := K + 1

/-- Exact ordered cover preserves one occurrence/index per input column, without requiring any
assumption about the scalar values stored at those columns. -/
theorem grouping_eq {n T ell : Nat} (cfg : Config n T ell) :
    grouping cfg.groups =
      { finiteIndices := T, arrayContainers := 1, listCells := T
        contextHandles := (T ⌈/⌉ ell) + 1 } := by
  have h := congrArg List.length cfg.flatten_groups
  simp only [List.length_flatten, List.length_finRange] at h
  simp only [grouping]
  rw [h]

/-- Geometric public source/path context envelope; private lambda copies are in retainedBound. -/
def publicBound (n K : Nat) : Inventory where
  extensionScalars := 7 * 2 ^ n + 2 * K + 4
  arrayContainers := 2 * 2 ^ n + 6
  contextHandles := 4 * 2 ^ n + 12

/-- Array-valued input positions and private/source/path multiplicity roots. Scalar weights use
getters, so no full signed BASE matrix is invented in the retained census. -/
def scalarInput {B : Type} [CommRing B] {n M P : Nat}
    (data : Logup.Lookup.Data B n M P)
    (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n)) : Inventory :=
  let mu := Logup.Lookup.multiplicities (B := B) (n := n) (P := P) indices
  { baseScalars := getterCells (fun i : Fin (M + P) => data (finSumFinEquiv.symm i)) +
      3 * familyCells mu
    naturalCounters := histogramCells indices
    finiteIndices := witnessCells indices
    arrayContainers := M + P + 1 + 3 * (P + 1) + 2
    contextHandles := 4 }

/-- Scalar inputs keep witness, histogram and the three multiplicity roles separate. -/
theorem scalarInput_eq {B : Type} [CommRing B] {n M P : Nat}
    (data : Logup.Lookup.Data B n M P)
    (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n)) :
    scalarInput data indices =
      { baseScalars := (M + 4 * P) * 2 ^ n
        naturalCounters := P * 2 ^ n
        finiteIndices := M * 2 ^ n
        arrayContainers := M + 4 * P + 6
        contextHandles := 4 } := by
  simp only [scalarInput, getterCells_eq, familyCells_eq, histogramCells_eq, witnessCells_eq]
  congr 1 <;> ring

section Tuple
open Logup.Lookup.Tuple
variable {B E : Type} [CommRing B] {b W n M P : Nat}
variable {schema : TaggedTuple.Schema B b W} {layout : ProviderLayout b P}

/-- Actual semantic keys, padded columns, schema and piece layout, witness and histogram, three
multiplicity roots, and both E cache matrices. Width-zero keys still retain their payload arrays. -/
def tupleInput (provider : PreparedProvider schema layout n M)
    (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n))
    (cache : Vector (Vector (CMlPolynomialEval E n) (M + P)) 2) : Inventory :=
  let mu := Logup.Lookup.multiplicities (B := B) (n := n) (P := P) indices
  { baseScalars := schemaTagCells schema + providerPayloadCells provider +
      providerCoefficientCells provider + 3 * familyCells mu
    extensionScalars := eagerCacheCells cache
    naturalCounters := schemaWidthCells schema + histogramCells indices
    finiteIndices := layoutCells layout + providerBusCells provider + witnessCells indices
    arrayContainers := 2 + 2 * (M + P) + (M + P) * 2 ^ n +
      (M + P) * (W + 1) + 5 + 3 * (P + 1) + 2 * (M + P) + 3
    contextHandles := 8 }

/-- Width-dependent typed payloads and maximum-width padded coefficients remain distinct.
Registered buses need not occur; their b-dependent schema terms are preserved explicitly. -/
theorem tupleInput_le (provider : PreparedProvider schema layout n M)
    (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n))
    (cache : Vector (Vector (CMlPolynomialEval E n) (M + P)) 2) :
    Fits (tupleInput provider indices cache)
      { baseScalars := b + (M + P) * 2 ^ n * W +
          (M + P) * (W + 1) * 2 ^ n + 3 * P * 2 ^ n
        extensionScalars := 2 * (M + P) * 2 ^ n
        naturalCounters := b + P * 2 ^ n
        finiteIndices := P + (M + P) * 2 ^ n + M * 2 ^ n
        arrayContainers := 13 + 4 * (M + P) + 3 * P +
          (M + P) * 2 ^ n + (M + P) * (W + 1)
        contextHandles := 8 } := by
  have hp := providerPayloadCells_le provider
  have hs := schemaCells_eq schema
  simp only [Fits, tupleInput, schemaTagCells, schemaWidthCells, Vector.size_toArray,
    providerCoefficientCells_eq, familyCells_eq, eagerCacheCells_eq, histogramCells_eq,
    layoutCells_eq, providerBusCells_eq, witnessCells_eq]
  constructor
  · nlinarith
  constructor
  · exact Nat.le_refl _
  constructor
  · exact Nat.le_refl _
  constructor
  · exact Nat.le_refl _
  constructor
  · omega
  constructor <;> exact Nat.le_refl _

/-- Separate BASE provider-construction roles for actual nested fixed-height coefficient builders.
Raw preparation inputs, ownership checks and opaque key/getter representations remain supplied. -/
def providerConstruction (provider : PreparedProvider schema layout n M) : Inventory where
  baseScalars := 3 * providerCoefficientCells provider +
    3 * (W + 1) * 2 ^ n + 3 * 2 ^ n
  arrayContainers := 3 * ((M + P) * (W + 1) + (M + P) + W + 3)
  finiteIndices := 3
  contextHandles := 4

/-- The actual three-level coefficient shape closes provider construction without assuming that
semantic key payloads have maximum width or that all registered buses occur. -/
theorem providerConstruction_eq (provider : PreparedProvider schema layout n M) :
    (providerConstruction provider).baseScalars =
      (3 * (M + P) * (W + 1) + 3 * (W + 1) + 3) * 2 ^ n := by
  rw [providerConstruction, providerCoefficientCells_eq]
  ring

/-- Actual eager cache output with old/new outer prefixes and one active row builder. Direct BASE
Horner uses a Nat cursor and has no per-row E coefficient buffer or W-sized index list. -/
def compressionConstruction (cache : Vector (Vector (CMlPolynomialEval E n) (M + P)) 2) :
    Inventory where
  extensionScalars := 3 * eagerCacheCells cache + 6 * 2 ^ n + 16
  arrayContainers := 6 * (M + P) + 12
  naturalCounters := 4
  finiteIndices := 4
  contextHandles := 4

/-- Both actual cache families and the active row builder give a width-independent E allowance;
W-dependent stored BASE coefficient columns are counted in the provider inventory instead. -/
theorem compressionConstruction_eq
    (cache : Vector (Vector (CMlPolynomialEval E n) (M + P)) 2) :
    (compressionConstruction cache).extensionScalars = (6 * (M + P) + 6) * 2 ^ n + 16 := by
  rw [compressionConstruction, eagerCacheCells_eq]
  ring
end Tuple

section Workspace
variable {B E : Type} {n T K ell : Nat}

/-- The named active workspaces, conservatively added across phases. Preparation/fold builders,
fast private initialization and the original dense source backend have distinct roles. The dense
input is an actual active mapped E table; generic views supply additional workspace separately. -/
def workspace [CommRing E] (prepared : Prepared E T K n) (z : Vector E n) (lambda : Vector E K)
    (backend : CMlPolynomialEval E n) (point : Vector E n) (W ell : Nat) : Inventory where
  extensionScalars := Buffers.prepareBuilderCells prepared +
    ((6 * T + 3 * K + 6) * 2 ^ n + 8) + Buffers.basisBuilderCells z lambda +
    (if n = 0 then 0 else Buffers.roundScalarScratch T K ell) +
    Buffers.denseBackendCells backend point + Buffers.sourceScalarScratch T K W
  finiteIndices := Buffers.roundIndexScratch (2 ^ n) K ell + 3 * (n + 1)
  arrayContainers := 12 * (2 * T + K + 5) + 6 * (n + 1) +
    3 * (2 * T + K) + 3 + 256 + 12 * (T + K) + 24
  listCells := Buffers.roundIndexScratch (2 ^ n) K ell + 3 * (T + K) +
    12 * (ell + 4) + 32
  contextHandles := 32

/-- Completed-phase buffers and expanded builders have separate contracts. This combined E
allowance uses the expanded one, while omitting all round buffers at zero rounds. -/
theorem workspace_extension_le [CommRing E] (prepared : Prepared E T K n) (z : Vector E n)
    (lambda : Vector E K) (backend : CMlPolynomialEval E n) (point : Vector E n) (W ell : Nat) :
    (workspace prepared z lambda backend point W ell).extensionScalars ≤
      (12 * T + 6 * K + 52) * 2 ^ n + 2 * K + 32 +
      (if n = 0 then 0 else 12 * T + 12 * K + 6 + 256 * (ell + 4)) +
      (6 * T + 3 * K + 3 * W + 67) := by
  have hb := Buffers.basisBuilderCells_le z lambda
  have hd := Buffers.denseBackendCells_le backend point
  have hr := Buffers.roundScalarScratch_le T K ell
  dsimp only [workspace]
  rw [Buffers.prepareBuilderCells_eq, Buffers.sourceScalarScratch_eq]
  have hsum : (6 * T + 3 * K + 6) * 2 ^ n + (6 * T + 3 * K + 6) * 2 ^ n +
      20 * 2 ^ n + 20 * 2 ^ n = (12 * T + 6 * K + 52) * 2 ^ n := by ring
  split_ifs <;> omega

/-- Every actual folded output has dimension at most the initial dimension, so the fold role in
workspace dominates its concrete outer/row builders. No final unused fold is required. -/
theorem fold_workspace_le {r : Nat} (next : State E T K r) (hr : r ≤ n) :
    Buffers.foldBuilderCells next ≤ (6 * T + 3 * K + 6) * 2 ^ n + 8 := by
  rw [Buffers.foldBuilderCells_eq]
  have hp : (2 : Nat) ^ r ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hr
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hp) _

/-- Combined named workspace bound. Row-sized arrays, coordinate tails and builder roles are
geometric; the separate width-dependent source buffer and round scratch remain visible. -/
def workspaceBound (n T K W ell : Nat) : Inventory where
  extensionScalars := (12 * T + 6 * K + 52) * 2 ^ n + 2 * K + 32 +
    (if n = 0 then 0 else 12 * T + 12 * K + 6 + 256 * (ell + 4)) +
    (6 * T + 3 * K + 3 * W + 67)
  finiteIndices := 5 * 2 ^ n + 2 * K + 5 * ell + 55
  arrayContainers := 42 * T + 27 * K + 6 * 2 ^ n + 349
  listCells := 2 * 2 ^ n + 3 * T + 5 * K + 17 * ell + 132
  contextHandles := 32

/-- Every workspace category has its own explicit bound. No arithmetic-request profile is used
as a storage bound, and n=0 does not allocate a private equality cache or round buffers. -/
theorem workspace_le [CommRing E] (prepared : Prepared E T K n) (z : Vector E n)
    (lambda : Vector E K) (backend : CMlPolynomialEval E n) (point : Vector E n) (W ell : Nat) :
    Fits (workspace prepared z lambda backend point W ell) (workspaceBound n T K W ell) := by
  have he := workspace_extension_le prepared z lambda backend point W ell
  have hn := dimension_le_rows n
  simp only [Fits, workspace, workspaceBound, Buffers.roundIndexScratch] at *
  constructor
  · exact Nat.le_refl 0
  constructor
  · exact he
  constructor
  · exact Nat.le_refl 0
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  · exact Nat.le_refl 32

/-- Histogram output/current/next counters, multiplicity nested cast builders and one temporary
signed BASE column. There is no flat cast-array or retained full signed-weight matrix. -/
def scalarPreprocessing {M P : Nat}
    (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n))
    (mu : Vector (CMlPolynomialEval B n) P)
    (source signed : CMlPolynomialEval B n) : Inventory where
  baseScalars := Buffers.multiplicityBuilderCells mu + Buffers.signedBaseColumnCells source signed
  naturalCounters := Buffers.histogramBuilderCells indices
    (Vector.histogram indices) (Vector.histogram indices)
  arrayContainers := 3 * (P + 1) + 10
  finiteIndices := 6
  contextHandles := 8

/-- Histogram and multiplicity-cast construction shared by both frontends. Tuple weights are
negated in E by compression, so this role contains no fictional BASE tuple-weight matrix. -/
def multiplicityPreprocessing {M P : Nat}
    (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n))
    (mu : Vector (CMlPolynomialEval B n) P) : Inventory where
  baseScalars := Buffers.multiplicityBuilderCells mu
  naturalCounters := Buffers.histogramBuilderCells indices
    (Vector.histogram indices) (Vector.histogram indices)
  arrayContainers := 3 * (P + 1) + 6
  finiteIndices := 4
  contextHandles := 4

/-- The common cast/histogram construction counts actual output dimensions without a flat cast
array or any tuple coefficient buffer. -/
theorem multiplicityPreprocessing_eq {M P : Nat}
    (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n))
    (mu : Vector (CMlPolynomialEval B n) P) :
    multiplicityPreprocessing indices mu =
      { baseScalars := (3 * P + 3) * 2 ^ n + 8
        naturalCounters := 3 * P * 2 ^ n + 8
        arrayContainers := 3 * P + 9
        finiteIndices := 4
        contextHandles := 4 } := by
  simp only [multiplicityPreprocessing, Buffers.multiplicityBuilderCells_eq,
    Buffers.histogramBuilderCells_eq]
  congr 1
  ring

/-- The actual reshaped mu, source column and dense counter dimensions expose all scalar
preprocessing roles independently of extension arithmetic profiles. -/
theorem scalarPreprocessing_eq {M P : Nat}
    (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n))
    (mu : Vector (CMlPolynomialEval B n) P) (source signed : CMlPolynomialEval B n) :
    scalarPreprocessing indices mu source signed =
      { baseScalars := (3 * P + 7) * 2 ^ n + 16
        naturalCounters := 3 * P * 2 ^ n + 8
        arrayContainers := 3 * P + 13
        finiteIndices := 6
        contextHandles := 8 } := by
  simp only [scalarPreprocessing, Buffers.multiplicityBuilderCells_eq,
    Buffers.signedBaseColumnCells_eq, Buffers.histogramBuilderCells_eq]
  congr 1 <;> ring
end Workspace

/-- Combine all named private, public, frontend, configuration and construction roles, then add
independent opaque allowances. The frontend and its preprocessing are explicit inventories; no
arbitrary source representation is inferred from a finite getter interface. -/
def complete (retained publicPart frontend grouping preprocessing workspace : Inventory)
    (extras : Allowances) : Inventory :=
  combine (combine (combine retained publicPart) (combine frontend grouping))
    (combine (combine preprocessing workspace) (allowanceCells extras))

/-- Every supplied opaque allowance survives unchanged as an additive offset in each category. -/
theorem complete_extension_eq
    (retained publicPart frontend grouping preprocessing workspace : Inventory)
    (extras : Allowances) :
    (complete retained publicPart frontend grouping preprocessing workspace
      extras).extensionScalars =
      retained.extensionScalars + publicPart.extensionScalars + frontend.extensionScalars +
        grouping.extensionScalars + preprocessing.extensionScalars + workspace.extensionScalars +
        extras.originalSource.extensionScalars + extras.viewsAndGetters.extensionScalars +
        extras.embeddingsAndPrimitives.extensionScalars + extras.callerAndRaw.extensionScalars := by
  simp only [complete, combine, allowanceCells]
  omega

/-- Category bounds compose before geometric simplification, preserving each explicit opaque
boundary. This theorem does not conflate BASE, E, Nat, Fin or container metrics. -/
theorem complete_le {r r' p p' f f' g g' s s' w w' : Inventory}
    (hr : Fits r r') (hp : Fits p p') (hf : Fits f f') (hg : Fits g g')
    (hs : Fits s s') (hw : Fits w w') (extras : Allowances) :
    Fits (complete r p f g s w extras) (complete r' p' f' g' s' w' extras) := by
  rcases hr with ⟨r₁, r₂, r₃, r₄, r₅, r₆, r₇⟩
  rcases hp with ⟨p₁, p₂, p₃, p₄, p₅, p₆, p₇⟩
  rcases hf with ⟨f₁, f₂, f₃, f₄, f₅, f₆, f₇⟩
  rcases hg with ⟨g₁, g₂, g₃, g₄, g₅, g₆, g₇⟩
  rcases hs with ⟨s₁, s₂, s₃, s₄, s₅, s₆, s₇⟩
  rcases hw with ⟨w₁, w₂, w₃, w₄, w₅, w₆, w₇⟩
  simp only [Fits, complete, combine]
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor <;> omega


section Defaults
variable {B E : Type} [CommRing B] [Field E] [DecidableEq E]
variable {n M P ell : Nat}

/-- Full declared ordinary scalar inventory on actual sent messages and actual selected call
arguments. The backend table/point identify one active original dense evaluator; the extra view
allowance must cover any supplied source view's additional work. Named active columns are actual
getters, not a materialized full signed-weight matrix. -/
def scalar (f : B →+* E) (cfg : Logup.Lookup.Config B n M P ell)
    (data : Logup.Lookup.Data B n M P)
    (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n))
    {ι : Type} (ambient : OracleSpec ι) (handler : QueryImpl ambient Id) (alpha : E)
    (joint : (Fin n → E) × (Fin ((M + P) ⌈/⌉ ell) → E))
    (history : Vector (Option E) n) (backend : CMlPolynomialEval E n)
    (point : Vector E n) (extras : Allowances) : Inventory :=
  let mu := Logup.Lookup.multiplicities (B := B) (n := n) (P := P) indices
  let wd := Logup.Lookup.weightedData data mu
  let prepared := simulateQ arithmeticAnswer (State.prepareProgram f alpha cfg.weighted.groups wd)
  let observed := observeProver ambient handler
    (proverWith callInterpreter call_erases (· ++ ·) [] f cfg.weighted wd ambient)
    alpha joint history
  let first : Fin (M + P) := ⟨0, cfg.weighted.total_pos⟩
  complete (retained prepared observed.1 observed.2.2 observed.2.1)
    (publicFields (Vector.ofFn joint.1) (Vector.ofFn joint.2) false)
    (scalarInput data indices) (grouping cfg.weighted.groups)
    (scalarPreprocessing indices mu (wd (0, first)) (wd (1, first)))
    (workspace prepared (Vector.ofFn joint.1) (Vector.ofFn joint.2) backend point 0 ell) extras

/-- The complete scalar ledger preserves a supplied opaque E offset in addition to all named
roles. Optional raw logging remains an explicitly separate inventory. -/
theorem scalar_offset {n M P ell : Nat} (f : B →+* E)
    (cfg : Logup.Lookup.Config B n M P ell) (data : Logup.Lookup.Data B n M P)
    (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n))
    {ι : Type} (ambient : OracleSpec ι) (handler : QueryImpl ambient Id) (alpha : E)
    (joint : (Fin n → E) × (Fin ((M + P) ⌈/⌉ ell) → E)) (history : Vector (Option E) n)
    (backend : CMlPolynomialEval E n) (point : Vector E n) (extras : Allowances) :
    (scalar f cfg data indices ambient handler alpha joint history backend point
      extras).extensionScalars =
      (scalar f cfg data indices ambient handler alpha joint history backend
        point {}).extensionScalars +
        (allowanceCells extras).extensionScalars := by
  simp only [scalar, complete, combine, allowanceCells]
  omega

open Logup.Lookup.Tuple
variable {b W : Nat} {schema : TaggedTuple.Schema B b W} {layout : ProviderLayout b P}

/-- Full declared tuple inventory using the actual once-only BASE histogram and beta cache, then
actual weighted preparation/messages. Provider construction, the eager compression workspace and
public buffered coefficient queries have separate roles; the private cache reads BASE directly. -/
def tuple (f : B →+* E) (cfg : Logup.Lookup.Config B n M P ell)
    (provider : PreparedProvider schema layout n M)
    (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n))
    {ι : Type} (ambient : OracleSpec ι) (handler : QueryImpl ambient Id) (beta alpha : E)
    (joint : (Fin n → E) × (Fin ((M + P) ⌈/⌉ ell) → E))
    (history : Vector (Option E) n) (backend : CMlPolynomialEval E n)
    (point : Vector E n) (extras : Allowances) : Inventory :=
  let mu := Logup.Lookup.multiplicities (B := B) (n := n) (P := P) indices
  let cache := simulateQ arithmeticAnswer (compressedTablesProgram f provider beta mu)
  let prepared := simulateQ arithmeticAnswer
    (State.prepareProgram (RingHom.id E) alpha cfg.weighted.groups (compressedData cache))
  let observed := observeProver ambient handler
    (proverWith callInterpreter call_erases (· ++ ·) [] (RingHom.id E) cfg.weighted
      (compressedData cache) ambient) alpha joint history
  complete (retained prepared observed.1 observed.2.2 observed.2.1)
    (publicFields (Vector.ofFn joint.1) (Vector.ofFn joint.2) true)
    (tupleInput provider indices cache) (grouping cfg.weighted.groups)
    (combine (multiplicityPreprocessing indices mu) (providerConstruction provider))
    (combine (workspace prepared (Vector.ofFn joint.1) (Vector.ofFn joint.2) backend point W ell)
      (compressionConstruction cache)) extras

/-- Closed scalar category envelopes, retaining each opaque offset and the zero-round omission.
All input and preprocessing roles are counted separately from the E-only request profile. -/
def scalarBound (n M P ell : Nat) (extras : Allowances) : Inventory :=
  let T := M + P
  let K := T ⌈/⌉ ell
  complete (retainedBound n T K ell) (publicBound n K)
    { baseScalars := (M + 4 * P) * 2 ^ n
      naturalCounters := P * 2 ^ n
      finiteIndices := M * 2 ^ n
      arrayContainers := M + 4 * P + 6
      contextHandles := 4 }
    { finiteIndices := T, arrayContainers := 1, listCells := T, contextHandles := K + 1 }
    { baseScalars := (3 * P + 7) * 2 ^ n + 16
      naturalCounters := 3 * P * 2 ^ n + 8
      arrayContainers := 3 * P + 13
      finiteIndices := 6
      contextHandles := 8 }
    (workspaceBound n T K 0 ell) extras

/-- The full declared scalar inventory has a bound in every category along the actual selected
optional history. No soundness, characteristic-size estimate or table-value premise is used. -/
theorem scalar_le (f : B →+* E) (cfg : Logup.Lookup.Config B n M P ell)
    (data : Logup.Lookup.Data B n M P)
    (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n))
    {ι : Type} (ambient : OracleSpec ι) (handler : QueryImpl ambient Id) (alpha : E)
    (joint : (Fin n → E) × (Fin ((M + P) ⌈/⌉ ell) → E))
    (history : Vector (Option E) n) (backend : CMlPolynomialEval E n)
    (point : Vector E n) (extras : Allowances) :
    Fits (scalar f cfg data indices ambient handler alpha joint history backend point extras)
      (scalarBound n M P ell extras) := by
  let mu := Logup.Lookup.multiplicities (B := B) (n := n) (P := P) indices
  let wd := Logup.Lookup.weightedData data mu
  let prepared := simulateQ arithmeticAnswer (State.prepareProgram f alpha cfg.weighted.groups wd)
  let observed := observeProver ambient handler
    (proverWith callInterpreter call_erases (· ++ ·) [] f cfg.weighted wd ambient)
    alpha joint history
  let first : Fin (M + P) := ⟨0, cfg.weighted.total_pos⟩
  have hr := observed_retained_le f cfg.weighted wd ambient handler alpha joint history
  have hp := publicFields_le (Vector.ofFn joint.1) (Vector.ofFn joint.2) false
  have hw := workspace_le prepared (Vector.ofFn joint.1) (Vector.ofFn joint.2) backend point 0 ell
  have h := complete_le hr hp (Fits.refl (scalarInput data indices))
    (Fits.refl (grouping cfg.weighted.groups))
    (Fits.refl (scalarPreprocessing indices mu (wd (0, first)) (wd (1, first)))) hw extras
  simpa only [scalar, scalarBound, scalarInput_eq, grouping_eq, scalarPreprocessing_eq,
    publicBound, mu, wd, prepared, observed, first] using h

/-- The scalar bound's BASE and Nat roles preserve histogram and casts; its E role includes
private/source/path tables, all statement prefixes and the actual named builder phases. -/
theorem scalarBound_fields (n M P ell : Nat) (extras : Allowances) :
    let T := M + P
    let K := T ⌈/⌉ ell
    let offset := allowanceCells extras
    scalarBound n M P ell extras =
      { baseScalars := (M + 7 * P + 7) * 2 ^ n + 16 + offset.baseScalars
        extensionScalars := (18 * T + 12 * K + 2 * ell + 67) * 2 ^ n +
          6 * T + 7 * K + 103 +
          (if n = 0 then 0 else 12 * T + 12 * K + 6 + 256 * (ell + 4)) + offset.extensionScalars
        naturalCounters := 4 * P * 2 ^ n + 8 + offset.naturalCounters
        finiteIndices := (M + 5) * 2 ^ n + T + 2 * K + 5 * ell + 61 + offset.finiteIndices
        arrayContainers := 10 * (2 * T + K + 1) * 2 ^ n + 10 * 2 ^ n +
          44 * T + 30 * K + M + 7 * P + 380 + offset.arrayContainers
        listCells := 2 * 2 ^ n + 4 * T + 5 * K + 17 * ell + 132 + offset.listCells
        contextHandles := 6 * 2 ^ n + K + 57 + offset.contextHandles } := by
  dsimp only
  simp only [scalarBound, complete, combine, retainedBound, publicBound, workspaceBound]
  congr 1 <;> ring

/-- Closed typed-provider and eager-cache category envelopes. The registered-bus b and padded
width W terms are explicit and are not bounded by occurring columns or characteristic. -/
def tupleBound (b W n M P ell : Nat) (extras : Allowances) : Inventory :=
  let T := M + P
  let K := T ⌈/⌉ ell
  complete (retainedBound n T K ell) (publicBound n K)
    { baseScalars := b + T * 2 ^ n * W + T * (W + 1) * 2 ^ n + 3 * P * 2 ^ n
      extensionScalars := 2 * T * 2 ^ n
      naturalCounters := b + P * 2 ^ n
      finiteIndices := P + T * 2 ^ n + M * 2 ^ n
      arrayContainers := 13 + 4 * T + 3 * P + T * 2 ^ n + T * (W + 1)
      contextHandles := 8 }
    { finiteIndices := T, arrayContainers := 1, listCells := T, contextHandles := K + 1 }
    (combine
      { baseScalars := (3 * P + 3) * 2 ^ n + 8
        naturalCounters := 3 * P * 2 ^ n + 8
        arrayContainers := 3 * P + 9
        finiteIndices := 4
        contextHandles := 4 }
      { baseScalars := 3 * (T * (W + 1) * 2 ^ n) + 3 * (W + 1) * 2 ^ n + 3 * 2 ^ n
        arrayContainers := 3 * (T * (W + 1) + T + W + 3)
        finiteIndices := 3
        contextHandles := 4 })
    (combine (workspaceBound n T K W ell)
      { extensionScalars := (6 * T + 6) * 2 ^ n + 16
        arrayContainers := 6 * T + 12
        naturalCounters := 4
        finiteIndices := 4
        contextHandles := 4 }) extras

/-- Full typed tuple inventory along the actual beta cache and weighted optional history. The
provider payloads use each registered width; opaque raw/getter/embedding storage stays supplied. -/
theorem tuple_le (f : B →+* E) (cfg : Logup.Lookup.Config B n M P ell)
    (provider : PreparedProvider schema layout n M)
    (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n))
    {ι : Type} (ambient : OracleSpec ι) (handler : QueryImpl ambient Id) (beta alpha : E)
    (joint : (Fin n → E) × (Fin ((M + P) ⌈/⌉ ell) → E))
    (history : Vector (Option E) n) (backend : CMlPolynomialEval E n)
    (point : Vector E n) (extras : Allowances) :
    Fits (tuple f cfg provider indices ambient handler beta alpha joint history backend point
      extras)
      (tupleBound b W n M P ell extras) := by
  let mu := Logup.Lookup.multiplicities (B := B) (n := n) (P := P) indices
  let cache := simulateQ arithmeticAnswer (compressedTablesProgram f provider beta mu)
  let prepared := simulateQ arithmeticAnswer
    (State.prepareProgram (RingHom.id E) alpha cfg.weighted.groups (compressedData cache))
  have hr := observed_retained_le (RingHom.id E) cfg.weighted (compressedData cache)
    ambient handler alpha joint history
  have hp := publicFields_le (Vector.ofFn joint.1) (Vector.ofFn joint.2) true
  have hw := workspace_le prepared (Vector.ofFn joint.1) (Vector.ofFn joint.2) backend point W ell
  have hc : Fits (compressionConstruction cache)
      { extensionScalars := (6 * (M + P) + 6) * 2 ^ n + 16
        arrayContainers := 6 * (M + P) + 12
        naturalCounters := 4
        finiteIndices := 4
        contextHandles := 4 } := by
    simp only [Fits, compressionConstruction, eagerCacheCells_eq]
    constructor
    · exact Nat.le_refl 0
    constructor
    · apply le_of_eq
      ring
    simp
  have h := complete_le hr hp (tupleInput_le provider indices cache)
    (Fits.refl (grouping cfg.weighted.groups))
    (Fits.refl (combine (multiplicityPreprocessing indices mu) (providerConstruction provider)))
    (hw.combine_bound hc) extras
  simpa only [tuple, tupleBound, publicBound, grouping_eq, multiplicityPreprocessing_eq,
    providerConstruction, providerCoefficientCells_eq, mu, cache, prepared] using h

/-- Each category of the tuple envelope preserves schema/width and opaque offsets explicitly.
The E envelope includes eager compression, separately from the original BASE coefficients. -/
theorem tupleBound_fields (b W n M P ell : Nat) (extras : Allowances) :
    let T := M + P
    let K := T ⌈/⌉ ell
    let offset := allowanceCells extras
    tupleBound b W n M P ell extras =
      { baseScalars := b +
          (T * W + 4 * T * (W + 1) + 6 * P + 3 * (W + 1) + 6) * 2 ^ n + 8 + offset.baseScalars
        extensionScalars := (26 * T + 12 * K + 2 * ell + 73) * 2 ^ n +
          6 * T + 7 * K + 3 * W + 119 +
          (if n = 0 then 0 else 12 * T + 12 * K + 6 + 256 * (ell + 4)) + offset.extensionScalars
        naturalCounters := b + 4 * P * 2 ^ n + 12 + offset.naturalCounters
        finiteIndices := (T + M + 5) * 2 ^ n + P + T + 2 * K + 5 * ell + 66 + offset.finiteIndices
        arrayContainers := 10 * (2 * T + K + 1) * 2 ^ n + 10 * 2 ^ n + T * 2 ^ n +
          57 * T + 30 * K + 6 * P + 4 * T * (W + 1) + 3 * W + 404 + offset.arrayContainers
        listCells := 2 * 2 ^ n + 4 * T + 5 * K + 17 * ell + 132 + offset.listCells
        contextHandles := 6 * 2 ^ n + K + 65 + offset.contextHandles } := by
  dsimp only
  simp only [tupleBound, complete, combine, retainedBound, publicBound, workspaceBound]
  congr 1 <;> ring

end Defaults

end Logup.Prover.Storage.Ledger
