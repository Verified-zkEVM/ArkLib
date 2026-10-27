/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ProofSystem.Logup.Prover.Resources.Arithmetic
public import ArkLib.ProofSystem.Logup.Lookup.Tuple.Provider

/-!
# Logical storage of retained honest prover data

Censuses read actual finite vector and array fields. State snapshots follow the exact selected
control at typed optional challenges through its existing argument carrying Call observation.
The observation's instrumentation list is not part of the ordinary Unit driver's stored data.

Counts refer to named logical payload positions. They may conservatively count aliases more than
once and make no claim about physical sharing, allocator capacity, closure layout, garbage
collection or live heap peaks. Original source/backend representations and their scratch require
explicit separate inventories; private table counts alone are not a complete storage ledger.
-/

@[expose] public section

open Interaction.Oracle OracleComp OracleSpec CompPoly Logup.Interaction
open Logup.Prover.Honest.Accounting
namespace Logup.Prover.Storage
variable {E : Type} {n T K : Nat}

/-- Count the scalar positions of one actual Boolean value table. -/
def tableCells (table : CMlPolynomialEval E n) : Nat := table.toArray.size

/-- Count scalar positions across an actual finite family of Boolean tables. -/
def familyCells (tables : Vector (CMlPolynomialEval E n) T) : Nat :=
  (tables.toList.map tableCells).sum

/-- A table has one scalar position for every Boolean row. -/
theorem tableCells_eq (table : CMlPolynomialEval E n) : tableCells table = 2 ^ n := by
  simp [tableCells]

/-- Table family payload size is the product of its two actual dimensions. -/
theorem familyCells_eq (tables : Vector (CMlPolynomialEval E n) T) :
    familyCells tables = T * 2 ^ n := by
  unfold familyCells
  have hm : tables.toList.map tableCells = tables.toList.map (fun _ => 2 ^ n) := by
    apply List.map_congr_left
    intro t _
    exact tableCells_eq t
  rw [hm]
  simp

/-- Count all denominator, weight and helper fields before the joint challenge. -/
def preparedCells (prepared : Prepared E T K n) : Nat :=
  familyCells prepared.denominator + familyCells prepared.weight + familyCells prepared.helper

/-- Count every denominator, weight, helper and kernel table of an actual private state. -/
def stateTableCells (state : State E T K n) : Nat :=
  preparedCells state.toPrepared + tableCells state.kernel

/-- Count the batching vector at one retained private state level, without assuming sharing. -/
def stateLambdaCells (state : State E T K n) : Nat := state.lambda.toArray.size

/-- Preparation retains its three full table families, including at zero variables. -/
theorem preparedCells_eq (prepared : Prepared E T K n) :
    preparedCells prepared = (2 * T + K) * 2 ^ n := by
  simp only [preparedCells, familyCells_eq]
  ring

/-- Each private state table family has its declared remaining Boolean dimension. -/
theorem stateTableCells_eq (state : State E T K n) :
    stateTableCells state = (2 * T + K + 1) * 2 ^ n := by
  simp only [stateTableCells, preparedCells_eq, tableCells_eq]
  ring

/-- Every retained state names all batching coefficients. -/
theorem stateLambdaCells_eq (state : State E T K n) : stateLambdaCells state = K := by
  simp [stateLambdaCells]

/-- Sum the row counts of all positive dimensional private state levels. -/
def positiveRows (n : Nat) : Nat := ∑ r ∈ Finset.range n, 2 ^ (r + 1)

/-- Positive levels retain at most twice the initial rows, omitting dimension zero. -/
theorem positiveRows_eq (n : Nat) : positiveRows n = 2 * 2 ^ n - 2 := by
  simp only [positiveRows, pow_succ]
  rw [← Finset.sum_mul]
  change Resources.messageRows n * 2 = _
  rw [Resources.messageRows_eq]
  have h : 0 < (2 : Nat) ^ n := Nat.pow_pos (by decide)
  omega

/-- Count target and challenge positions in every verifier statement prefix. -/
def prefixCells (n : Nat) : Nat := ∑ j ∈ Finset.range (n + 1), (j + 1)

/-- Even retaining every statement prefix gives a geometric scalar bound. -/
theorem prefixCells_le (n : Nat) : prefixCells n ≤ 2 * 2 ^ n := by
  induction n with
  | zero => simp [prefixCells]
  | succ n ih =>
    have h : n + 2 ≤ 2 ^ (n + 1) := Nat.succ_le_of_lt Nat.lt_two_pow_self
    simp only [prefixCells, Finset.sum_range_succ] at ih ⊢
    rw [pow_succ] at h ⊢
    omega

section Calls
variable {B : Type} [CommRing B] [CommRing E]

/-- One actual message call identifies its current private state table snapshot. -/
def callTableCells : Call B E T K → Nat
  | .message _ _ state => stateTableCells state
  | _ => 0

/-- One actual message call identifies its current batching vector snapshot. -/
def callLambdaCells : Call B E T K → Nat
  | .message _ _ state => stateLambdaCells state
  | _ => 0

/-- Count table snapshots at the message calls of an observed selected continuation. -/
def positiveStateTables (calls : List (Call B E T K)) : Nat :=
  (calls.map callTableCells).sum

/-- Count batching snapshots at those same actual message calls. -/
def positiveStateLambda (calls : List (Call B E T K)) : Nat :=
  (calls.map callLambdaCells).sum

/-- Concatenating observed histories adds their named table snapshots. -/
theorem positiveStateTables_append (xs ys : List (Call B E T K)) :
    positiveStateTables (xs ++ ys) = positiveStateTables xs + positiveStateTables ys := by
  simp [positiveStateTables]

/-- Concatenating histories adds batching snapshots without a sharing convention. -/
theorem positiveStateLambda_append (xs ys : List (Call B E T K)) :
    positiveStateLambda (xs ++ ys) = positiveStateLambda xs + positiveStateLambda ys := by
  simp [positiveStateLambda]
end Calls

section Observed
variable {B : Type} [CommRing B] [CommRing E] [Inv E] [DecidableEq E]
variable {ell : Nat}

/-- One additional positive level contributes exactly its Boolean table size. -/
theorem positiveRows_succ (n : Nat) : positiveRows (n + 1) = positiveRows n + 2 ^ (n + 1) := by
  simp [positiveRows, Finset.sum_range_succ]

/-- Every actual optional history retains only positive table levels and one batching vector
per message; abort and terminal branches create no extra folded state. -/
theorem observed_positive_state_cells_le {ι : Type} (ambient : OracleSpec ι)
    (handler : QueryImpl ambient Id) (groups : Vector (List (Fin T)) K)
    (hgroups : ∀ k, (groups.get k).length ≤ ell) (count : Nat)
    (state : State E T K count) (history : Vector (Option E) count)
    (before : List (Call B E T K)) :
    let calls := (observeNative ambient handler count
      (nativeWith (callInterpreter (B := B)) call_erases (· ++ ·) ambient groups hgroups
        count state before) history).2
    positiveStateTables calls ≤ positiveStateTables before + (2 * T + K + 1) * positiveRows count ∧
    positiveStateLambda calls ≤ positiveStateLambda before + count * K := by
  induction count generalizing before with
  | zero => simp [observeNative, nativeWith, positiveRows]
  | succ count ih =>
    cases count with
    | zero =>
      rw [observeNative_one]
      simp [callInterpreter, messageWith_snd, positiveStateTables, positiveStateLambda,
        callTableCells, callLambdaCells, stateTableCells_eq, stateLambdaCells_eq, positiveRows]
    | succ count =>
      rw [observeNative_succ_succ]
      cases hc : history[0] with
      | none =>
        change positiveStateTables
            (before ++ [Call.message (B := B) (count + 1) groups state]) ≤ _ ∧
          positiveStateLambda (before ++ [Call.message (B := B) (count + 1) groups state]) ≤ _
        simp only [positiveStateTables_append, positiveStateLambda_append]
        simp only [positiveStateTables, positiveStateLambda, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, Nat.add_zero, callTableCells, callLambdaCells,
          stateTableCells_eq, stateLambdaCells_eq]
        rw [positiveRows_succ, Nat.mul_add]
        simp only [Nat.add_mul, Nat.one_mul]
        constructor <;> omega
      | some r =>
        let call := Call.fold (B := B) (count + 1) state r
        let next := simulateQ arithmeticAnswer call.program
        have hi := ih next history.tail
          (before ++ [Call.message (B := B) (count + 1) groups state] ++ [call])
        change positiveStateTables (observeNative ambient handler (count + 1)
            (nativeWith (callInterpreter (B := B)) call_erases (· ++ ·) ambient groups hgroups
              (count + 1) next
              (before ++ [Call.message (B := B) (count + 1) groups state] ++ [call]))
            history.tail).2 ≤ _ ∧
          positiveStateLambda (observeNative ambient handler (count + 1)
            (nativeWith (callInterpreter (B := B)) call_erases (· ++ ·) ambient groups hgroups
              (count + 1) next
              (before ++ [Call.message (B := B) (count + 1) groups state] ++ [call]))
            history.tail).2 ≤ _
        rw [positiveRows_succ, Nat.mul_add]
        simp only [positiveStateTables_append, positiveStateLambda_append] at hi
        simp only [positiveStateTables, positiveStateLambda, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, Nat.add_zero, callTableCells, callLambdaCells,
          stateTableCells_eq, stateLambdaCells_eq, call] at hi
        dsimp only [call, positiveStateTables, positiveStateLambda] at ⊢
        simp only [Nat.add_mul, Nat.one_mul] at hi ⊢
        constructor <;> omega
end Observed

variable {B E : Type} {n M P b W : Nat}

/-- Scalars carried by the actual canonical coefficient messages. -/
def messageCells [CommSemiring E] {ell : Nat}
    (messages : List (Sumcheck.Impl.Representation.Message E (ell + 2))) : Nat :=
  (messages.map fun q => q.val.val.size).sum

/-- Retaining every sent coefficient message uses its actual canonical size. -/
theorem messageCells_le [CommSemiring E] {ell : Nat}
    (messages : List (Sumcheck.Impl.Representation.Message E (ell + 2))) :
    messageCells messages ≤ messages.length * (ell + 3) := by
  induction messages with
  | nil => simp [messageCells]
  | cons q qs ih =>
    have h := Sumcheck.Impl.Representation.size_le E (ell + 2) q
    simp only [messageCells, List.map_cons, List.sum_cons, List.length_cons]
    change q.val.val.size + messageCells qs ≤ _
    simp only [Nat.add_mul, Nat.one_mul]
    omega

/-- Arbitrary optional histories send at most the declared number of native messages. -/
theorem observed_message_length_le [CommRing E] {ell : Nat} {C : Type} {ι : Type}
    (ambient : OracleSpec ι) (handler : QueryImpl ambient Id) (count : Nat)
    (strategy : NativeStrategy (E := E) ambient ell count C)
    (history : Vector (Option E) count) :
    (observeNative ambient handler count strategy history).1.length ≤ count := by
  induction count with
  | zero => simp [observeNative]
  | succ count ih =>
    rw [observeNative]
    cases history[0] with
    | none => simp
    | some r =>
      exact Nat.succ_le_succ (ih _ history.tail)

/-- Canonical messages obey the coefficient bound even when the verifier aborts early. -/
theorem observed_message_cells_le [CommRing E] {ell : Nat} {C : Type} {ι : Type}
    (ambient : OracleSpec ι) (handler : QueryImpl ambient Id) (count : Nat)
    (strategy : NativeStrategy (E := E) ambient ell count C)
    (history : Vector (Option E) count) :
    messageCells (observeNative ambient handler count strategy history).1 ≤ count * (ell + 3) :=
  (messageCells_le _).trans (Nat.mul_le_mul_right _
    (observed_message_length_le ambient handler count strategy history))

/-- Actual finite witness positions, irrespective of duplicate table values. -/
def witnessCells {U L : Nat} (indices : Vector (Fin U) L) : Nat := indices.toArray.size

/-- Natural counters retained by the actual dense indexed histogram. -/
def histogramCells {U L : Nat} (indices : Vector (Fin U) L) : Nat :=
  (Vector.histogram indices).toArray.size

/-- The witness stores one index per query row. -/
theorem witnessCells_eq {U L : Nat} (indices : Vector (Fin U) L) :
    witnessCells indices = L := by simp [witnessCells]

/-- The histogram covers all table positions, including unused positions. -/
theorem histogramCells_eq {U L : Nat} (indices : Vector (Fin U) L) :
    histogramCells indices = U := by simp [histogramCells]

/-- Count the actual cast and reshaped multiplicity payload, separately from natural counters. -/
theorem multiplicityCells_eq [NatCast B] {L : Nat} (indices : Vector (Fin (P * 2 ^ n)) L) :
    familyCells (Logup.Lookup.multiplicities (B := B) indices) = P * 2 ^ n :=
  familyCells_eq _

/-- Named source columns returned by both roles of an actual finite table getter. -/
def getterCells {A : Type} {L : Nat} (data : Fin L → CMlPolynomialEval A n) : Nat :=
  familyCells (Vector.ofFn data)

/-- Finite interface payload positions do not bound the representation of a getter closure. -/
theorem getterCells_eq {A : Type} {L : Nat} (data : Fin L → CMlPolynomialEval A n) :
    getterCells data = L * 2 ^ n := familyCells_eq _

/-- Count the signed base weight columns returned by the actual scalar frontend. -/
def signedWeightCells [One B] [Neg B] (data : Logup.Lookup.Data B n M P)
    (mu : Vector (CMlPolynomialEval B n) P) : Nat :=
  getterCells fun i => Logup.Lookup.weightedData data mu (1, i)

/-- Unit query columns and negated multiplicity columns both have the declared height. -/
theorem signedWeightCells_eq [One B] [Neg B] (data : Logup.Lookup.Data B n M P)
    (mu : Vector (CMlPolynomialEval B n) P) :
    signedWeightCells data mu = (M + P) * 2 ^ n := getterCells_eq _

/-- Count both actual eager value and signed weight matrices, retaining their distinct roles. -/
def eagerCacheCells (cache : Vector (Vector (CMlPolynomialEval E n) T) 2) : Nat :=
  (cache.toList.map familyCells).sum

/-- The selected eager representation contains exactly two complete source matrices. -/
theorem eagerCacheCells_eq (cache : Vector (Vector (CMlPolynomialEval E n) T) 2) :
    eagerCacheCells cache = 2 * T * 2 ^ n := by
  unfold eagerCacheCells
  have hm : cache.toList.map familyCells = cache.toList.map (fun _ => T * 2 ^ n) := by
    apply List.map_congr_left
    intro table _
    exact familyCells_eq table
  rw [hm]
  simp [Nat.two_mul, Nat.add_mul]

section Provider
open Logup.Lookup.Tuple
variable {schema : TaggedTuple.Schema B b W} {layout : ProviderLayout b P}

/-- Actual scalar payload positions of one variable width typed key. -/
def keyPayloadCells (key : schema.Key) : Nat := key.2.toArray.size

/-- Payload widths are bounded by the declared maximum, without requiring every bus to occur. -/
theorem keyPayloadCells_le (key : schema.Key) : keyPayloadCells key ≤ W := by
  simpa [keyPayloadCells] using schema.width_le key.1

/-- Actual semantic payloads in every original key row, distinct from padded coefficients. -/
def providerPayloadCells [Zero B] (prepared : PreparedProvider schema layout n M) : Nat :=
  (prepared.keyRows.toList.map fun column => (column.toList.map keyPayloadCells).sum).sum

/-- Every typed payload is bounded using its own registered bus width. -/
theorem providerPayloadCells_le [Zero B] (prepared : PreparedProvider schema layout n M) :
    providerPayloadCells prepared ≤ (M + P) * 2 ^ n * W := by
  have hrow (column : CMlPolynomialEval schema.Key n) :
      (column.toList.map keyPayloadCells).sum ≤ 2 ^ n * W := by
    calc
      _ ≤ (column.toList.map (fun _ => W)).sum :=
        List.sum_le_sum (by intro k hk; exact keyPayloadCells_le k)
      _ = 2 ^ n * W := by simp
  calc
    _ ≤ (prepared.keyRows.toList.map (fun _ => 2 ^ n * W)).sum :=
      List.sum_le_sum (by intro c hc; exact hrow c)
    _ = (M + P) * 2 ^ n * W := by simp [Nat.mul_assoc]

/-- One bus index per actual semantic key, counted independently of its payload. -/
def providerBusCells [Zero B] (prepared : PreparedProvider schema layout n M) : Nat :=
  (prepared.keyRows.toList.map fun column => column.toArray.size).sum

/-- Original semantic keys retain one registered bus per column and row. -/
theorem providerBusCells_eq [Zero B] (prepared : PreparedProvider schema layout n M) :
    providerBusCells prepared = (M + P) * 2 ^ n := familyCells_eq _

/-- Stored padded coefficient columns, including each bus tag at the common final position. -/
def providerCoefficientCells [Zero B] (prepared : PreparedProvider schema layout n M) : Nat :=
  (prepared.coefficientColumns.toList.map familyCells).sum

/-- Eager padding uses the declared maximum width, including unused buses and zero padding. -/
theorem providerCoefficientCells_eq [Zero B] (prepared : PreparedProvider schema layout n M) :
    providerCoefficientCells prepared = (M + P) * (W + 1) * 2 ^ n := by
  unfold providerCoefficientCells
  have hm : prepared.coefficientColumns.toList.map familyCells =
      prepared.coefficientColumns.toList.map (fun _ => (W + 1) * 2 ^ n) := by
    apply List.map_congr_left
    intro table _
    exact familyCells_eq table
  rw [hm]
  simp [Nat.mul_assoc]

/-- Registered tag positions are retained even when their bus is absent from all key rows. -/
def schemaTagCells (schema : TaggedTuple.Schema B b W) : Nat := schema.tags.toArray.size

/-- Registered natural widths are a separate schema inventory. -/
def schemaWidthCells (schema : TaggedTuple.Schema B b W) : Nat := schema.widths.toArray.size

/-- Public piece owners are separate from the bus indices in individual key rows. -/
def layoutCells (layout : ProviderLayout b P) : Nat := layout.tableBus.toArray.size

/-- Neither schema census assumes a bound on the number of occurring keys. -/
theorem schemaCells_eq (schema : TaggedTuple.Schema B b W) :
    schemaTagCells schema = b ∧ schemaWidthCells schema = b := by
  simp [schemaTagCells, schemaWidthCells]

/-- Each declared physical piece retains its own registered owner. -/
theorem layoutCells_eq (layout : ProviderLayout b P) : layoutCells layout = P := by
  simp [layoutCells]
end Provider

variable {E : Type} {n : Nat}
/-- One actual statement stores its target and its finite challenge prefix. -/
def statementCells {i : Fin (n + 1)} (s : Sumcheck.Spec.StatementRound E n i) : Nat :=
  (#[s.target] : Array E).size + (Vector.ofFn s.challenges).toArray.size

/-- Statement payload size depends on the actual prefix dimension. -/
theorem statementCells_eq {i : Fin (n + 1)} (s : Sumcheck.Spec.StatementRound E n i) :
    statementCells s = i.val + 1 := by simp [statementCells, Nat.add_comm]

/-- Census all finite target and challenge fields, without a prefix sharing assumption. -/
def statementHistoryCells (states : (i : Fin (n + 1)) → Sumcheck.Spec.StatementRound E n i) : Nat :=
  ∑ i : Fin (n + 1), statementCells (states i)

/-- Every family of well typed statement snapshots has the triangular payload census. -/
theorem statementHistoryCells_eq
    (states : (i : Fin (n + 1)) → Sumcheck.Spec.StatementRound E n i) :
    statementHistoryCells states = prefixCells n := by
  simp only [statementHistoryCells, statementCells_eq, prefixCells]
  exact Fin.sum_univ_eq_sum_range (fun j => j + 1) (n + 1)

/-- Coordinate positions of all actual nonempty successive tail vectors. -/
def coordinateTailCells : {n : Nat} → Vector E n → Nat
  | 0, _ => 0
  | _n + 1, x => x.toArray.size + coordinateTailCells x.tail

/-- Coordinate tails and all statement target slots give the same triangular census. -/
theorem coordinateTailCells_prefix {n : Nat} (x : Vector E n) :
    coordinateTailCells x + (n + 1) = prefixCells n := by
  induction n with
  | zero => simp [coordinateTailCells, prefixCells]
  | succ n ih =>
    have h := ih x.tail
    simp only [coordinateTailCells, Vector.size_toArray]
    simp only [prefixCells, Finset.sum_range_succ] at h ⊢
    omega

/-- Retaining every coordinate tail is geometrically bounded. -/
theorem coordinateTailCells_le {n : Nat} (x : Vector E n) :
    coordinateTailCells x ≤ 2 * 2 ^ n := by
  have h := coordinateTailCells_prefix x
  have hp := prefixCells_le n
  omega

section Retained
variable {B E : Type} [CommRing B] [CommRing E] [Inv E] [DecidableEq E]
variable {T K ell n : Nat}

/-- Scalar positions in the named source allowance, prepared state, original helper message,
positive private state snapshots and native coefficient transcript. Unlisted source, public,
backend and workspace roles must be supplied separately in a complete inventory. -/
def retainedScalarCells (sourceCells : Nat) (prepared : Prepared E T K n)
    (originalHelper : Vector (CMlPolynomialEval E n) K) (calls : List (Call B E T K))
    (messages : List (Sumcheck.Impl.Representation.Message E (ell + 2))) : Nat :=
  sourceCells + preparedCells prepared + familyCells originalHelper +
    positiveStateTables calls + positiveStateLambda calls + messageCells messages

/-- The actual optional continuation has a geometric named scalar inventory. The explicit
source allowance is preserved; finite getter dimensions alone do not bound source representation. -/
theorem observed_retainedScalarCells_le {ι : Type} (ambient : OracleSpec ι)
    (handler : QueryImpl ambient Id) (groups : Vector (List (Fin T)) K)
    (hgroups : ∀ k, (groups.get k).length ≤ ell) (sourceCells : Nat)
    (prepared : Prepared E T K n) (originalHelper : Vector (CMlPolynomialEval E n) K)
    (state : State E T K n) (history : Vector (Option E) n) :
    let observed := observeNative ambient handler n
      (nativeWith (callInterpreter (B := B)) call_erases (· ++ ·) ambient groups hgroups
        n state []) history
    retainedScalarCells sourceCells prepared originalHelper observed.2 observed.1 ≤
      sourceCells + (2 * T + 2 * K) * 2 ^ n + (2 * T + K + 1) * positiveRows n +
        n * K + n * (ell + 3) := by
  have hs := observed_positive_state_cells_le (B := B) ambient handler groups hgroups
    n state history []
  have hm := observed_message_cells_le ambient handler n
    (nativeWith (callInterpreter (B := B)) call_erases (· ++ ·) ambient groups hgroups
      n state []) history
  dsimp only at hs hm ⊢
  simp only [positiveStateTables, positiveStateLambda, List.map_nil, List.sum_nil,
    Nat.zero_add] at hs
  simp only [retainedScalarCells, preparedCells_eq, familyCells_eq,
    positiveStateTables, positiveStateLambda]
  have hbase : (2 * T + K) * 2 ^ n + K * 2 ^ n = (2 * T + 2 * K) * 2 ^ n := by ring
  omega
end Retained

end Logup.Prover.Storage
