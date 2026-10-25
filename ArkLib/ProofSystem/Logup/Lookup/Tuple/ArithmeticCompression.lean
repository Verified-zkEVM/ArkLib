/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.ProofSystem.Logup.Lookup.Tuple.Source
public import ArkLib.ToCompPoly.Univariate.ArithmeticHorner
/-!
# Eager tuple compression with exact arithmetic profiles

After beta and before alpha, materialize each compressed value and signed weight once. Value
rows use the shared seeded Horner driver with a direct reader of stored base coefficient cells;
no intermediate challenge-field coefficient row is allocated. Weight rows issue actual challenge-
field subtraction from zero for table multiplicities. Cached data uses only vector getters.

With N=2^n and D=(M+P)N, each value row visits W+1 stored base cells and embeds their entries.
There are D(W+1) such visits, PN retained-multiplicity visits, MN one assignments and PN zero
operands, with D value and D weight output entries. These are source sites, not allocator counts.

Metadata marks designated source sites: one value-row start, each stored base-cell read/embedding,
and each output-cell store; query weights mark a one assignment and store, while table weights mark
zero, the retained base-cell read/embedding and store. These counts are not machine time, opaque
embedding implementation cost, natural-number bit complexity, allocator traffic or peak memory.
The base histogram and provider preparation precede this program and require separate accounting.
-/

@[expose] public section
open CompPoly OracleComp OracleSpec
open scoped BigOperators
namespace Logup.Lookup.Tuple
variable {B E : Type} [CommRing B] [CommRing E] [Inv E] [DecidableEq E]
variable {b W n M P : Nat} {schema : TaggedTuple.Schema B b W}
variable {layout : ProviderLayout b P}

@[no_expose] private def storedRead (f : B →+* E)
    (prepared : PreparedProvider schema layout n M) (slot : Fin (M + P))
    (row : Fin (2 ^ n)) (j : Nat) : OracleComp (ArithmeticSpec E) E := do
  Arithmetic.tick
  if h : j < W + 1 then
    return f (prepared.coefficientColumns[slot.val][j].get row)
  else return 0

private def storedValue (f : B →+* E)
    (prepared : PreparedProvider schema layout n M) (slot : Fin (M + P))
    (row : Fin (2 ^ n)) (j : Nat) : E :=
  if h : j < W + 1 then f (prepared.coefficientColumns[slot.val][j].get row) else 0

private theorem profile_storedRead (f : B →+* E)
    (prepared : PreparedProvider schema layout n M) (slot : Fin (M + P))
    (row : Fin (2 ^ n)) (j : Nat) :
    profileArithmetic (storedRead f prepared slot row j) =
      (storedValue f prepared slot row j,
        arithmeticCost (ArithmeticOp.metadata : ArithmeticOp E)) := by
  by_cases h : j < W + 1 <;>
    simp [storedRead, storedValue, h]

@[no_expose] private def valueCellProgram (f : B →+* E)
    (prepared : PreparedProvider schema layout n M) (beta : E)
    (slot : Fin (M + P)) (row : Fin (2 ^ n)) : OracleComp (ArithmeticSpec E) E := do
  Arithmetic.tick
  let value ← Arithmetic.evalHornerWithReadProgram (storedRead f prepared slot row) (W + 1) beta
  Arithmetic.tick
  return value

private def cellValue (f : B →+* E)
    (prepared : PreparedProvider schema layout n M) (beta : E)
    (slot : Fin (M + P)) (row : Fin (2 ^ n)) : E :=
  Id.run (CPolynomial.Raw.evalHornerM (R := E) (m := Id) (storedValue (E := E) f prepared slot row)
    (fun a b => a * b) (fun a b => a + b) (W + 1) beta)

private theorem profile_valueCellProgram (f : B →+* E)
    (prepared : PreparedProvider schema layout n M) (beta : E)
    (slot : Fin (M + P)) (row : Fin (2 ^ n)) :
    profileArithmetic (valueCellProgram f prepared beta slot row) =
      (cellValue f prepared beta slot row,
        fun kind => if kind = .add then W else if kind = .mul then W
          else if kind = .metadata then W + 3 else 0) := by
  simp only [valueCellProgram, profileArithmetic_bind, profileArithmetic_tick]
  rw [Arithmetic.profileArithmetic_evalHornerWithReadProgram
    (storedRead f prepared slot row) (storedValue f prepared slot row)
    (fun _ => arithmeticCost (ArithmeticOp.metadata : ArithmeticOp E)) (W + 1) beta
    (fun i _ => profile_storedRead f prepared slot row i)]
  dsimp only
  simp only [profileArithmetic_pure]
  apply Prod.ext
  · rfl
  · funext kind
    cases kind <;>
      simp [Arithmetic.hornerCost, Arithmetic.hornerStepCost,
        arithmeticCost, ArithmeticOp.costKind, Nat.add_comm, Nat.add_left_comm]

/-- Construct compressed value tables once using direct Horner reads of stored base coefficients. -/
@[no_expose] def compressedValuesProgram (f : B →+* E)
    (prepared : PreparedProvider schema layout n M) (beta : E) :
    OracleComp (ArithmeticSpec E) (Vector (CMlPolynomialEval E n) (M + P)) :=
  Vector.ofFnM fun slot => Vector.ofFnM fun row => valueCellProgram f prepared beta slot row


omit [Inv E] [DecidableEq E] in
private theorem cellValue_eq_fingerprint (f : B →+* E)
    (prepared : PreparedProvider schema layout n M) (beta : E)
    (slot : Fin (M + P)) (row : Fin (2 ^ n)) :
    cellValue f prepared beta slot row =
      schema.fingerprint f beta (prepared.keyRows[slot.val].get row) := by
  let coeffs : Vector E (W + 1) := Vector.ofFn fun j =>
    f (prepared.coefficientColumns[slot.val][j.val].get row)
  have hread (j : Nat) (hj : j < W + 1) :
      storedValue f prepared slot row j = coeffs.toArray[j]?.getD 0 := by
    simp [storedValue, hj, coeffs]
  have hvalue : cellValue f prepared beta slot row =
      CPolynomial.Raw.evalHornerSeeded beta coeffs.toArray := by
    unfold cellValue CPolynomial.Raw.evalHornerSeeded
    simp only [Vector.size_toArray]
    exact CPolynomial.Raw.evalHornerM_congr_read (m := Id) _ _ _ _ _ _ hread
  rw [hvalue, CPolynomial.Raw.evalHornerSeeded_toArray_eq_sum,
    TaggedTuple.Schema.fingerprint_eq_sum_coefficient]
  apply Finset.sum_congr rfl
  intro j _
  simp only [coeffs, Vector.getElem_ofFn]
  rw [prepared.coefficients slot j row]

@[no_expose] private def markedValue (x : E) : OracleComp (ArithmeticSpec E) E := do
  Arithmetic.tick
  return x

private theorem profile_markedValue (x : E) : profileArithmetic (markedValue x) =
    (x, arithmeticCost (ArithmeticOp.metadata : ArithmeticOp E)) := by
  simp [markedValue]

@[no_expose] private def weightCellProgram (f : B →+* E) (mu : Vector (CMlPolynomialEval B n) P)
    (slot : Fin M ⊕ Fin P) (row : Fin (2 ^ n)) : OracleComp (ArithmeticSpec E) E :=
  match slot with
  | .inl _ => do
    let one ← markedValue (1 : E)
    markedValue one
  | .inr p => do
    let zero ← markedValue (0 : E)
    let mapped ← markedValue (f (mu[p.val].get row))
    let neg ← Arithmetic.sub zero mapped
    markedValue neg.val

private def weightColumn (f : B →+* E) (mu : Vector (CMlPolynomialEval B n) P)
    (slot : Fin M ⊕ Fin P) : CMlPolynomialEval E n :=
  slot.elim (fun _ => Vector.replicate (2 ^ n) 1)
    (fun p => Vector.map (fun b => -f b) mu[p.val])

private def weightCellCost (slot : Fin M ⊕ Fin P) : ArithmeticCost := fun kind =>
  match slot with
  | .inl _ => if kind = .metadata then 2 else 0
  | .inr _ => if kind = .metadata then 3 else if kind = .sub then 1 else 0

private theorem profile_weightCellProgram (f : B →+* E)
    (mu : Vector (CMlPolynomialEval B n) P) (slot : Fin M ⊕ Fin P) (row : Fin (2 ^ n)) :
    profileArithmetic (weightCellProgram f mu slot row) =
      ((weightColumn f mu slot).get row, weightCellCost slot) := by
  cases slot with
  | inl q =>
    simp only [weightCellProgram, profileArithmetic_bind, profile_markedValue]
    apply Prod.ext
    · simp [weightColumn, Vector.get_eq_getElem]
    · funext kind
      cases kind <;> simp [arithmeticCost, ArithmeticOp.costKind, weightCellCost]
  | inr p =>
    simp only [weightCellProgram, profileArithmetic_bind, profile_markedValue,
      profileArithmetic_sub]
    apply Prod.ext
    · simp [weightColumn, Vector.get_eq_getElem]
    · funext kind
      cases kind <;> simp [arithmeticCost, ArithmeticOp.costKind, weightCellCost]

/-- Materialize unit query weights and the actual subtractions of mapped table multiplicities. -/
@[no_expose] def compressedWeightsProgram (f : B →+* E) (mu : Vector (CMlPolynomialEval B n) P) :
    OracleComp (ArithmeticSpec E) (Vector (CMlPolynomialEval E n) (M + P)) :=
  Vector.ofFnM fun column : Fin (M + P) =>
    Vector.ofFnM fun row => weightCellProgram f mu (finSumFinEquiv.symm column) row

/-- Signed weights issue PN subtractions and markers for constants, base reads and output stores. -/
theorem profileArithmetic_compressedWeightsProgram (f : B →+* E)
    (mu : Vector (CMlPolynomialEval B n) P) :
    profileArithmetic (compressedWeightsProgram (M := M) f mu) =
      (Vector.ofFn (fun column => (finSumFinEquiv.symm column).elim
        (fun _ => Vector.replicate (2 ^ n) 1)
        (fun p => Vector.map (fun b => -f b) mu[p.val])),
        fun kind => if kind = .sub then P * 2 ^ n
          else if kind = .metadata then 2 * M * 2 ^ n + 3 * P * 2 ^ n else 0) := by
  have hcol (slot : Fin M ⊕ Fin P) :
      profileArithmetic (Vector.ofFnM fun row => weightCellProgram f mu slot row) =
        (weightColumn f mu slot, fun kind => 2 ^ n * weightCellCost slot kind) := by
    have h := profileArithmetic_ofFnM_uniform
      (fun row => weightCellProgram f mu slot row)
      (fun row => (weightColumn f mu slot).get row) (weightCellCost slot)
      (fun row => profile_weightCellProgram f mu slot row)
    simpa only [Vector.get_eq_getElem, Vector.ofFn_getElem] using h
  rw [compressedWeightsProgram, profileArithmetic_ofFnM _ _ _ (fun i => hcol _)]
  congr 1
  funext kind
  rw [Fin.sum_univ_add]
  cases kind <;>
    simp [weightCellCost, finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
      Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
private theorem profile_compressedValues_raw (f : B →+* E)
    (prepared : PreparedProvider schema layout n M) (beta : E) :
    profileArithmetic (compressedValuesProgram f prepared beta) =
      (Vector.ofFn fun slot => Vector.ofFn fun row => cellValue f prepared beta slot row,
        fun kind => if kind = .add then (M + P) * 2 ^ n * W
          else if kind = .mul then (M + P) * 2 ^ n * W
          else if kind = .metadata then (M + P) * 2 ^ n * (W + 3) else 0) := by
  rw [compressedValuesProgram]
  have hcol (slot : Fin (M + P)) := profileArithmetic_ofFnM_uniform
    (fun row => valueCellProgram f prepared beta slot row)
    (fun row => cellValue f prepared beta slot row)
    (fun kind => if kind = .add then W else if kind = .mul then W
      else if kind = .metadata then W + 3 else 0)
    (fun row => profile_valueCellProgram f prepared beta slot row)
  rw [profileArithmetic_ofFnM_uniform _ _ _ hcol]
  apply Prod.ext
  · rfl
  · funext kind
    cases kind <;> simp [Nat.mul_assoc]
/-- Each value row uses W multiplications/additions and W+3 designated nonfield-site markers. -/
theorem profileArithmetic_compressedValuesProgram (f : B →+* E)
    (prepared : PreparedProvider schema layout n M) (beta : E) :
    profileArithmetic (compressedValuesProgram f prepared beta) =
      (Vector.ofFn fun slot => prepared.fingerprintData f beta (finSumFinEquiv.symm slot),
        fun kind => if kind = .add then (M + P) * 2 ^ n * W
          else if kind = .mul then (M + P) * 2 ^ n * W
          else if kind = .metadata then (M + P) * 2 ^ n * (W + 3) else 0) := by
  rw [profile_compressedValues_raw]
  congr 1
  apply Vector.ext
  intro slot hslot
  apply Vector.ext
  intro row hrow
  simpa [PreparedProvider.fingerprintData, PreparedProvider.keyData,
    Vector.get_eq_getElem] using
    cellValue_eq_fingerprint f prepared beta ⟨slot, hslot⟩ ⟨row, hrow⟩
/-- Read the two materialized E-table families by their typed value/weight and column indices. -/
def compressedData (cache : Vector (Vector (CMlPolynomialEval E n) (M + P)) 2) :
    Fin 2 × Fin (M + P) → CMlPolynomialEval E n := fun i => cache[i.1.val][i.2.val]

/-- Eagerly construct both compressed values and signed weights with the selected programs. -/
@[no_expose] def compressedTablesProgram (f : B →+* E)
    (prepared : PreparedProvider schema layout n M) (beta : E)
    (mu : Vector (CMlPolynomialEval B n) P) :
    OracleComp (ArithmeticSpec E) (Vector (Vector (CMlPolynomialEval E n) (M + P)) 2) := do
  let values ← compressedValuesProgram f prepared beta
  let weights ← compressedWeightsProgram (M := M) f mu
  return #v[values, weights]

/-- Exact executed E requests and designated nonfield-site markers of eager tuple compression. -/
def compressionCost (n M P W : Nat) : ArithmeticCost := fun kind => match kind with
  | .add | .mul => (M + P) * 2 ^ n * W
  | .sub => P * 2 ^ n
  | .metadata => (M + P) * 2 ^ n * (W + 3) + 2 * M * 2 ^ n + 3 * P * 2 ^ n
  | _ => 0

/-- All nine coordinates include weight construction and value/weight output-cell markers. -/
theorem profileArithmetic_compressedTablesProgram (f : B →+* E)
    (prepared : PreparedProvider schema layout n M) (beta : E)
    (mu : Vector (CMlPolynomialEval B n) P) :
    profileArithmetic (compressedTablesProgram f prepared beta mu) =
      (#v[Vector.ofFn (fun slot => prepared.fingerprintData f beta (finSumFinEquiv.symm slot)),
        Vector.ofFn (fun column => (finSumFinEquiv.symm column).elim
          (fun _ => Vector.replicate (2 ^ n) 1)
          (fun p => Vector.map (fun b => -f b) mu[p.val]))],
        compressionCost n M P W) := by
  simp only [compressedTablesProgram, profileArithmetic_bind,
    profileArithmetic_compressedValuesProgram, profileArithmetic_compressedWeightsProgram,
    profileArithmetic_pure]
  apply Prod.ext
  · rfl
  · funext kind
    cases kind <;> simp [compressionCost, Nat.add_assoc]

/-- The actual selected cache program supplies exactly the reference weighted Boolean data. -/
theorem simulateQ_compressedTablesProgram (f : B →+* E)
    (prepared : PreparedProvider schema layout n M) (beta : E)
    (mu : Vector (CMlPolynomialEval B n) P) :
    compressedData (simulateQ arithmeticAnswer (compressedTablesProgram f prepared beta mu)) =
      prepared.weightedData f beta mu := by
  rw [← profileArithmetic_fst, profileArithmetic_compressedTablesProgram]
  funext i
  rcases i with ⟨kind, slot⟩
  fin_cases kind
  · simp [compressedData, PreparedProvider.weightedData, Logup.Lookup.weightedData]
  · simp [compressedData, PreparedProvider.weightedData, Logup.Lookup.weightedData,
      CMlPolynomialEval.map, Vector.map_map, Function.comp_def]
end Logup.Lookup.Tuple
