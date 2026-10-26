/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Prover.StorageBuffers
import Mathlib.Algebra.Field.ZMod
import Lean.Compiler.IR

/-! # Named buffers of actual builders, affine circuits, normalization and dense table backends -/

open CompPoly CPolynomial OracleComp OracleSpec
open Logup.Prover.Storage Logup.Prover.Storage.Buffers
open Lean Elab Command
namespace LogupStorageBuffersTest

def coefficient (N : Nat) (i : Fin N) : Rat := (i.val + 1 : Nat)
def coefficientStep (N : Nat) (i : Fin N) :
    OracleComp (ArithmeticSpec Rat) {a : Rat // a = coefficient N i} := do
  let value ← Arithmetic.mul (coefficient N i) 1
  pure ⟨value.val, by simpa using value.property⟩

def certified (N processed : Nat) : Nat × Nat :=
  (certifiedBuilderCells (coefficient N) (coefficientStep N) processed,
    certifiedBuilderIndexCells N processed)

example {R : Type*} [Zero R] [BEq R] [LawfulBEq R] (p : Array R) :
    (CPolynomial.ofArray p).val.size ≤ p.size := CPolynomial.size_ofArray_le p

def affine (x y : Rat) : Raw Rat := Raw.affine x y

def listMapProbe (processed : Nat) : List (Raw Rat) :=
  let xs : List Rat := [7, 0, -3, 9]
  List.mapTR.loop (fun a => affine a (a + 1)) (xs.drop processed)
    (((xs.take processed).map fun a => affine a (a + 1)).reverse)

def pairInputs (ell : Nat) : List (FractionPair (Raw Rat)) :=
  (List.range ell).map fun i => ⟨affine (i % 3 : Nat) (i + 1 : Nat),
    affine (if i % 2 = 0 then 0 else 2) (if i % 3 = 0 then 0 else -1)⟩

def fractionProbe (ell : Nat) := Raw.fractionSum (pairInputs ell)

def prepared (n : Nat) :=
  Logup.Prover.State.prepareProgram (RingHom.id Rat) 0 (#v[[0], [1]] : Vector (List (Fin 2)) 2)
    (fun i : Fin 2 × Fin 2 => Vector.ofFn fun u : Fin (2 ^ n) =>
      if i.1 = 0 then (u.val % 3 : Nat) else if i.2 = 0 then (1 : Rat) else -1)

def actualPrepared (n : Nat) := simulateQ arithmeticAnswer (prepared n)

def backendProbe : Nat × Nat × Nat :=
  let values : CMlPolynomialEval Int 3 := #v[0, 7, -3, 9, 2, 0, 11, -5]
  let point : Vector Int 3 := #v[2, -1, 3]
  (backendValuesCells values point, denseBackendCells values point,
    basisBuilderCells point (#v[0, 5] : Vector Int 2))

example : backendProbe = (15, 95, 99) := by
  norm_num [backendProbe, denseBackendCells, basisBuilderCells, backendValuesCells_eq,
    basisValuesCells_eq, coordinateTailCells]
example : denseBackendCells (#v[2] : CMlPolynomialEval Int 0) #v[] = 11 := by decide
example : basisBuilderCells (#v[] : Vector Int 0) (#v[3, 5] : Vector Int 2) = 0 := rfl
example : basisBuilderCells (#v[2] : Vector (ZMod 4) 1) #v[0, 2] = 32 := by
  norm_num [basisBuilderCells, basisValuesCells_eq, coordinateTailCells]
example : denseBackendCells (#v[0, 2] : CMlPolynomialEval (ZMod 4) 1) #v[2] = 28 := by decide

/-- Actual selected affine binders and their helper-get list have a separate exact census. -/
def actualRowInputs : Nat :=
  let initial := simulateQ arithmeticAnswer
    (Logup.Prover.State.startProgram (actualPrepared 2) (![3, 5]) (![1, 0]))
  affineInputCells
    (simulateQ arithmeticAnswer
      (Logup.Prover.RoundCoefficients.affineRowsProgram initial.denominator (0 : Fin 2)))
    (simulateQ arithmeticAnswer
      (Logup.Prover.RoundCoefficients.affineRowsProgram initial.weight (0 : Fin 2)))
    (simulateQ arithmeticAnswer
      (Logup.Prover.RoundCoefficients.affineRowsProgram initial.helper (0 : Fin 2)))
    (simulateQ arithmeticAnswer (CMlPolynomialEval.affineRowProgram initial.kernel (0 : Fin 2))).val

/-- External generic caller with no field or nonzero assumptions on any row. -/
def phaseCaller {R : Type} [CommRing R] (fresh acc : FractionPair (Raw R))
    (which : Fin 3) : Nat := fractionPhaseCells fresh acc which

run_cmd do
  unless (CPolynomial.ofArray (#[0, 7, 0, 0] : Array Nat)).val.size == 2 &&
      (CPolynomial.ofArray (#[0, 0, 0] : Array Nat)).val.size == 0 do
    throwError "minimal Nat/Zero/BEq canonical size fixture changed"
  for N in [0, 1, 2, 7, 32] do
    for processed in List.range (N + 3) do
      unless certified N processed == (2 * N, 2 * N) do
        throwError "recursive certified heads/suffix/output or separate index census changed"
  for processed in List.range 7 do
    unless listMapProbe processed == [affine 7 8, affine 0 1, affine (-3) (-2), affine 9 10] &&
        cells (listMapProbe processed) == 8 do
      throwError "List.mapTR reverse accumulator was confused with a push or certified list builder"
  let input : Array Nat := #[3, 0, 7, 2, 5]
  let f : Nat → Rat := fun a => (a : Rat) - 2
  for i in List.range input.size do
    let acc := (input.extract 0 i).map f
    unless pushBuilderCells acc (f input[i]!) (input.map f) ≤ 3 * input.size do
      throwError "mapped old/new/full logical prefix bound changed"
  unless (Array.extract.loop (#[7, 0, -3, 9, 4] : Array Int) 3 4 #[11, 13]).size == 3 &&
      (Array.extract.loop (#[7, 0, -3, 9, 4] : Array Int) 3 9 #[11, 13]).size == 2 do
    throwError "actual extract loop's short-copy or immediate stop branch changed"
  for ell in List.range 17 do
    let pairs := pairInputs ell
    let fraction := fractionProbe ell
    let fresh : FractionPair (Raw Rat) := ⟨affine 0 1, affine 0 0⟩
    let helper := affine 0 3
    let residual := Raw.subRaw (Raw.mulRaw helper fraction.denominator) fraction.numerator
    let batch := Raw.smul (2 : Rat) residual
    let kernel := affine (-1) 3
    let row := Raw.addRaw helper (Raw.mulRaw kernel batch)
    let normalized := simulateQ arithmeticAnswer (Arithmetic.canonicalRawProgram row)
    unless fraction.numerator.size ≤ ell + 1 && fraction.denominator.size ≤ ell + 1 &&
        residual.size ≤ ell + 2 && batch.size ≤ ell + 2 && row.size ≤ ell + 3 do
      throwError "actual padded affine fraction/residual/row width invariant failed"
    for which in List.finRange 3 do
      unless fractionPhaseCells fresh fraction which ≤ 21 * (ell + 4) do
        throwError "one of the three fresh-affine-left product workspaces exceeded its bound"
    for processed in List.range (ell + 2) do
      unless groupPairBufferCells pairs processed ≤ 8 * ell do
        throwError "actual mapped/reversed group roles exceeded their occurrence bound"
    unless residualPhaseCells fraction helper ≤ 19 * (ell + 4) &&
        cells (batchStepBuffers #[] residual 2) ≤ 6 * (ell + 4) &&
        cells (helperStepBuffers #[] helper) ≤ 2 * (ell + 4) &&
        circuitPhaseCells helper batch kernel ≤ 18 * (ell + 4) &&
        cells (rowStepBuffers #[] row) ≤ 4 * (ell + 4) &&
        cells (normalizationBuffers row normalized.val) ≤ 2 * (ell + 4) do
      throwError "a concrete completed-buffer phase exceeded its declared census"
    unless normalized.val.val.size ≤ row.size && streamedPhaseBudget ell ≤ 96 * (ell + 4) &&
        expandedPhaseBudget ell ≤ 256 * (ell + 4) &&
        roundScalarScratch 3 2 ell ≤ 12 * 3 + 12 * 2 + 6 + 256 * (ell + 4) do
      throwError "single-prefix normalization or completed/expanded phase distinction changed"
  for n in [0, 1, 2, 3] do
    let ready := actualPrepared n
    unless prepareBuilderCells ready == 24 * 2 ^ n + 24 do
      throwError "actual pole-inclusive prepare fields and active-column builders lost their census"
  unless actualRowInputs == 18 do
    throwError "actual completed affine input18 was confused with expanded builder input54"
  unless backendProbe == (15, 95, 99) do
    throwError "dense source arrays and separately selected fast-basis arrays were conflated"
  let counts : Vector Nat 3 := #v[1, 2, 0]
  unless histogramBuilderCells (#v[0, 1, 1] : Vector (Fin 3) 3) counts counts == 17 do
    throwError "histogram old/next counters were confused with cast BASE multiplicities"
  let mu : Vector (CMlPolynomialEval Int 1) 2 := #v[#v[2, 0], #v[1, 0]]
  unless multiplicityBuilderCells mu == 26 &&
      signedBaseColumnCells (n := 1) (#v[2, 0] : Vector Int 2) #v[-2, 0] == 16 do
    throwError "reshape builders or temporary signed BASE columns were omitted"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``CPolynomial.size_ofArray_le, ``cells_le, ``ofFn_go_size,
      ``pushBuilderCells_le, ``ofFn_pushBuilderCells_le, ``rowArrayCells_le,
      ``rowWidth_push, ``rowPushBuilderCells_le, ``ascendingPushInvariant,
      ``decreasingPushInvariant, ``extract_loop_size_le, ``map_pushBuilderCells_le,
      ``certifiedBuilderCells_le, ``certifiedBuilderIndexCells_le,
      ``affineRowsProgram_output_size, ``actualAffineInputCells_eq, ``cells_mapTR_loop_le,
      ``cells_listMap_step_le,
      ``tableArrayCells_eq, ``tablePushBuilderCells_le, ``backendValuesCells_eq,
      ``basisValuesCells_eq, ``denseBackendCells_le, ``basisBuilderCells_le,
      ``prepareBuilderCells_eq, ``foldBuilderCells_eq, ``multiplicityBuilderCells_eq,
      ``histogramBuilderCells_eq, ``signedBaseColumnCells_eq, ``sourceAnswerCells_eq,
      ``sourceScalarScratch_eq, ``size_convolutionPrefix_le, ``convolutionBuffers_width,
      ``cells_convolutionBuffers_le, ``cells_fractionStepBuffers_le,
      ``cells_residualStepBuffers_le, ``cells_batchStepBuffers_le, ``cells_helperStepBuffers_le,
      ``cells_circuitStepBuffers_le, ``cells_rowStepBuffers_le, ``cells_normalizationBuffers_le,
      ``groupPairBufferCells_le, ``pairCells_mapTR_loop_le, ``pairMapBuilderCells_le,
      ``roundIndexScratch_components_le, ``fractionPhaseCells_le,
      ``residualPhaseCells_le, ``circuitPhaseCells_le, ``streamedPhaseBudget_le,
      ``expandedPhaseBudget_le, ``roundScalarScratch_le] do
    unless (← collectAxioms name).all allowed.contains do
      throwError "unexpected named-buffer axiom: {name}"
  for name in #[``phaseCaller, ``certified, ``listMapProbe, ``fractionProbe, ``actualPrepared,
      ``backendProbe, ``actualRowInputs, ``roundScalarScratch, ``prepareBuilderCells,
      ``backendValuesCells,
      ``basisBuilderCells, ``normalizationBuffers] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "missing executable named-buffer caller IR: {name}"
  logInfo "builder cases, coefficient phases and separate init/backend cells passed"

end LogupStorageBuffersTest
