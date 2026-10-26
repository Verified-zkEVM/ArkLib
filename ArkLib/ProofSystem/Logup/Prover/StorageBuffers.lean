/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ProofSystem.Logup.Prover.Storage
public import ArkLib.ProofSystem.Logup.Prover.ArithmeticRound
public import ArkLib.ToCompPoly.Univariate.ArithmeticNormalization
public import ArkLib.ToCompPoly.Univariate.Size

/-!
# Logical contents of named construction and coefficient buffers

The censuses distinguish three builders. Standard vector and array loops push into prefixes;
List.mapTR builds a reverse accumulator; certifiedMap retains certified heads and a returned
list suffix before certifiedOfFn converts the final list to an array. Their invariants are
proved separately. Fin/index positions and list/array roles are not coefficient positions.

Coefficient bounds follow the selected affine-left convolution, streamed groups/rows and single
final normalization. Completed buffers have a 96(ell+4) allowance; their declared old/new
construction roles have the separate conservative allowance 256(ell+4). Fixed-height preparation,
private folds, fast-basis initialization and the pinned dense source evaluator have their own
inventories. Source evalMle is not the private optimized fold and does not build a basis table.

These are declared named-container payload censuses. They may count aliases more than once and
assert no heap peak, allocator capacity, physical sharing, compiler stack/closure layout, garbage
collection or all-historical-allocation bound. Supplied getter/embedding/backend representations
and additional workspace remain explicit allowances in a complete ledger. The combined retained,
input, public-context and simultaneous-workspace inventory is a separate consumer.
-/

@[expose] public section

open CompPoly CPolynomial OracleComp OracleSpec
namespace Logup.Prover.Storage.Buffers
variable {R : Type*}

/-- Count scalar coefficient positions across the declared array roles. -/
def cells (buffers : List (Raw R)) : Nat := (buffers.map Array.size).sum

/-- A common coefficient width bounds the payload of an actual finite buffer list. -/
theorem cells_le (buffers : List (Raw R)) (width : Nat)
    (h : ∀ p ∈ buffers, p.size ≤ width) : cells buffers ≤ buffers.length * width := by
  induction buffers with
  | nil => simp [cells]
  | cons p ps ih =>
    have hp := h p (by simp)
    have ht := ih (by intro q hq; exact h q (by simp [hq]))
    simp only [cells, List.map_cons, List.sum_cons, List.length_cons]
    change p.size + cells ps ≤ _
    simp only [Nat.add_mul, Nat.one_mul]
    omega

/-- Coefficient positions in an actual list of raw numerator/denominator records. -/
def pairCells (pairs : List (FractionPair (Raw R))) : Nat :=
  (pairs.map fun pair => pair.numerator.size + pair.denominator.size).sum

/-- Each freshly bound pair has two padded coefficients in either component. -/
theorem pairCells_le (pairs : List (FractionPair (Raw R)))
    (h : ∀ pair ∈ pairs, pair.numerator.size ≤ 2 ∧ pair.denominator.size ≤ 2) :
    pairCells pairs ≤ 4 * pairs.length := by
  unfold pairCells
  calc
    _ ≤ (pairs.map (fun _ => 4)).sum := List.sum_le_sum (by
      intro pair hp
      have := h pair hp
      omega)
    _ = 4 * pairs.length := by simp [Nat.mul_comm]

/-- The group mapper's actual reverse-accumulator output preserves both fresh-component bounds. -/
theorem pairCells_mapTR_loop_le {A : Type*} (f : A → FractionPair (Raw R))
    (remaining : List A) (acc : List (FractionPair (Raw R))) (N : Nat)
    (hlen : acc.length + remaining.length ≤ N)
    (hacc : ∀ pair ∈ acc, pair.numerator.size ≤ 2 ∧ pair.denominator.size ≤ 2)
    (hnew : ∀ input ∈ remaining,
      (f input).numerator.size ≤ 2 ∧ (f input).denominator.size ≤ 2) :
    pairCells (List.mapTR.loop f remaining acc) ≤ 4 * N := by
  have hw : ∀ pair ∈ List.mapTR.loop f remaining acc,
      pair.numerator.size ≤ 2 ∧ pair.denominator.size ≤ 2 := by
    intro pair hpair
    rw [List.mapTR_loop_eq] at hpair
    rcases List.mem_append.mp hpair with ha | hn
    · exact hacc pair (List.mem_reverse.mp ha)
    · rcases List.mem_map.mp hn with ⟨input, hi, rfl⟩
      exact hnew input hi
  have h := pairCells_le (List.mapTR.loop f remaining acc) hw
  rw [List.mapTR_loop_eq] at h ⊢
  simp only [List.length_append, List.length_reverse, List.length_map] at h
  exact h.trans (Nat.mul_le_mul_left 4 hlen)

/-- Old/new pair-map reverse prefixes and the final list fit the expanded group-input allowance. -/
theorem pairMapBuilderCells_le {A : Type*} (f : A → FractionPair (Raw R))
    (head : A) (remaining : List A) (acc : List (FractionPair (Raw R))) (N : Nat)
    (hlen : acc.length + (head :: remaining).length ≤ N)
    (hacc : ∀ pair ∈ acc, pair.numerator.size ≤ 2 ∧ pair.denominator.size ≤ 2)
    (hnew : ∀ input ∈ head :: remaining,
      (f input).numerator.size ≤ 2 ∧ (f input).denominator.size ≤ 2) :
    pairCells acc + pairCells (f head :: acc) +
      pairCells (List.mapTR.loop f (head :: remaining) acc) ≤ 12 * N := by
  have ha := (pairCells_le acc hacc).trans
    (Nat.mul_le_mul_left 4 (show acc.length ≤ N by simp only [List.length_cons] at hlen; omega))
  have hn := pairCells_le (f head :: acc) (by
    intro pair hpair
    rcases List.mem_cons.mp hpair with rfl | hpair
    · exact hnew head (by simp)
    · exact hacc pair hpair)
  have hn' := hn.trans (Nat.mul_le_mul_left 4 (show (f head :: acc).length ≤ N by
    simp only [List.length_cons] at hlen ⊢
    omega))
  have ho := pairCells_mapTR_loop_le f (head :: remaining) acc N hlen hacc hnew
  omega

/-- The mapped input and the active suffix of the reversed fold have distinct list roles.
The right fold's standard implementation consumes this one reversed suffix through foldlM. -/
def groupPairBufferCells (pairs : List (FractionPair (Raw R))) (processed : Nat) : Nat :=
  pairCells pairs + pairCells (pairs.reverse.drop processed)

/-- The actual mapped group and active reversed suffix use at most eight cells per occurrence. -/
theorem groupPairBufferCells_le (pairs : List (FractionPair (Raw R))) (processed ell : Nat)
    (hlen : pairs.length ≤ ell)
    (h : ∀ pair ∈ pairs, pair.numerator.size ≤ 2 ∧ pair.denominator.size ≤ 2) :
    groupPairBufferCells pairs processed ≤ 8 * ell := by
  have hp := pairCells_le pairs h
  have hs := pairCells_le (pairs.reverse.drop processed) (by
    intro pair hpair
    exact h pair (List.mem_reverse.mp (List.mem_of_mem_drop hpair)))
  simp only [List.length_drop, List.length_reverse] at hs
  unfold groupPairBufferCells
  omega

/-- Lists used by actual selected coefficient operators carry their own Fin/index positions. -/
def roundIndexScratch (rows K ell : Nat) : Nat := 2 * rows + 2 * K + 5 * (ell + 4) + 32

/-- The row index list, group index list, reversed group suffix and coefficient-builder indices
are separate from the E coefficients and from their container headers. -/
theorem roundIndexScratch_components_le (rows K ell : Nat) (processed : Nat) :
    rows + K + 2 * ell + (ell + 4) +
      ((List.finRange (ell + 4)).drop processed).length + min processed (ell + 4) + 16 ≤
      roundIndexScratch rows K ell := by
  simp only [roundIndexScratch, List.length_drop, List.length_finRange]
  omega

/-- The selected List.mapTR output consists of the reversed old accumulator followed by
mapped remaining inputs; these are list roles, not Array.ofFnM prefixes. -/
theorem cells_mapTR_loop_le {A : Type*} (f : A → Raw R) (remaining : List A)
    (acc : List (Raw R)) (N width : Nat) (hlen : acc.length + remaining.length ≤ N)
    (hacc : ∀ row ∈ acc, row.size ≤ width)
    (hnew : ∀ input ∈ remaining, (f input).size ≤ width) :
    cells (List.mapTR.loop f remaining acc) ≤ N * width := by
  have hw : ∀ row ∈ List.mapTR.loop f remaining acc, row.size ≤ width := by
    intro row hrow
    rw [List.mapTR_loop_eq] at hrow
    rcases List.mem_append.mp hrow with ha | hn
    · exact hacc row (List.mem_reverse.mp ha)
    · rcases List.mem_map.mp hn with ⟨input, hi, rfl⟩
      exact hnew input hi
  have h := cells_le (List.mapTR.loop f remaining acc) width hw
  rw [List.mapTR_loop_eq] at h
  simp only [List.length_append, List.length_reverse, List.length_map] at h
  rw [List.mapTR_loop_eq]
  exact h.trans (Nat.mul_le_mul_right width hlen)

/-- Old/new reverse accumulators and actual final List.mapTR output are counted independently. -/
theorem cells_listMap_step_le {A : Type*} (f : A → Raw R) (head : A) (remaining : List A)
    (acc : List (Raw R)) (N width : Nat)
    (hlen : acc.length + (head :: remaining).length ≤ N)
    (hacc : ∀ row ∈ acc, row.size ≤ width)
    (hnew : ∀ input ∈ head :: remaining, (f input).size ≤ width) :
    cells acc + cells (f head :: acc) + cells (List.mapTR.loop f (head :: remaining) acc) ≤
      3 * N * width := by
  have ha := cells_le acc width hacc
  have hn := cells_le (f head :: acc) width (by
    intro row hrow
    rcases List.mem_cons.mp hrow with rfl | hrow
    · exact hnew head (by simp)
    · exact hacc row hrow)
  have ho := cells_mapTR_loop_le f (head :: remaining) acc N width hlen hacc hnew
  have ha' := ha.trans (Nat.mul_le_mul_right width (show acc.length ≤ N by
    simp only [List.length_cons] at hlen
    omega))
  have hn' := hn.trans (Nat.mul_le_mul_right width (show (f head :: acc).length ≤ N by
    simp only [List.length_cons] at hlen ⊢
    omega))
  have he : 3 * N * width = N * width + N * width + N * width := by ring
  omega

/-- The pure standard array builder's exact decreasing-counter size invariant. -/
theorem ofFn_go_size {N : Nat} (f : Fin N → R) (acc : Array R)
    (remaining : Nat) (h : remaining ≤ N) :
    (Array.ofFn.go f acc remaining h).size = acc.size + remaining := by
  induction remaining generalizing acc with
  | zero => rfl
  | succ remaining ih => simp [Array.ofFn.go, ih, Nat.add_comm, Nat.add_left_comm]

/-- Old and next standard builder prefixes together with the full result, by logical positions. -/
def pushBuilderCells (acc : Array R) (next : R) (result : Array R) : Nat :=
  acc.size + (acc.push next).size + result.size

/-- The actual standard monadic vector loop carries acc.size=i; a successful branch has i<N. -/
theorem pushBuilderCells_le {N i : Nat} (acc : Array R) (next : R) (result : Vector R N)
    (hsize : acc.size = i) (hi : i < N) :
    pushBuilderCells acc next result.toArray ≤ 3 * N := by
  simp only [pushBuilderCells, Array.size_push, Vector.size_toArray]
  omega

/-- Pure ofFn uses the distinct invariant acc.size+remaining=N. -/
theorem ofFn_pushBuilderCells_le {N remaining : Nat} (f : Fin N → R)
    (acc : Array R) (next : R) (h : remaining ≤ N)
    (hsize : acc.size + remaining = N) (hr : 0 < remaining) :
    pushBuilderCells acc next (Array.ofFn.go f acc remaining h) ≤ 3 * N := by
  simp only [pushBuilderCells, Array.size_push, ofFn_go_size]
  omega

/-- Count actual array payload positions in a standard outer coefficient-row builder. -/
def rowArrayCells (rows : Array (Raw R)) : Nat := (rows.toList.map Array.size).sum

/-- A row-width invariant bounds every standard outer-builder prefix. -/
theorem rowArrayCells_le (rows : Array (Raw R)) (width : Nat)
    (h : ∀ row ∈ rows.toList, row.size ≤ width) :
    rowArrayCells rows ≤ rows.size * width := by
  unfold rowArrayCells
  calc
    _ ≤ (rows.toList.map (fun _ => width)).sum :=
      List.sum_le_sum (by intro row hrow; exact h row hrow)
    _ = rows.size * width := by simp

/-- A real push step preserves the per-row payload invariant. -/
theorem rowWidth_push (rows : Array (Raw R)) (next : Raw R) (width : Nat)
    (h : ∀ row ∈ rows.toList, row.size ≤ width) (hn : next.size ≤ width) :
    ∀ row ∈ (rows.push next).toList, row.size ≤ width := by
  intro row hrow
  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hrow
  rcases hrow with hrow | rfl
  · exact h row hrow
  · exact hn

/-- The standard outer vector loop counts old/new prefixes and output payloads separately. -/
theorem rowPushBuilderCells_le {N i : Nat} (rows : Array (Raw R)) (next : Raw R)
    (result : Vector (Raw R) N) (width : Nat) (hsize : rows.size = i) (hi : i < N)
    (hrows : ∀ row ∈ rows.toList, row.size ≤ width) (hn : next.size ≤ width)
    (hout : ∀ row ∈ result.toList, row.size ≤ width) :
    rowArrayCells rows + rowArrayCells (rows.push next) + rowArrayCells result.toArray ≤
      3 * N * width := by
  have h₁ := rowArrayCells_le rows width hrows
  have h₂ := rowArrayCells_le (rows.push next) width (rowWidth_push rows next width hrows hn)
  have h₃ := rowArrayCells_le result.toArray width hout
  have hi₁ : rows.size ≤ N := by omega
  have hi₂ : (rows.push next).size ≤ N := by simp; omega
  have h₁' := h₁.trans (Nat.mul_le_mul_right width hi₁)
  have h₂' := h₂.trans (Nat.mul_le_mul_right width hi₂)
  simp only [Vector.size_toArray] at h₃
  have hm : 3 * N * width = N * width + N * width + N * width := by ring
  rw [hm]
  omega

/-- Standard push loops preserve the increasing cursor invariant, including the mapM reference. -/
theorem ascendingPushInvariant {i : Nat} (acc : Array R) (next : R) (h : acc.size = i) :
    (acc.push next).size = i + 1 := by simp [h]

/-- Pure ofFn and extract use decreasing counters; their prefix invariant is different from
Vector.ofFnM's increasing index, although each successful step pushes exactly one value. -/
theorem decreasingPushInvariant {remaining total : Nat} (acc : Array R) (next : R)
    (h : acc.size + remaining = total) (hr : 0 < remaining) :
    (acc.push next).size + (remaining - 1) = total ∧
      acc.size ≤ total ∧ (acc.push next).size ≤ total := by
  simp only [Array.size_push]
  omega

/-- The actual pure extract loop cannot exceed its original prefix plus remaining copy budget. -/
theorem extract_loop_size_le (input : Array R) (remaining cursor : Nat) (acc : Array R) :
    (Array.extract.loop input remaining cursor acc).size ≤ acc.size + remaining := by
  induction remaining generalizing cursor acc with
  | zero => simp [Array.extract.loop]
  | succ remaining ih =>
    rw [Array.extract.loop]
    split
    · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (cursor + 1) (acc.push input[cursor])
    · simp

/-- Actual mapped input/output sizes and its old/new reference prefixes are bounded separately.
The compiler's overwrite implementation has the same number of logical buffer positions. -/
theorem map_pushBuilderCells_le {A : Type*} (input : Array A) (f : A → R)
    (acc : Array R) (next : R) (i : Nat) (hsize : acc.size = i) (hi : i < input.size) :
    pushBuilderCells acc next (input.map f) ≤ 3 * input.size := by
  simp only [pushBuilderCells, Array.size_push, Array.size_map]
  omega


/-- Bound affine rows and the helper-get list are separate logical payload roles. -/
def affineInputCells {T K : Nat} (denominator weight : Vector (Raw R) T)
    (helper : Vector (Raw R) K) (kernel : Raw R) : Nat :=
  rowArrayCells denominator.toArray + rowArrayCells weight.toArray +
    rowArrayCells helper.toArray + kernel.size + cells ((List.finRange K).map helper.get)

section Certified
variable {F : Type} [CommRing F] [Inv F] [DecidableEq F]

/-- Recursive certifiedMap retains certified head values and one current returned list suffix.
Only certifiedOfFn's final conversion produces an array; this census does not posit a push loop. -/
def certifiedBuilderCells {N : Nat} (f : Fin N → F)
    (step : (i : Fin N) → OracleComp (ArithmeticSpec F) {a : F // a = f i})
    (processed : Nat) : Nat :=
  (((List.finRange N).take processed).map f).length +
    (simulateQ arithmeticAnswer (Arithmetic.certifiedMap f step
      ((List.finRange N).drop processed))).val.length +
    (simulateQ arithmeticAnswer (Arithmetic.certifiedOfFn f step)).val.size

/-- Certification identifies the retained heads, actual returned suffix and actual output sizes. -/
theorem certifiedBuilderCells_le {N : Nat} (f : Fin N → F)
    (step : (i : Fin N) → OracleComp (ArithmeticSpec F) {a : F // a = f i}) (processed : Nat) :
    certifiedBuilderCells f step processed ≤ 3 * N := by
  have hs := (simulateQ arithmeticAnswer (Arithmetic.certifiedMap f step
    ((List.finRange N).drop processed))).property
  have ho := (simulateQ arithmeticAnswer (Arithmetic.certifiedOfFn f step)).property
  simp only [certifiedBuilderCells, hs, ho, List.length_map, List.length_take,
    List.length_drop, List.length_finRange, Array.size_ofFn]
  omega

/-- Fin/index positions of the original explicit list, its active suffix and pending call sites
are separate from coefficient payloads and from array/container counts. -/
def certifiedBuilderIndexCells (N processed : Nat) : Nat :=
  (List.finRange N).length + ((List.finRange N).drop processed).length + min processed N

/-- Recursive list-builder index roles are linear in the declared coefficient width. -/
theorem certifiedBuilderIndexCells_le (N processed : Nat) :
    certifiedBuilderIndexCells N processed ≤ 3 * N := by
  simp only [certifiedBuilderIndexCells, List.length_finRange, List.length_drop]
  omega

/-- Actual selected affine-row callbacks return two coefficients, supplying the push invariant. -/
theorem affineRowsProgram_output_size {r m : Nat}
    (tables : Vector (CMlPolynomialEval F (r + 1)) m) (j : Fin (2 ^ r)) (i : Fin m) :
    (Vector.get
      (simulateQ arithmeticAnswer
        (Logup.Prover.RoundCoefficients.affineRowsProgram tables j)) i).size = 2 := by
  rw [← profileArithmetic_fst, Logup.Prover.RoundCoefficients.profileArithmetic_affineRowsProgram]
  simp only [Vector.get_eq_getElem, Vector.getElem_ofFn, CMlPolynomialEval.size_affineRow]

/-- Actual selected row binders and the helper-get list have the exact completed input census. -/
theorem actualAffineInputCells_eq {r T K : Nat}
    (denominator weight : Vector (CMlPolynomialEval F (r + 1)) T)
    (helper : Vector (CMlPolynomialEval F (r + 1)) K)
    (kernel : CMlPolynomialEval F (r + 1)) (j : Fin (2 ^ r)) :
    affineInputCells
      (simulateQ arithmeticAnswer (Logup.Prover.RoundCoefficients.affineRowsProgram denominator j))
      (simulateQ arithmeticAnswer (Logup.Prover.RoundCoefficients.affineRowsProgram weight j))
      (simulateQ arithmeticAnswer (Logup.Prover.RoundCoefficients.affineRowsProgram helper j))
      (simulateQ arithmeticAnswer (CMlPolynomialEval.affineRowProgram kernel j)).val =
        4 * T + 4 * K + 2 := by
  have hrows {m : Nat} (tables : Vector (CMlPolynomialEval F (r + 1)) m) :
      simulateQ arithmeticAnswer (Logup.Prover.RoundCoefficients.affineRowsProgram tables j) =
        Vector.ofFn (fun i => CMlPolynomialEval.affineRow (tables.get i) j) := by
    rw [← profileArithmetic_fst,
      Logup.Prover.RoundCoefficients.profileArithmetic_affineRowsProgram]
  have hb := (simulateQ arithmeticAnswer (CMlPolynomialEval.affineRowProgram kernel j)).property
  simp only [hrows, hb, affineInputCells, rowArrayCells, cells, Vector.toList_toArray,
    Vector.toList_ofFn, List.map_map, List.map_ofFn, Function.comp_def, Vector.get_eq_getElem,
    Vector.getElem_ofFn, CMlPolynomialEval.size_affineRow]
  simp only [List.ofFn_const, List.map_const', List.length_finRange, List.sum_replicate,
    Nat.nsmul_eq_mul]
  omega

end Certified

/-- Scalar positions in actual fixed-height table objects retained by an outer array builder. -/
def tableArrayCells {N : Nat} (tables : Array (Vector R N)) : Nat :=
  (tables.toList.map fun table => table.toArray.size).sum

/-- Fixed-height inner vectors determine every outer prefix payload exactly. -/
theorem tableArrayCells_eq {N : Nat} (tables : Array (Vector R N)) :
    tableArrayCells tables = tables.size * N := by simp [tableArrayCells]

/-- Any successful standard outer-builder branch preserves the declared table height. -/
theorem tablePushBuilderCells_le {N columns i : Nat} (tables : Array (Vector R N))
    (next : Vector R N) (result : Vector (Vector R N) columns)
    (hsize : tables.size = i) (hi : i < columns) :
    tableArrayCells tables + tableArrayCells (tables.push next) +
      tableArrayCells result.toArray ≤ 3 * columns * N := by
  simp only [tableArrayCells_eq, Array.size_push, Vector.size_toArray]
  have ho := Nat.mul_le_mul_right N (show tables.size ≤ columns by omega)
  have hn := Nat.mul_le_mul_right N (show tables.size + 1 ≤ columns by omega)
  have he : 3 * columns * N = columns * N + columns * N + columns * N := by ring
  omega

section TableAlgorithms
variable {R : Type} [CommRing R]

/-- Census actual values arrays traversed by the pinned source evaluator, including dimension0.
Its evalMleStep is the existing two-product source backend, not the private optimized fold. -/
def backendValuesCells : {n : Nat} → CMlPolynomialEval R n → Vector R n → Nat
  | 0, values, _ => values.toArray.size
  | _n + 1, values, x => values.toArray.size +
      backendValuesCells (CMlPolynomialEval.evalMleStep values x.head) x.tail

/-- Actual source evaluation traverses exactly the geometric sequence of table sizes. -/
theorem backendValuesCells_eq {n : Nat} (values : CMlPolynomialEval R n) (x : Vector R n) :
    backendValuesCells values x = 2 * 2 ^ n - 1 := by
  induction n with
  | zero => simp [backendValuesCells]
  | succ n ih =>
    simp only [backendValuesCells, Vector.size_toArray, ih, pow_succ]
    have hp : 0 < (2 : Nat) ^ n := Nat.pow_pos (by decide)
    omega

/-- Explicit fast initialization has its own tail-first basis arrays, separate from source MLE. -/
def basisValuesCells : {n : Nat} → Vector R n → Nat
  | 0, x => (CMlPolynomialEval.lagrangeBasisFast x).toArray.size
  | _n + 1, x => basisValuesCells x.tail +
      (CMlPolynomialEval.lagrangeBasisFast x).toArray.size

/-- The explicitly selected fast builder has the separate geometric basis-array census. -/
theorem basisValuesCells_eq {n : Nat} (x : Vector R n) :
    basisValuesCells x = 2 * 2 ^ n - 1 := by
  induction n with
  | zero => simp [basisValuesCells]
  | succ n ih =>
    simp only [basisValuesCells, Vector.size_toArray, ih, pow_succ]
    have hp : 0 < (2 : Nat) ^ n := Nat.pow_pos (by decide)
    omega

/-- Completed evaluator arrays, old/new builder prefixes, actual coordinate tails and bounded
local scalar operands. The original BASE table is a separate input payload role. -/
def denseBackendCells {n : Nat} (values : CMlPolynomialEval R n) (x : Vector R n) : Nat :=
  3 * backendValuesCells values x + 3 * coordinateTailCells x + 8 * (n + 1)

/-- Values arrays, copy/build prefixes, coordinate tails and local slots are geometrically
bounded. -/
theorem denseBackendCells_le {n : Nat} (values : CMlPolynomialEval R n) (x : Vector R n) :
    denseBackendCells values x ≤ 20 * 2 ^ n := by
  have hp := coordinateTailCells_le x
  have hn : n + 1 ≤ 2 ^ n := Nat.succ_le_of_lt Nat.lt_two_pow_self
  simp only [denseBackendCells, backendValuesCells_eq]
  omega

/-- Actual fast-basis array/tail roles and old/new lambda-builder prefixes. The resulting lambda
is already counted in State; zero-round default control omits this entire initializer. -/
def basisBuilderCells {n K : Nat} (x : Vector R n) (lambda : Vector R K) : Nat :=
  if n = 0 then 0 else
    3 * basisValuesCells x + 3 * coordinateTailCells x + 2 * lambda.toArray.size + 8 * (n + 1)

/-- Zero native rounds omit the complete initializer, even for a nonempty batching vector. -/
theorem basisBuilderCells_zero {K : Nat} (x : Vector R 0) (lambda : Vector R K) :
    basisBuilderCells x lambda = 0 := by simp [basisBuilderCells]

/-- Positive-round basis and lambda builders obey their declared geometric allowance. -/
theorem basisBuilderCells_le {n K : Nat} (x : Vector R n) (lambda : Vector R K) :
    basisBuilderCells x lambda ≤ 20 * 2 ^ n + 2 * K := by
  have hp := coordinateTailCells_le x
  have hn : n + 1 ≤ 2 ^ n := Nat.succ_le_of_lt Nat.lt_two_pow_self
  simp only [basisBuilderCells, basisValuesCells_eq, Vector.size_toArray]
  split_ifs <;> omega
end TableAlgorithms

variable {E : Type} {n T K : Nat}

/-- Preparation's completed/old/new outer D/W/H builder roles, current column builders and local
primitive operands. Denominators are constructed directly; no full mapped value matrix exists. -/
def prepareBuilderCells (prepared : Logup.Prover.Prepared E T K n) : Nat :=
  3 * preparedCells prepared + 6 * 2 ^ n + 24

/-- The actual prepared dimensions close the nested-builder census without a mapped-value matrix. -/
theorem prepareBuilderCells_eq (prepared : Logup.Prover.Prepared E T K n) :
    prepareBuilderCells prepared = (6 * T + 3 * K + 6) * 2 ^ n + 24 := by
  rw [prepareBuilderCells, preparedCells_eq]
  ring

/-- Every nonterminal measured fold has fixed-height outer outputs and one active row builder.
Old input states and repeated lambda fields are counted by the retained-history census. -/
def foldBuilderCells (next : Logup.Prover.State E T K n) : Nat :=
  3 * stateTableCells next + 3 * 2 ^ n + 8

/-- The actual next-state dimensions close the outer and active-column fold census. -/
theorem foldBuilderCells_eq (next : Logup.Prover.State E T K n) :
    foldBuilderCells next = (6 * T + 3 * K + 6) * 2 ^ n + 8 := by
  rw [foldBuilderCells, stateTableCells_eq]
  ring

/-- Scalar multiplicity casting uses nested outer/row builders of the actual reshaped output.
There is no additional flat BASE cast-array in the selected multiplicities constructor. -/
def multiplicityBuilderCells {B : Type} (mu : Vector (CMlPolynomialEval B n) K) : Nat :=
  3 * familyCells mu + 3 * 2 ^ n + 8

/-- Outer and active-row casting roles are bounded from the actual reshaped output. -/
theorem multiplicityBuilderCells_eq {B : Type} (mu : Vector (CMlPolynomialEval B n) K) :
    multiplicityBuilderCells mu = (3 * K + 3) * 2 ^ n + 8 := by
  rw [multiplicityBuilderCells, familyCells_eq]
  ring

/-- Natural histogram old/next vectors stay dense over all table positions. Cursor, old count,
incremented count and bounds are reserved separately from the witness's Fin positions. -/
def histogramBuilderCells {L U : Nat} (indices : Vector (Fin U) L)
    (current next : Vector Nat U) : Nat :=
  (Vector.histogram indices).toArray.size + current.toArray.size + next.toArray.size + 8

/-- Every current/next dense counter vector keeps its declared natural domain. -/
theorem histogramBuilderCells_eq {L U : Nat} (indices : Vector (Fin U) L)
    (current next : Vector Nat U) : histogramBuilderCells indices current next = 3 * U + 8 := by
  simp only [histogramBuilderCells, Vector.size_toArray]
  omega

/-- One temporary signed BASE column and its old/new mapping roles, plus a current source column.
The caller supplies any additional representation/workspace of an opaque getter or embedding. -/
def signedBaseColumnCells {B : Type*} (source result : Vector B (2 ^ n)) : Nat :=
  source.toArray.size + 3 * result.toArray.size + 8

/-- Current source and signed-column roles retain the actual common row height. -/
theorem signedBaseColumnCells_eq {B : Type*} (source result : Vector B (2 ^ n)) :
    signedBaseColumnCells source result = 4 * 2 ^ n + 8 := by simp [signedBaseColumnCells]; omega

/-- Actual bound answers of a terminal weighted-source query. -/
def sourceAnswerCells {R : Type*} (values weights : Vector R T) (helpers : Vector R K) : Nat :=
  values.toArray.size + weights.toArray.size + helpers.toArray.size

/-- The existing terminal source binds one value and weight per column and one helper per group. -/
theorem sourceAnswerCells_eq {R : Type*} (values weights : Vector R T) (helpers : Vector R K) :
    sourceAnswerCells values weights helpers = 2 * T + K := by
  simp only [sourceAnswerCells, Vector.size_toArray]
  omega

/-- Bound-answer outer builders, buffered tuple Horner coefficients and direct scalar
reconstruction locals. No basis table, sparse polynomial or group-residual array is constructed. -/
def sourceScalarScratch (T K W : Nat) : Nat := 3 * (2 * T + K) + 3 * (W + 1) + 64

/-- Separate answer, coefficient-buffer and scalar-local allowances have the stated closed form. -/
theorem sourceScalarScratch_eq (T K W : Nat) :
    sourceScalarScratch T K W = 6 * T + 3 * K + 3 * W + 67 := by
  unfold sourceScalarScratch
  omega

variable [CommRing R]

/-- Actual partial convolution accumulates shifted scalar multiples in source index order. -/
def convolutionPrefix (p q : Raw R) (indices : List Nat) (acc : Raw R) : Raw R :=
  indices.foldl (fun a j => Raw.addRaw a (Raw.mulPowX j (Raw.smul (p[j]?.getD 0) q))) acc

/-- Every bounded source-index prefix preserves the convolution width invariant. -/
theorem size_convolutionPrefix_le (p q : Raw R) (indices : List Nat) (acc : Raw R)
    (hi : ∀ j ∈ indices, j < p.size) (ha : acc.size ≤ p.size + q.size) :
    (convolutionPrefix p q indices acc).size ≤ p.size + q.size := by
  induction indices generalizing acc with
  | nil => exact ha
  | cons j js ih =>
    apply ih
    · intro i hmem
      exact hi i (by simp [hmem])
    · rw [Raw.size_addRaw, Raw.size_mulPowX, Raw.size_smul]
      apply max_le ha
      have hj := hi j (by simp)
      omega

/-- Named inputs, completed product and old/row/shifted/new/returned convolution fields. -/
def convolutionBuffers (p q : Raw R) : List (Raw R) :=
  [p, q, Raw.mulRaw p q] ++ (List.range p.size).flatMap fun i =>
    [convolutionPrefix p q (List.range i) #[],
      Raw.smul (p[i]?.getD 0) q,
      Raw.mulPowX i (Raw.smul (p[i]?.getD 0) q),
      convolutionPrefix p q (List.range (i + 1)) #[],
      Raw.mulRaw p q]

/-- Each affine-left source row contributes five declared convolution array roles. -/
theorem convolutionBuffers_length (p q : Raw R) :
    (convolutionBuffers p q).length = 3 + 5 * p.size := by
  simpa [convolutionBuffers, List.length_flatMap] using
    (show p.size * 5 + 1 + 1 + 1 = 3 + 5 * p.size by omega)

/-- Every declared convolution field fits the sum of the two input widths. -/
theorem convolutionBuffers_width (p q : Raw R) :
    ∀ a ∈ convolutionBuffers p q, a.size ≤ p.size + q.size := by
  intro a ha
  simp only [convolutionBuffers, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatMap, List.mem_range] at ha
  rcases ha with (rfl|rfl|rfl)|⟨i, hi, ha⟩
  · omega
  · omega
  · exact (Raw.size_mulRaw_le _ _).trans (by omega)
  · rcases ha with rfl|rfl|rfl|rfl|rfl
    · apply size_convolutionPrefix_le
      · intro j hj
        have hji : j < i := List.mem_range.mp hj
        omega
      · simp
    · simp
    · simp only [Raw.size_mulPowX, Raw.size_smul]
      omega
    · apply size_convolutionPrefix_le
      · intro j hj
        have hji : j < i + 1 := List.mem_range.mp hj
        omega
      · simp
    · exact (Raw.size_mulRaw_le _ _).trans (by omega)

/-- An affine-left convolution has at most thirteen named arrays of bounded width. -/
theorem cells_convolutionBuffers_le (p q : Raw R) (ell : Nat)
    (hp : p.size ≤ 2) (hq : q.size ≤ ell + 2) :
    cells (convolutionBuffers p q) ≤ 13 * (ell + 4) := by
  have hw : ∀ a ∈ convolutionBuffers p q, a.size ≤ ell + 4 := by
    intro a ha
    exact (convolutionBuffers_width p q a ha).trans (by omega)
  have h := cells_le (convolutionBuffers p q) (ell + 4) hw
  rw [convolutionBuffers_length] at h
  have hl : 3 + 5 * p.size ≤ 13 := by omega
  exact h.trans (Nat.mul_le_mul_right _ hl)

/-- Actual fresh/current fraction fields, cross-products and returned numerator/denominator. -/
def fractionStepBuffers (fresh acc : FractionPair (Raw R)) : List (Raw R) :=
  [fresh.numerator, fresh.denominator, acc.numerator, acc.denominator,
    Raw.mulRaw fresh.numerator acc.denominator, Raw.mulRaw fresh.denominator acc.numerator,
    (Raw.fractionCombine fresh acc).numerator, (Raw.fractionCombine fresh acc).denominator]

/-- Each of the eight fraction fields has the bounded padded coefficient width. -/
theorem cells_fractionStepBuffers_le (fresh acc : FractionPair (Raw R)) (ell : Nat)
    (hf : fresh.numerator.size ≤ 2 ∧ fresh.denominator.size ≤ 2)
    (ha : acc.numerator.size ≤ ell + 1 ∧ acc.denominator.size ≤ ell + 1) :
    cells (fractionStepBuffers fresh acc) ≤ 8 * (ell + 4) := by
  have hn := Raw.size_mulRaw_le fresh.numerator acc.denominator
  have hc := Raw.size_mulRaw_le fresh.denominator acc.numerator
  have hd := Raw.size_mulRaw_le fresh.denominator acc.denominator
  have hw : ∀ p ∈ fractionStepBuffers fresh acc, p.size ≤ ell + 4 := by
    intro p hp
    simp only [fractionStepBuffers, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · simp only [Raw.fractionCombine, Raw.size_addRaw]
      apply max_le <;> omega
    · simp only [Raw.fractionCombine]
      omega
  simpa [fractionStepBuffers] using cells_le (fractionStepBuffers fresh acc) (ell + 4) hw

/-- Actual fraction fields and subtraction intermediates of one helper residual. -/
def residualStepBuffers (fraction : FractionPair (Raw R)) (helper : Raw R) : List (Raw R) :=
  [fraction.numerator, fraction.denominator, helper,
    Raw.mulRaw helper fraction.denominator, Raw.neg fraction.numerator,
    Raw.subRaw (Raw.mulRaw helper fraction.denominator) fraction.numerator]

/-- The helper product, negated numerator and difference preserve the residual width. -/
theorem cells_residualStepBuffers_le (fraction : FractionPair (Raw R)) (helper : Raw R)
    (ell : Nat) (hf : fraction.numerator.size ≤ ell + 1 ∧
      fraction.denominator.size ≤ ell + 1) (hh : helper.size ≤ 2) :
    cells (residualStepBuffers fraction helper) ≤ 6 * (ell + 4) := by
  have hm := Raw.size_mulRaw_le helper fraction.denominator
  have hn := Raw.size_subRaw (#[] : Raw R) fraction.numerator
  simp only [Raw.subRaw, Raw.size_addRaw, Array.size_empty, max_eq_right (Nat.zero_le _)] at hn
  have hw : ∀ p ∈ residualStepBuffers fraction helper, p.size ≤ ell + 4 := by
    intro p hp
    simp only [residualStepBuffers, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · omega
    · omega
    · omega
    · omega
    · rw [hn]
      omega
    · rw [Raw.size_subRaw]
      apply max_le <;> omega
  simpa [residualStepBuffers] using cells_le (residualStepBuffers fraction helper) (ell + 4) hw

/-- The batch body binds one residual, one scaled residual and the next accumulator. -/
def batchStepBuffers (acc residual : Raw R) (lambda : R) : List (Raw R) :=
  [acc, residual, Raw.smul lambda residual, Raw.addRaw acc (Raw.smul lambda residual)]

/-- One streamed residual and its old/new batch fields have bounded total payload. -/
theorem cells_batchStepBuffers_le (acc residual : Raw R) (lambda : R) (ell : Nat)
    (ha : acc.size ≤ ell + 2) (hr : residual.size ≤ ell + 2) :
    cells (batchStepBuffers acc residual lambda) ≤ 6 * (ell + 4) := by
  have hw : ∀ p ∈ batchStepBuffers acc residual lambda, p.size ≤ ell + 4 := by
    intro p hp
    simp only [batchStepBuffers, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · omega
    · omega
    · simpa using hr.trans (by omega : ell + 2 ≤ ell + 4)
    · rw [Raw.size_addRaw, Raw.size_smul]
      apply max_le <;> omega
  have h := cells_le (batchStepBuffers acc residual lambda) (ell + 4) hw
  change cells (batchStepBuffers acc residual lambda) ≤ 4 * (ell + 4) at h
  exact h.trans (by omega)

/-- One helper-sum step carries only the old, fresh and next affine coefficient arrays. -/
def helperStepBuffers (acc fresh : Raw R) : List (Raw R) := [acc, fresh, Raw.addRaw acc fresh]

/-- Adding affine helper arrays keeps all three named fields affine. -/
theorem cells_helperStepBuffers_le (acc fresh : Raw R) (ell : Nat)
    (ha : acc.size ≤ 2) (hf : fresh.size ≤ 2) :
    cells (helperStepBuffers acc fresh) ≤ 2 * (ell + 4) := by
  simp only [cells, helperStepBuffers, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Raw.size_addRaw]
  omega

/-- Final circuit fields after the streamed batch; the active product is counted separately. -/
def circuitStepBuffers (helperSum batch kernel : Raw R) : List (Raw R) :=
  [helperSum, batch, kernel, Raw.mulRaw kernel batch,
    Raw.addRaw helperSum (Raw.mulRaw kernel batch)]

/-- The completed helper sum, batch and final result fit the circuit width bound. -/
theorem cells_circuitStepBuffers_le (helperSum batch kernel : Raw R) (ell : Nat)
    (hh : helperSum.size ≤ 2) (hb : batch.size ≤ ell + 2) (hk : kernel.size ≤ 2) :
    cells (circuitStepBuffers helperSum batch kernel) ≤ 5 * (ell + 4) := by
  have hm := Raw.size_mulRaw_le kernel batch
  have hw : ∀ p ∈ circuitStepBuffers helperSum batch kernel, p.size ≤ ell + 4 := by
    intro p hp
    simp only [circuitStepBuffers, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · omega
    · omega
    · omega
    · omega
    · rw [Raw.size_addRaw]
      apply max_le <;> omega
  simpa [circuitStepBuffers] using cells_le (circuitStepBuffers helperSum batch kernel)
    (ell + 4) hw

/-- One streamed row-sum step carries old, current-row and next padded arrays. -/
def rowStepBuffers (acc row : Raw R) : List (Raw R) := [acc, row, Raw.addRaw acc row]

/-- The current row and old/new row accumulators retain their common padded width. -/
theorem cells_rowStepBuffers_le (acc row : Raw R) (ell : Nat)
    (ha : acc.size ≤ ell + 3) (hr : row.size ≤ ell + 3) :
    cells (rowStepBuffers acc row) ≤ 4 * (ell + 4) := by
  simp only [cells, rowStepBuffers, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Raw.size_addRaw]
  omega

/-- The selected original-array normalizer returns at most one extracted canonical prefix. -/
def normalizationBuffers (original : Raw R) (result : CPolynomial R) : List (Raw R) :=
  [original, result.val]

/-- Original padded data and one canonical result use at most twice the declared width. -/
theorem cells_normalizationBuffers_le [BEq R] [LawfulBEq R]
    (original : Raw R) (result : CPolynomial R) (ell : Nat)
    (hr : result = CPolynomial.ofArray original) (ho : original.size ≤ ell + 3) :
    cells (normalizationBuffers original result) ≤ 2 * (ell + 4) := by
  have h := CPolynomial.size_ofArray_le original
  subst result
  simp only [cells, normalizationBuffers, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil]
  omega

/-- The three actual fraction products keep the fresh affine component on the left. -/
def fractionProductInputs (fresh acc : FractionPair (Raw R)) : Fin 3 → Raw R × Raw R :=
  ![(fresh.numerator, acc.denominator), (fresh.denominator, acc.numerator),
    (fresh.denominator, acc.denominator)]

/-- Completed fraction fields plus one active product's explicit convolution buffers. -/
def fractionPhaseCells (fresh acc : FractionPair (Raw R)) (which : Fin 3) : Nat :=
  let inputs := fractionProductInputs fresh acc which
  cells (fractionStepBuffers fresh acc) + cells (convolutionBuffers inputs.1 inputs.2)

/-- Every one of the three active products fits the complete fraction-phase allowance. -/
theorem fractionPhaseCells_le (fresh acc : FractionPair (Raw R)) (which : Fin 3) (ell : Nat)
    (hf : fresh.numerator.size ≤ 2 ∧ fresh.denominator.size ≤ 2)
    (ha : acc.numerator.size ≤ ell + 1 ∧ acc.denominator.size ≤ ell + 1) :
    fractionPhaseCells fresh acc which ≤ 21 * (ell + 4) := by
  have hb := cells_fractionStepBuffers_le fresh acc ell hf ha
  have hleft : (fractionProductInputs fresh acc which).1.size ≤ 2 := by
    fin_cases which <;> simp [fractionProductInputs] <;> omega
  have hright : (fractionProductInputs fresh acc which).2.size ≤ ell + 2 := by
    fin_cases which <;> simp [fractionProductInputs] <;> omega
  have hm := cells_convolutionBuffers_le
    (fractionProductInputs fresh acc which).1 (fractionProductInputs fresh acc which).2
    ell hleft hright
  dsimp only [fractionPhaseCells]
  omega

/-- Actual residual subtraction buffers plus the affine-helper-left product workspace. -/
def residualPhaseCells (fraction : FractionPair (Raw R)) (helper : Raw R) : Nat :=
  cells (residualStepBuffers fraction helper) +
    cells (convolutionBuffers helper fraction.denominator)

/-- The residual fields and affine-helper product fit their combined phase allowance. -/
theorem residualPhaseCells_le (fraction : FractionPair (Raw R)) (helper : Raw R) (ell : Nat)
    (hf : fraction.numerator.size ≤ ell + 1 ∧ fraction.denominator.size ≤ ell + 1)
    (hh : helper.size ≤ 2) : residualPhaseCells fraction helper ≤ 19 * (ell + 4) := by
  have hb := cells_residualStepBuffers_le fraction helper ell hf hh
  have hm := cells_convolutionBuffers_le helper fraction.denominator ell hh (by omega)
  unfold residualPhaseCells
  omega

/-- Actual final circuit fields plus the affine-kernel-left product workspace. -/
def circuitPhaseCells (helperSum batch kernel : Raw R) : Nat :=
  cells (circuitStepBuffers helperSum batch kernel) + cells (convolutionBuffers kernel batch)

/-- The final fields and affine-kernel product fit their combined phase allowance. -/
theorem circuitPhaseCells_le (helperSum batch kernel : Raw R) (ell : Nat)
    (hh : helperSum.size ≤ 2) (hb : batch.size ≤ ell + 2) (hk : kernel.size ≤ 2) :
    circuitPhaseCells helperSum batch kernel ≤ 18 * (ell + 4) := by
  have hf := cells_circuitStepBuffers_le helperSum batch kernel ell hh hb hk
  have hm := cells_convolutionBuffers_le kernel batch ell hk hb
  unfold circuitPhaseCells
  omega

/-- Capacity of the declared phase snapshots and their operation-local scalar fields. -/
def streamedPhaseBudget (ell : Nat) : Nat :=
  (8 + 21 + 19 + 6 + 2 + 18 + 4 + 2) * (ell + 4) + (8 + 8 + 8 + 8 + 8 + 8 + 8)

/-- The sum of completed phase allowances is bounded uniformly, including empty groups. -/
theorem streamedPhaseBudget_le (ell : Nat) : streamedPhaseBudget ell ≤ 96 * (ell + 4) := by
  unfold streamedPhaseBudget
  omega

/-- Complete phase-array census plus old/new construction roles for each phase output.
Certified list builders use heads/suffix/toArray invariants; vector builders use actual pushes. -/
def expandedPhaseBudget (ell : Nat) : Nat :=
  3 * (8 + 21 + 19 + 6 + 2 + 18 + 4 + 2) * (ell + 4) + 56

/-- Adding the separately proved construction roles preserves a linear width allowance. -/
theorem expandedPhaseBudget_le (ell : Nat) : expandedPhaseBudget ell ≤ 256 * (ell + 4) := by
  unfold expandedPhaseBudget
  omega

/-- Separate affine input and helper-get list builder roles, plus phase/operator workspace. -/
def roundScalarScratch (T K ell : Nat) : Nat :=
  3 * (4 * T + 4 * K + 2) + expandedPhaseBudget ell

/-- Affine row/list builders and coefficient phases give the stated separate round bound. -/
theorem roundScalarScratch_le (T K ell : Nat) :
    roundScalarScratch T K ell ≤ 12 * T + 12 * K + 6 + 256 * (ell + 4) := by
  have h := expandedPhaseBudget_le ell
  unfold roundScalarScratch
  omega

end Logup.Prover.Storage.Buffers
