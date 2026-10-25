/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.ProofSystem.Logup.Prover.ArithmeticRound

/-!
# Primitive profiles of streamed round-message construction

The recurrences follow the executed row programs, actual padded accumulator widths, and the one
final reverse-scan normalization. General bounds retain the sum of squared group lengths and a
batch-width contribution. Only a positive group-length partition with at most T groups specializes
to a constant multiple of `2 ^ r * T * ell` per supported profile coordinate.

These are request counts of the same program selected by `messageByProgram`. Source openings,
initialization, table folding, allocations and machine runtime are separate costs.
-/

@[expose] public section

open CompPoly CPolynomial CMlPolynomialEval OracleComp OracleSpec
namespace Logup.Prover.RoundCoefficients
variable {F : Type} [CommRing F] [Inv F] [DecidableEq F] {r T K : ℕ}

/-- A row binds each adjacent input pair once, then executes the coefficient circuit. -/
theorem profileArithmetic_rowProgram (groups : Vector (List (Fin T)) K)
    (lambda : Vector F K) (denominator weight : Vector (CMlPolynomialEval F (r + 1)) T)
    (helper : Vector (CMlPolynomialEval F (r + 1)) K)
    (kernel : CMlPolynomialEval F (r + 1)) (j : Fin (2 ^ r)) :
    (profileArithmetic (rowProgram groups lambda denominator weight helper kernel j)).2 =
      (fun kind => (2 * T + K + 1) *
        (if kind = .valueRead then 2 else if kind = .sub then 1 else 0)) +
      (profileArithmetic (CoefficientCircuit.circuitProgram groups (affineRow kernel j) lambda
        (Vector.ofFn fun i => affineRow (denominator.get i) j)
        (Vector.ofFn fun i => affineRow (weight.get i) j)
        (Vector.ofFn fun k => affineRow (helper.get k) j))).2 := by
  simp only [rowProgram, profileArithmetic_bind, profileArithmetic_affineRowsProgram,
    profileArithmetic_certified_val]
  funext kind
  cases kind <;> simp [profileArithmetic_affineRowProgram, Nat.add_mul,
    Nat.add_assoc, Nat.two_mul]

/-- An empty row traversal makes no additional requests. -/
theorem profileArithmetic_coefficientsFromProgram_nil
    (groups : Vector (List (Fin T)) K) (lambda : Vector F K)
    (denominator weight : Vector (CMlPolynomialEval F (r + 1)) T)
    (helper : Vector (CMlPolynomialEval F (r + 1)) K)
    (kernel : CMlPolynomialEval F (r + 1)) (acc : Raw F) :
    (profileArithmetic
      (coefficientsFromProgram [] groups lambda denominator weight helper kernel acc)).2 = 0 := rfl

/-- Each streamed row charges its actual circuit and the selected padded addition. -/
theorem profileArithmetic_coefficientsFromProgram_cons (j : Fin (2 ^ r))
    (rows : List (Fin (2 ^ r))) (groups : Vector (List (Fin T)) K) (lambda : Vector F K)
    (denominator weight : Vector (CMlPolynomialEval F (r + 1)) T)
    (helper : Vector (CMlPolynomialEval F (r + 1)) K)
    (kernel : CMlPolynomialEval F (r + 1)) (acc : Raw F) :
    (profileArithmetic
      (coefficientsFromProgram (j :: rows) groups lambda denominator weight helper kernel acc)).2 =
      arithmeticCost (ArithmeticOp.metadata : ArithmeticOp F) +
      (profileArithmetic (rowProgram groups lambda denominator weight helper kernel j)).2 +
      (profileArithmetic
        (Arithmetic.addRaw acc (row groups lambda denominator weight helper kernel j))).2 +
      (profileArithmetic (coefficientsFromProgram rows groups lambda denominator weight helper
        kernel (Raw.addRaw acc (row groups lambda denominator weight helper kernel j)))).2 := by
  simp only [coefficientsFromProgram, List.foldlM_cons, profileArithmetic_bind,
    profileArithmetic_tick, profileArithmetic_pure, profileArithmetic_certified_val,
    profileArithmetic_rowProgram_fst, add_zero, add_assoc]
  rw [profileArithmetic_rowProgram_fst]

/-- The complete traversal adds one initial control step to its Boolean suffix rows. -/
theorem profileArithmetic_coefficientsProgram (groups : Vector (List (Fin T)) K)
    (lambda : Vector F K) (denominator weight : Vector (CMlPolynomialEval F (r + 1)) T)
    (helper : Vector (CMlPolynomialEval F (r + 1)) K)
    (kernel : CMlPolynomialEval F (r + 1)) :
    (profileArithmetic (coefficientsProgram groups lambda denominator weight helper kernel)).2 =
      arithmeticCost (ArithmeticOp.metadata : ArithmeticOp F) +
      (profileArithmetic (coefficientsFromProgram (List.finRange (2 ^ r)) groups lambda
        denominator weight helper kernel #[])).2 := by
  simp [coefficientsProgram, profileArithmetic_bind]

/-- Message construction adds exactly one final reverse-scan normalization. -/
theorem profileArithmetic_messageProgram (groups : Vector (List (Fin T)) K)
    (lambda : Vector F K) (denominator weight : Vector (CMlPolynomialEval F (r + 1)) T)
    (helper : Vector (CMlPolynomialEval F (r + 1)) K)
    (kernel : CMlPolynomialEval F (r + 1)) :
    (profileArithmetic (messageProgram groups lambda denominator weight helper kernel)).2 =
      (profileArithmetic (coefficientsProgram groups lambda denominator weight helper kernel)).2 +
      (profileArithmetic (Arithmetic.canonicalRawProgram
        (coefficients groups lambda denominator weight helper kernel))).2 := by
  simp only [messageProgram, profileArithmetic_bind, profileArithmetic_map,
    Arithmetic.profileArithmetic_canonicalRawProgram]
  rw [profileArithmetic_coefficientsProgram_fst]

/-- A general per-coordinate row bound retains squared group lengths and batch widths. -/
def rowBudget (groups : Vector (List (Fin T)) K) (ell : ℕ) : ℕ :=
  ((List.finRange K).map fun k => 100 * ((groups.get k).length + 1) ^ 2).sum +
    20 * (K + 1) * (ell + 3) + (4 * T + 2 * K + 2)

/-- Every supported row coordinate is bounded without coverage or nonempty-group premises. -/
theorem profileArithmetic_rowProgram_le (groups : Vector (List (Fin T)) K)
    (lambda : Vector F K) (denominator weight : Vector (CMlPolynomialEval F (r + 1)) T)
    (helper : Vector (CMlPolynomialEval F (r + 1)) K)
    (kernel : CMlPolynomialEval F (r + 1)) (j : Fin (2 ^ r)) (ell : ℕ)
    (hgroups : ∀ k, (groups.get k).length ≤ ell) (kind : ArithmeticCostKind) :
    (profileArithmetic (rowProgram groups lambda denominator weight helper kernel j)).2 kind ≤
      if kind = .add ∨ kind = .mul ∨ kind = .sub ∨ kind = .coefficientRead ∨
        kind = .metadata ∨ kind = .valueRead then rowBudget groups ell else 0 := by
  have hc := CoefficientCircuit.profileArithmetic_circuitProgram_le groups (affineRow kernel j)
    lambda (Vector.ofFn fun i => affineRow (denominator.get i) j)
    (Vector.ofFn fun i => affineRow (weight.get i) j)
    (Vector.ofFn fun k => affineRow (helper.get k) j) ell hgroups
    (by simp) (by simp) (by simp) (by simp) kind
  rw [profileArithmetic_rowProgram]
  cases kind <;>
    simp only [Pi.add_apply, rowBudget, reduceCtorEq, or_true, or_false, or_self,
      ite_true, ite_false, Nat.mul_zero, Nat.mul_one] at hc ⊢ <;> omega

/-- Streaming bounded-width rows adds linear per-row accumulation work. -/
theorem profileArithmetic_coefficientsFromProgram_le (rows : List (Fin (2 ^ r)))
    (groups : Vector (List (Fin T)) K) (lambda : Vector F K)
    (denominator weight : Vector (CMlPolynomialEval F (r + 1)) T)
    (helper : Vector (CMlPolynomialEval F (r + 1)) K)
    (kernel : CMlPolynomialEval F (r + 1)) (acc : Raw F) (ell : ℕ)
    (hgroups : ∀ k, (groups.get k).length ≤ ell) (hacc : acc.size ≤ ell + 3)
    (kind : ArithmeticCostKind) :
    (profileArithmetic
      (coefficientsFromProgram rows groups lambda denominator weight helper kernel acc)).2 kind ≤
      if kind = .add ∨ kind = .mul ∨ kind = .sub ∨ kind = .coefficientRead ∨
        kind = .metadata ∨ kind = .valueRead then
        rows.length * (rowBudget groups ell + 2 * (ell + 4)) else 0 := by
  induction rows generalizing acc with
  | nil =>
    rw [profileArithmetic_coefficientsFromProgram_nil]
    cases kind <;> simp
  | cons j rows ih =>
    have hr := profileArithmetic_rowProgram_le groups lambda denominator weight helper kernel
      j ell hgroups kind
    have hs := size_row_le groups lambda denominator weight helper kernel j ell hgroups
    have hn : (Raw.addRaw acc (row groups lambda denominator weight helper kernel j)).size ≤
        ell + 3 := by
      rw [Raw.size_addRaw]
      exact max_le hacc hs
    have ht := ih _ hn
    have hm := max_le hacc hs
    rw [profileArithmetic_coefficientsFromProgram_cons]
    cases kind <;>
      simp only [Pi.add_apply, Arithmetic.profileArithmetic_addRaw, arithmeticCost,
        ArithmeticOp.costKind, List.length_cons, reduceCtorEq, or_true, or_false, or_self,
        ite_true, ite_false, Nat.add_mul, Nat.mul_add] at hr ht ⊢ <;> omega

/-- The Boolean traversal visits exactly `2 ^ r` suffix rows. -/
theorem profileArithmetic_coefficientsProgram_le (groups : Vector (List (Fin T)) K)
    (lambda : Vector F K) (denominator weight : Vector (CMlPolynomialEval F (r + 1)) T)
    (helper : Vector (CMlPolynomialEval F (r + 1)) K)
    (kernel : CMlPolynomialEval F (r + 1)) (ell : ℕ)
    (hgroups : ∀ k, (groups.get k).length ≤ ell) (kind : ArithmeticCostKind) :
    (profileArithmetic
      (coefficientsProgram groups lambda denominator weight helper kernel)).2 kind ≤
      if kind = .add ∨ kind = .mul ∨ kind = .sub ∨ kind = .coefficientRead ∨
        kind = .metadata ∨ kind = .valueRead then
        2 ^ r * (rowBudget groups ell + 2 * (ell + 4)) + 1 else 0 := by
  have h := profileArithmetic_coefficientsFromProgram_le (List.finRange (2 ^ r)) groups lambda
    denominator weight helper kernel #[] ell hgroups (by simp) kind
  rw [profileArithmetic_coefficientsProgram]
  cases kind <;>
    simp only [Pi.add_apply, arithmeticCost, ArithmeticOp.costKind, List.length_finRange,
      reduceCtorEq, or_true, or_false, or_self, ite_true, ite_false] at h ⊢ <;> omega

/-- Canonical messages add a linear final scan to the general row envelope. -/
theorem profileArithmetic_messageProgram_le (groups : Vector (List (Fin T)) K)
    (lambda : Vector F K) (denominator weight : Vector (CMlPolynomialEval F (r + 1)) T)
    (helper : Vector (CMlPolynomialEval F (r + 1)) K)
    (kernel : CMlPolynomialEval F (r + 1)) (ell : ℕ)
    (hgroups : ∀ k, (groups.get k).length ≤ ell) (kind : ArithmeticCostKind) :
    (profileArithmetic (messageProgram groups lambda denominator weight helper kernel)).2 kind ≤
      if kind = .add ∨ kind = .mul ∨ kind = .sub ∨ kind = .coefficientRead ∨
        kind = .metadata ∨ kind = .valueRead ∨ kind = .eq then
        2 ^ r * (rowBudget groups ell + 2 * (ell + 4)) + ell + 5 else 0 := by
  have hc := profileArithmetic_coefficientsProgram_le groups lambda denominator weight helper
    kernel ell hgroups kind
  have ht := Arithmetic.profileArithmetic_canonicalRawProgram_le
    (coefficients groups lambda denominator weight helper kernel) kind
  have hs := size_coefficients_le groups lambda denominator weight helper kernel ell hgroups
  rw [profileArithmetic_messageProgram]
  cases kind <;>
    simp only [Pi.add_apply, reduceCtorEq, or_true, or_false, or_self, ite_true, ite_false]
      at hc ht ⊢ <;> omega

/-- Only final normalization tests coefficients for zero. -/
theorem profileArithmetic_messageProgram_eq_le (groups : Vector (List (Fin T)) K)
    (lambda : Vector F K) (denominator weight : Vector (CMlPolynomialEval F (r + 1)) T)
    (helper : Vector (CMlPolynomialEval F (r + 1)) K)
    (kernel : CMlPolynomialEval F (r + 1)) (ell : ℕ)
    (hgroups : ∀ k, (groups.get k).length ≤ ell) :
    (profileArithmetic (messageProgram groups lambda denominator weight helper kernel)).2 .eq ≤
      ell + 3 := by
  have hc := profileArithmetic_coefficientsProgram_le groups lambda denominator weight helper
    kernel ell hgroups .eq
  have ht := Arithmetic.profileArithmetic_canonicalRawProgram_le
    (coefficients groups lambda denominator weight helper kernel) .eq
  have hs := size_coefficients_le groups lambda denominator weight helper kernel ell hgroups
  rw [profileArithmetic_messageProgram]
  simp at hc ht
  change ((_ : ℕ) + _) ≤ _
  omega

/-- Every row reads exactly two endpoints per retained input table, independently of groups. -/
theorem profileArithmetic_rowProgram_valueRead (groups : Vector (List (Fin T)) K)
    (lambda : Vector F K) (denominator weight : Vector (CMlPolynomialEval F (r + 1)) T)
    (helper : Vector (CMlPolynomialEval F (r + 1)) K)
    (kernel : CMlPolynomialEval F (r + 1)) (j : Fin (2 ^ r)) :
    (profileArithmetic (rowProgram groups lambda denominator weight helper kernel j)).2
      .valueRead = 4 * T + 2 * K + 2 := by
  let ell := Finset.univ.sup (fun k : Fin K => (groups.get k).length)
  have hgroups (k : Fin K) : (groups.get k).length ≤ ell :=
    Finset.le_sup (f := fun k : Fin K => (groups.get k).length) (Finset.mem_univ k)
  have hc := CoefficientCircuit.profileArithmetic_circuitProgram_le groups (affineRow kernel j)
    lambda (Vector.ofFn fun i => affineRow (denominator.get i) j)
    (Vector.ofFn fun i => affineRow (weight.get i) j)
    (Vector.ofFn fun k => affineRow (helper.get k) j) ell hgroups
    (by simp) (by simp) (by simp) (by simp) .valueRead
  rw [profileArithmetic_rowProgram]
  simp at hc
  simp only [Pi.add_apply, reduceCtorEq, ite_true]
  omega

/-- Endpoint reads follow the number of selected rows, including repeats. -/
theorem profileArithmetic_coefficientsFromProgram_valueRead (rows : List (Fin (2 ^ r)))
    (groups : Vector (List (Fin T)) K) (lambda : Vector F K)
    (denominator weight : Vector (CMlPolynomialEval F (r + 1)) T)
    (helper : Vector (CMlPolynomialEval F (r + 1)) K)
    (kernel : CMlPolynomialEval F (r + 1)) (acc : Raw F) :
    (profileArithmetic
      (coefficientsFromProgram rows groups lambda denominator weight helper kernel acc)).2
      .valueRead = rows.length * (4 * T + 2 * K + 2) := by
  induction rows generalizing acc with
  | nil => rw [profileArithmetic_coefficientsFromProgram_nil]; simp
  | cons j rows ih =>
    rw [profileArithmetic_coefficientsFromProgram_cons]
    have hr := profileArithmetic_rowProgram_valueRead groups lambda denominator weight helper
      kernel j
    have ht := ih (Raw.addRaw acc (row groups lambda denominator weight helper kernel j))
    simp only [Pi.add_apply, arithmeticCost, ArithmeticOp.costKind, reduceCtorEq, ite_false,
      Arithmetic.profileArithmetic_addRaw, hr, ht, List.length_cons, Nat.add_mul]
    omega

/-- Canonicalization adds no table reads to the complete Boolean traversal. -/
theorem profileArithmetic_messageProgram_valueRead (groups : Vector (List (Fin T)) K)
    (lambda : Vector F K) (denominator weight : Vector (CMlPolynomialEval F (r + 1)) T)
    (helper : Vector (CMlPolynomialEval F (r + 1)) K)
    (kernel : CMlPolynomialEval F (r + 1)) :
    (profileArithmetic (messageProgram groups lambda denominator weight helper kernel)).2
      .valueRead = 2 ^ r * (4 * T + 2 * K + 2) := by
  have ht := Arithmetic.profileArithmetic_canonicalRawProgram_le
    (coefficients groups lambda denominator weight helper kernel) .valueRead
  have hrows := profileArithmetic_coefficientsFromProgram_valueRead (List.finRange (2 ^ r))
    groups lambda denominator weight helper kernel #[]
  rw [profileArithmetic_messageProgram, profileArithmetic_coefficientsProgram]
  simp only [Pi.add_apply, arithmeticCost, ArithmeticOp.costKind, reduceCtorEq, ite_false,
    zero_add, hrows, List.length_finRange]
  simp at ht
  omega

/-- A positive group-length partition specializes the general row envelope. -/
theorem rowBudget_le_of_length_sum (groups : Vector (List (Fin T)) K) (ell : ℕ)
    (hT : 0 < T) (hell : 0 < ell) (hK : K ≤ T)
    (hgroups : ∀ k, (groups.get k).length ≤ ell)
    (htotal : ((List.finRange K).map fun k => (groups.get k).length).sum = T) :
    rowBudget groups ell ≤ 600 * T * ell := by
  have hs : ((List.finRange K).map fun k => 100 * ((groups.get k).length + 1) ^ 2).sum ≤
      100 * (ell + 2) * T + 100 * K := by
    calc
      _ ≤ ((List.finRange K).map fun k =>
          100 * (ell + 2) * (groups.get k).length + 100).sum := by
        apply List.sum_le_sum
        intro k _
        have hb := Nat.mul_le_mul_right (groups.get k).length (hgroups k)
        nlinarith
      _ = 100 * (ell + 2) * T + 100 * K := by
        simp [List.sum_map_add, List.sum_map_mul_left, htotal, Nat.mul_comm]
  have ha : K + 1 ≤ 2 * T := by omega
  have hb : ell + 3 ≤ 4 * ell := by omega
  have hm := Nat.mul_le_mul ha hb
  have hpos : 0 < T * ell := Nat.mul_pos hT hell
  have hmul := Nat.mul_le_mul_left T (show 1 ≤ ell by omega)
  unfold rowBudget
  nlinarith

/-- Under positive partition bounds, each supported coordinate is at most `1000 * 2 ^ r * T *
ell`. -/
theorem profileArithmetic_messageProgram_le_of_length_sum
    (groups : Vector (List (Fin T)) K) (lambda : Vector F K)
    (denominator weight : Vector (CMlPolynomialEval F (r + 1)) T)
    (helper : Vector (CMlPolynomialEval F (r + 1)) K)
    (kernel : CMlPolynomialEval F (r + 1)) (ell : ℕ)
    (hT : 0 < T) (hell : 0 < ell) (hK : K ≤ T)
    (hgroups : ∀ k, (groups.get k).length ≤ ell)
    (htotal : ((List.finRange K).map fun k => (groups.get k).length).sum = T)
    (kind : ArithmeticCostKind) :
    (profileArithmetic (messageProgram groups lambda denominator weight helper kernel)).2 kind ≤
      if kind = .add ∨ kind = .mul ∨ kind = .sub ∨ kind = .coefficientRead ∨
        kind = .metadata ∨ kind = .valueRead ∨ kind = .eq then
        1000 * 2 ^ r * T * ell else 0 := by
  have hc := profileArithmetic_messageProgram_le groups lambda denominator weight helper kernel
    ell hgroups kind
  have hb := rowBudget_le_of_length_sum groups ell hT hell hK hgroups htotal
  have hpos : 0 < T * ell := Nat.mul_pos hT hell
  have hmul := Nat.mul_le_mul_right ell (show 1 ≤ T by omega)
  have hU : rowBudget groups ell + 2 * (ell + 4) ≤ 610 * (T * ell) := by
    simp only [Nat.mul_assoc] at hb
    omega
  have hm := Nat.mul_le_mul_left (2 ^ r) hU
  have hrows : 1 ≤ 2 ^ r := by
    have hzero : 0 < (2 : ℕ) ^ r := by positivity
    omega
  have hg := Nat.mul_le_mul_right (T * ell) hrows
  split_ifs at hc ⊢ <;> nlinarith

end Logup.Prover.RoundCoefficients
