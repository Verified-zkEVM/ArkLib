/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Elias Judin
-/

import CompPoly.Multilinear.Semantics
import Mathlib.Data.Nat.Log

/-!
# Polynomial stacking

This file defines polynomial blocks, their concatenated layout, selector
points, and the alignment conditions used by selector evaluation.

## References

* [leanVM specification, Section 5.1](https://github.com/leanEthereum/leanVM/releases)
-/

namespace Stacking

open scoped BigOperators

open CompPoly

variable {R : Type*}

/-- A single stacking block: an evaluation vector `Pᵢ : CMlPolynomialEval R νᵢ`
together with its number of variables `νᵢ`, packaged as a dependent pair so a
list of blocks may mix different sizes. -/
abbrev Block (R : Type*) : Type _ := Σ m : ℕ, CMlPolynomialEval R m

/-- The number of stored cells `2 ^ νᵢ` of a block. -/
def Block.cells (b : Block R) : ℕ := 2 ^ b.1

/-- Total number of concatenated cells `∑ᵢ 2 ^ νᵢ` across all blocks. -/
def totalCells (bs : List (Block R)) : ℕ := (bs.map Block.cells).sum

/-- Number of variables of the stacked polynomial: `clog₂` of the total number
of cells, i.e. the smallest `ν` with `2 ^ ν ≥ ∑ᵢ 2 ^ νᵢ`. -/
def stackVars (bs : List (Block R)) : ℕ := Nat.clog 2 (totalCells bs)

/-- Offset of block `i`: `oᵢ = ∑_{i' < i} 2 ^ ν_{i'}`, the starting position of
block `i` in the concatenation. -/
def offset (bs : List (Block R)) (i : ℕ) : ℕ := ((bs.take i).map Block.cells).sum

/-- Value stored at global position `j` of the (unpadded) concatenation: walk
the blocks accumulating their sizes, returning `Pᵢ[j - oᵢ]` for the block that
contains `j`, and `0` once `j` runs past the concatenation (zero padding). -/
def cellAt [Zero R] : List (Block R) → ℕ → R
  | [], _ => 0
  | b :: rest, j =>
      if h : j < 2 ^ b.1 then b.2[j]'h else cellAt rest (j - 2 ^ b.1)

/-- Descending-size concatenation with zero padding:
`stack [P₁, …, Pₙ] = P₁ ++ ⋯ ++ Pₙ ++ zeroPad`, an evaluation vector of length
`2 ^ stackVars bs`. The definition is total; selector lemmas separately assume
that the inputs are ordered by descending size `ν₁ ≥ ⋯ ≥ νₙ`. -/
def stack [Zero R] (bs : List (Block R)) : CMlPolynomialEval R (stackVars bs) :=
  Vector.ofFn (fun k : Fin (2 ^ stackVars bs) ↦ cellAt bs k.val)

/-- The stacking invariant that block variable counts are in
non-increasing order. -/
def Descending (bs : List (Block R)) : Prop :=
  bs.Pairwise fun a b ↦ b.1 ≤ a.1

/-- Every block ends within the unpadded concatenation. -/
theorem offset_add_cells_le_totalCells (bs : List (Block R)) (i : Fin bs.length) :
    offset bs i.val + (bs.get i).cells ≤ totalCells bs := by
  induction bs with
  | nil => exact Fin.elim0 i
  | cons b rest ih =>
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simp [offset, totalCells, Block.cells]
      · simpa [offset, totalCells, Block.cells, Nat.add_assoc] using
          Nat.add_le_add_left (ih j) b.cells

/-- Looking up a local block cell at its concatenation offset returns that
block's stored value, independently of the size-order invariant. -/
theorem cellAt_offset_add [Zero R] (bs : List (Block R)) (i : Fin bs.length)
    (x : Fin (2 ^ (bs.get i).1)) :
    cellAt bs (offset bs i.val + x.val) = (bs.get i).2[x] := by
  induction bs with
  | nil => exact Fin.elim0 i
  | cons b rest ih =>
      cases i using Fin.cases with
      | zero =>
          simpa [offset, cellAt] using (Vector.get_eq_getElem b.2 x).symm
      | succ j =>
          simpa [offset, cellAt, Block.cells, Nat.add_assoc] using ih j x

/-- Descending block sizes make every block offset a multiple of that block's
hypercube size. -/
theorem pow_dvd_offset_of_descending (bs : List (Block R)) (hdesc : Descending bs)
    (i : Fin bs.length) :
    2 ^ (bs.get i).1 ∣ offset bs i.val := by
  induction bs with
  | nil => exact Fin.elim0 i
  | cons b rest ih =>
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simp [offset]
      · have hdesc' : (∀ a ∈ rest, a.1 ≤ b.1) ∧ Descending rest := by
          simpa [Descending] using hdesc
        have hrest : Descending rest := hdesc'.2
        have hhead : (rest.get j).1 ≤ b.1 := by
          exact hdesc'.1 (rest.get j) (List.get_mem rest j)
        have hpow : 2 ^ (rest.get j).1 ∣ 2 ^ b.1 :=
          (Nat.pow_dvd_pow_iff_le_right (by decide)).2 hhead
        simpa [offset, Block.cells, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          dvd_add hpow (ih hrest j)

/-- Every real block has no more variables than its padded stack. -/
theorem block_vars_le_stackVars (bs : List (Block R)) (i : Fin bs.length) :
    (bs.get i).1 ≤ stackVars bs := by
  apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).1
  calc
    2 ^ (bs.get i).1 ≤ offset bs i.val + 2 ^ (bs.get i).1 := Nat.le_add_left _ _
    _ ≤ totalCells bs := offset_add_cells_le_totalCells bs i
    _ ≤ 2 ^ stackVars bs := Nat.le_pow_clog (by decide) _

/-- The selector bit vector of block `i`: the big-endian binary encoding of
`oᵢ / 2 ^ νᵢ` on `stackVars - νᵢ` bits. Under the descending-size invariant the
offset `oᵢ` is a multiple of `2 ^ νᵢ`, so this quotient is exact and the
selector addresses exactly the high bits of block `i`'s cells inside the
stack. -/
def selBits (bs : List (Block R)) (i : Fin bs.length) :
    Vector Bool (stackVars bs - (bs.get i).1) :=
  CompPoly.Bits.toBE (stackVars bs - (bs.get i).1) (offset bs i.val / 2 ^ (bs.get i).1)

/-- The selector point `(selᵢ, z)` in the paper's big-endian coordinates. The selector
occupies the high coordinates and the within-block point occupies the low
coordinates. -/
def selPoint [Zero R] [One R] (bs : List (Block R)) (i : Fin bs.length)
    (hle : (bs.get i).1 ≤ stackVars bs) (z : Vector R (bs.get i).1) :
    Vector R (stackVars bs) :=
  Vector.ofFn fun j : Fin (stackVars bs) ↦
    if hhigh : j.val < stackVars bs - (bs.get i).1 then
      if (offset bs i.val / 2 ^ (bs.get i).1).testBit
          (stackVars bs - (bs.get i).1 - 1 - j.val) then
        (1 : R)
      else
        0
    else
      z[j.val - (stackVars bs - (bs.get i).1)]'(by omega)

/-- The selector point of block `i`, together with a within-block point `z`,
assembled into a single evaluation point of the stack.

The paper writes this point as `(sel_i, z)`, where `sel_i` is the high-bit
selector. CompPoly's `cubePoint` indexes coordinates little-endian, so the Lean
vector stores `z` in the low coordinates and the selector quotient
`offset / 2^νᵢ` in the high coordinates. -/
def selPointLE [Zero R] [One R] (bs : List (Block R)) (i : Fin bs.length)
    (_hle : (bs.get i).1 ≤ stackVars bs) (z : Vector R (bs.get i).1) :
    Vector R (stackVars bs) :=
  Vector.ofFn fun j : Fin (stackVars bs) ↦
    if hlocal : j.val < (bs.get i).1 then
      z[j.val]'hlocal
    else if (offset bs i.val / 2 ^ (bs.get i).1).testBit (j.val - (bs.get i).1) then
      (1 : R)
    else
      0

/-- Reversing the big-endian selector point produces the internal
little-endian selector point at the reversed local evaluation point. -/
theorem selPoint_reverse [Zero R] [One R] (bs : List (Block R)) (i : Fin bs.length)
    (hle : (bs.get i).1 ≤ stackVars bs) (z : Vector R (bs.get i).1) :
    (selPoint bs i hle z).reverse = selPointLE bs i hle z.reverse := by
  apply Vector.ext
  intro j hj
  rw [← Vector.get_eq_getElem (selPoint bs i hle z).reverse ⟨j, hj⟩]
  rw [← Vector.get_eq_getElem (selPointLE bs i hle z.reverse) ⟨j, hj⟩]
  rw [Vector.get_reverse]
  have hsplit : stackVars bs - (bs.get i).1 + (bs.get i).1 = stackVars bs :=
    Nat.sub_add_cancel hle
  by_cases hlocal : j < (bs.get i).1
  · simp only [selPoint, selPointLE, Vector.get_ofFn, Fin.rev]
    split
    next hhigh => omega
    next hhigh =>
      rw [← Vector.get_eq_getElem z.reverse ⟨j, hlocal⟩, Vector.get_reverse]
      rw [Vector.get_eq_getElem]
      simp only [Fin.rev]
      congr 1
      omega
  · simp only [selPoint, selPointLE, Vector.get_ofFn, Fin.rev]
    split
    next hhigh =>
      have hindex :
          stackVars bs - (bs.get i).1 - 1 - (stackVars bs - (j + 1)) =
            j - (bs.get i).1 := by
        apply (Nat.sub_eq_iff_eq_add (by omega)).2
        omega
      rw [hindex]
    next hhigh => omega

/-- Alignment hypotheses for block `i` inside a stack.

The first conjunct is the paper's offset divisibility invariant. The second
states that the whole block lies inside the padded stack domain. The third
connects the abstract offset to the concrete `cellAt` concatenation. Descending
block sizes imply these conditions. -/
def AlignedAt [Zero R] (bs : List (Block R)) (i : Fin bs.length) : Prop :=
  offset bs i.val % 2 ^ (bs.get i).1 = 0 ∧
    offset bs i.val + 2 ^ (bs.get i).1 ≤ 2 ^ stackVars bs ∧
    ∀ x : Fin (2 ^ (bs.get i).1),
      cellAt bs (offset bs i.val + x.val) = (bs.get i).2[x]

/-- The descending-size invariant implies all selector-alignment
side conditions. -/
theorem alignedAt_of_descending [Zero R] (bs : List (Block R))
    (hdesc : Descending bs) (i : Fin bs.length) :
    AlignedAt bs i := by
  refine ⟨Nat.dvd_iff_mod_eq_zero.mp (pow_dvd_offset_of_descending bs hdesc i), ?_, ?_⟩
  · exact (offset_add_cells_le_totalCells bs i).trans (Nat.le_pow_clog (by decide) _)
  · exact cellAt_offset_add bs i

/-- The selector quotient exactly reconstructs the aligned offset. -/
theorem selector_quot_mul_pow [Zero R] (bs : List (Block R)) (i : Fin bs.length)
    (haligned : AlignedAt bs i) :
    (offset bs i.val / 2 ^ (bs.get i).1) * 2 ^ (bs.get i).1 = offset bs i.val := by
  exact Nat.div_mul_cancel (Nat.dvd_iff_mod_eq_zero.mpr haligned.1)

/-- The selector quotient fits in the high coordinates of the stacked cube. -/
theorem selector_quot_lt [Zero R] (bs : List (Block R)) (i : Fin bs.length)
    (hle : (bs.get i).1 ≤ stackVars bs) (haligned : AlignedAt bs i) :
    offset bs i.val / 2 ^ (bs.get i).1 < 2 ^ (stackVars bs - (bs.get i).1) := by
  let m := (bs.get i).1
  let n := stackVars bs
  let o := offset bs i.val
  let q := o / 2 ^ m
  have hqm : q * 2 ^ m = o := selector_quot_mul_pow (R := R) bs i haligned
  have hbound : o + 2 ^ m ≤ 2 ^ n := haligned.2.1
  have hpow : 2 ^ (n - m) * 2 ^ m = 2 ^ n := by
    simpa [m, n] using (pow_sub_mul_pow (a := 2) (m := m) (n := n) hle)
  have hmul : (q + 1) * 2 ^ m ≤ 2 ^ n := by
    calc
      (q + 1) * 2 ^ m = q * 2 ^ m + 2 ^ m := by rw [Nat.add_mul, one_mul]
      _ = o + 2 ^ m := by rw [hqm]
      _ ≤ 2 ^ n := hbound
  have hleq : q + 1 ≤ 2 ^ (n - m) := by
    rw [← hpow] at hmul
    exact Nat.le_of_mul_le_mul_right hmul (Nat.two_pow_pos m)
  simpa [q, o, m, n] using Nat.lt_of_succ_le hleq

/-- The low coordinates of the internal selector point are the local point. -/
theorem selPoint_get_low [Zero R] [One R] (bs : List (Block R)) (i : Fin bs.length)
    (hle : (bs.get i).1 ≤ stackVars bs) (z : Vector R (bs.get i).1)
    (j : Fin (bs.get i).1) :
    (selPointLE bs i hle z)[j.val]'(Nat.lt_of_lt_of_le j.isLt hle) = z[j] := by
  simp [selPointLE]

/-- The high coordinates of the internal selector point encode the block offset. -/
theorem selPoint_get_high [Zero R] [One R] (bs : List (Block R)) (i : Fin bs.length)
    (hle : (bs.get i).1 ≤ stackVars bs) (z : Vector R (bs.get i).1)
    (j : Fin (stackVars bs - (bs.get i).1)) :
    (selPointLE bs i hle z)[(bs.get i).1 + j.val]'(by omega) =
      if (offset bs i.val / 2 ^ (bs.get i).1).testBit j.val then (1 : R) else 0 := by
  simp [selPointLE]

/-- The global index of local cell `x` inside an aligned block. -/
def selectedIndex [Zero R] (bs : List (Block R)) (i : Fin bs.length)
    (haligned : AlignedAt bs i) (x : Fin (2 ^ (bs.get i).1)) : Fin (2 ^ stackVars bs) :=
  ⟨offset bs i.val + x.val, by
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left x.isLt _) haligned.2.1⟩

/-- The value of a selected global index is its block offset plus its local index. -/
@[simp]
theorem selectedIndex_val [Zero R] (bs : List (Block R)) (i : Fin bs.length)
    (haligned : AlignedAt bs i) (x : Fin (2 ^ (bs.get i).1)) :
    (selectedIndex bs i haligned x).val = offset bs i.val + x.val := rfl

/-- Embedding local cells into an aligned block is injective. -/
theorem selectedIndex_injective [Zero R] (bs : List (Block R)) (i : Fin bs.length)
    (haligned : AlignedAt bs i) :
    Function.Injective (selectedIndex bs i haligned) := by
  intro x y hxy
  apply Fin.ext
  simpa only [selectedIndex_val, Nat.add_left_cancel_iff] using congrArg Fin.val hxy

/-- Looking up a selected stack cell recovers the corresponding block cell. -/
@[simp]
theorem stack_selectedIndex [Zero R] (bs : List (Block R)) (i : Fin bs.length)
    (haligned : AlignedAt bs i) (x : Fin (2 ^ (bs.get i).1)) :
    (stack bs)[selectedIndex bs i haligned x] = (bs.get i).2[x] := by
  simp [stack, selectedIndex, haligned.2.2 x]

/-- An aligned selected index is the concatenation of its local and selector bits. -/
theorem selectedIndex_eq_joinBits [Zero R] (bs : List (Block R)) (i : Fin bs.length)
    (hle : (bs.get i).1 ≤ stackVars bs) (haligned : AlignedAt bs i)
    (x : Fin (2 ^ (bs.get i).1)) :
    (selectedIndex bs i haligned x).val =
      (Nat.joinBits x
        ⟨offset bs i.val / 2 ^ (bs.get i).1,
          selector_quot_lt (R := R) bs i hle haligned⟩).val := by
  unfold selectedIndex Nat.joinBits
  dsimp
  have h_and_zero := Nat.and_shl_eq_zero_of_lt_two_pow
    (a := offset bs i.val / 2 ^ (bs.get i).1) (b := x.val) (hb := x.isLt)
  calc
    offset bs i.val + x.val =
        (offset bs i.val / 2 ^ (bs.get i).1) * 2 ^ (bs.get i).1 + x.val := by
      rw [selector_quot_mul_pow (R := R) bs i haligned]
    _ = (offset bs i.val / 2 ^ (bs.get i).1) <<< (bs.get i).1 + x.val := by
      rw [Nat.shiftLeft_eq, mul_comm]
    _ = (offset bs i.val / 2 ^ (bs.get i).1) <<< (bs.get i).1 ||| x.val := by
      exact Nat.sum_of_and_eq_zero_is_or h_and_zero

/-- A selected index has the local cell's bits in its low coordinates. -/
theorem selectedIndex_testBit_low [Zero R] (bs : List (Block R)) (i : Fin bs.length)
    (hle : (bs.get i).1 ≤ stackVars bs) (haligned : AlignedAt bs i)
    (x : Fin (2 ^ (bs.get i).1)) (j : Fin (bs.get i).1) :
    (selectedIndex bs i haligned x).val.testBit j.val = x.val.testBit j.val := by
  rw [selectedIndex_eq_joinBits (R := R) bs i hle haligned x]
  have hget :
      Nat.getBit j.val
          (Nat.joinBits x
            ⟨offset bs i.val / 2 ^ (bs.get i).1,
              selector_quot_lt (R := R) bs i hle haligned⟩).val =
        Nat.getBit j.val x.val := by
    rw [Nat.getBit_joinBits]
    simp
  apply Bool.eq_iff_iff.mpr
  rw [Nat.testBit_true_eq_getBit_eq_1 (j.val)
    (Nat.joinBits x
      ⟨offset bs i.val / 2 ^ (bs.get i).1,
        selector_quot_lt (R := R) bs i hle haligned⟩).val]
  rw [Nat.testBit_true_eq_getBit_eq_1 (j.val) x.val]
  rw [hget]

/-- A selected index has the selector quotient's bits in its high coordinates. -/
theorem selectedIndex_testBit_high [Zero R] (bs : List (Block R)) (i : Fin bs.length)
    (hle : (bs.get i).1 ≤ stackVars bs) (haligned : AlignedAt bs i)
    (x : Fin (2 ^ (bs.get i).1)) (j : Fin (stackVars bs - (bs.get i).1)) :
    (selectedIndex bs i haligned x).val.testBit ((bs.get i).1 + j.val) =
      (offset bs i.val / 2 ^ (bs.get i).1).testBit j.val := by
  rw [selectedIndex_eq_joinBits (R := R) bs i hle haligned x]
  have hnot : ¬(bs.get i).1 + j.val < (bs.get i).1 := by omega
  have hsub : (bs.get i).1 + j.val - (bs.get i).1 = j.val := by omega
  have hget :
      Nat.getBit ((bs.get i).1 + j.val)
          (Nat.joinBits x
            ⟨offset bs i.val / 2 ^ (bs.get i).1,
              selector_quot_lt (R := R) bs i hle haligned⟩).val =
        Nat.getBit j.val (offset bs i.val / 2 ^ (bs.get i).1) := by
    rw [Nat.getBit_joinBits]
    simp
  apply Bool.eq_iff_iff.mpr
  rw [Nat.testBit_true_eq_getBit_eq_1 ((bs.get i).1 + j.val)
    (Nat.joinBits x
      ⟨offset bs i.val / 2 ^ (bs.get i).1,
        selector_quot_lt (R := R) bs i hle haligned⟩).val]
  rw [Nat.testBit_true_eq_getBit_eq_1 j.val (offset bs i.val / 2 ^ (bs.get i).1)]
  rw [hget]

/-- The high bits of any stacked index fit in the high-coordinate cube. -/
theorem highBits_no_shl_lt (bs : List (Block R)) (i : Fin bs.length)
    (hle : (bs.get i).1 ≤ stackVars bs) (w : Fin (2 ^ stackVars bs)) :
    Nat.getHighBits_no_shl (bs.get i).1 w.val < 2 ^ (stackVars bs - (bs.get i).1) := by
  let m := (bs.get i).1
  let n := stackVars bs
  have hpow : 2 ^ (n - m) * 2 ^ m = 2 ^ n := by
    simpa [m, n] using (pow_sub_mul_pow (a := 2) (m := m) (n := n) hle)
  rw [Nat.getHighBits_no_shl, Nat.shiftRight_eq_div_pow]
  rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos m)]
  rw [hpow]
  exact w.isLt

/-- Low `νᵢ` bits of a global stack index, interpreted as a local block index. -/
def lowIndex (bs : List (Block R)) (i : Fin bs.length)
    (w : Fin (2 ^ stackVars bs)) : Fin (2 ^ (bs.get i).1) :=
  ⟨Nat.getLowBits (bs.get i).1 w.val, Nat.getLowBits_lt_two_pow _⟩

/-- High bits of a global stack index, interpreted as a selector index. -/
def highIndex (bs : List (Block R)) (i : Fin bs.length)
    (hle : (bs.get i).1 ≤ stackVars bs)
    (w : Fin (2 ^ stackVars bs)) : Fin (2 ^ (stackVars bs - (bs.get i).1)) :=
  ⟨Nat.getHighBits_no_shl (bs.get i).1 w.val, highBits_no_shl_lt bs i hle w⟩

/-- Block `i`'s aligned selector quotient as a high-coordinate cube index. -/
def selectorIndex [Zero R] (bs : List (Block R)) (i : Fin bs.length)
    (hle : (bs.get i).1 ≤ stackVars bs) (haligned : AlignedAt bs i) :
    Fin (2 ^ (stackVars bs - (bs.get i).1)) :=
  ⟨offset bs i.val / 2 ^ (bs.get i).1, selector_quot_lt bs i hle haligned⟩

/-- Splitting a selected index into low bits recovers its local index. -/
@[simp]
theorem lowIndex_selectedIndex [Zero R] (bs : List (Block R)) (i : Fin bs.length)
    (haligned : AlignedAt bs i) (x : Fin (2 ^ (bs.get i).1)) :
    lowIndex bs i (selectedIndex bs i haligned x) = x := by
  apply Fin.ext
  unfold lowIndex
  simp only [selectedIndex_val, Nat.getLowBits_eq_mod_two_pow]
  rw [← selector_quot_mul_pow (R := R) bs i haligned]
  rw [Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_eq_of_lt x.isLt,
    Nat.mod_eq_of_lt x.isLt]

/-- Splitting a selected index into high bits recovers the block selector. -/
@[simp]
theorem highIndex_selectedIndex [Zero R] (bs : List (Block R)) (i : Fin bs.length)
    (hle : (bs.get i).1 ≤ stackVars bs) (haligned : AlignedAt bs i)
    (x : Fin (2 ^ (bs.get i).1)) :
    highIndex bs i hle (selectedIndex bs i haligned x) = selectorIndex bs i hle haligned := by
  apply Fin.ext
  unfold highIndex selectorIndex
  simp only [selectedIndex_val, Nat.getHighBits_no_shl, Nat.shiftRight_eq_div_pow]
  rw [← selector_quot_mul_pow (R := R) bs i haligned]
  rw [Nat.mul_comm (offset bs i.val / 2 ^ (bs.get i).1)]
  rw [Nat.mul_add_div (Nat.two_pow_pos _) _ _, Nat.div_eq_of_lt x.isLt, Nat.add_zero]
  exact (Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)).symm

/-- If a stacked index has block `i`'s selector quotient as its high bits, it is selected. -/
theorem mem_selectedIndex_image_of_highBits_eq [Zero R] (bs : List (Block R))
    (i : Fin bs.length) (haligned : AlignedAt bs i) (w : Fin (2 ^ stackVars bs))
    (hhigh :
      Nat.getHighBits_no_shl (bs.get i).1 w.val =
        offset bs i.val / 2 ^ (bs.get i).1) :
    w ∈ Finset.image (selectedIndex bs i haligned)
        (Finset.univ : Finset (Fin (2 ^ (bs.get i).1))) := by
  let m := (bs.get i).1
  let q := offset bs i.val / 2 ^ m
  let x : Fin (2 ^ m) := ⟨Nat.getLowBits m w.val, Nat.getLowBits_lt_two_pow m⟩
  refine Finset.mem_image.mpr ⟨x, Finset.mem_univ _, ?_⟩
  apply Fin.ext
  have hqmul : q * 2 ^ m = offset bs i.val := by
    simpa [q, m] using selector_quot_mul_pow (R := R) bs i haligned
  have hq : q = w.val / 2 ^ m := by
    rw [Nat.getHighBits_no_shl, Nat.shiftRight_eq_div_pow] at hhigh
    simpa [q, m] using hhigh.symm
  calc
    (selectedIndex bs i haligned x).val = offset bs i.val + Nat.getLowBits m w.val := rfl
    _ = q * 2 ^ m + Nat.getLowBits m w.val := by rw [hqmul]
    _ = (w.val / 2 ^ m) * 2 ^ m + w.val % 2 ^ m := by
      rw [hq, Nat.getLowBits_eq_mod_two_pow]
    _ = w.val := Nat.div_add_mod' w.val (2 ^ m)

/-- At a selected global index, the selector equality-kernel weight is the local weight. -/
theorem selector_weight_selected [CommRing R] (bs : List (Block R)) (i : Fin bs.length)
    (hle : (bs.get i).1 ≤ stackVars bs) (haligned : AlignedAt bs i)
    (z : Vector R (bs.get i).1) (x : Fin (2 ^ (bs.get i).1)) :
    CompPoly.Multilinear.eqHat (selPointLE bs i hle z)
        (CompPoly.Multilinear.cubePointLE (stackVars bs) (selectedIndex bs i haligned x)) =
      CompPoly.Multilinear.eqHat z (CompPoly.Multilinear.cubePointLE (bs.get i).1 x) := by
  unfold CompPoly.Multilinear.eqHat CompPoly.Multilinear.cubePointLE
  simp +decide only [Fin.getElem_fin, BitVec.getLsb_eq_getElem, BitVec.getElem_ofFin,
    selectedIndex_val, List.get_eq_getElem, Vector.getElem_ofFn, mul_ite, mul_one, mul_zero]
  let m := (bs.get i).1
  let n := stackVars bs
  let d := n - m
  let q := offset bs i.val / 2 ^ m
  let y := selectedIndex bs i haligned x
  let s := selPointLE bs i hle z
  let f : Fin n → R := fun j ↦
    (if y.val.testBit j.val then s[j] else 0) +
      (1 - s[j]) * (1 - if y.val.testBit j.val then (1 : R) else 0)
  let g : Fin m → R := fun j ↦
    (if x.val.testBit j.val then z[j] else 0) +
      (1 - z[j]) * (1 - if x.val.testBit j.val then (1 : R) else 0)
  change (∏ j : Fin n, f j) = ∏ j : Fin m, g j
  have hmn : m + d = n := by
    omega
  rw [← Fin.prod_congr' (f := f) hmn]
  rw [Fin.prod_trunc]
  · apply Finset.prod_congr rfl
    intro j _
    have hjbit : (offset bs i.val + x.val).testBit j.val = x.val.testBit j.val := by
      simpa [selectedIndex] using selectedIndex_testBit_low (R := R) bs i hle haligned x j
    simp [f, g, s, y, m, selectedIndex, hjbit, selPointLE]
  · intro j
    have hbit : y.val.testBit (m + j.val) = q.testBit j.val := by
      simpa [y, q, m, n, d] using
        selectedIndex_testBit_high (R := R) bs i hle haligned x j
    have hs : s[m + j.val] = if q.testBit j.val then (1 : R) else 0 := by
      simpa [s, q, m, n, d] using selPoint_get_high bs i hle z j
    by_cases hq : q.testBit j.val
    · simp [f, hbit, hs, hq]
    · simp [f, hbit, hs, hq]

/-- Evaluating the stacked multilinear polynomial at an aligned selector point
agrees with evaluating the original block multilinear polynomial. -/
theorem selector_eval_eqLE [CommRing R] (bs : List (Block R)) (i : Fin bs.length)
    (hle : (bs.get i).1 ≤ stackVars bs) (haligned : AlignedAt bs i)
    (z : Vector R (bs.get i).1) :
    (stack bs).eval (selPointLE bs i hle z) = (bs.get i).2.eval z := by
  rw [CompPoly.Multilinear.eqHat_interpolationLE, CompPoly.Multilinear.eqHat_interpolationLE]
  let m := (bs.get i).1
  let n := stackVars bs
  let q := offset bs i.val / 2 ^ m
  let selected : Finset (Fin (2 ^ n)) :=
    Finset.image (selectedIndex bs i haligned) (Finset.univ : Finset (Fin (2 ^ m)))
  let lhsWeight : Fin (2 ^ n) → R := fun w ↦
    CompPoly.Multilinear.eqHat (selPointLE bs i hle z)
        (CompPoly.Multilinear.cubePointLE n w) *
      (stack bs)[w]
  let rhsWeight : Fin (2 ^ m) → R := fun x ↦
    CompPoly.Multilinear.eqHat z (CompPoly.Multilinear.cubePointLE m x) * (bs.get i).2[x]
  change (∑ w : Fin (2 ^ n), lhsWeight w) = ∑ x : Fin (2 ^ m), rhsWeight x
  have hselected_eval : ∀ x : Fin (2 ^ m),
      lhsWeight (selectedIndex bs i haligned x) = rhsWeight x := by
    intro x
    calc
      lhsWeight (selectedIndex bs i haligned x) =
          CompPoly.Multilinear.eqHat (selPointLE bs i hle z)
              (CompPoly.Multilinear.cubePointLE n (selectedIndex bs i haligned x)) *
            (stack bs)[selectedIndex bs i haligned x] := rfl
      _ = CompPoly.Multilinear.eqHat z (CompPoly.Multilinear.cubePointLE m x) *
          (bs.get i).2[x] := by
        rw [selector_weight_selected (R := R) bs i hle haligned z x,
          stack_selectedIndex (R := R) bs i haligned x]
      _ = rhsWeight x := rfl
  have hzero : ∀ w : Fin (2 ^ n), w ∉ selected → lhsWeight w = 0 := by
    intro w hw
    have hhigh_ne : Nat.getHighBits_no_shl m w.val ≠ q := by
      intro hhigh
      apply hw
      dsimp [selected]
      simpa [m, n, q] using
        mem_selectedIndex_image_of_highBits_eq (R := R) bs i haligned w hhigh
    have hhigh_lt : Nat.getHighBits_no_shl m w.val < 2 ^ (n - m) := by
      simpa [m, n] using highBits_no_shl_lt (R := R) bs i hle w
    have hq_lt : q < 2 ^ (n - m) := by
      simpa [m, n, q] using selector_quot_lt (R := R) bs i hle haligned
    obtain ⟨k, hklt, hkbit⟩ :
        ∃ k, k < n - m ∧ Nat.testBit (Nat.getHighBits_no_shl m w.val) k ≠ q.testBit k := by
      obtain ⟨k, hkbit⟩ :
          ∃ k, Nat.testBit (Nat.getHighBits_no_shl m w.val) k ≠ q.testBit k := by
        by_contra hbits
        apply hhigh_ne
        apply Nat.eq_of_testBit_eq
        intro k
        by_contra hkbit
        exact hbits ⟨k, hkbit⟩
      refine ⟨k, ?_, hkbit⟩
      by_contra hk
      have hle_k : n - m ≤ k := Nat.le_of_not_gt hk
      have hpow_le : 2 ^ (n - m) ≤ 2 ^ k :=
        pow_le_pow_right' (by norm_num : 1 ≤ (2 : ℕ)) hle_k
      have hhigh_bit : Nat.testBit (Nat.getHighBits_no_shl m w.val) k = false :=
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hhigh_lt hpow_le)
      have hq_bit : q.testBit k = false :=
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hq_lt hpow_le)
      exact hkbit (by rw [hhigh_bit, hq_bit])
    let j : Fin n := ⟨m + k, by omega⟩
    have hfactor :
        (selPointLE bs i hle z)[j] * (CompPoly.Multilinear.cubePointLE n w)[j] +
            (1 - (selPointLE bs i hle z)[j]) *
              (1 - (CompPoly.Multilinear.cubePointLE n w)[j]) = 0 := by
      have hs :
          (selPointLE bs i hle z)[j] = if q.testBit k then (1 : R) else 0 := by
        simpa [j, m, n, q] using selPoint_get_high bs i hle z ⟨k, hklt⟩
      have hshift :
          (Nat.getHighBits_no_shl m w.val).testBit k = w.val.testBit (m + k) := by
        unfold Nat.getHighBits_no_shl
        rw [Nat.testBit_shiftRight]
      have hc :
          (CompPoly.Multilinear.cubePointLE n w)[j] =
            if (Nat.getHighBits_no_shl m w.val).testBit k then (1 : R) else 0 := by
        unfold CompPoly.Multilinear.cubePointLE
        simpa +decide [Vector.ofFn, j, m, n] using
          congrArg (fun b : Bool ↦ if b then (1 : R) else 0) hshift.symm
      by_cases hqk : q.testBit k <;>
        by_cases hwk : (Nat.getHighBits_no_shl m w.val).testBit k <;>
          simp [hs, hc, hqk, hwk] at hkbit ⊢
    have hweight_zero :
        CompPoly.Multilinear.eqHat (selPointLE bs i hle z)
            (CompPoly.Multilinear.cubePointLE n w) = 0 := by
      unfold CompPoly.Multilinear.eqHat
      exact Finset.prod_eq_zero (s := Finset.univ) (i := j) (by simp) hfactor
    simp [lhsWeight, hweight_zero]
  calc
    (∑ w : Fin (2 ^ n), lhsWeight w) = ∑ w ∈ selected, lhsWeight w := by
      rw [Finset.sum_subset (Finset.subset_univ selected)]
      intro w _ hw
      exact hzero w hw
    _ = ∑ x : Fin (2 ^ m), lhsWeight (selectedIndex bs i haligned x) := by
      rw [Finset.sum_image]
      intro x _ y _ hxy
      exact selectedIndex_injective (R := R) bs i haligned hxy
    _ = ∑ x : Fin (2 ^ m), rhsWeight x := by
      exact Finset.sum_congr rfl fun x _ ↦ hselected_eval x

/-- In big-endian coordinates, evaluating the stacked MLE at `(selᵢ, z)` agrees
with evaluating block `i` at `z`. -/
theorem selector_eval_eq [CommRing R] (bs : List (Block R)) (i : Fin bs.length)
    (hle : (bs.get i).1 ≤ stackVars bs) (haligned : AlignedAt bs i)
    (z : Vector R (bs.get i).1) :
    CompPoly.Multilinear.mleEval (stack bs) (selPoint bs i hle z) =
      CompPoly.Multilinear.mleEval (bs.get i).2 z := by
  calc
    CompPoly.Multilinear.mleEval (stack bs) (selPoint bs i hle z) =
        (stack bs).eval (selPoint bs i hle z).reverse :=
      CompPoly.Multilinear.mleEval_eq_eval_reverse _ _
    _ = (stack bs).eval (selPointLE bs i hle z.reverse) := by rw [selPoint_reverse]
    _ = (bs.get i).2.eval z.reverse := selector_eval_eqLE bs i hle haligned z.reverse
    _ = CompPoly.Multilinear.mleEval (bs.get i).2 z :=
      (CompPoly.Multilinear.mleEval_eq_eval_reverse _ _).symm

end Stacking
