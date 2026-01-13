/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Gregor Mitscha-Baude
-/

import ArkLib.Data.List.Lemmas
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Data.Nat.Log

/-!
# Auxiliary lemmas for `Array`
-/

universe u

namespace Array

variable {α : Type*} {unit : α}

/-- Checks if an array of elements from a type `R` is a boolean array, i.e., if every element is
  either `0` or `1`. -/
def isBoolean {R : Type _} [Zero R] [One R] (a : Array R) : Prop :=
    ∀ i : Fin a.size, (a[i] = 0) ∨ (a[i] = 1)

/-- Interpret an array as the binary representation of a number, sending `0` to `0` and `≠ 0` to
  `1`. -/
def toNum {R : Type _} [Zero R] [DecidableEq R] (a : Array R) : ℕ :=
  (a.map (fun r => if r = 0 then 0 else 1)).reverse.foldl (fun acc elem => (acc * 2) + elem) 0

theorem leftpad_toList {a : Array α} {n : Nat} {unit : α} :
    a.leftpad n unit = mk (a.toList.leftpad n unit) := by
  induction h : a.toList with
  | nil => simp_all
  | cons hd tl ih => simp_all [size_eq_length_toList]

theorem rightpad_toList {a : Array α} {n : Nat} {unit : α} :
    a.rightpad n unit = mk (a.toList.rightpad n unit) := by
  induction h : a.toList with
  | nil => simp_all
  | cons hd tl ih => simp_all [size_eq_length_toList]

theorem rightpad_getElem_eq_getD {a : Array α} {n : Nat} {unit : α} {i : Nat}
    (h : i < (a.rightpad n unit).size) : (a.rightpad n unit)[i] = a.getD i unit := by
  rcases Nat.lt_or_ge i a.size with h' | h' <;> simp [h']

/-- `Array` version of `List.matchSize`, which rightpads the arrays to the same length. -/
@[reducible]
def matchSize (a b : Array α) (unit : α) : Array α × Array α :=
  (a.rightpad (b.size) unit, b.rightpad (a.size) unit)

theorem matchSize_toList {a b : Array α} {unit : α} :
    matchSize a b unit =
      let (a', b') := List.matchSize a.toList b.toList unit
      (mk a', mk b') := by
  simp [matchSize, List.matchSize]

theorem getElem?_eq_toList {a : Array α} {i : ℕ} : a.toList[i]? = a[i]? := by
  rw (occs := .pos [2]) [← Array.toArray_toList (xs := a)]
  rw [List.getElem?_toArray]

attribute [simp] Array.getElem?_eq_getElem

-- @[simp] theorem matchSize_comm (a : Array α) (b : Array α) (unit : α) :
--     matchSize a b unit = (matchSize b a unit).swap := by
--   simp [matchSize, List.matchSize]

/-- find index from the end of an array -/
def findIdxRev? (cond : α → Bool) (as : Array α) : Option (Fin as.size) :=
  find ⟨ as.size, Nat.lt_succ_self _ ⟩
where
  find : Fin (as.size + 1) → Option (Fin as.size)
    | 0 => none
    | ⟨ i+1, h ⟩ =>
      if (cond as[i]) then
        some ⟨ i, Nat.lt_of_succ_lt_succ h ⟩
      else
        find ⟨ i, Nat.lt_of_succ_lt h ⟩

/-- if findIdxRev? finds an index, the condition is satisfied on that element -/
def findIdxRev?_def {cond} {as : Array α} {k : Fin as.size} :
  findIdxRev? cond as = some k → cond as[k] := by
  suffices aux : ∀ i, findIdxRev?.find cond as i = some k → cond as[k] by apply aux
  intro i
  unfold findIdxRev?.find
  induction i using findIdxRev?.find.induct cond as with
  | case1 => simp
  | case2 => simp [*]; rintro rfl; assumption
  | case3 => unfold findIdxRev?.find; simp [*]; assumption

/-- if findIdxRev? finds an index, then for every greater index the condition doesn't hold -/
def findIdxRev?_maximal {cond} {as : Array α} {k : Fin as.size} :
  findIdxRev? cond as = some k → ∀ j : Fin as.size, j > k → ¬ cond as[j] := by
  suffices aux : ∀ i, findIdxRev?.find cond as i = some k →
    ∀ j : Fin as.size, j > k → j.val < i → ¬ cond as[j] by
    intro h j j_gt_k
    exact aux ⟨ as.size, Nat.lt_succ_self _ ⟩ h j j_gt_k j.is_lt
  intro i
  unfold findIdxRev?.find
  induction i using findIdxRev?.find.induct cond as with
  | case1 => simp
  | case2 i =>
    simp [*]
    rintro rfl j (_: j > i) (_: j < i + 1) -- contradiction
    omega
  | case3 i _ not_true ih =>
    simp [*]
    unfold findIdxRev?.find
    intro h j j_gt_k j_lt_isucc
    specialize ih h j j_gt_k
    rcases (Nat.lt_or_eq_of_le (Nat.le_of_lt_succ j_lt_isucc): j < i ∨ j = i) with (j_lt_i | rfl)
    · specialize ih j_lt_i
      rwa [Bool.not_eq_true] at ih
    · simp only [not_true]

/-- if the condition is false on all elements, then findIdxRev? finds nothing -/
theorem findIdxRev?_eq_none {cond} {as : Array α} (h : ∀ i, (hi : i < as.size) → ¬ cond as[i]) :
  findIdxRev? cond as = none
:= by
  apply aux
where
  aux i : findIdxRev?.find cond as i = none := by
    unfold findIdxRev?.find
    split
    next => tauto
    next _ j _ =>
      split -- then/else cases inside .find
      next cond_true =>
        have cond_false : ¬ cond as[j] := h j _
        have : False := cond_false cond_true
        contradiction
      -- recursively invoke the theorem we are proving!
      apply aux

theorem findIdxRev?_emtpy_none {cond} {as : Array α} (h : as = #[]) :
  findIdxRev? cond as = none
:= by
  rw [h]
  apply findIdxRev?_eq_none
  simp

/-- if the condition is true on some element, then findIdxRev? finds something -/
theorem findIdxRev?_eq_some {cond} {as : Array α} (h : ∃ i, ∃ hi : i < as.size, cond as[i]) :
  ∃ k : Fin as.size, findIdxRev? cond as = some k
:= by
  obtain ⟨ i, hi, hcond ⟩ := h
  apply aux ⟨ as.size, Nat.lt_succ_self _ ⟩ ⟨ .mk i hi, hi, hcond ⟩
where
  aux (i : Fin (as.size + 1)) (h': ∃ i' : Fin as.size, i' < i.val ∧ cond as[i']) :
    ∃ k, findIdxRev?.find cond as i = some k := by
    unfold findIdxRev?.find
    split
    next => tauto
    next _ j hj =>
      split -- then/else cases inside .find
      · use .mk j (by omega)
      · obtain ⟨ k, hk : k < j + 1, hcond ⟩ := h'
        apply aux -- recursively invoke the theorem we are proving!
        have : k.val ≠ j := by rintro rfl; contradiction
        have : k.val < j := by omega
        use k

/-- Right-pads an array with `unit` elements until its length is a power of two. Returns the padded
  array and the number of elements added. -/
def rightpadPowerOfTwo (unit : α) (a : Array α) : Array α :=
  a.rightpad (2 ^ (Nat.clog 2 a.size)) unit

@[simp] theorem rightpadPowerOfTwo_size (unit : α) (a : Array α) :
    (a.rightpadPowerOfTwo unit).size = 2 ^ (Nat.clog 2 a.size) := by
  simp [rightpadPowerOfTwo, Nat.le_pow_iff_clog_le]

/-- Get the last element of an array, assuming the array is non-empty. -/
def getLast (a : Array α) (h : a.size > 0) : α := a[a.size - 1]

/-- Get the last element of an array, or `v₀` if the array is empty. -/
def getLastD (a : Array α) (v₀ : α) : α := a.getD (a.size - 1) v₀

@[simp] theorem popWhile_nil_or_last_false (p : α → Bool) (as : Array α)
    (h : (as.popWhile p).size > 0) : ¬ (p <| (as.popWhile p).getLast h) := sorry

end Array
