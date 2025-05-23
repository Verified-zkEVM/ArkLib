/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Mathlib.Data.Nat.Log
import Batteries.Data.List.Lemmas
import Batteries.Data.Array.Lemmas
import Batteries.Data.Nat.Lemmas
import Mathlib.Data.List.GetD
import Mathlib.Data.ZMod.Basic

/-!
  # Helper Functions and Lemmas

  TODO: split these files into different files based on each namespace
-/

namespace Nat

-- Note: this is already done with `Nat.sub_add_eq_max`
theorem max_eq_add_sub {m n : Nat} : Nat.max m n = m + (n - m) := by
  by_cases h : n ≤ m
  · simp [Nat.sub_eq_zero_of_le, h]
  · simp only [Nat.max_eq_right (Nat.le_of_not_le h), Nat.add_sub_of_le (Nat.le_of_not_le h)]

-- TODO: add lemmas connecting `log2` and `log`, and `nextPowerOfTwo` and `pow`?

-- @[simp] theorem log2_eq_log_two (n : Nat) : log2 n = log 2 n
--   | 0 => by simp
--   | n + 1 => by simp

-- @[simp] theorem nextPowerOfTwo_eq_pow_clog (n : Nat) : nextPowerOfTwo n = 2 ^ (clog2 n) := by

-- Note: `iterateRec` is not as efficient as `Nat.iterate`. For the repeated squaring in
-- exponentiation, we need to additionally do memoization of intermediate values.
-- TODO: add this
-- See [Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/.E2.9C.94.20Binary.20version.20of.20.60Nat.2Eiterate.60.3F/near/468437958)

/-- Iterate a binary operation `op` for `n` times by decomposing `n` in base `b`,
  then recursively computing the result. -/
def iterateRec {α : Sort*} (op : α → α) (n : ℕ) (b : ℕ) (h : b ≥ 2) : α → α :=
  if n = 0 then id
  else op^[n % b] ∘ (iterateRec op (n / b) b h)^[b]
termination_by n
decreasing_by
  simp_wf
  rename_i hn
  exact Nat.div_lt_self (Nat.ne_zero_iff_zero_lt.mp hn) h

/-- Special case of `Nat.iterateRec` where the base `b` is binary.
  Corresponds to repeated squaring for exponentiation. -/
def iterateBin {α : Sort*} (op : α → α) (n : ℕ) : α → α := iterateRec op n 2 (by decide)

notation:max f "^["n"]₂" => Nat.iterateBin f n

end Nat

namespace Function

@[simp]
lemma iterateRec_zero {α : Sort*} {b : ℕ} {h : b ≥ 2} (op : α → α) :
    Nat.iterateRec op 0 b h = id := by simp [Nat.iterateRec]

@[simp]
lemma iterateRec_lt_base {α : Type*} {b k : ℕ} (op : α → α) {h : b ≥ 2} (hk : k < b) :
    Nat.iterateRec op k b h = op^[k] := by
  unfold Nat.iterateRec
  have h1 : k % b = k := Nat.mod_eq_of_lt (by omega)
  have h2 : k / b = 0 := Nat.div_eq_of_lt (by omega)
  simp [h1, h2]
  intro hZero; simp [hZero]

theorem iterateRec_eq_iterate {α : Type*} {b : ℕ} {h : b ≥ 2} (op : α → α) (n : Nat) :
    Nat.iterateRec op n b h = op^[n] := by
  induction n using Nat.caseStrongRecOn with
  | zero => simp [Nat.iterateRec]
  | ind k ih =>
    unfold Nat.iterateRec
    have : (k + 1) / b ≤ k := by
      refine Nat.le_of_lt_add_one ?_
      obtain hPos : k + 1 > 0 := by omega
      exact Nat.div_lt_self hPos h
    rw [ih ((k + 1) / b) this, ←iterate_mul, ←iterate_add, Nat.mod_add_div' (k + 1) b]
    simp

theorem iterateBin_eq_iterate {α : Type*} (op : α → α) (n : Nat) :
    op^[n]₂ = op^[n] := by simp [Nat.iterateBin, iterateRec_eq_iterate]

end Function

namespace List

universe u v w

variable {m : Type u → Type v} [Monad m] [LawfulMonad m] {α : Type w} {β : Type u}
    (f : α → β) (l : List α)

theorem mapM_single (f : α → m β) (a : α) : List.mapM f [a] = return [← f a] := by
  rw [← List.mapM'_eq_mapM]
  simp only [mapM', bind_pure_comp, map_pure]

@[simp]
theorem getLastI_append_single [Inhabited α] (x : α) : (l ++ [x]).getLastI = x := by
  simp only [List.getLastI_eq_getLast?, List.getLast?_append, List.getLast?_singleton,
    Option.some_or]

variable {α : Type*} {unit : α}

@[simp] theorem leftpad_eq_self (l : List α) (n : Nat) (h : l.length ≥ n) :
    leftpad n unit l = l := by simp [leftpad, Nat.sub_eq_zero_of_le h]

@[simp] theorem rightpad_length (n : Nat) (unit : α) (l : List α) :
    (rightpad n unit l).length = max n l.length := by
  simp only [rightpad, length_append, length_replicate, Nat.add_comm l.length _, Nat.sub_add_eq_max]

@[simp] theorem rightpad_prefix (n : Nat) (unit : α) (l : List α) :
    l <+: rightpad n unit l := by
  simp only [IsPrefix, rightpad]
  exact Exists.intro (replicate (n - l.length) unit) rfl

@[simp] theorem rightpad_suffix (n : Nat) (unit : α) (l : List α) :
    replicate (n - l.length) unit <:+ rightpad n unit l := by
  simp only [IsSuffix, rightpad]
  exact Exists.intro l rfl

@[simp] theorem rightpad_eq_self (l : List α) (n : Nat) (h : n ≤ l.length) :
    rightpad n unit l = l := by simp [rightpad, Nat.sub_eq_zero_of_le h]

theorem rightpad_eq_rightpad_max (l : List α) (n : Nat) :
    rightpad n unit l = rightpad (max n l.length) unit l := by simp [rightpad]; omega

theorem rightpad_eq_rightpad_append_replicate_of_ge
  (l : List α) (m n : Nat) (h : n ≤ m) :
    rightpad m unit l = rightpad n unit l ++ replicate (m - max n l.length) unit := by
  simp [rightpad]; omega

theorem rightpad_eq_if_rightpad_eq_of_ge (l l' : List α) (m n n' : Nat) (h : n ≤ m) (h' : n' ≤ m) :
    rightpad n unit l = rightpad n' unit l' →
        rightpad m unit l = rightpad m unit l' := by
  intro hEq
  rw [rightpad_eq_rightpad_append_replicate_of_ge l _ n h]
  rw [rightpad_eq_rightpad_append_replicate_of_ge l' _ n' h']
  have hLen : max n l.length = max n' l'.length := calc
    max n l.length = (rightpad n unit l).length := Eq.symm (rightpad_length n unit l)
    _ = (rightpad n' unit l').length := congrArg length hEq
    _ = max n' l'.length := rightpad_length n' unit l'
  simp [hEq, hLen]
  sorry

@[simp] theorem rightpad_twice_eq_rightpad_max (m n : Nat) (unit : α) (l : List α) :
    rightpad n unit (rightpad m unit l) = rightpad (max m n) unit l := by
  rw (config := { occs := .neg [0] }) [rightpad, rightpad_length]
  simp [rightpad]
  by_cases h : m.max n ≤ l.length
  · simp [Nat.max_le.mp h]
  · refine Nat.eq_sub_of_add_eq ?_
    conv => { enter [1, 1]; rw [Nat.add_comm] }
    rw [Nat.add_assoc, Nat.sub_add_eq_max, Nat.sub_add_eq_max]
    simp at h
    by_cases h' : m ≤ l.length <;> omega

-- lemma getD_eq_getElem {l : List α} {i : Nat} {unit : α} (hi : i < l.length) :
--     l.getD i unit = l[i] := by
--   rw [getD_eq_getElem?_getD, getElem?_eq_getElem hi, Option.getD_some]

-- lemma getD_eq_default {l : List α} {i : Nat} {unit : α} (hi : i ≥ l.length) :
--     l.getD i unit = unit := by
--   rw [getD_eq_getElem?_getD, getElem?_eq_none hi, Option.getD_none]

@[simp] theorem rightpad_getD_eq_getD (l : List α) (n : Nat) (unit : α) (i : Nat) :
    (rightpad n unit l).getD i unit = l.getD i unit := by
  rcases (Nat.lt_or_ge i l.length) with h_lt | h_ge
  · have h_lt': i < (rightpad n unit l).length := by rw [rightpad_length]; omega
    simp only [h_lt, h_lt', getD_eq_getElem] -- eliminate `getD`
    simp [h_lt, getElem_append]
  rw [getD_eq_default _ _ h_ge] -- eliminate second `getD` for `unit`
  rcases (Nat.lt_or_ge i n) with h_lt₂ | h_ge₂
  · have h_lt' : i < (rightpad n unit l).length := by rw [rightpad_length]; omega
    rw [getD_eq_getElem _ _ h_lt'] -- eliminate first `getD`
    simp [h_ge, getElem_append]
  · have h_ge' : i ≥ (rightpad n unit l).length := by rw [rightpad_length]; omega
    rw [getD_eq_default _ _ h_ge'] -- eliminate first `getD`

theorem rightpad_getElem_eq_getD {a b : List α} {unit : α} {i : Nat}
  (h: i < (a.rightpad b.length unit).length) :
    (a.rightpad b.length unit)[i] = a.getD i unit := by
  rw [← rightpad_getD_eq_getD a b.length, getD_eq_getElem _ _ h]

/-- Given two lists of potentially different lengths, right-pads the shorter list with `unit`
  elements until they are the same length. -/
def matchSize (l₁ : List α) (l₂ : List α) (unit : α) : List α × List α :=
  (l₁.rightpad (l₂.length) unit, l₂.rightpad (l₁.length) unit)

theorem matchSize_comm (l₁ : List α) (l₂ : List α) (unit : α) :
    matchSize l₁ l₂ unit = (matchSize l₂ l₁ unit).swap := by
  simp [matchSize]

/-- `List.matchSize` returns two equal lists iff the two lists agree at every index `i : Nat`
  (extended by `unit` if necessary). -/
theorem matchSize_eq_iff_forall_eq (l₁ l₂ : List α) (unit : α) :
    (fun (x, y) => x = y) (matchSize l₁ l₂ unit) ↔ ∀ i : Nat, l₁.getD i unit = l₂.getD i unit :=
  by sorry
    -- TODO: finish this lemma based on `rightpad_getD_eq_getD`

/-- `List.dropWhile` but starting from the last element. Performed by `dropWhile` on the reversed
  list, followed by a reversal. -/
def dropLastWhile (p : α → Bool) (l : List α) : List α :=
  (l.reverse.dropWhile p).reverse

lemma zipWith_const {α β : Type _} {f : α → β → β} {l₁ : List α} {l₂ : List β}
  (h₁ : l₁.length = l₂.length) (h₂ : ∀ a b, f a b = b) : l₁.zipWith f l₂ = l₂ := by
  induction' l₁ with hd tl ih generalizing l₂ <;> rcases l₂ <;> aesop

end List

-- abbrev isBoolean {R : Type _} [Zero R] [One R] (x : R) : Prop := x = 0 ∨ x = 1

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
  | nil => simp_all [h]
  | cons hd tl ih => simp_all [ih, h, size_eq_length_toList]

theorem rightpad_toList {a : Array α} {n : Nat} {unit : α} :
    a.rightpad n unit = mk (a.toList.rightpad n unit) := by
  induction h : a.toList with
  | nil => simp_all [h]
  | cons hd tl ih => simp_all [ih, h, size_eq_length_toList]

theorem rightpad_getElem_eq_getD {a : Array α} {n : Nat} {unit : α} {i : Nat}
    (h : i < (a.rightpad n unit).size) : (a.rightpad n unit)[i] = a.getD i unit := by
  simp_rw [rightpad_toList] at h ⊢
  sorry

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
def findIdxRev?_def {cond} {as: Array α} {k : Fin as.size} :
  findIdxRev? cond as = some k → cond as[k] := by
  suffices aux : ∀ i, findIdxRev?.find cond as i = some k → cond as[k] by apply aux
  intro i
  unfold findIdxRev?.find
  induction i using findIdxRev?.find.induct cond as with
  | case1 => simp
  | case2 => simp [*]; rintro rfl; assumption
  | case3 => unfold findIdxRev?.find; simp [*]; assumption

/-- if findIdxRev? finds an index, then for every greater index the condition doesn't hold -/
def findIdxRev?_maximal {cond} {as: Array α} {k : Fin as.size} :
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
theorem findIdxRev?_eq_some {cond} {as : Array α} (h: ∃ i, ∃ hi : i < as.size, cond as[i]) :
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

namespace List

namespace Vector

variable {α : Type*}

def interleave {n : Nat} (xs : Vector α n) (ys : Vector α n) : Vector α (2 * n) := sorry

-- def pairwise {α : Type} {n : Nat} (v : Vector α (2 * n)) : Vector (α × α) n :=
--   Vector.ofFn (fun i =>
--     let j := 2 * i
--     (v.get ⟨j, by omega; exact i.isLt⟩,
--      v.get ⟨j + 1, by simp [Nat.mul_two, Nat.lt_succ]; exact i.isLt⟩))

def chunkPairwise {α : Type} : {n : Nat} → Vector α (2 * n) → Vector (α × α) n
  | 0, Vector.nil => Vector.nil
  | n + 1, xs => by
    have : 2 * (n + 1) = 2 * n + 2 := by omega
    rw [this] at xs
    exact ⟨xs.head, xs.tail.head⟩ ::ᵥ chunkPairwise xs.tail.tail

end Vector

end List

/-- Equivalence between `α` and the sum of `{a // p a}` and `{a // ¬ p a}` -/
@[simps]
def subtypeSumComplEquiv {α : Type*} {p : α → Prop} [DecidablePred p] :
    {a // p a} ⊕ {a // ¬ p a} ≃ α where
  toFun := fun x => match x with
    | Sum.inl a => a.1
    | Sum.inr a => a.1
  invFun := fun x =>
    if h : p x then Sum.inl ⟨x, h⟩ else Sum.inr ⟨x, h⟩
  left_inv := fun x => match x with
    | Sum.inl a => by simp [a.2]
    | Sum.inr a => by simp [a.2]
  right_inv := fun x => by simp; split_ifs <;> simp

namespace List

-- TODO: put this elsewhere (for some reason `@[to_additive]` doesn't work)
def partialSum {α : Type*} [AddMonoid α] (l : List α) : List α :=
  [0] ++ match l with
  | [] => []
  | a :: l' => (partialSum l').map (a + ·)

@[to_additive existing]
def partialProd {α : Type*} [Monoid α] (l : List α) : List α :=
  [1] ++ match l with
  | [] => []
  | a :: l' => (partialProd l').map (a * ·)

@[simp]
theorem partialSum_nil : [].partialSum = [0] := rfl

variable {α : Type*} [AddMonoid α]

@[simp]
theorem partialSum_succ {a : α} {l : List α} :
    (a :: l).partialSum = [0] ++ (partialSum l).map (a + ·) := rfl

variable [Preorder α] [DecidableRel ((· < ·) : α → α → Prop)]

-- Pinpoint the first element in the list whose partial sum up to that point is more than `j`
def findSum (l : List α) (j : α) : Option α := l.partialSum.find? (j < ·)

-- TODO: extend theorems to more general types than just `ℕ`

theorem findSum_of_le_sum {l : List ℕ} {j : ℕ} (h : j < l.sum) : ∃ n, findSum l j = some n := by
  match l with
  | [] => simp only [sum_nil, not_lt_zero'] at h ⊢
  | a :: l' =>
    simp at h
    sorry
    -- by_cases h' : j < a
    -- · use a
    --   simp [findSum, h', findSome?_cons]
    -- · simp [findSum, h'] at h
    --   specialize @findSum_of_le_sum l' (j - a)
    --   simp at h

-- Pinpoint the first index in the list whose partial sum is more than `j`
def findSumIdx (l : List α) (j : α) : ℕ := l.partialSum.findIdx (j < ·)

-- Variant of `findSumIdx` with bounds
def findSumIdx' (l : List ℕ) (j : Fin l.sum) : Fin l.length := ⟨findSumIdx l j, sorry⟩

def findSumIdxWith (l : List ℕ) (j : Fin l.sum) : (i : Fin l.length) × Fin (l.get i) := sorry

@[simp]
theorem ranges_length_eq_self_length {l : List ℕ} : l.ranges.length = l.length := by
  induction l with
  | nil => simp only [List.ranges, List.length_nil]
  | cons n l' ih => simp only [List.ranges, List.length_cons, List.length_map, ih]

@[simp]
theorem ranges_nil : List.ranges [] = [] := rfl

@[simp]
theorem ranges_succ {a : ℕ} {l : List ℕ} :
    List.ranges (a :: l) = range a :: l.ranges.map (map (a + ·)) := rfl

end List
