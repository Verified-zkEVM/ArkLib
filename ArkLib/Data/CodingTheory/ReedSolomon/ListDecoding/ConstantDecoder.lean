/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Mathlib.Data.List.Count
import Mathlib.Data.List.Nodup
import Std.Data.TreeMap.Lemmas

/-!
# Executable decoder for constant Reed--Solomon messages

For message dimension `k = 1`, decoding is frequency counting: return `[c]`
exactly when `c` occurs at least `A` times.  The implementation accumulates
counts in a balanced tree map and therefore does not enumerate the field or
perform a quadratic duplicate-elimination scan.  Its comparison requirements
are explicit so concrete prime-field implementations can supply them.
-/

namespace ReedSolomon.ListDecoding.ConstantDecoder

variable {F : Type*} [BEq F] [LawfulBEq F]
variable (cmp : F → F → Ordering) [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]

/-- Increment an optional frequency, creating a count of one when absent. -/
def increment : Option ℕ → Option ℕ
  | none => some 1
  | some count => some (count + 1)

/-- Count received values in a balanced comparison tree. -/
def frequencyMap : List F → Std.TreeMap F ℕ cmp
  | [] => {}
  | value :: values => (frequencyMap values).alter value increment

/-- Return singleton coefficient lists for values meeting the agreement
threshold. -/
def decode (threshold : ℕ) (received : List F) : List (List F) :=
  (frequencyMap cmp received).toList.filterMap fun entry =>
    if threshold ≤ entry.2 then some [entry.1] else none

/-- The tree stores exactly the positive list frequency of each value. -/
theorem getElem?_frequencyMap (value : F) (received : List F) :
    (frequencyMap cmp received)[value]? =
      if received.count value = 0 then none else some (received.count value) := by
  induction received with
  | nil => simp [frequencyMap]
  | cons head tail ih =>
      rw [frequencyMap, Std.TreeMap.getElem?_alter]
      by_cases heq : head = value
      · subst head
        have hcompare : cmp value value = .eq :=
          Std.LawfulEqCmp.compare_eq_iff_eq.mpr rfl
        simp only [hcompare, ↓reduceIte, ih]
        by_cases hzero : tail.count value = 0 <;> simp [increment, hzero]
      · rw [if_neg (fun h => heq (Std.LawfulEqCmp.compare_eq_iff_eq.mp h)), ih]
        simp [heq]

/-- Exact `k = 1` membership: `[value]` is returned exactly at frequency at
least `threshold`. -/
theorem mem_decode_iff (threshold : ℕ) (received : List F) (value : F)
    (hthreshold : 1 ≤ threshold) :
    [value] ∈ decode cmp threshold received ↔ threshold ≤ received.count value := by
  rw [decode, List.mem_filterMap]
  constructor
  · rintro ⟨⟨key, count⟩, hentry, hselected⟩
    split at hselected
    · injection hselected with hkey
      have hkey' : key = value := by simpa using hkey
      subst key
      have hstored := (Std.TreeMap.mem_toList_iff_getElem?_eq_some).mp hentry
      rw [getElem?_frequencyMap] at hstored
      split at hstored
      · contradiction
      · injection hstored with hcount
        omega
    · contradiction
  · intro hcount
    have hpositive : received.count value ≠ 0 := by omega
    have hentry : (value, received.count value) ∈ (frequencyMap cmp received).toList := by
      rw [Std.TreeMap.mem_toList_iff_getElem?_eq_some, getElem?_frequencyMap,
        if_neg hpositive]
    exact ⟨(value, received.count value), hentry, by simp [hcount]⟩

omit [BEq F] [LawfulBEq F] in
/-- The decoder never repeats a coefficient list. -/
theorem decode_nodup (threshold : ℕ) (received : List F) :
    (decode cmp threshold received).Nodup := by
  have hpairwise : (decode cmp threshold received).Pairwise (· ≠ ·) := by
    apply (Std.TreeMap.distinct_keys_toList
      (t := frequencyMap cmp received)).filterMap
    intro left right hdistinct leftOutput hleft rightOutput hright
    split at hleft <;> split at hright
    · injection hleft with hleftEq
      injection hright with hrightEq
      subst leftOutput
      subst rightOutput
      intro hequal
      apply hdistinct
      apply Std.LawfulEqCmp.compare_eq_iff_eq.mpr
      simpa using hequal
    all_goals contradiction
  exact List.nodup_iff_pairwise_ne.mpr hpairwise

end ReedSolomon.ListDecoding.ConstantDecoder
