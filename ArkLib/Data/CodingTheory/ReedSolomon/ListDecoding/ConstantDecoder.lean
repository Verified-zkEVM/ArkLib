/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.ExactOutput
public import Mathlib.Data.List.Count
public import Mathlib.Data.List.Nodup
public import Std.Data.TreeMap.Lemmas

/-!
# Executable decoder for constant Reed--Solomon messages

For message dimension `k = 1`, decoding is frequency counting: return `[c]`
exactly when `c` occurs at least `A` times.  The implementation accumulates
counts in a balanced tree map and therefore does not enumerate the field or
perform a quadratic duplicate-elimination scan.  Its comparison requirements
are explicit so concrete prime-field implementations can supply them.

The exact-output theorem assumes a positive threshold. At threshold zero,
exactness would require every field constant, including values absent from the
received word, whereas the frequency map deliberately stores only observed
values.
-/

@[expose] public section

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

/-- Every returned vector is a singleton meeting the positive frequency threshold. -/
theorem mem_decode_iff_exists (threshold : ℕ) (received : List F) (output : List F)
    (hthreshold : 1 ≤ threshold) :
    output ∈ decode cmp threshold received ↔
      ∃ value, output = [value] ∧ threshold ≤ received.count value := by
  rw [decode, List.mem_filterMap]
  constructor
  · rintro ⟨⟨key, count⟩, hentry, hselected⟩
    split at hselected
    · injection hselected with houtput
      have hstored := (Std.TreeMap.mem_toList_iff_getElem?_eq_some).mp hentry
      rw [getElem?_frequencyMap] at hstored
      split at hstored
      · contradiction
      · injection hstored with hcount
        exact ⟨key, houtput.symm, by omega⟩
    · contradiction
  · rintro ⟨value, rfl, hcount⟩
    have hpositive : received.count value ≠ 0 := by
      omega
    have hentry : (value, received.count value) ∈ (frequencyMap cmp received).toList := by
      rw [Std.TreeMap.mem_toList_iff_getElem?_eq_some, getElem?_frequencyMap,
        if_neg hpositive]
    exact ⟨(value, received.count value), hentry, by simp [hcount]⟩

section ExactOutput

open Polynomial JetHornerMachine

variable [Field F] [DecidableEq F]

/-- Execute the constant decoder directly on an indexed received word.

The evaluation domain is unnecessary at runtime because every dimension-one
codeword is constant. It appears only in `run_exact`, where agreement is stated
using the common Reed--Solomon contract.
-/
def run {n : ℕ} (threshold : ℕ) (received : Fin n → F) : List (List F) :=
  decode cmp threshold (List.ofFn received)

omit [Field F] in
private theorem count_ofFn_eq_agree_constant {n : ℕ}
    (received : Fin n → F) (value : F) :
    (List.ofFn received).count value = Code.agree (fun _ => value) received := by
  rw [List.count_eq_length_filter]
  change (List.filter (fun x => x == value) (List.ofFn received)).length =
    (Finset.univ.filter fun i => value = received i).card
  rw [Finset.card_filter]
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.ofFn_succ, List.filter_cons, Fin.sum_univ_succ]
      by_cases h : received 0 = value
      · simp only [h, beq_self_eq_true, ↓reduceIte, List.length_cons]
        rw [ih]
        omega
      · simp only [beq_iff_eq, h, ↓reduceIte, Ne.symm h]
        rw [ih]
        simp

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
private theorem singleton_polynomial (value : F) :
    coefficientPolynomial [value] = C value := by
  simp [coefficientPolynomial]

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
private theorem degree_lt_one_eq_constant {polynomial : F[X]}
    (hdegree : polynomial.degree < 1) :
    polynomial = C (polynomial.coeff 0) := by
  by_cases hzero : polynomial = 0
  · simp [hzero]
  · apply Polynomial.eq_C_of_natDegree_eq_zero
    have : polynomial.natDegree < 1 :=
      (Polynomial.natDegree_lt_iff_degree_lt hzero).mpr hdegree
    omega

private theorem count_eq_agree_constant {n : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F) (value : F) :
    (List.ofFn received).count value =
      Code.agree (evalOnPoints domain (C value)) received := by
  rw [count_ofFn_eq_agree_constant]
  congr 1
  funext i
  simp [evalOnPoints]

/-- Literal Reed--Solomon exact-output contract for message dimension one.

This proves all four `ExactOutput` clauses: the decoded polynomials are unique,
the coefficient lists are unique, polynomial membership is exact, and
coefficient-list membership is exact. The positive-threshold premise is needed
because `run` visits observed values rather than enumerating the field.
-/
theorem run_exact {n : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (threshold : ℕ) (hthreshold : 1 ≤ threshold) :
    ExactOutput domain received 1 threshold (run cmp threshold received) := by
  -- Fixed width makes polynomial interpretation injective. The common constructor derives
  -- both duplicate-freedom clauses and vector exactness from these two semantic directions.
  apply exactOutput_of_sound_complete domain received 1 threshold _
    (decode_nodup cmp threshold (List.ofFn received))
  · intro coefficients hcoefficients
    -- A retained key yields exactly one coefficient and has enough indexed agreements.
    obtain ⟨value, rfl, hcount⟩ :=
      (mem_decode_iff_exists cmp threshold (List.ofFn received) coefficients hthreshold).mp
        hcoefficients
    simp only [List.length_singleton, singleton_polynomial]
    exact ⟨trivial, Polynomial.degree_C_lt,
      (count_eq_agree_constant domain received value) ▸ hcount⟩
  · intro polynomial hdegree hagree
    -- Degree below one forces a constant, so the frequency table cannot miss a wanted message.
    have hconstant := degree_lt_one_eq_constant hdegree
    let value := polynomial.coeff 0
    have hcount : threshold ≤ (List.ofFn received).count value := by
      rw [count_eq_agree_constant domain received value]
      simpa [value, ← hconstant] using hagree
    exact ⟨[value], (mem_decode_iff cmp threshold _ value hthreshold).mpr hcount,
      by simpa [singleton_polynomial, value] using hconstant.symm⟩

end ExactOutput

end ReedSolomon.ListDecoding.ConstantDecoder
