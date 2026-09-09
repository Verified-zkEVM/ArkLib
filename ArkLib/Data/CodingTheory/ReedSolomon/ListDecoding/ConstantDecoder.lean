/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Output.AgreementMachine
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.SeparateSample.SeparateSampleFieldExecution
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
open SeparateSampleFieldExecution (ExactOutput)

variable [Field F] [DecidableEq F]

/-- Execute the constant decoder directly on an indexed received word. -/
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

/-- Literal Reed--Solomon exact-output contract for message dimension one. -/
theorem run_exact {n : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (threshold : ℕ) (hthreshold : 1 ≤ threshold) :
    ExactOutput domain received 1 threshold (run cmp threshold received) := by
  refine ⟨?_, decode_nodup cmp threshold (List.ofFn received), ?_, ?_⟩
  · rw [run,
      List.nodup_map_iff_inj_on (decode_nodup cmp threshold (List.ofFn received))]
    intro left hleft right hright hequal
    obtain ⟨leftValue, rfl, _⟩ :=
      (mem_decode_iff_exists cmp threshold (List.ofFn received) left hthreshold).mp hleft
    obtain ⟨rightValue, rfl, _⟩ :=
      (mem_decode_iff_exists cmp threshold (List.ofFn received) right hthreshold).mp hright
    rw [singleton_polynomial, singleton_polynomial] at hequal
    exact congrArg List.singleton (Polynomial.C_injective hequal)
  · intro polynomial
    constructor
    · intro hpolynomial
      obtain ⟨coefficients, hcoefficients, rfl⟩ := List.mem_map.mp hpolynomial
      obtain ⟨value, rfl, hcount⟩ :=
        (mem_decode_iff_exists cmp threshold (List.ofFn received) coefficients hthreshold).mp
          hcoefficients
      rw [singleton_polynomial]
      exact ⟨Polynomial.degree_C_lt,
        (count_eq_agree_constant domain received value) ▸ hcount⟩
    · rintro ⟨hdegree, hagree⟩
      have hconstant := degree_lt_one_eq_constant hdegree
      let value := polynomial.coeff 0
      have hcount : threshold ≤ (List.ofFn received).count value := by
        rw [count_eq_agree_constant domain received value]
        simpa [value, ← hconstant] using hagree
      apply List.mem_map.mpr
      exact ⟨[value], (mem_decode_iff cmp threshold _ value hthreshold).mpr hcount,
        by simpa [singleton_polynomial, value] using hconstant.symm⟩
  · intro coefficients
    constructor
    · intro hcoefficients
      obtain ⟨value, rfl, hcount⟩ :=
        (mem_decode_iff_exists cmp threshold (List.ofFn received) coefficients hthreshold).mp
          hcoefficients
      simp only [List.length_singleton, singleton_polynomial]
      exact ⟨trivial, Polynomial.degree_C_lt,
        (count_eq_agree_constant domain received value) ▸ hcount⟩
    · rintro ⟨hlength, _, hagree⟩
      obtain ⟨value, rfl⟩ := List.length_eq_one_iff.mp hlength
      apply (mem_decode_iff cmp threshold _ value hthreshold).mpr
      rw [count_eq_agree_constant domain received value]
      simpa only [singleton_polynomial] using hagree

end ExactOutput

end ReedSolomon.ListDecoding.ConstantDecoder
