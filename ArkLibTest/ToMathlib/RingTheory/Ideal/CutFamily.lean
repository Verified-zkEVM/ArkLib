/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.RingTheory.Ideal.CutFamily
import Mathlib.RingTheory.Int.Basic

/-!
# Acceptance tests for iterated retained cut families

These examples use the public API through an ordinary import, in the Noetherian ring `ℤ`. They
compute the iterated family of `{(0)}` cut by `2` and then by `4` to be `{(2)}`, show that the
same cuts retained by `s = 2` give the empty family, and use this to check that the covering
property needs `s ∉ Q` and that `retainedCutFamily_of_forall_mem` needs `s ∉ P`. They check that
primality of the members for `cuts = []` really needs primality of the starting family, that the
retained minimal primes of the total cut lie in the family, and they apply the abstract weight
bound to the weight counting the zero ideal.
-/

namespace Ideal

/-- `(2)` is a prime of `ℤ`. -/
theorem isPrime_span_two : (span {(2 : ℤ)}).IsPrime :=
  (span_singleton_prime (by norm_num)).mpr (Int.prime_iff_natAbs_prime.mpr Nat.prime_two)

/-- Cutting `{(0)}` by `2` and keeping primes that avoid `s` gives `{(2)}` when `2 ∤ s`. -/
theorem retainedCutFamily_bot_two {s : ℤ} (hs : s ∉ span {(2 : ℤ)}) :
    retainedCutFamily {(⊥ : Ideal ℤ)} s 2 = {span {2}} := by
  have := isPrime_span_two
  ext Q
  simp only [mem_retainedCutFamily, Finset.mem_singleton, exists_eq_left, bot_sup_eq,
    mem_retainedMinimalPrimes, minimalPrimes_eq_subsingleton_self, Set.mem_singleton_iff,
    and_iff_left_iff_imp]
  rintro rfl
  exact hs

/-- `1 ∉ (2)`. -/
theorem one_notMem_span_two : (1 : ℤ) ∉ span {(2 : ℤ)} := by
  rw [mem_span_singleton]
  norm_num

/-- A concrete iterated family: cutting `{(0)}` by `2` gives `{(2)}`, and the second cut by
`4 ∈ (2)` changes nothing (`retainedCutFamily_of_forall_mem`). -/
theorem iteratedRetainedCutFamily_two_four :
    iteratedRetainedCutFamily {(⊥ : Ideal ℤ)} 1 [2, 4] = {span {2}} := by
  rw [iteratedRetainedCutFamily_cons, retainedCutFamily_bot_two one_notMem_span_two,
    iteratedRetainedCutFamily_cons, iteratedRetainedCutFamily_nil]
  refine retainedCutFamily_of_forall_mem fun P hP ↦ ?_
  rw [Finset.mem_singleton.mp hP]
  exact ⟨isPrime_span_two, one_notMem_span_two, mem_span_singleton.mpr (by norm_num)⟩

/-- Retaining by `s = 2` removes the only component `(2)`: the family is empty. -/
theorem iteratedRetainedCutFamily_two_retained_by_two :
    iteratedRetainedCutFamily {(⊥ : Ideal ℤ)} 2 [2] = ∅ := by
  have := isPrime_span_two
  rw [iteratedRetainedCutFamily_cons, iteratedRetainedCutFamily_nil]
  ext Q
  simp only [mem_retainedCutFamily, Finset.mem_singleton, exists_eq_left, bot_sup_eq,
    mem_retainedMinimalPrimes, minimalPrimes_eq_subsingleton_self, Set.mem_singleton_iff,
    Finset.notMem_empty, iff_false, not_and, not_not]
  rintro rfl
  exact mem_span_singleton_self 2

/-- The members computed by `iteratedRetainedCutFamily_two_four` contain `(0)` and both cuts, as
`exists_le_of_mem_iteratedRetainedCutFamily` says. -/
example : ∀ Q ∈ iteratedRetainedCutFamily {(⊥ : Ideal ℤ)} 1 [2, 4],
    (2 : ℤ) ∈ Q ∧ (4 : ℤ) ∈ Q := fun Q hQ ↦ by
  obtain ⟨-, -, -, h⟩ := exists_le_of_mem_iteratedRetainedCutFamily hQ
  exact ⟨h 2 (by simp), h 4 (by simp)⟩

/-- The covering property applied to the prime `(2)`, which contains `(0)` and both cuts and does
not contain `1`. -/
example : ∃ J ∈ iteratedRetainedCutFamily {(⊥ : Ideal ℤ)} 1 [2, 4], J ≤ span {2} := by
  have := isPrime_span_two
  obtain ⟨J, hJ, -, hJQ⟩ := exists_mem_iteratedRetainedCutFamily_le (Ps := {(⊥ : Ideal ℤ)})
    (cuts := [2, 4]) (Finset.mem_singleton_self _) bot_le one_notMem_span_two
    (by simp [mem_span_singleton])
  exact ⟨J, hJ, hJQ⟩

/-- The covering property needs `s ∉ Q`: the prime `(2)` contains `(0)` and the cut `2`, but with
`s = 2 ∈ (2)` the family has no member at all. -/
example : ¬ ∃ J ∈ iteratedRetainedCutFamily {(⊥ : Ideal ℤ)} 2 [2], J ≤ span {2} := by
  rw [iteratedRetainedCutFamily_two_retained_by_two]
  simp

/-- `retainedCutFamily_of_forall_mem` needs `s ∉ P`: the prime `(2)` contains the cut `4`, but a
cut retained by `2` drops it. -/
example : retainedCutFamily {span {(2 : ℤ)}} 2 4 ≠ {span {2}} := by
  have := isPrime_span_two
  intro h
  have hmem : span {(2 : ℤ)} ∈ retainedCutFamily {span {(2 : ℤ)}} 2 4 :=
    by rw [h]; exact Finset.mem_singleton_self _
  exact (of_mem_retainedCutFamily hmem).2.2.2 (mem_span_singleton_self 2)

/-- For `cuts = []` the family is the starting family, so primality of the members needs
primality of `Ps`: `(4)` is not prime. -/
example : ∃ Q ∈ iteratedRetainedCutFamily {span {(4 : ℤ)}} 1 [], ¬ Q.IsPrime := by
  refine ⟨span {4}, Finset.mem_singleton_self _, fun h ↦ ?_⟩
  have := h.mem_or_mem (x := 2) (y := 2) (mem_span_singleton.mpr (by norm_num))
  simp only [or_self, mem_span_singleton] at this
  norm_num at this

/-- The retained minimal prime `(2)` of the total cut `(0) ⊔ (2, 4)` is a member. -/
example : span {(2 : ℤ)} ∈ iteratedRetainedCutFamily {(⊥ : Ideal ℤ)} 1 [2, 4] := by
  have := isPrime_span_two
  refine retainedMinimalPrimes_subset_iteratedRetainedCutFamily
    (fun P hP ↦ Finset.mem_singleton.mp hP ▸ isPrime_bot) (Finset.mem_singleton_self _) 1 [2, 4]
    (mem_retainedMinimalPrimes.mpr ⟨?_, one_notMem_span_two⟩)
  have hspan : (⊥ : Ideal ℤ) ⊔ span {f | f ∈ [(2 : ℤ), 4]} = span {2} := by
    rw [bot_sup_eq]
    refine le_antisymm (span_le.mpr ?_) (span_mono (by simp))
    intro f hf
    change f ∈ [(2 : ℤ), 4] at hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl
    · exact mem_span_singleton_self 2
    · exact mem_span_singleton.mpr (by norm_num)
  rw [hspan, minimalPrimes_eq_subsingleton_self]
  rfl

/-- The abstract weight bound, for the weight `1` on `(0)` and `0` elsewhere: in the domain `ℤ`
cutting by a nonzero element never produces `(0)`, and cutting by `0` returns the prime itself, so
the number of zero ideals in the family never increases. -/
example (Ps : Finset (Ideal ℤ)) (hprime : ∀ P ∈ Ps, P.IsPrime) (s : ℤ) (cuts : List ℤ) :
    ∑ Q ∈ iteratedRetainedCutFamily Ps s cuts, (if Q = ⊥ then 1 else 0 : ℕ) ≤
      ∑ P ∈ Ps, (if P = ⊥ then 1 else 0 : ℕ) := by
  refine sum_iteratedRetainedCutFamily_le _ (fun _ ↦ Nat.zero_le _) hprime s cuts ?_
  intro P hP f _
  have := hP
  by_cases hf : f = 0
  · subst f
    rw [span_singleton_eq_bot.mpr rfl, sup_bot_eq]
    refine (Finset.sum_le_sum_of_subset (retainedMinimalPrimes_subset P s)).trans ?_
    rw [minimalPrimesFinset_of_isPrime, Finset.sum_singleton]
  · refine (Finset.sum_eq_zero fun Q hQ ↦ ?_).trans_le (Nat.zero_le _)
    split_ifs with hQbot
    swap
    · rfl
    subst hQbot
    have hfQ := (mem_retainedMinimalPrimes.mp hQ).1.le
      (mem_sup_right (mem_span_singleton_self f))
    exact hf ((Submodule.mem_bot ℤ).mp hfQ)

end Ideal
