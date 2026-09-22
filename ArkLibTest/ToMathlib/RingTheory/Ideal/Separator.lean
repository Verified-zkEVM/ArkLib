/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.RingTheory.Ideal.Separator
import Mathlib.RingTheory.Int.Basic

/-!
# Acceptance tests for separators of prime families

The examples produce separators for the primes `(2)` and `(3)` of `ℤ` and check a concrete
choice by hand, show that a comparable family `(0) ≤ (2)` has no separators, treat the family with
one prime, and derive the source-shaped statement, with separate conditions for `s i ∉ P i` and
`s i ∈ P j`, from the general one.
-/

namespace SeparatorTest

open Ideal

/-- The ideal `(p)` of `ℤ` for a prime number `p` is prime. -/
theorem isPrime_span_int {p : ℕ} (hp : p.Prime) : (span {(p : ℤ)}).IsPrime :=
  (span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hp)

/-- The primes `(2)` and `(3)` of `ℤ` are incomparable, so they have separators. -/
example : ∃ s : Fin 2 → ℤ, ∀ i j, s i ∈ ![span {(2 : ℤ)}, span {3}] j ↔ i ≠ j := by
  refine exists_separators_of_pairwise_not_le (fun i ↦ ?_) fun i j hij ↦ ?_
  · fin_cases i
    · exact isPrime_span_int (p := 2) Nat.prime_two
    · exact isPrime_span_int (p := 3) Nat.prime_three
  · fin_cases i <;> fin_cases j <;> simp_all [mem_span_singleton]

/-- A concrete choice of separators for `(2)` and `(3)`: `3` lies in `(3)` and not in `(2)`, and
`2` lies in `(2)` and not in `(3)`. -/
example : ∀ i j : Fin 2, ![(3 : ℤ), 2] i ∈ ![span {(2 : ℤ)}, span {3}] j ↔ i ≠ j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [mem_span_singleton]

/-- Incomparability is needed: for the comparable primes `(0) ≤ (2)` of `ℤ`, a separator for
`(2)` would lie in `(0)` and not in `(2)`, which is impossible. -/
example : ¬∃ s : Fin 2 → ℤ, ∀ i j, s i ∈ ![(⊥ : Ideal ℤ), span {2}] j ↔ i ≠ j := by
  rintro ⟨s, hs⟩
  have h0 : s 1 ∈ (⊥ : Ideal ℤ) := (hs 1 0).mpr (by decide)
  have h1 : s 1 ∉ span {(2 : ℤ)} := fun h ↦ (hs 1 1).mp h rfl
  rw [mem_bot] at h0
  exact h1 (h0 ▸ zero_mem _)

/-- A family with one prime has a separator outside that prime. -/
example {R : Type*} [CommRing R] (P : Ideal R) [hP : P.IsPrime] :
    ∃ s : Unit → R, s () ∉ P := by
  obtain ⟨s, hs⟩ := exists_separators_of_pairwise_not_le (P := fun _ : Unit ↦ P) (fun _ ↦ hP)
    (fun i j hij ↦ absurd (Subsingleton.elim i j) hij)
  exact ⟨s, fun h ↦ (hs () ()).mp h rfl⟩

/-- The source's form: separate conditions `s i ∉ P i` and `s i ∈ P j` for `i ≠ j`, with
incomparability stated for `i ≠ j`. -/
example {R ι : Type*} [CommRing R] [Fintype ι] (P : ι → Ideal R) (hP : ∀ i, (P i).IsPrime)
    (hinc : ∀ ⦃i j⦄, i ≠ j → ¬P i ≤ P j) :
    ∃ s : ι → R, (∀ i, s i ∉ P i) ∧ ∀ i j, i ≠ j → s i ∈ P j := by
  obtain ⟨s, hs⟩ := exists_separators_of_pairwise_not_le hP hinc
  exact ⟨s, fun i h ↦ (hs i i).mp h rfl, fun i j hij ↦ (hs i j).mpr hij⟩

/-- Distinct minimal primes over one ideal are incomparable, so any finite family of them has
separators. -/
example {R ι : Type*} [CommRing R] [Finite ι] {I : Ideal R} (P : ι → Ideal R)
    (hP : ∀ i, P i ∈ I.minimalPrimes) (hinj : Function.Injective P) :
    ∃ s : ι → R, ∀ i j, s i ∈ P j ↔ i ≠ j :=
  exists_separators_of_pairwise_not_le (fun i ↦ (hP i).isPrime)
    fun _ _ hij ↦ not_le_of_mem_minimalPrimes (hP _) (hP _) (hinj.ne hij)

end SeparatorTest
