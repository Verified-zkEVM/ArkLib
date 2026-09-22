/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.RingTheory.Nullstellensatz.CutFamily
import Mathlib.Algebra.MvPolynomial.Division

/-!
# Acceptance tests for zero loci covered by iterated retained cut families

These examples use the public API through an ordinary import. In `ℚ[x, y]` they compute the cut of
`{⊥}` by `x`, retained by `s`, to be `{(x)}` when `x ∤ s`, and use the point cover to place the
point `(0, 5)` on `(x)`. The boundary example shows that the point cover needs `s(x) ≠ 0`: with
`s = x` the family is empty although the origin satisfies every other hypothesis. The last example
derives the point cover for a single cut.
-/

open MvPolynomial

namespace NullstellensatzCutFamilyTest

/-- The coordinate ring `ℚ[x, y]` of the plane. -/
local notation "R₂" => MvPolynomial (Fin 2) ℚ

/-- Cutting `{⊥}` by `x`, retained by `s`, gives `{(x)}` when `s ∉ (x)`. -/
theorem retainedCutFamily_bot_X0 {s : R₂} (hs : s ∉ Ideal.span {(X 0 : R₂)}) :
    Ideal.retainedCutFamily {(⊥ : Ideal R₂)} s (X 0) = {Ideal.span {X 0}} := by
  have : (Ideal.span {(X 0 : R₂)}).IsPrime :=
    (Ideal.span_singleton_prime (X_ne_zero 0)).mpr X_prime
  ext Q
  simp only [Ideal.mem_retainedCutFamily, Finset.mem_singleton, exists_eq_left, bot_sup_eq,
    Ideal.mem_retainedMinimalPrimes, Ideal.minimalPrimes_eq_subsingleton_self,
    Set.mem_singleton_iff, and_iff_left_iff_imp]
  rintro rfl
  exact hs

/-- The point cover places `(0, 5)`, a zero of `x`, on the only member `(x)` of the family of
`{⊥}` cut by `x`. -/
example : (![0, 5] : Fin 2 → ℚ) ∈ zeroLocus ℚ (Ideal.span {(X 0 : R₂)}) := by
  have h1 : (1 : R₂) ∉ Ideal.span {(X 0 : R₂)} := fun h ↦
    ((Ideal.span_singleton_prime (X_ne_zero 0)).mpr X_prime).ne_top
      ((Ideal.eq_top_iff_one _).mpr h)
  obtain ⟨Q, hQ, -, hxQ⟩ := exists_mem_iteratedRetainedCutFamily_of_mem_zeroLocus
    (Ps := {(⊥ : Ideal R₂)}) (s := 1) (cuts := [X 0]) (x := (![0, 5] : Fin 2 → ℚ))
    (Finset.mem_singleton_self _) (by simp [zeroLocus]) (by simp) (by simp)
  rw [Ideal.iteratedRetainedCutFamily_cons, Ideal.iteratedRetainedCutFamily_nil,
    retainedCutFamily_bot_X0 h1, Finset.mem_singleton] at hQ
  exact hQ ▸ hxQ

/-- The point cover needs `s(x) ≠ 0`: with `s = x`, the origin is a zero of `⊥` and of the cut
`x`, but the family of `{⊥}` cut by `x` and retained by `x` is empty. -/
example : ¬ ∃ Q ∈ Ideal.iteratedRetainedCutFamily {(⊥ : Ideal R₂)} (X 0) [X 0],
    (0 : Fin 2 → ℚ) ∈ zeroLocus ℚ Q := by
  have : (Ideal.span {(X 0 : R₂)}).IsPrime :=
    (Ideal.span_singleton_prime (X_ne_zero 0)).mpr X_prime
  rintro ⟨Q, hQ, -⟩
  rw [Ideal.iteratedRetainedCutFamily_cons, Ideal.iteratedRetainedCutFamily_nil,
    Ideal.mem_retainedCutFamily] at hQ
  obtain ⟨P, hP, hQ⟩ := hQ
  rw [Finset.mem_singleton.mp hP, bot_sup_eq, Ideal.mem_retainedMinimalPrimes,
    Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_singleton_iff] at hQ
  exact hQ.2 (hQ.1 ▸ Ideal.mem_span_singleton_self _)

/-- The point cover for a single cut `f`: the one-cut family is the iterated family for the list
`[f]`. -/
example {F σ E : Type*} [Field F] [Finite σ] [Field E] [Algebra F E]
    (Ps : Finset (Ideal (MvPolynomial σ F))) {s f : MvPolynomial σ F} (x : σ → E)
    (hx : ∃ P ∈ Ps, x ∈ zeroLocus E P) (hxf : aeval x f = 0) (hxs : aeval x s ≠ 0) :
    ∃ Q ∈ Ideal.retainedCutFamily Ps s f, x ∈ zeroLocus E Q := by
  obtain ⟨P, hP, hxP⟩ := hx
  obtain ⟨Q, hQ, -, hxQ⟩ := exists_mem_iteratedRetainedCutFamily_of_mem_zeroLocus (cuts := [f])
    hP hxP hxs (by simpa using hxf)
  exact ⟨Q, hQ, hxQ⟩

end NullstellensatzCutFamilyTest
