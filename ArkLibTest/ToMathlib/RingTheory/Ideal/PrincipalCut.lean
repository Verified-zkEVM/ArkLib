/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.RingTheory.Ideal.PrincipalCut
import Mathlib.RingTheory.Int.Basic

/-!
# Acceptance tests for principal-cut dimension drop

These examples exercise the public API through an ordinary import. They check that the generic
dimension and strictness statements do not require Noetherianity, that the retained-family
corollary has exactly the finiteness assumption needed by its indexing finset, and that the
non-membership and proper-cut boundaries are visible in the statement.
-/

namespace Ideal

/-- Strict quotient dimension drop needs only a commutative ring and primality of the smaller
ideal. -/
example {R : Type*} [CommRing R] {P J : Ideal R} [P.IsPrime] (hPJ : P < J) :
    ringKrullDim (R ⧸ J) + 1 ≤ ringKrullDim (R ⧸ P) :=
  ringKrullDim_quotient_succ_le_of_lt hPJ

/-- Principal-cut strictness exposes the essential hypothesis that the cutting element is not
already in the original prime. -/
example {R : Type*} [CommRing R] {P J : Ideal R} {f : R}
    (hf : f ∉ P) (hJ : J ∈ (P ⊔ span {f}).minimalPrimes) : P < J :=
  lt_of_mem_minimalPrimes_sup_span hf hJ

/-- Noetherianity enters only when the finite retained-minimal-prime representation is used. -/
example {R : Type*} [CommRing R] [IsNoetherianRing R] {P J : Ideal R} [P.IsPrime] {f s : R}
    (hf : f ∉ P) (hJ : J ∈ (P ⊔ span {f}).retainedMinimalPrimes s) :
    ringKrullDim (R ⧸ J) + 1 ≤ ringKrullDim (R ⧸ P) :=
  retained_cut_krullDim_succ_le hf hJ

/-- The non-membership assumption cannot be dropped: cutting a prime by zero leaves the same
prime, which is minimal over the cut but is not strictly larger than itself. -/
example {R : Type*} [CommRing R] (P : Ideal R) [P.IsPrime] :
    P ∈ (P ⊔ span {0}).minimalPrimes ∧ ¬ P < P := by
  constructor
  · simp [minimalPrimes_eq_subsingleton_self]
  · exact lt_irrefl P

/-- A cut by a unit is the whole ring and has no minimal primes. Thus minimal-prime membership,
rather than a hidden global nonemptiness assumption, is the properness witness in the API. -/
example {R : Type*} [CommRing R] (P : Ideal R) :
    (P ⊔ span {1}).minimalPrimes = ∅ := by
  simp [minimalPrimes_eq_empty_iff]

/-- A concrete cut in `ℤ`: cutting the prime `(0)` by `2` has the minimal prime `(2)`, which
strictly contains `(0)`, and the quotient dimension drops. -/
example : (⊥ : Ideal ℤ) < span {2} ∧
    ringKrullDim (ℤ ⧸ span {(2 : ℤ)}) + 1 ≤ ringKrullDim (ℤ ⧸ (⊥ : Ideal ℤ)) := by
  have hprime : (span {(2 : ℤ)}).IsPrime :=
    (span_singleton_prime (by norm_num)).mpr (Int.prime_iff_natAbs_prime.mpr Nat.prime_two)
  have hJ : span {(2 : ℤ)} ∈ ((⊥ : Ideal ℤ) ⊔ span {2}).minimalPrimes := by
    rw [bot_sup_eq, minimalPrimes_eq_subsingleton_self]
    rfl
  have h2 : (2 : ℤ) ∉ (⊥ : Ideal ℤ) := by simp
  exact ⟨lt_of_mem_minimalPrimes_sup_span h2 hJ,
    ringKrullDim_quotient_succ_le_of_lt (lt_of_mem_minimalPrimes_sup_span h2 hJ)⟩

end Ideal
