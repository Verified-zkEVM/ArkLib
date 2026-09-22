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

For relative codimension one they compute the relative height `1` of the component `(2)` of the
cut of `(0)` by `2` in `ℤ`, show that cutting by `0` gives relative height `0`, check that a
strictly larger ideal has nonzero image without primality, and derive the forms with primality of
`P` as an explicit argument and the conjunct `J.IsPrime`.
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

/-! ### Relative codimension one -/

/-- In `ℤ`, the component `(2)` of the cut of `(0)` by `2` has height `1` in `ℤ ⧸ (0)`. -/
example : ((span {(2 : ℤ)}).map (Quotient.mk (⊥ : Ideal ℤ))).height = 1 := by
  have hprime : (span {(2 : ℤ)}).IsPrime :=
    (span_singleton_prime (by norm_num)).mpr (Int.prime_iff_natAbs_prime.mpr Nat.prime_two)
  have hJ : span {(2 : ℤ)} ∈ ((⊥ : Ideal ℤ) ⊔ span {2}).minimalPrimes := by
    rw [bot_sup_eq, minimalPrimes_eq_subsingleton_self]
    rfl
  exact map_quotient_height_eq_one_of_mem_minimalPrimes_sup_span (by simp) hJ

/-- The non-membership assumption is needed for relative height `1`: cutting a prime `P` by `0`
has the minimal prime `P`, whose image in `R ⧸ P` is `⊥`, of height `0`. -/
example {R : Type*} [CommRing R] (P : Ideal R) [P.IsPrime] :
    P ∈ (P ⊔ span {0}).minimalPrimes ∧ (P.map (Quotient.mk P)).height = 0 := by
  refine ⟨by simp [minimalPrimes_eq_subsingleton_self], ?_⟩
  rw [map_quotient_self, height_bot]

/-- A strictly larger ideal has nonzero image in the quotient, with no primality assumption:
`(4) < (2)` in `ℤ`, and `(2)` maps to a nonzero ideal of `ℤ ⧸ (4)`. -/
example : (span {(2 : ℤ)}).map (Quotient.mk (span {(4 : ℤ)})) ≠ ⊥ := by
  refine map_quotient_ne_bot_of_lt (lt_of_le_of_ne ?_ fun h ↦ ?_)
  · rw [span_singleton_le_span_singleton]
    norm_num
  · have : (2 : ℤ) ∈ span {(4 : ℤ)} := h ▸ mem_span_singleton_self 2
    rw [mem_span_singleton] at this
    norm_num at this

/-- The existence form in `ℤ`: the cut of `(0)` by `2` is proper and has a component of relative
height `1`. -/
example : ∃ J ∈ ((⊥ : Ideal ℤ) ⊔ span {2}).minimalPrimes,
    ⊥ < J ∧ (J.map (Quotient.mk (⊥ : Ideal ℤ))).height = 1 := by
  refine exists_principalCut_component_relative_codimension_one (by simp) ?_
  rw [bot_sup_eq, Ne, span_singleton_eq_top, Int.isUnit_iff]
  norm_num

/-- A minimal prime `J` of the cut of a prime `P` by `f ∉ P` is prime, strictly contains `P`, and
has height one in `R ⧸ P`. -/
example {R : Type*} [CommRing R] [IsNoetherianRing R] {P J : Ideal R} (hP : P.IsPrime) {f : R}
    (hf : f ∉ P) (hJ : J ∈ (P ⊔ span {f}).minimalPrimes) :
    J.IsPrime ∧ P < J ∧ (J.map (Quotient.mk P)).height = 1 :=
  ⟨hJ.isPrime, lt_of_mem_minimalPrimes_sup_span hf hJ,
    map_quotient_height_eq_one_of_mem_minimalPrimes_sup_span hf hJ⟩

/-- The existence of a component of relative height one, with the conjunct `J.IsPrime`. -/
example {R : Type*} [CommRing R] [IsNoetherianRing R] {P : Ideal R} (hP : P.IsPrime) {f : R}
    (hf : f ∉ P) (hcut : P ⊔ span {f} ≠ ⊤) :
    ∃ J : Ideal R, J ∈ (P ⊔ span {f}).minimalPrimes ∧
      J.IsPrime ∧ P < J ∧ (J.map (Quotient.mk P)).height = 1 := by
  obtain ⟨J, hJ, hlt, hh⟩ := exists_principalCut_component_relative_codimension_one hf hcut
  exact ⟨J, hJ, hJ.isPrime, hlt, hh⟩

/-! ### Retained cut families -/

/-- In `ℤ`, cutting the prime `(2)` by `4 ∈ (2)` and keeping the primes that avoid `1` leaves the
single component `(2)`. -/
example : ((span {(2 : ℤ)}) ⊔ span {4}).retainedMinimalPrimes 1 = {span {(2 : ℤ)}} := by
  have : (span {(2 : ℤ)}).IsPrime :=
    (span_singleton_prime (by norm_num)).mpr (Int.prime_iff_natAbs_prime.mpr Nat.prime_two)
  refine retainedMinimalPrimes_sup_span_of_mem (mem_span_singleton.mpr (by norm_num)) ?_
  rw [mem_span_singleton]
  norm_num

/-- The hypothesis `s ∉ P` of `retainedMinimalPrimes_sup_span_of_mem` is needed: if `s ∈ P`,
every retained component would contain `P` and avoid `s`, so the family is empty. -/
example {R : Type*} [CommRing R] [IsNoetherianRing R] {P : Ideal R} {s f : R} (hs : s ∈ P) :
    (P ⊔ span {f}).retainedMinimalPrimes s = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun Q hQ ↦ ?_
  obtain ⟨-, hPQ, -, hsQ⟩ := of_mem_retainedMinimalPrimes_sup_span hQ
  exact hsQ (hPQ hs)

/-- Membership in the family that is `{P}` when `f ∈ P` and the retained minimal primes of
`P ⊔ span {f}` otherwise. By
`retainedMinimalPrimes_sup_span_of_mem` the two cases agree, and the conclusion is
`of_mem_retainedMinimalPrimes_sup_span`. -/
example {R : Type*} [CommRing R] [IsNoetherianRing R]
    {P Q : Ideal R} {s f : R} [Decidable (f ∈ P)] (hP : P.IsPrime) (hs : s ∉ P)
    (hQ : Q ∈ (if f ∈ P then {P} else (P ⊔ span {f}).retainedMinimalPrimes s)) :
    Q.IsPrime ∧ P ≤ Q ∧ f ∈ Q ∧ s ∉ Q := by
  have hfam : (if f ∈ P then {P} else (P ⊔ span {f}).retainedMinimalPrimes s) =
      (P ⊔ span {f}).retainedMinimalPrimes s := by
    split_ifs with hf
    · exact (retainedMinimalPrimes_sup_span_of_mem hf hs).symm
    · rfl
  exact of_mem_retainedMinimalPrimes_sup_span (hfam ▸ hQ)

end Ideal
