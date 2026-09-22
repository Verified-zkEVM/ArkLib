/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian

/-!
# Minimal primes of a Noetherian ideal as a finset

In a Noetherian commutative semiring the minimal primes over an ideal form a finite set
(`Ideal.finite_minimalPrimes_of_isNoetherianRing`). This file packages that set as a `Finset`,
so that it can index finite sums and unions, and defines the minimal primes *retained* by an
element `s`: those that do not contain `s`.

For a polynomial ideal `I`, the retained minimal primes index the algebraic components on which
`s` is not identically zero. This does not assert that each component has a point over a given
field extension. The point-cover statements for `MvPolynomial.zeroLocus` are in
`ArkLib.ToMathlib.RingTheory.Nullstellensatz`. The principal-cut Krull-dimension consequences of
this finite family are in `ArkLib.ToMathlib.RingTheory.Ideal.PrincipalCut`.

## Main definitions

* `Ideal.minimalPrimesFinset I`: the minimal primes over `I`, as a `Finset`.
* `Ideal.retainedMinimalPrimes I s`: the minimal primes over `I` that do not contain `s`,
  defined as a filter of `Ideal.minimalPrimesFinset I`.

## Main statements

* `Ideal.mem_minimalPrimesFinset` and `Ideal.mem_retainedMinimalPrimes`: membership laws.
* `Ideal.exists_mem_retainedMinimalPrimes_le`: every prime `Q` over `I` with `s ∉ Q` contains a
  retained minimal prime. This is the algebraic content of the regular-point cover.
* `Ideal.retainedMinimalPrimes_eq_empty_iff`: no minimal prime is retained exactly when `s` lies
  in the radical of `I`.
* `Ideal.retainedMinimalPrimes_of_isUnit`: a unit retains every minimal prime.

## Proof outline

Membership reduces to `Set.Finite.mem_toFinset` and `Finset.mem_filter`. The existence statement
applies `Ideal.exists_minimalPrimes_le` to `Q` and observes that a prime below `Q` cannot contain
`s`. The emptiness criterion uses `Ideal.sInf_minimalPrimes`: the radical is the intersection of
the minimal primes.
-/

@[expose] public section

namespace Ideal

variable {R : Type*} [CommSemiring R] [IsNoetherianRing R]

/-- The minimal primes over an ideal `I` of a Noetherian commutative semiring, as a `Finset`.

The underlying set is `I.minimalPrimes`, which is finite by
`Ideal.finite_minimalPrimes_of_isNoetherianRing`. The Noetherian hypothesis is what makes the
set finite: in the non-Noetherian product ring `ℕ → ℤ`, the zero ideal has the infinitely many
minimal primes `{f | f n = 0}`, one for each `n`. For `I = ⊤` the finset is empty. -/
noncomputable def minimalPrimesFinset (I : Ideal R) : Finset (Ideal R) :=
  (I.finite_minimalPrimes_of_isNoetherianRing R).toFinset

/-- An ideal belongs to `I.minimalPrimesFinset` exactly when it is a minimal prime over `I`. -/
@[simp]
theorem mem_minimalPrimesFinset {I P : Ideal R} :
    P ∈ I.minimalPrimesFinset ↔ P ∈ I.minimalPrimes := by
  simp [minimalPrimesFinset]

/-- The finset `I.minimalPrimesFinset`, viewed as a set, is `I.minimalPrimes`. -/
@[simp, norm_cast]
theorem coe_minimalPrimesFinset (I : Ideal R) :
    (I.minimalPrimesFinset : Set (Ideal R)) = I.minimalPrimes := by
  simp [minimalPrimesFinset]

/-- There are no minimal primes over `I` exactly when `I` is the whole ring. Every proper ideal
lies in a maximal ideal, and hence over some minimal prime. -/
theorem minimalPrimesFinset_eq_empty_iff {I : Ideal R} :
    I.minimalPrimesFinset = ∅ ↔ I = ⊤ := by
  rw [← Finset.coe_eq_empty, coe_minimalPrimesFinset, minimalPrimes_eq_empty_iff]

/-- A prime ideal is its own unique minimal prime. -/
theorem minimalPrimesFinset_of_isPrime (I : Ideal R) [I.IsPrime] :
    I.minimalPrimesFinset = {I} := by
  rw [← Finset.coe_inj, coe_minimalPrimesFinset, Finset.coe_singleton,
    minimalPrimes_eq_subsingleton_self]

/-- The minimal primes over `I` retained by `s`: those that do not contain `s`.

For an ideal `I` of polynomials, these index the algebraic components on which `s` is not
identically zero; this does not require a point over any particular field extension.
The family is defined as a filter of `I.minimalPrimesFinset`. It equals `I.minimalPrimesFinset`
when `s` is a unit (`retainedMinimalPrimes_of_isUnit`) and is empty exactly when `s` lies in the
radical of `I` (`retainedMinimalPrimes_eq_empty_iff`). -/
noncomputable def retainedMinimalPrimes (I : Ideal R) (s : R) : Finset (Ideal R) := by
  classical
  exact I.minimalPrimesFinset.filter (fun P ↦ s ∉ P)

/-- An ideal is retained by `s` exactly when it is a minimal prime over `I` not containing `s`. -/
@[simp]
theorem mem_retainedMinimalPrimes {I P : Ideal R} {s : R} :
    P ∈ I.retainedMinimalPrimes s ↔ P ∈ I.minimalPrimes ∧ s ∉ P := by
  classical
  simp [retainedMinimalPrimes]

/-- The retained minimal primes form a subfamily of all minimal primes. -/
theorem retainedMinimalPrimes_subset (I : Ideal R) (s : R) :
    I.retainedMinimalPrimes s ⊆ I.minimalPrimesFinset := fun _ hP ↦
  mem_minimalPrimesFinset.mpr (mem_retainedMinimalPrimes.mp hP).1

/-- Every prime `Q` over `I` that does not contain `s` contains a minimal prime over `I` retained
by `s`.

Both hypotheses are needed. Every minimal prime over `I` contains `I`, so if `I ≰ Q` none lies
below `Q`; for `I = ⊤` there are no minimal primes at all. If `s ∈ Q`, take `I = Q`: the only
minimal prime over `Q` is `Q` itself, which contains `s`, so nothing is retained. -/
theorem exists_mem_retainedMinimalPrimes_le {I Q : Ideal R} [Q.IsPrime] {s : R}
    (hIQ : I ≤ Q) (hsQ : s ∉ Q) :
    ∃ P ∈ I.retainedMinimalPrimes s, P ≤ Q := by
  obtain ⟨P, hP, hPQ⟩ := I.exists_minimalPrimes_le hIQ
  exact ⟨P, mem_retainedMinimalPrimes.mpr ⟨hP, fun hsP ↦ hsQ (hPQ hsP)⟩, hPQ⟩

/-- No minimal prime over `I` is retained by `s` exactly when `s` lies in the radical of `I`,
that is, when `s` lies in every minimal prime over `I` (`Ideal.sInf_minimalPrimes`). In
particular the retained family is empty whenever `s ∈ I`. -/
theorem retainedMinimalPrimes_eq_empty_iff {I : Ideal R} {s : R} :
    I.retainedMinimalPrimes s = ∅ ↔ s ∈ I.radical := by
  rw [← sInf_minimalPrimes, Submodule.mem_sInf, Finset.eq_empty_iff_forall_notMem]
  simp only [mem_retainedMinimalPrimes, not_and, not_not]

/-- A unit lies in no prime ideal, so it retains every minimal prime. -/
theorem retainedMinimalPrimes_of_isUnit (I : Ideal R) {s : R} (hs : IsUnit s) :
    I.retainedMinimalPrimes s = I.minimalPrimesFinset := by
  ext P
  simp only [mem_retainedMinimalPrimes, mem_minimalPrimesFinset, and_iff_left_iff_imp]
  intro hP hsP
  exact hP.isPrime.ne_top (P.eq_top_of_isUnit_mem hsP hs)

end Ideal
