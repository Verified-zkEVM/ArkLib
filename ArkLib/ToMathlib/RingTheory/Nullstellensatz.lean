/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# Zero loci covered by retained minimal primes

Let `k` be a field, `σ` a finite type, `I` an ideal of `MvPolynomial σ k` and `s` a polynomial.
Over any field extension `K` of `k`, a point of the zero locus of `I` at which `s` does not
vanish lies on the zero locus of one of the finitely many minimal primes over `I` retained by
`s` (`Ideal.retainedMinimalPrimes I s`). Components of the zero locus contained in `{s = 0}` are
not needed for such points. The file also records how the zero locus of `I ⊔ J` and of an added
single equation decompose.

## Main statements

* `MvPolynomial.mem_zeroLocus_iff_le_ker_aeval`: a point is a zero of `I` exactly when `I` lies in
  the kernel of evaluation at that point.
* `MvPolynomial.zeroLocus_sup` and `MvPolynomial.mem_zeroLocus_sup_span_singleton_iff`: the zero
  locus of a sum of ideals is the intersection of the zero loci.
* `MvPolynomial.exists_retainedMinimalPrime_of_mem_zeroLocus`: every zero of `I` at which `s` does
  not vanish is a zero of some retained minimal prime.
* `MvPolynomial.mem_zeroLocus_and_eval_ne_zero_iff_retained`: the part of the zero locus of `I`
  where `s ≠ 0` is exactly the union of the corresponding parts for the retained minimal primes.
* `MvPolynomial.mem_zeroLocus_and_cut_iff_retained`: the same statement after adding one equation
  `f = 0`, with the retained minimal primes of `I ⊔ Ideal.span {f}`.

## Proof outline

The kernel of evaluation at a point `x : σ → K` is a prime ideal because `K` is a field. If `x`
is a zero of `I` then `I` lies in this kernel, and if `s` does not vanish at `x` then `s` is not in
it. `Ideal.exists_mem_retainedMinimalPrimes_le` then supplies a retained minimal prime inside the
kernel, and `x` is a zero of that prime. The converse direction is `zeroLocus_anti_mono`, since
every minimal prime over `I` contains `I`. The finiteness of the family comes from
`Ideal.retainedMinimalPrimes`, which needs `MvPolynomial σ k` to be Noetherian; this is the only
use of `Finite σ`.

The field `K` is arbitrary. Algebraic closedness is not used: the cover statements only pass from
a point to its evaluation kernel, never from a prime to a point.

## References

This file is extracted from ArkLib at source revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`, file
`ArkLib/ToMathlib/AlgebraicGeometry/PrincipalOpen/Cuts.lean`. The theorems
`MvPolynomial.exists_retainedMinimalPrime_of_mem_zeroLocus`,
`MvPolynomial.mem_zeroLocus_and_eval_ne_zero_iff_retained` and
`MvPolynomial.mem_zeroLocus_and_cut_iff_retained` keep the source names and statements, with the
coefficient field and extension renamed to `k` and `K` to match
`Mathlib.RingTheory.Nullstellensatz`. The source proved the ideal-sum description of the cut
inline; here it is the public lemma `MvPolynomial.mem_zeroLocus_sup_span_singleton_iff`, derived
from `MvPolynomial.zeroLocus_sup`. The prime-ideal step is the generic
`Ideal.exists_mem_retainedMinimalPrimes_le`.

Deferred: the Krull-dimension drop of the same source file, the finite zero-dimensional
results of `ArkLib/ToMathlib/AlgebraicGeometry/ZeroLocus/ZeroDimensional.lean`, and every result
that needs algebraic closedness or the affine Hilbert polynomial.
-/

@[expose] public section

namespace MvPolynomial

variable {k K σ : Type*} [Field k] [Field K] [Algebra k K]

/-- A point `x` is a zero of the ideal `I` exactly when `I` lies in the kernel of evaluation at
`x`. -/
theorem mem_zeroLocus_iff_le_ker_aeval {I : Ideal (MvPolynomial σ k)} {x : σ → K} :
    x ∈ zeroLocus K I ↔ I ≤ RingHom.ker (aeval x) :=
  Iff.rfl

/-- The zero locus of a sum of ideals is the intersection of their zero loci. -/
theorem zeroLocus_sup (I J : Ideal (MvPolynomial σ k)) :
    zeroLocus K (I ⊔ J) = zeroLocus K I ∩ zeroLocus K J := by
  ext x
  simp only [Set.mem_inter_iff, mem_zeroLocus_iff_le_ker_aeval, sup_le_iff]

/-- Adding one generator `f` to an ideal `I` cuts its zero locus by the equation `f = 0`. -/
theorem mem_zeroLocus_sup_span_singleton_iff {I : Ideal (MvPolynomial σ k)}
    {f : MvPolynomial σ k} {x : σ → K} :
    x ∈ zeroLocus K (I ⊔ Ideal.span {f}) ↔ x ∈ zeroLocus K I ∧ aeval x f = 0 := by
  rw [zeroLocus_sup, Set.mem_inter_iff, zeroLocus_span]
  simp

variable [Finite σ]

/-- Every zero `x` of the ideal `I` at which `s` does not vanish is a zero of some minimal prime
over `I` retained by `s`, that is, of some minimal prime that does not contain `s`.

The point `x` may have coordinates in any field extension `K` of `k`; `K` need not be
algebraically closed. The hypothesis `aeval x s ≠ 0` is needed: for `I = Ideal.span {X 0 * X 1}`
in two variables and `s = X 0`, the only retained minimal prime is the ideal of the line
`X 1 = 0`, and the zero `(0, 1)` of `I` does not lie on it. -/
theorem exists_retainedMinimalPrime_of_mem_zeroLocus
    (I : Ideal (MvPolynomial σ k)) (s : MvPolynomial σ k) (x : σ → K)
    (hx : x ∈ zeroLocus K I) (hs : aeval x s ≠ 0) :
    ∃ P ∈ I.retainedMinimalPrimes s, x ∈ zeroLocus K P := by
  have : (RingHom.ker (aeval (R := k) x)).IsPrime := RingHom.ker_isPrime _
  obtain ⟨P, hP, hPx⟩ :=
    Ideal.exists_mem_retainedMinimalPrimes_le (Q := RingHom.ker (aeval (R := k) x))
      (mem_zeroLocus_iff_le_ker_aeval.mp hx) hs
  exact ⟨P, hP, mem_zeroLocus_iff_le_ker_aeval.mpr hPx⟩

/-- The points of the zero locus of `I` at which `s` does not vanish are exactly the points, at
which `s` does not vanish, of the zero loci of the minimal primes over `I` retained by `s`. The
field extension `K` is arbitrary. -/
theorem mem_zeroLocus_and_eval_ne_zero_iff_retained
    (I : Ideal (MvPolynomial σ k)) (s : MvPolynomial σ k) (x : σ → K) :
    (x ∈ zeroLocus K I ∧ aeval x s ≠ 0) ↔
      ∃ P ∈ I.retainedMinimalPrimes s, x ∈ zeroLocus K P ∧ aeval x s ≠ 0 := by
  constructor
  · rintro ⟨hx, hs⟩
    obtain ⟨P, hP, hxP⟩ := exists_retainedMinimalPrime_of_mem_zeroLocus I s x hx hs
    exact ⟨P, hP, hxP, hs⟩
  · rintro ⟨P, hP, hx, hs⟩
    exact ⟨zeroLocus_anti_mono (Ideal.mem_retainedMinimalPrimes.mp hP).1.le hx, hs⟩

/-- Adding the equation `f = 0` to a zero locus, at points where `s` does not vanish, is described
by the retained minimal primes of the ideal sum `I ⊔ Ideal.span {f}`: a point `x` with
`aeval x s ≠ 0` is a zero of `I` and of `f` exactly when it is a zero of one of those primes.

No hypothesis relates `f` to `I`. If `f ∈ I`, the cut is `I` itself; if `f` is a unit, the ideal
sum is `⊤`, it has no minimal primes, and both sides are false. -/
theorem mem_zeroLocus_and_cut_iff_retained
    (I : Ideal (MvPolynomial σ k)) (s f : MvPolynomial σ k) (x : σ → K) :
    (x ∈ zeroLocus K I ∧ aeval x f = 0 ∧ aeval x s ≠ 0) ↔
      ∃ P ∈ (I ⊔ Ideal.span {f}).retainedMinimalPrimes s,
        x ∈ zeroLocus K P ∧ aeval x s ≠ 0 := by
  rw [← mem_zeroLocus_and_eval_ne_zero_iff_retained, mem_zeroLocus_sup_span_singleton_iff,
    and_assoc]

end MvPolynomial
