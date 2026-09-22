/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Separators for a finite family of prime ideals

Let `P : ι → Ideal R` be a finite family of prime ideals of a commutative semiring, no two of which
are comparable. For each `i` there is an element `s i` that lies in every `P j` with `j ≠ i` but
not in `P i`: take a product over `j ≠ i` of elements of `P j \ P i`, which is outside `P i`
because `P i` is prime. Such a family of separators is what a filtered comparison of the quotients
by `P i` with the quotient by `⨅ i, P i` needs.

Incomparability is also necessary: if `P j ≤ P i` with `j ≠ i`, then `s i ∈ P j ≤ P i`. The
minimal primes over an ideal are pairwise incomparable, so they always admit separators when
there are finitely many of them.

## Main statements

* `Ideal.exists_separators_of_pairwise_not_le`: a finite pairwise-incomparable family of prime
  ideals has separators `s` with `s i ∈ P j ↔ i ≠ j`.
* `Ideal.not_le_of_mem_minimalPrimes`: distinct minimal primes over the same ideal are
  incomparable.

## References

Ported from ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`. The separator
construction is the first half of
`AffineHilbert.exists_separators_sum_shifted_hilbertFunction_le_iInf` in
`ArkLib/ToMathlib/AlgebraicGeometry/Hilbert/PrimeFamily.lean`, where it was stated for ideals of
`MvPolynomial σ F` together with a Hilbert-function inequality. Here it is a statement about prime
ideals of any commutative semiring, and the Hilbert-function half is
`MvPolynomial.exists_sum_affineHilbertFunction_le_iInf` in
`ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertComponents`. The incomparability of minimal
primes is the private `minimalPrime_pairwise_incomparable` of
`ArkLib/ToMathlib/AlgebraicGeometry/PrincipalCut/ComponentCoefficient.lean`, stated for an
arbitrary commutative semiring.
-/

@[expose] public section

namespace Ideal

variable {R ι : Type*} [CommSemiring R]

/-- A finite family of prime ideals, no two of which are comparable, has separators: elements
`s i` with `s i ∈ P j` exactly when `i ≠ j`.

For `j ≠ i` choose `w i j ∈ P j \ P i`, which exists because `P j` is not contained in `P i`, and
let `s i` be the product of the `w i j` over `j ≠ i`. It lies in each `P j`, `j ≠ i`, through one
factor, and not in `P i` because `P i` is prime and contains no factor. Finiteness of `ι` makes
the product finite. Incomparability is necessary: if `P j ≤ P i` for some `j ≠ i`, then
`s i ∈ P j` forces `s i ∈ P i`. For a single prime, `s` is the constant `1`. -/
theorem exists_separators_of_pairwise_not_le [Finite ι] {P : ι → Ideal R}
    (hP : ∀ i, (P i).IsPrime) (hinc : Pairwise fun i j ↦ ¬P i ≤ P j) :
    ∃ s : ι → R, ∀ i j, s i ∈ P j ↔ i ≠ j := by
  classical
  have := Fintype.ofFinite ι
  have hw : ∀ i j, i ≠ j → ∃ w, w ∈ P j ∧ w ∉ P i := fun i j hij ↦
    SetLike.not_le_iff_exists.mp (hinc hij.symm)
  choose! w hwP hwnP using hw
  refine ⟨fun i ↦ ∏ j ∈ Finset.univ.erase i, w i j, fun i j ↦ ⟨fun hmem hij ↦ ?_, fun hij ↦ ?_⟩⟩
  · subst hij
    have := hP i
    obtain ⟨j, hj, hwj⟩ := (IsPrime.prod_mem_iff (p := P i)).mp hmem
    exact hwnP i j (Finset.ne_of_mem_erase hj).symm hwj
  · exact prod_mem (P j) (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩) (hwP i j hij)

/-- Two distinct minimal primes over the same ideal are incomparable: if `P ≤ Q`, minimality of
`Q` over `I` gives `Q ≤ P`. -/
theorem not_le_of_mem_minimalPrimes {I P Q : Ideal R} (hP : P ∈ I.minimalPrimes)
    (hQ : Q ∈ I.minimalPrimes) (hPQ : P ≠ Q) : ¬P ≤ Q :=
  fun hle ↦ hPQ (le_antisymm hle (hQ.2 hP.1 hle))

end Ideal
