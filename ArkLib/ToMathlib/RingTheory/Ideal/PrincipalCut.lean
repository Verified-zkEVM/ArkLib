/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-!
# Krull-dimension drop and relative height one along a principal cut

Let `P` be a prime ideal and let `f ∉ P`. Every minimal prime `J` over
`P ⊔ Ideal.span {f}` strictly contains `P`. The quotient map from `R ⧸ P` to `R ⧸ J`
therefore kills a nonzero element of the domain `R ⧸ P`; Mathlib's
`ringKrullDim_succ_le_of_surjective` then gives the successor inequality between their quotient
Krull dimensions. Away from infinite top dimension, this is the expected drop by at least one.

In a Noetherian ring the drop is sharp relative to `P`: the image of `J` in the domain `R ⧸ P`
has height exactly one. Krull's principal ideal theorem, in Mathlib's form
`Ideal.map_height_le_one_of_mem_minimalPrimes`, bounds the height by one, and the image is
nonzero because `P < J`. This is a statement about heights in `R ⧸ P`; it does not say that
`ringKrullDim (R ⧸ J) + 1 = ringKrullDim (R ⧸ P)`, which would need a catenary or equidimensional
hypothesis.

This file is purely ideal-theoretic. It does not assume that `R` is a polynomial ring, that a
minimal-prime component has a rational point, or that any ideal is radical. The non-membership
`f ∉ P` is explicit and essential. Noetherianity is used by the retained-family corollary, because
`Ideal.retainedMinimalPrimes` is a finite family, and by the height statements, through Krull's
principal ideal theorem; the order and dimension-drop statements do not need it.

## Main statements

* `Ideal.ringKrullDim_quotient_succ_le_of_lt`: a strict inclusion out of a prime ideal gives the
  quotient-dimension successor inequality (and hence a strict drop away from `⊤`).
* `Ideal.lt_of_mem_minimalPrimes_sup_span`: a minimal prime of a principal cut strictly contains
  the original prime when the cutting element is not in it.
* `Ideal.retained_cut_krullDim_succ_le`: the corresponding dimension drop for a retained minimal
  prime of the cut.
* `Ideal.of_mem_retainedMinimalPrimes_sup_span`, `Ideal.retainedMinimalPrimes_sup_span_of_mem`:
  the retained minimal primes of a cut `I ⊔ span {f}`, and the trivial cut of a prime by one of
  its elements.
* `Ideal.map_quotient_ne_bot_of_lt`: an ideal strictly above `P` has nonzero image in `R ⧸ P`.
* `Ideal.map_quotient_height_eq_one_of_mem_minimalPrimes_sup_span`: a minimal prime of the cut
  has height one in `R ⧸ P`, and `Ideal.exists_principalCut_component_relative_codimension_one`
  gives such a minimal prime when the cut is proper.

## Boundary behavior

If `f ∈ P`, the strictness conclusion is false in general: for `f = 0`, `P` itself is the unique
minimal prime over `P ⊔ Ideal.span {f}`. If the cut ideal is the whole ring, it has no minimal
prime, so the hypotheses cannot supply `J`. Accordingly membership of `J` in the relevant
minimal-prime family is the properness witness of each theorem about a given `J`; only the
existence statement `exists_principalCut_component_relative_codimension_one` assumes properness
of the cut directly.
-/

@[expose] public section

namespace Ideal

variable {R : Type*} [CommRing R]

/-- A strict inclusion `P < J` from a prime ideal gives the quotient-dimension successor
inequality. When the right side is not `⊤`, this expresses a drop by at least one.

Choose `f ∈ J \ P`. Its class in `R ⧸ P` is nonzero and hence a non-zero-divisor because `P` is
prime, while the quotient map to `R ⧸ J` kills it. No Noetherian hypothesis is needed. -/
theorem ringKrullDim_quotient_succ_le_of_lt {P J : Ideal R} [P.IsPrime] (hPJ : P < J) :
    ringKrullDim (R ⧸ J) + 1 ≤ ringKrullDim (R ⧸ P) := by
  obtain ⟨f, hfJ, hfP⟩ := SetLike.exists_of_lt hPJ
  apply ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hPJ.le)
    (Ideal.Quotient.factor_surjective hPJ.le) (r := Ideal.Quotient.mk P f)
  · rw [mem_nonZeroDivisors_iff_ne_zero]
    exact fun hf ↦ hfP (Ideal.Quotient.eq_zero_iff_mem.mp hf)
  · exact Ideal.Quotient.eq_zero_iff_mem.mpr hfJ

/-- A minimal prime over the principal cut `P ⊔ Ideal.span {f}` strictly contains `P` when
`f ∉ P`.

The non-membership hypothesis is essential: if `f = 0`, the cut is `P` and `P` is its own
minimal prime. -/
theorem lt_of_mem_minimalPrimes_sup_span {P J : Ideal R} {f : R}
    (hf : f ∉ P) (hJ : J ∈ (P ⊔ Ideal.span {f}).minimalPrimes) : P < J := by
  apply lt_of_le_of_ne (le_sup_left.trans hJ.le)
  intro heq
  apply hf
  rw [heq]
  exact hJ.le ((show Ideal.span {f} ≤ P ⊔ Ideal.span {f} from le_sup_right)
    (Ideal.subset_span (Set.mem_singleton f)))

/-- An ideal strictly containing `P` has nonzero image in `R ⧸ P`. The image is `⊥` exactly when
`J ≤ P`, since the kernel of the quotient map is `P`; no primality of `P` is needed. -/
theorem map_quotient_ne_bot_of_lt {P J : Ideal R} (hPJ : P < J) :
    J.map (Ideal.Quotient.mk P) ≠ ⊥ := by
  rw [Ne, map_eq_bot_iff_le_ker, mk_ker]
  exact hPJ.not_ge

variable [IsNoetherianRing R]

/-- A retained minimal prime of the principal cut by `f ∉ P` satisfies the quotient-dimension
successor inequality, and therefore lies at least one dimension below the original prime component
when that component's quotient dimension is not `⊤`.

Membership in `retainedMinimalPrimes` supplies both minimal-prime membership and the retained
condition `s ∉ J`; only the former is needed for this dimension inequality. No existence of a
rational point on the retained component is asserted. -/
theorem retained_cut_krullDim_succ_le {P J : Ideal R} [P.IsPrime] {f s : R}
    (hf : f ∉ P) (hJ : J ∈ (P ⊔ Ideal.span {f}).retainedMinimalPrimes s) :
    ringKrullDim (R ⧸ J) + 1 ≤ ringKrullDim (R ⧸ P) := by
  exact ringKrullDim_quotient_succ_le_of_lt
    (lt_of_mem_minimalPrimes_sup_span hf (mem_retainedMinimalPrimes.mp hJ).1)

/-- Every retained minimal prime `Q` of the cut `I ⊔ span {f}` is a prime containing `I` and `f`
and not containing `s`. No hypothesis on `I`, `f` or `s` is needed: membership in the retained
family supplies all four facts. -/
theorem of_mem_retainedMinimalPrimes_sup_span {I Q : Ideal R} {s f : R}
    (hQ : Q ∈ (I ⊔ span {f}).retainedMinimalPrimes s) :
    Q.IsPrime ∧ I ≤ Q ∧ f ∈ Q ∧ s ∉ Q := by
  obtain ⟨hmin, hs⟩ := mem_retainedMinimalPrimes.mp hQ
  exact ⟨hmin.isPrime, le_sup_left.trans hmin.le,
    hmin.le (mem_sup_right (mem_span_singleton_self f)), hs⟩

/-- Cutting a prime `P` by an element `f ∈ P` changes nothing: if `s ∉ P`, the only retained
minimal prime of `P ⊔ span {f}` is `P`. Hence, for a prime `P` with `s ∉ P`, the retained cut
family needs no case split on whether `f ∈ P`. The hypothesis `s ∉ P` is needed: if `s ∈ P` the
family is empty. -/
theorem retainedMinimalPrimes_sup_span_of_mem {P : Ideal R} [P.IsPrime] {s f : R} (hf : f ∈ P)
    (hs : s ∉ P) : (P ⊔ span {f}).retainedMinimalPrimes s = {P} := by
  rw [sup_eq_left.mpr ((span_singleton_le_iff_mem P).mpr hf)]
  ext Q
  simp only [mem_retainedMinimalPrimes, minimalPrimes_eq_subsingleton_self, Set.mem_singleton_iff,
    Finset.mem_singleton, and_iff_left_iff_imp]
  rintro rfl
  exact hs

/-- Let `P` be prime and `f ∉ P`. Every minimal prime `J` over `P ⊔ span {f}` has height exactly
one in the domain `R ⧸ P`.

The image of `J` is a minimal prime over the principal ideal generated by the class of `f`, so
Krull's principal ideal theorem bounds its height by one; this is where Noetherianity is used. The
image is nonzero because `P < J`, and a nonzero ideal of a domain has positive height; this is
where primality of `P` is used. The hypothesis `f ∉ P` is needed: for `f = 0` the only minimal
prime is `P`, whose image is `⊥`, of height zero. -/
theorem map_quotient_height_eq_one_of_mem_minimalPrimes_sup_span {P J : Ideal R} [P.IsPrime]
    {f : R} (hf : f ∉ P) (hJ : J ∈ (P ⊔ span {f}).minimalPrimes) :
    (J.map (Ideal.Quotient.mk P)).height = 1 := by
  refine le_antisymm (map_height_le_one_of_mem_minimalPrimes hJ) ?_
  rw [Order.one_le_iff_ne_zero, Ne, height_eq_zero_iff_eq_bot]
  exact map_quotient_ne_bot_of_lt (lt_of_mem_minimalPrimes_sup_span hf hJ)

/-- A proper principal cut `P ⊔ span {f}` of a prime `P` by `f ∉ P` has a minimal prime `J` with
`P < J` and of height one in `R ⧸ P`. Properness is needed for a minimal prime to exist: the cut
by a unit is `⊤`, which has none. -/
theorem exists_principalCut_component_relative_codimension_one {P : Ideal R} [P.IsPrime] {f : R}
    (hf : f ∉ P) (hcut : P ⊔ span {f} ≠ ⊤) :
    ∃ J ∈ (P ⊔ span {f}).minimalPrimes,
      P < J ∧ (J.map (Ideal.Quotient.mk P)).height = 1 :=
  let ⟨J, hJ⟩ := (P ⊔ span {f}).nonempty_minimalPrimes hcut
  ⟨J, hJ, lt_of_mem_minimalPrimes_sup_span hf hJ,
    map_quotient_height_eq_one_of_mem_minimalPrimes_sup_span hf hJ⟩

end Ideal
