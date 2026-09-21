/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-!
# Krull-dimension drop along a principal cut

Let `P` be a prime ideal and let `f ∉ P`. Every minimal prime `J` over
`P ⊔ Ideal.span {f}` strictly contains `P`. The quotient map from `R ⧸ P` to `R ⧸ J`
therefore kills a nonzero element of the domain `R ⧸ P`; Mathlib's
`ringKrullDim_succ_le_of_surjective` then gives the successor inequality between their quotient
Krull dimensions. Away from infinite top dimension, this is the expected drop by at least one.

This file is purely ideal-theoretic. It does not assume that `R` is a polynomial ring, that a
minimal-prime component has a rational point, or that any ideal is radical. The non-membership
`f ∉ P` is explicit and essential. The retained-family corollary requires Noetherianity only
because `Ideal.retainedMinimalPrimes` is a finite family; the two underlying order and dimension
statements do not.

## Main statements

* `Ideal.ringKrullDim_quotient_succ_le_of_lt`: a strict inclusion out of a prime ideal gives the
  quotient-dimension successor inequality (and hence a strict drop away from `⊤`).
* `Ideal.lt_of_mem_minimalPrimes_sup_span`: a minimal prime of a principal cut strictly contains
  the original prime when the cutting element is not in it.
* `Ideal.retained_cut_krullDim_succ_le`: the corresponding dimension drop for a retained minimal
  prime of the cut.

## Boundary behavior

If `f ∈ P`, the strictness conclusion is false in general: for `f = 0`, `P` itself is the unique
minimal prime over `P ⊔ Ideal.span {f}`. If the cut ideal is the whole ring, it has no minimal
prime, so the hypotheses cannot supply `J`. Accordingly this module makes no separate
nonemptiness or properness assertion; membership of `J` in the relevant minimal-prime family is
the explicit properness witness needed by each theorem.

## References

These declarations are ported from ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`, file
`ArkLib/ToMathlib/AlgebraicGeometry/PrincipalOpen/Cuts.lean`. The first two declarations preserve
the source's effective generality: the source placed them in a Noetherian section but explicitly
omitted that instance from both statements.
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

end Ideal
