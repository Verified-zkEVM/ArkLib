/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertRadical
public import ArkLib.ToMathlib.RingTheory.Nullstellensatz.FiniteQuotient

/-!
# Finite zero loci and zero-dimensional coordinate quotients

Let `k` be a field, `σ` a finite type and `I` an ideal of `MvPolynomial σ k`. For an
algebraically closed extension `K` of `k`, the Nullstellensatz says that a polynomial vanishing on
the zero locus of `I` in `K ^ σ` lies in the radical of `I`. Hence, for a radical ideal, evaluation
at the points of the zero locus is injective on the coordinate quotient.

When `k` itself is algebraically closed and the zero locus in `k ^ σ` is finite, evaluation embeds
the quotient by `I.radical` into the finite-dimensional space of functions on the zero locus. The
radical and `I` have Hilbert polynomials of the same natural degree, so the quotient by `I` is
finite-dimensional as well. Conversely a finite-dimensional quotient has a finite zero locus. So
the zero locus is finite exactly when the affine Hilbert polynomial of `I` has natural degree
zero, for every ideal `I`.

## Main statements

* `MvPolynomial.zeroLocus_radical`: an ideal and its radical have the same zeros.
* `MvPolynomial.zeroLocusEvaluation_injective`: evaluation on the zero locus over an algebraically
  closed extension is injective on the quotient by a radical ideal.
* `MvPolynomial.moduleFinite_of_finite_zeroLocus`: over an algebraically closed field, a finite
  zero locus makes the coordinate quotient finite-dimensional.
* `MvPolynomial.finite_zeroLocus_iff_moduleFinite`,
  `MvPolynomial.finite_zeroLocus_iff_natDegree_affineHilbertPolynomial_eq_zero`: the two
  characterizations of a finite zero locus.
-/

@[expose] public section

noncomputable section

namespace MvPolynomial

variable {k K σ : Type*} [Field k] [Field K] [Algebra k K]

/-- An ideal and its radical have the same zeros over any field extension: if `p ^ n ∈ I`
vanishes at `x`, so does `p`, because `K` has no nilpotents. -/
theorem zeroLocus_radical (I : Ideal (MvPolynomial σ k)) :
    zeroLocus K I.radical = zeroLocus K I := by
  refine (zeroLocus_anti_mono I.le_radical).antisymm fun x hx p ⟨n, hn⟩ ↦ ?_
  exact eq_zero_of_pow_eq_zero (n := n) (by rw [← map_pow]; exact hx _ hn)

/-- For a radical ideal `I` and an algebraically closed extension `K` of `k`, evaluation at the
points of the zero locus of `I` in `K ^ σ` is injective on `MvPolynomial σ k ⧸ I`.

A polynomial vanishing on the zero locus lies in `I.radical = I` by the Nullstellensatz
(`vanishingIdeal_zeroLocus_eq_radical`). Radicality is needed: for `I = (X ^ 2)` in one variable
the class of `X` is nonzero but vanishes at the only zero `0`. Algebraic closedness is needed: for
`k = K = ℝ` and `I = (X ^ 2 + 1)`, which is prime, the zero locus is empty. -/
theorem zeroLocusEvaluation_injective [IsAlgClosed K] [Finite σ] (I : Ideal (MvPolynomial σ k))
    (hI : I.IsRadical) :
    Function.Injective (LinearMap.pi fun x : zeroLocus K I ↦
      (zeroLocusPointHom I x).toLinearMap) := by
  intro x y hxy
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine Ideal.Quotient.eq.mpr ?_
  rw [← hI.radical, ← vanishingIdeal_zeroLocus_eq_radical (K := K)]
  intro z hz
  have he := congrFun hxy ⟨z, hz⟩
  change aeval z p = aeval z q at he
  rw [map_sub, he, sub_self]

variable [Finite σ]

/-- Over an algebraically closed field `k`, an ideal of `MvPolynomial σ k` with finitely many
zeros in `k ^ σ` has a finite-dimensional coordinate quotient.

Evaluation embeds the quotient by `I.radical` into the functions on the finite zero locus
(`zeroLocusEvaluation_injective`, `zeroLocus_radical`). Its Hilbert polynomial then has natural
degree zero, and so does that of `I` (`natDegree_affineHilbertPolynomial_radical`). Algebraic
closedness is needed: over `ℝ`, the ideal `(X ^ 2 + Y ^ 2 + 1)` has no real zeros, but its
quotient is infinite-dimensional. -/
theorem moduleFinite_of_finite_zeroLocus [IsAlgClosed k] (I : Ideal (MvPolynomial σ k))
    (hV : (zeroLocus k I).Finite) : Module.Finite k (MvPolynomial σ k ⧸ I) := by
  rw [← zeroLocus_radical] at hV
  have : Fintype (zeroLocus k I.radical) := hV.fintype
  have : Module.Finite k (MvPolynomial σ k ⧸ I.radical) :=
    Module.Finite.of_injective _
      (zeroLocusEvaluation_injective (K := k) I.radical I.radical_isRadical)
  refine moduleFinite_of_natDegree_affineHilbertPolynomial_eq_zero ?_
  rw [← natDegree_affineHilbertPolynomial_radical, natDegree_affineHilbertPolynomial_eq_zero_iff]
  infer_instance

/-- Over an algebraically closed field `k`, the zero locus of `I` in `k ^ σ` is finite exactly
when the coordinate quotient is finite-dimensional. The reverse direction holds over any field
(`finite_zeroLocus_of_finite_quotient`). -/
theorem finite_zeroLocus_iff_moduleFinite [IsAlgClosed k] (I : Ideal (MvPolynomial σ k)) :
    (zeroLocus k I).Finite ↔ Module.Finite k (MvPolynomial σ k ⧸ I) :=
  ⟨moduleFinite_of_finite_zeroLocus I, fun _ ↦ finite_zeroLocus_of_finite_quotient I⟩

/-- Over an algebraically closed field `k`, the zero locus of `I` in `k ^ σ` is finite exactly
when the affine Hilbert polynomial of `I` has natural degree zero. No radical hypothesis is
needed. -/
theorem finite_zeroLocus_iff_natDegree_affineHilbertPolynomial_eq_zero [IsAlgClosed k]
    (I : Ideal (MvPolynomial σ k)) :
    (zeroLocus k I).Finite ↔ (affineHilbertPolynomial I).natDegree = 0 := by
  rw [finite_zeroLocus_iff_moduleFinite, natDegree_affineHilbertPolynomial_eq_zero_iff]

end MvPolynomial
