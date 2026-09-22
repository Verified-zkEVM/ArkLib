/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.RingTheory.Ideal.CutFamily
public import ArkLib.ToMathlib.RingTheory.Nullstellensatz

/-!
# Zero loci covered by iterated retained cut families

Let `k` be a field, `σ` a finite type, `Ps` a finite family of ideals of `MvPolynomial σ k`, `s` a
polynomial and `cuts` a list of polynomials. Over any field extension `K` of `k`, a zero of a
member `P` of `Ps` at which `s` does not vanish and at which every element of `cuts` vanishes is a
zero of some member `Q ⊇ P` of `Ideal.iteratedRetainedCutFamily Ps s cuts`.

The proof applies the ideal-theoretic covering property
`Ideal.exists_mem_iteratedRetainedCutFamily_le` to the kernel of evaluation at the point, which is
prime because `K` is a field. No algebraic closedness is used.

## Main statements

* `MvPolynomial.exists_mem_iteratedRetainedCutFamily_of_mem_zeroLocus`: the point cover.

## References

Ported from ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`, file
`ArkLib/ToMathlib/AlgebraicGeometry/CutFamily/Iteration.lean`, namespace `AffineHilbert`.
`exists_mem_iteratedRetainedCutFamily_of_mem_zeroLocus` keeps its name. The source assumed
`∃ P ∈ Ps, x ∈ zeroLocus E P`; here `P` is an explicit member, and the conclusion adds `P ≤ Q`.
The source's one-cut form `exists_mem_retainedCutFamily_of_mem_zeroLocus` is the case
`cuts = [f]`, since `Ideal.iteratedRetainedCutFamily Ps s [f]` is by definition
`Ideal.retainedCutFamily Ps s f`.
-/

@[expose] public section

namespace MvPolynomial

variable {k K σ : Type*} [Field k] [Field K] [Algebra k K] [Finite σ]

/-- Let `x` be a zero, over a field extension `K`, of a member `P` of `Ps`, at which `s` does not
vanish and every element of `cuts` vanishes. Then `x` is a zero of some member `Q` of the iterated
retained cut family with `P ≤ Q`.

The hypothesis `aeval x s ≠ 0` is needed: every member avoids `s` after one cut, so a point with
`s = 0` can be covered only for `cuts = []`. The vanishing of the cuts at `x` is needed because
every member contains every cut. -/
theorem exists_mem_iteratedRetainedCutFamily_of_mem_zeroLocus
    {Ps : Finset (Ideal (MvPolynomial σ k))} {P : Ideal (MvPolynomial σ k)} (hP : P ∈ Ps)
    {s : MvPolynomial σ k} {cuts : List (MvPolynomial σ k)} {x : σ → K}
    (hxP : x ∈ zeroLocus K P) (hxs : aeval x s ≠ 0) (hcuts : ∀ f ∈ cuts, aeval x f = 0) :
    ∃ Q ∈ Ideal.iteratedRetainedCutFamily Ps s cuts, P ≤ Q ∧ x ∈ zeroLocus K Q := by
  have : (RingHom.ker (aeval (R := k) x)).IsPrime := RingHom.ker_isPrime _
  obtain ⟨Q, hQ, hPQ, hQx⟩ := Ideal.exists_mem_iteratedRetainedCutFamily_le hP
    (mem_zeroLocus_iff_le_ker_aeval.mp hxP) (mt RingHom.mem_ker.mp hxs)
    (fun f hf ↦ RingHom.mem_ker.mpr (hcuts f hf))
  exact ⟨Q, hQ, hPQ, mem_zeroLocus_iff_le_ker_aeval.mpr hQx⟩

end MvPolynomial
