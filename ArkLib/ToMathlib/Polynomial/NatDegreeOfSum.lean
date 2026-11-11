/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilia Vlasov
-/
module

public import Mathlib.Algebra.Polynomial.BigOperators

/-!
# ArkLib.ToMathlib.Polynomial.NatDegreeOfSum

Natural-degree bounds for sums of polynomials.

* `Polynomial.natDegree_sum_lt_of_forall_lt`: a strict bound on every summand bounds the sum.
* `Polynomial.natDegree_eval_C_le`: a uniform bound on the coefficients of a bivariate polynomial
  bounds its specialization of the outer variable at any constant. It is the challenge-degree
  bound for the specialized denominator in
  `ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.HalfGap.Line`.
-/

@[expose] public section

namespace Polynomial

/-- If every summand has natural degree below `n`, with `n ≠ 0`, so does the sum. -/
theorem natDegree_sum_lt_of_forall_lt.{u_1, w}
    {ι : Type w} (s : Finset ι) {S : Type u_1} [Semiring S]
  {n : ℕ} [inst : NeZero n] (f : ι → Polynomial S) (h : ∀ i ∈ s, (f i).natDegree < n) :
  (∑ i ∈ s, f i).natDegree < n := by
  rw [←Nat.le_pred_iff_lt (by aesop (add safe forward [inst.out]) (add safe (by omega)))]
  exact natDegree_sum_le_of_forall_le _ _ <| fun i hi ↦
    Nat.le_pred_of_lt (h _ hi)

/-- **Specializing the outer variable of a bivariate polynomial at a constant.** If every
coefficient of `Q : S[X][Y]` has natural degree at most `b`, then so does `Q.eval (C x)` for every
`x : S`: it is `∑ j, Q.coeff j * C x ^ j`, and multiplying by a constant does not raise the
degree. The bound is uniform in `x`, so the product of `m` such specializations has natural degree
at most `m * b`. -/
theorem natDegree_eval_C_le {S : Type*} [Semiring S] {Q : S[X][X]} {b : ℕ}
    (h : ∀ j, (Q.coeff j).natDegree ≤ b) (x : S) :
    (Q.eval (C x)).natDegree ≤ b := by
  rw [eval_eq_sum]
  refine natDegree_sum_le_of_forall_le _ _ fun j _ ↦ natDegree_mul_le.trans ?_
  rw [← C_pow, natDegree_C, add_zero]
  exact h j

end Polynomial
