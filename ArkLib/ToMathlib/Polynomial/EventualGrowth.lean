/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Order.Interval.Set.Infinite

/-!
# Polynomials compared on large natural numbers

Affine Hilbert functions are known only through their values at large natural numbers, so the
polynomials that describe them are compared by their values on a tail `N ≥ N₀` of `ℕ`. This file
collects the comparison lemmas that do not mention ideals.

Over a commutative domain of characteristic zero, two polynomials that agree on a tail of `ℕ` are
equal. Over an Archimedean ordered normed field such as `ℚ` or `ℝ`, a polynomial that is
eventually nonnegative on `ℕ` has a nonnegative leading coefficient, and if `Q ≤ R` eventually on
`ℕ` with `Q` eventually nonnegative, then `Q` has natural degree at most that of `R`, with leading
coefficients compared when the degrees agree.

The backward difference `Polynomial.backwardDifference b P = P - taylor (-b) P` evaluates to
`P x - P (x - b)`. It has natural degree at most `natDegree P - 1`, and its coefficient in degree
`natDegree P - 1` is `b * natDegree P * leadingCoeff P`, over every commutative ring. Combining the
two, a polynomial that is eventually nonnegative and eventually at most `P N - P (N - b)` has
natural degree at most `natDegree P - 1` and a coefficient in that degree at most
`b * natDegree P * leadingCoeff P`. This is the arithmetic behind the principal-cut degree drop of
affine Hilbert polynomials.

## Main statements

* `Polynomial.eq_of_eventually_eval_natCast_eq`: agreement on a tail of `ℕ` forces equality.
* `Polynomial.backwardDifference`, `Polynomial.eval_backwardDifference`: the difference
  `P x - P (x - b)` as a polynomial.
* `Polynomial.natDegree_backwardDifference_le`,
  `Polynomial.coeff_backwardDifference_natDegree_sub_one`,
  `Polynomial.natDegree_backwardDifference_eq_and_leadingCoeff`: its degree and top coefficient.
* `Polynomial.leadingCoeff_nonneg_of_eventually_eval_natCast_nonneg`: eventual nonnegativity on
  `ℕ` gives a nonnegative leading coefficient.
* `Polynomial.natDegree_le_of_eventually_eval_natCast_le`: eventual comparison on `ℕ` compares
  natural degrees and, for equal degrees, leading coefficients.
* `Polynomial.natDegree_le_and_coeff_le_of_eventually_eval_natCast_le_backwardDifference`: the
  bound on a polynomial eventually below a backward difference.

## References

Ported from ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`, namespace
`AffineHilbert`: `polynomial_eq_of_eval_nat_ge` from
`ArkLib/ToMathlib/AlgebraicGeometry/Hilbert/Polynomial.lean`, and `backwardDifference`,
`natDegree_backwardDifference_le`, `coeff_backwardDifference_pred_natDegree`,
`backwardDifference_natDegree_eq_and_leadingCoeff`, the private
`leadingCoeff_nonneg_of_eventually_eval_nat_nonneg` and
`natDegree_le_of_eventually_eval_nat_le` from
`ArkLib/ToMathlib/AlgebraicGeometry/PrincipalCut/Degree.lean`. The source worked over `ℚ` with a
natural shift `b`. Here equality on a tail holds over any commutative domain of characteristic
zero; the backward-difference algebra holds over any commutative ring with a shift in the ring,
and the coefficient identity needs no positivity of the degree; the order statements hold over
any Archimedean ordered normed field with the order topology. The comparison lemma
`natDegree_le_of_eventually_eval_natCast_le` no longer assumes `Q ≠ 0`. The final lemma is the
polynomial half of the source's `principalCut_eventualPolynomial_degree_and_coeff`, separated from
the Hilbert-function inequality. It needs neither a sign condition on `b` nor the eventual
positivity of `P`, which the source took from the Hilbert function, and its conclusion also holds
for `Q = 0`, so the source's disjunction with `Q = 0` is not needed.

The rescaled and affine growth lemmas of `Hilbert/PolynomialGrowthRescaling.lean` and
`Hilbert/PolynomialGrowthAffine.lean`, and the coefficient bounds of
`Hilbert/PrimeFamilyCoefficient.lean`, are not ported here.
-/

@[expose] public section

noncomputable section

open Filter

namespace Polynomial

section Domain

variable {R : Type*} [CommRing R] [IsDomain R] [CharZero R]

/-- Two polynomials over a commutative domain of characteristic zero that agree at every natural
number `N ≥ N₀` are equal. The natural numbers past `N₀` are infinitely many distinct elements of
`R`, and a nonzero polynomial has finitely many roots. Characteristic zero is needed: over
`ZMod p` the polynomials `X ^ p` and `X` agree at every natural number. -/
theorem eq_of_eventually_eval_natCast_eq {P Q : R[X]} {N₀ : ℕ}
    (h : ∀ N ≥ N₀, P.eval (N : R) = Q.eval (N : R)) : P = Q := by
  apply eq_of_infinite_eval_eq
  refine ((Set.Ici_infinite N₀).image Nat.cast_injective.injOn).mono ?_
  rintro x ⟨N, hN, rfl⟩
  exact h N hN

/-- The filter form of `eq_of_eventually_eval_natCast_eq`. -/
theorem eq_of_eventually_atTop_eval_natCast_eq {P Q : R[X]}
    (h : ∀ᶠ N : ℕ in atTop, P.eval (N : R) = Q.eval (N : R)) : P = Q :=
  let ⟨_, hN₀⟩ := eventually_atTop.mp h
  eq_of_eventually_eval_natCast_eq hN₀

end Domain

section BackwardDifference

variable {R : Type*} [CommRing R]

/-- The backward difference of `P` with step `b`: the polynomial `P(X) - P(X - b)`. -/
def backwardDifference (b : R) (P : R[X]) : R[X] :=
  P - taylor (-b) P

@[simp]
theorem eval_backwardDifference (b x : R) (P : R[X]) :
    (backwardDifference b P).eval x = P.eval x - P.eval (x - b) := by
  rw [backwardDifference, eval_sub, taylor_eval, ← sub_eq_add_neg]

/-- A step of zero gives the zero polynomial. -/
@[simp]
theorem backwardDifference_zero_left (P : R[X]) : backwardDifference 0 P = 0 := by
  simp [backwardDifference]

/-- A constant polynomial has zero backward difference. -/
@[simp]
theorem backwardDifference_C (b c : R) : backwardDifference b (C c) = 0 := by
  simp [backwardDifference]

/-- The backward difference lowers the natural degree by at least one. The leading terms of `P`
and of its shift `taylor (-b) P` coincide, so they cancel. For a constant `P` both sides are
`0`. -/
theorem natDegree_backwardDifference_le (b : R) (P : R[X]) :
    (backwardDifference b P).natDegree ≤ P.natDegree - 1 := by
  rcases Nat.eq_zero_or_pos P.natDegree with hd | hd
  · rw [eq_C_of_natDegree_eq_zero hd, backwardDifference_C, natDegree_zero]
    exact Nat.zero_le _
  refine natDegree_le_iff_coeff_eq_zero.mpr fun n hn ↦ ?_
  have hn' : P.natDegree ≤ n := by
    have : P.natDegree - 1 < n := by exact_mod_cast hn
    omega
  rw [backwardDifference, coeff_sub]
  rcases hn'.eq_or_lt with heq | hlt
  · subst heq
    rw [taylor_coeff, hasseDeriv_natDegree_eq_C, eval_C, sub_eq_zero]
    rfl
  · rw [coeff_eq_zero_of_natDegree_lt hlt,
      coeff_eq_zero_of_natDegree_lt ((natDegree_taylor P (-b)).symm ▸ hlt), sub_zero]

/-- The coefficient of the backward difference in degree `natDegree P - 1` is
`b * natDegree P * leadingCoeff P`: the shift `P(X - b)` changes the coefficient of
`X ^ (d - 1)` by `-b * d * leadingCoeff P`, where `d = natDegree P`. The identity also holds for
a constant `P`, where both sides are `0`. -/
theorem coeff_backwardDifference_natDegree_sub_one (b : R) (P : R[X]) :
    (backwardDifference b P).coeff (P.natDegree - 1) = b * P.natDegree * P.leadingCoeff := by
  rcases Nat.eq_zero_or_pos P.natDegree with hd | hd
  · rw [hd, Nat.cast_zero, mul_zero, zero_mul, eq_C_of_natDegree_eq_zero hd,
      backwardDifference_C, coeff_zero]
  set d := P.natDegree with hd_def
  have hlin : (hasseDeriv (d - 1) P).natDegree ≤ 1 :=
    (natDegree_hasseDeriv_le P (d - 1)).trans (by omega)
  have hcoeff1 : (hasseDeriv (d - 1) P).coeff 1 = d * P.leadingCoeff := by
    rw [hasseDeriv_coeff, show 1 + (d - 1) = d by omega, leadingCoeff, ← hd_def]
    congr 1
    obtain ⟨e, he⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
    rw [he, Nat.succ_sub_one, Nat.choose_succ_self_right]
  have hcoeff0 : (hasseDeriv (d - 1) P).coeff 0 = P.coeff (d - 1) := by
    rw [hasseDeriv_coeff, zero_add, Nat.choose_self, Nat.cast_one, one_mul]
  rw [backwardDifference, coeff_sub, taylor_coeff, eq_X_add_C_of_natDegree_le_one hlin,
    eval_add, eval_mul, eval_C, eval_X, eval_C, hcoeff1, hcoeff0]
  ring

/-- When `b * natDegree P * leadingCoeff P ≠ 0`, the backward difference has natural degree
exactly `natDegree P - 1`, with that value as its leading coefficient. The hypothesis is
necessary: for `b = 0`, or for a constant `P`, the backward difference is zero. -/
theorem natDegree_backwardDifference_eq_and_leadingCoeff {b : R} {P : R[X]}
    (h : b * P.natDegree * P.leadingCoeff ≠ 0) :
    (backwardDifference b P).natDegree = P.natDegree - 1 ∧
      (backwardDifference b P).leadingCoeff = b * P.natDegree * P.leadingCoeff := by
  have hcoeff := coeff_backwardDifference_natDegree_sub_one b P
  have hdeg := natDegree_eq_of_le_of_coeff_ne_zero (natDegree_backwardDifference_le b P)
    (hcoeff.symm ▸ h)
  exact ⟨hdeg, by rw [leadingCoeff, hdeg, hcoeff]⟩

/-- Over a domain of characteristic zero, a nonzero step and a nonconstant polynomial give a
backward difference of natural degree exactly `natDegree P - 1`. -/
theorem natDegree_backwardDifference_eq_and_leadingCoeff_of_ne_zero [IsDomain R] [CharZero R]
    {b : R} (hb : b ≠ 0) {P : R[X]} (hd : 0 < P.natDegree) :
    (backwardDifference b P).natDegree = P.natDegree - 1 ∧
      (backwardDifference b P).leadingCoeff = b * P.natDegree * P.leadingCoeff :=
  natDegree_backwardDifference_eq_and_leadingCoeff <| mul_ne_zero
    (mul_ne_zero hb (Nat.cast_ne_zero.mpr hd.ne'))
    (leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt hd))

end BackwardDifference

section Order

variable {K : Type*} [NormedField K] [LinearOrder K] [IsStrictOrderedRing K] [OrderTopology K]
  [Archimedean K]

/-- A polynomial that is eventually nonnegative on the natural numbers has a nonnegative leading
coefficient. A nonconstant polynomial with negative leading coefficient tends to `-∞`, and the
natural numbers tend to `+∞` because `K` is Archimedean. -/
theorem leadingCoeff_nonneg_of_eventually_eval_natCast_nonneg {P : K[X]}
    (h : ∀ᶠ N : ℕ in atTop, 0 ≤ P.eval (N : K)) : 0 ≤ P.leadingCoeff := by
  by_contra! hlc
  rcases Nat.eq_zero_or_pos P.natDegree with hd | hd
  · obtain ⟨N, hN⟩ := h.exists
    rw [eq_C_of_natDegree_eq_zero hd, eval_C] at hN
    rw [leadingCoeff, hd] at hlc
    exact hlc.not_ge hN
  · have ht := P.tendsto_atBot_of_leadingCoeff_nonpos (natDegree_pos_iff_degree_pos.mp hd) hlc.le
    obtain ⟨N, hN, hN'⟩ :=
      (h.and ((ht.comp tendsto_natCast_atTop_atTop).eventually_lt_atBot 0)).exists
    exact hN'.not_ge hN

/-- A nonzero polynomial that is eventually nonnegative on the natural numbers has a positive
leading coefficient. -/
theorem leadingCoeff_pos_of_eventually_eval_natCast_nonneg {P : K[X]} (hP : P ≠ 0)
    (h : ∀ᶠ N : ℕ in atTop, 0 ≤ P.eval (N : K)) : 0 < P.leadingCoeff :=
  (leadingCoeff_nonneg_of_eventually_eval_natCast_nonneg h).lt_of_ne'
    (leadingCoeff_ne_zero.mpr hP)

/-- If `Q` is eventually nonnegative on the natural numbers and eventually at most `R` there,
then `natDegree Q ≤ natDegree R`, and when the natural degrees agree,
`leadingCoeff Q ≤ leadingCoeff R`.

Both conclusions come from the nonnegative leading coefficients of `Q` and `R - Q`. The
nonnegativity of `Q` is necessary: `Q = -X ^ 2` lies below `R = 0` everywhere. -/
theorem natDegree_le_of_eventually_eval_natCast_le {Q R : K[X]}
    (hQ : ∀ᶠ N : ℕ in atTop, 0 ≤ Q.eval (N : K))
    (hle : ∀ᶠ N : ℕ in atTop, Q.eval (N : K) ≤ R.eval (N : K)) :
    Q.natDegree ≤ R.natDegree ∧
      (Q.natDegree = R.natDegree → Q.leadingCoeff ≤ R.leadingCoeff) := by
  have hQlc := leadingCoeff_nonneg_of_eventually_eval_natCast_nonneg hQ
  have hdiff : 0 ≤ (R - Q).leadingCoeff := leadingCoeff_nonneg_of_eventually_eval_natCast_nonneg
    (hle.mono fun N hN ↦ by rw [eval_sub]; exact sub_nonneg.mpr hN)
  constructor
  · by_contra! hlt
    have hQ0 : Q ≠ 0 := ne_zero_of_natDegree_gt hlt
    rw [leadingCoeff_sub_of_degree_lt' (degree_lt_degree hlt), neg_nonneg] at hdiff
    exact leadingCoeff_ne_zero.mpr hQ0 (le_antisymm hdiff hQlc)
  · intro hdeg
    by_cases hR : R = 0
    · subst hR
      rw [zero_sub, leadingCoeff_neg, neg_nonneg] at hdiff
      rwa [leadingCoeff_zero]
    by_cases hQ0 : Q = 0
    · subst hQ0
      rwa [sub_zero] at hdiff
    by_cases hlc : R.leadingCoeff = Q.leadingCoeff
    · exact hlc.ge
    have hdegree : R.degree = Q.degree := by
      rw [degree_eq_natDegree hR, degree_eq_natDegree hQ0, hdeg]
    rw [leadingCoeff_sub_of_degree_eq hdegree hlc] at hdiff
    exact sub_nonneg.mp hdiff

/-- A polynomial `Q` that is eventually nonnegative on the natural numbers and eventually at most
`P N - P (N - b)` there satisfies `natDegree Q ≤ natDegree P - 1` and
`Q.coeff (natDegree P - 1) ≤ b * natDegree P * leadingCoeff P`.

When `Q` reaches degree `natDegree P - 1`, the coefficient bound compares leading coefficients
with the backward difference. Otherwise the coefficient is `0`, and the right side is nonnegative:
either it is `0`, or it is the leading coefficient of the backward difference, which is eventually
at least `Q` and hence eventually nonnegative. No sign condition on `b` or on `P` is needed, and
the conclusion includes `Q = 0`. -/
theorem natDegree_le_and_coeff_le_of_eventually_eval_natCast_le_backwardDifference
    {b : K} {P Q : K[X]} (hQ : ∀ᶠ N : ℕ in atTop, 0 ≤ Q.eval (N : K))
    (hle : ∀ᶠ N : ℕ in atTop, Q.eval (N : K) ≤ (backwardDifference b P).eval (N : K)) :
    Q.natDegree ≤ P.natDegree - 1 ∧
      Q.coeff (P.natDegree - 1) ≤ b * P.natDegree * P.leadingCoeff := by
  obtain ⟨hdeg, hlc⟩ := natDegree_le_of_eventually_eval_natCast_le hQ hle
  have hBdeg := natDegree_backwardDifference_le b P
  refine ⟨hdeg.trans hBdeg, ?_⟩
  rcases (hdeg.trans hBdeg).lt_or_eq with hlt | heq
  · rw [coeff_eq_zero_of_natDegree_lt hlt]
    by_cases h0 : b * P.natDegree * P.leadingCoeff = 0
    · exact h0.ge
    rw [← (natDegree_backwardDifference_eq_and_leadingCoeff h0).2]
    exact leadingCoeff_nonneg_of_eventually_eval_natCast_nonneg
      ((hQ.and hle).mono fun _ h ↦ h.1.trans h.2)
  · have hBeq : (backwardDifference b P).natDegree = Q.natDegree :=
      le_antisymm (heq ▸ hBdeg) hdeg
    calc Q.coeff (P.natDegree - 1) = Q.leadingCoeff := by rw [leadingCoeff, heq]
      _ ≤ (backwardDifference b P).leadingCoeff := hlc hBeq.symm
      _ = b * P.natDegree * P.leadingCoeff := by
        rw [leadingCoeff, hBeq, heq, coeff_backwardDifference_natDegree_sub_one]

end Order

end Polynomial
