/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# `q`-ary entropy function

The `q`-ary entropy function `H_q : [0, 1] → ℝ`,

  `H_q(x) = x * log_q(q-1) - x * log_q x - (1-x) * log_q (1-x)` .

It is defined as Mathlib's natural-logarithm `Real.qaryEntropy` renormalised to base `q`,
rather than by the three `logb` terms above (which `qEntropy_eq_logb_form` recovers), so that
the whole `Real.qaryEntropy` and `Real.binEntropy` API — continuity, differentiability, sign,
monotonicity, concavity — transfers through a single division by the positive constant
`Real.log q`. For `q = 2` this is the standard binary entropy in bits.

## Main definitions

* `CodingTheory.qEntropy`: the base-`q` entropy function `H_q`.

## Main statements

* `CodingTheory.qEntropy_eq_logb_form`: the three-`logb`-term formula.
* `CodingTheory.qEntropy_eq_qaryEntropy_div_log`: the bridge to Mathlib.
* `CodingTheory.qEntropy_one_sub_inv`: `H_q(1 - 1/q) = 1`, the base-`q` normalisation;
  it is also the maximum, whence `CodingTheory.qEntropy_le_one`.
* `CodingTheory.qEntropy_nonneg`, `CodingTheory.qEntropy_pos`: sign on `[0, 1]` / `(0, 1)`.
* `CodingTheory.qEntropy_strictMonoOn`, `CodingTheory.qEntropy_strictAntiOn`: strict
  monotonicity either side of the maximum at `1 - 1/q`.
* `CodingTheory.qEntropy_continuous`, `CodingTheory.concaveOn_qEntropy`.
* `CodingTheory.qEntropy_zero`, `CodingTheory.qEntropy_one`: the endpoints of `[0, 1]`.
* `CodingTheory.qEntropy_two`, `CodingTheory.qEntropy_two_inv`: the binary case, in bits.
* `CodingTheory.qEntropy_of_le_one`: the degenerate `q ≤ 1` regime is identically `0`.

## References

* [Arnon, G., Boneh, D., Fenzi, G., *Open Problems in List Decoding and
  Correlated Agreement*][ABF26]
-/

namespace CodingTheory

open Real

variable {q : ℕ} {x : ℝ}

/-- The `q`-ary entropy function on `[0, 1]`,

  `H_q(x) = x * log_q(q-1) - x * log_q x - (1-x) * log_q (1-x)`

(see `qEntropy_eq_logb_form`), defined as Mathlib's natural-log `Real.qaryEntropy` rescaled
to base `q`. For `q = 2` it is the binary entropy function in bits.

The convention `Real.log 0 = 0` makes the endpoints well-defined, `qEntropy q 0 = 0` and
`qEntropy q 1 = log_q (q-1)`.

For `q ≤ 1` the function is identically `0` (`qEntropy_of_le_one`), since `Real.log q = 0`
there. The intended range is `2 ≤ q`, an alphabet size; consumers needing a meaningful value
must guard for it themselves. -/
noncomputable def qEntropy (q : ℕ) (x : ℝ) : ℝ := Real.qaryEntropy q x / Real.log q

/-- `qEntropy` is `Real.qaryEntropy` rescaled by `Real.log q`. True by definition, and
named so that call sites can rewrite in either direction without unfolding.

Deliberately not `simp`: the `logb`-based spelling is the intended normal form. -/
lemma qEntropy_eq_qaryEntropy_div_log (q : ℕ) (x : ℝ) :
    qEntropy q x = Real.qaryEntropy q x / Real.log q := rfl

/-- `qEntropy` in expanded form,
`H_q(x) = x * log_q(q-1) - x * log_q x - (1-x) * log_q (1-x)`.

Holds unconditionally: for `q ≤ 1` both sides are `0`. -/
lemma qEntropy_eq_logb_form (q : ℕ) (x : ℝ) :
    qEntropy q x =
      x * Real.logb q (q - 1) - x * Real.logb q x - (1 - x) * Real.logb q (1 - x) := by
  rw [qEntropy, Real.qaryEntropy, Real.binEntropy]
  simp only [Real.logb, Real.log_inv]
  push_cast
  ring

@[simp]
lemma qEntropy_zero (q : ℕ) : qEntropy q 0 = 0 := by
  simp [qEntropy]

/-- Value at the right endpoint of `[0, 1]`: `H_q(1) = log_q (q - 1)`. In particular
`H_2(1) = 0`. -/
@[simp]
lemma qEntropy_one (q : ℕ) : qEntropy q 1 = Real.logb q (q - 1) := by
  rw [qEntropy, Real.qaryEntropy_one, Real.logb]
  push_cast
  rfl

/-- The `q ≤ 1` regime is degenerate: `Real.log q = 0`, so `H_0` and `H_1` are identically
`0`. This is the formal content of the boundary caveat in `qEntropy`'s docstring. -/
lemma qEntropy_of_le_one (hq : q ≤ 1) (x : ℝ) : qEntropy q x = 0 := by
  have hlog : Real.log q = 0 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hq with h | h <;> simp [h]
  simp [qEntropy, hlog]

/-- For `q = 2`, `qEntropy` is Mathlib's binary entropy measured in bits. -/
lemma qEntropy_two (x : ℝ) : qEntropy 2 x = Real.binEntropy x / Real.log 2 := by
  simp [qEntropy]

/-- `H_2(1/2) = 1`: one bit. -/
@[simp]
lemma qEntropy_two_inv : qEntropy 2 (2⁻¹ : ℝ) = 1 := by
  rw [qEntropy_two, Real.binEntropy_two_inv, div_self (Real.log_ne_zero_of_pos_of_ne_one
    (by norm_num) (by norm_num))]

/-- `H_q` is non-negative on `[0, 1]`, including the degenerate `q ≤ 1` regime where it
is identically zero. -/
lemma qEntropy_nonneg (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) : 0 ≤ qEntropy q x := by
  by_cases hq : q ≤ 1
  · rw [qEntropy_of_le_one hq]
  · exact div_nonneg (Real.qaryEntropy_nonneg hx₀ hx₁)
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ q by omega)))

/-- `H_q` is strictly positive on the open interval `(0, 1)` when `2 ≤ q`. -/
lemma qEntropy_pos (hq : 2 ≤ q) (hx₀ : 0 < x) (hx₁ : x < 1) : 0 < qEntropy q x :=
  div_pos (Real.qaryEntropy_pos hx₀ hx₁) (Real.log_pos (by exact_mod_cast hq))

/-- Base-`q` normalisation: `H_q(1 - 1/q) = 1`.

The point `1 - 1/q` is the maximiser of `H_q` on `[0, 1]` (`qEntropy_strictMonoOn`,
`qEntropy_strictAntiOn`), and the base-`q` scaling is the one making that maximum `1`.
Specialises to `H_2(1/2) = 1` and `H_3(2/3) = 1`. -/
lemma qEntropy_one_sub_inv (hq : 2 ≤ q) : qEntropy q (1 - 1 / q) = 1 := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hqm1 : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  have hself : Real.logb q (q : ℝ) = 1 := Real.logb_self_eq_one hq1
  have hsub : (1 : ℝ) - (1 - 1 / (q : ℝ)) = 1 / (q : ℝ) := by ring
  have hlow : Real.logb q ((1 : ℝ) - 1 / (q : ℝ)) = Real.logb q ((q : ℝ) - 1) - 1 := by
    rw [show (1 : ℝ) - 1 / (q : ℝ) = ((q : ℝ) - 1) / (q : ℝ) by field_simp,
      Real.logb_div (ne_of_gt hqm1) (ne_of_gt hq0), hself]
  have hinv : Real.logb q (1 / (q : ℝ)) = -1 := by
    rw [Real.logb_div one_ne_zero (ne_of_gt hq0), Real.logb_one, hself]; ring
  rw [qEntropy_eq_logb_form, hsub, hlow, hinv]
  field_simp
  ring

/-- `H_q` is continuous (the rescaling is by a constant, so this holds for every `q`,
including the degenerate `q ≤ 1`). -/
@[fun_prop]
lemma qEntropy_continuous (q : ℕ) : Continuous (qEntropy q) :=
  Real.qaryEntropy_continuous.div_const _

/-- `H_q` is strictly increasing on `[0, 1 - 1/q]`, i.e. up to its maximum. -/
lemma qEntropy_strictMonoOn (hq : 2 ≤ q) :
    StrictMonoOn (qEntropy q) (Set.Icc 0 (1 - 1 / q)) := by
  have hlog : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq)
  intro a ha b hb hab
  simp only [qEntropy]
  gcongr
  exact Real.qaryEntropy_strictMonoOn hq ha hb hab

/-- `H_q` is strictly decreasing on `[1 - 1/q, 1]`, i.e. past its maximum. -/
lemma qEntropy_strictAntiOn (hq : 2 ≤ q) :
    StrictAntiOn (qEntropy q) (Set.Icc (1 - 1 / q) 1) := by
  have hlog : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq)
  intro a ha b hb hab
  simp only [qEntropy]
  gcongr
  exact Real.qaryEntropy_strictAntiOn hq ha hb hab

/-- `H_q ≤ 1` on `[0, 1]`: the base-`q` entropy of a `q`-ary symbol never exceeds one
`q`-ary symbol's worth of information. For `q ≥ 2` the bound is attained at `1 - 1/q`
(`qEntropy_one_sub_inv`); for `q ≤ 1` the function is identically zero. -/
lemma qEntropy_le_one (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) : qEntropy q x ≤ 1 := by
  by_cases hqle : q ≤ 1
  · rw [qEntropy_of_le_one hqle]
    norm_num
  have hq : 2 ≤ q := by omega
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  have hmax₀ : (0 : ℝ) ≤ 1 - 1 / (q : ℝ) := by
    rw [sub_nonneg, div_le_one (by linarith)]; linarith
  have hmax₁ : (1 : ℝ) - 1 / (q : ℝ) ≤ 1 := by
    have : (0 : ℝ) < 1 / (q : ℝ) := by positivity
    linarith
  rw [← qEntropy_one_sub_inv hq]
  rcases le_total x (1 - 1 / (q : ℝ)) with h | h
  · exact (qEntropy_strictMonoOn hq).monotoneOn ⟨hx₀, h⟩ ⟨hmax₀, le_rfl⟩ h
  · exact (qEntropy_strictAntiOn hq).antitoneOn ⟨le_rfl, hmax₁⟩ ⟨h, hx₁⟩ h

/-- `H_q` is concave on `[0, 1]`, inherited from `Real.strictConcaveOn_qaryEntropy` through
nonnegative rescaling. This includes `q = 0` and `q = 1`, where the rescaling and hence
`qEntropy` are zero. (Strict concavity also holds in the nondegenerate regime, but Mathlib has no
`StrictConcaveOn.smul`, so only the non-strict form is transported here.) -/
lemma concaveOn_qEntropy (q : ℕ) : ConcaveOn ℝ (Set.Icc 0 1) (qEntropy q) := by
  have hc : (0 : ℝ) ≤ (Real.log q)⁻¹ := by
    by_cases hq0 : q = 0
    · simp [hq0]
    · exact inv_nonneg.mpr (Real.log_nonneg (by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hq0)))
  refine ((Real.strictConcaveOn_qaryEntropy (q := q)).concaveOn.smul hc).congr ?_
  intro y _
  simp [qEntropy, div_eq_inv_mul]

end CodingTheory
