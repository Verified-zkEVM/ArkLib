/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import CompPoly.Bivariate.GuruswamiSudan.Root.Common.Lemmas
public import CompPoly.Univariate.Roots.Correctness
-- These coefficient-array proofs reduce the implementation representation of both
-- `CBivariate` and its underlying computable univariate polynomials.
import all CompPoly.Bivariate.Basic
import all CompPoly.Univariate.Basic
import all CompPoly.Univariate.Raw.Core
import all CompPoly.Univariate.ToPoly.Core

/-!
# Executable content of a bivariate polynomial

For `Q` represented as `F[X][Y]`, its content in `Y` is the gcd of its
`F[X]` coefficients.  This is the first normalization step in the ordinary
Reed--Solomon decoder.  The construction below folds the executable monic gcd
over the stored coefficient array and proves that the result divides every
coefficient of `Q`.
-/

@[expose] public section

namespace CompPoly.CBivariate

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- Monic gcd of the first `bound` coefficients of `Q`, starting with zero. -/
def yContentUpTo (Q : CBivariate F) : ℕ → CPolynomial F
  | 0 => 0
  | bound + 1 =>
      CPolynomial.gcdMonic (yContentUpTo Q bound) (Q.val.coeff bound)

/-- The executable content of `Q` as a polynomial in `Y` over `F[X]`. -/
def yContent (Q : CBivariate F) : CPolynomial F :=
  yContentUpTo Q Q.val.size

/-- The partial content divides every coefficient already included in its fold. -/
theorem yContentUpTo_dvd_coeff (Q : CBivariate F) {index bound : ℕ}
    (hindex : index < bound) :
    (yContentUpTo Q bound).toPoly ∣ (Q.val.coeff index).toPoly := by
  induction bound with
  | zero => omega
  | succ bound ih =>
      rw [yContentUpTo]
      by_cases hlt : index < bound
      · exact (CPolynomial.toPoly_gcdMonic_dvd_left _ _).trans (ih hlt)
      · have heq : index = bound := by omega
        subst index
        exact CPolynomial.toPoly_gcdMonic_dvd_right _ _

/-- The computed `Y`-content divides every `F[X]` coefficient of `Q`. -/
theorem yContent_dvd_coeff (Q : CBivariate F) (index : ℕ) :
    (yContent Q).toPoly ∣ (Q.val.coeff index).toPoly := by
  by_cases hindex : index < Q.val.size
  · exact yContentUpTo_dvd_coeff Q hindex
  · have hzero : Q.val.coeff index = 0 :=
      CPolynomial.coeff_eq_zero_of_size_le Q (Nat.le_of_not_gt hindex)
    rw [hzero, CPolynomial.toPoly_zero]
    exact dvd_zero _

/-- Every common divisor of the first `bound` coefficients divides their
computed monic gcd. -/
theorem dvd_yContentUpTo (Q : CBivariate F) (divisor : Polynomial F) {bound : ℕ}
    (hdivisor : ∀ index, index < bound → divisor ∣ (Q.val.coeff index).toPoly) :
    divisor ∣ (yContentUpTo Q bound).toPoly := by
  induction bound with
  | zero =>
      rw [yContentUpTo, CPolynomial.toPoly_zero]
      exact dvd_zero divisor
  | succ bound ih =>
      rw [yContentUpTo]
      let : DecidableEq F := instDecidableEqOfLawfulBEq
      rw [CPolynomial.gcdMonic_toPoly_eq_normalize_gcd]
      apply (EuclideanDomain.dvd_gcd (ih fun index hindex => hdivisor index (by omega))
        (hdivisor bound (Nat.lt_succ_self bound))).trans
      exact (normalize_associated _).symm.dvd

/-- Universal characterization of the executable `Y`-content: its divisors
are exactly the common divisors of all `F[X]` coefficients of `Q`. -/
theorem dvd_yContent_iff (Q : CBivariate F) (divisor : Polynomial F) :
    divisor ∣ (yContent Q).toPoly ↔
      ∀ index, divisor ∣ (Q.val.coeff index).toPoly := by
  constructor
  · intro hdivisor index
    exact hdivisor.trans (yContent_dvd_coeff Q index)
  · intro hdivisor
    exact dvd_yContentUpTo Q divisor fun index _ => hdivisor index

/-- A nonzero bivariate polynomial has nonzero `Y`-content. -/
theorem yContent_ne_zero {Q : CBivariate F} (hQ : Q ≠ 0) : yContent Q ≠ 0 := by
  intro hcontent
  apply hQ
  rw [CPolynomial.eq_zero_iff_coeff_zero]
  intro index
  have hdivisor := yContent_dvd_coeff Q index
  rw [hcontent, CPolynomial.toPoly_zero, zero_dvd_iff] at hdivisor
  exact (CPolynomial.toPoly_eq_zero_iff (Q.val.coeff index)).mp hdivisor

/-- Divide every `Y`-coefficient by the computed content. -/
def primitivePartY (Q : CBivariate F) : CPolynomial (CPolynomial F) :=
  CPolynomial.ofArray (Q.val.map fun coefficient => coefficient / yContent Q)

theorem coeff_primitivePartY_of_lt (Q : CBivariate F) {index : ℕ}
    (hindex : index < Q.val.size) :
    CPolynomial.coeff (primitivePartY Q) index = Q.val.coeff index / yContent Q := by
  rw [primitivePartY, CPolynomial.coeff_ofArray]
  rw [CPolynomial.Raw.coeff, Array.getD_eq_getD_getElem?, Array.getElem?_map,
    Array.getElem?_eq_getElem hindex, Option.map_some, Option.getD_some]
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hindex,
    Option.getD_some]

/-- Removing the computed content is exact: multiplying the coefficientwise
quotient by that content reconstructs the original bivariate polynomial. -/
theorem C_yContent_mul_primitivePartY {Q : CBivariate F} (hQ : Q ≠ 0) :
    (CPolynomial.C (yContent Q) : CPolynomial (CPolynomial F)) *
      (primitivePartY Q : CPolynomial (CPolynomial F)) = Q := by
  rw [CPolynomial.eq_iff_coeff]
  intro index
  rw [CPolynomial.coeff_C_mul]
  by_cases hindex : index < Q.val.size
  · rw [coeff_primitivePartY_of_lt Q hindex]
    rw [← sub_eq_zero, ← CPolynomial.toPoly_eq_zero_iff,
      CPolynomial.toPoly_sub, CPolynomial.toPoly_mul]
    have hquotient :
        ((Q.val.coeff index / yContent Q : CPolynomial F)).toPoly =
          (Q.val.coeff index).toPoly / (yContent Q).toPoly :=
      CPolynomial.div_toPoly_eq_div _ _
    rw [hquotient]
    have hcontent : (yContent Q).toPoly ≠ 0 :=
      (CPolynomial.toPoly_eq_zero_iff (yContent Q)).not.mpr (yContent_ne_zero hQ)
    exact sub_eq_zero.mpr
      (EuclideanDomain.mul_div_cancel' hcontent (yContent_dvd_coeff Q index))
  · have hle : Q.val.size ≤ index := Nat.le_of_not_gt hindex
    have hprimitive : CPolynomial.coeff (primitivePartY Q) index = 0 := by
      rw [primitivePartY, CPolynomial.coeff_ofArray,
        Array.getD_eq_getD_getElem?, Array.getElem?_map,
        Array.getElem?_eq_none hle, Option.map_none, Option.getD_none]
    have hcoefficient : CPolynomial.coeff Q index = 0 :=
      CPolynomial.coeff_eq_zero_of_size_le Q hle
    rw [hprimitive, hcoefficient, mul_zero]

/-- Removing `Y`-content preserves the univariate polynomials that solve the
bivariate root equation. -/
theorem composeY_primitivePartY_eq_zero_iff {Q : CBivariate F} (hQ : Q ≠ 0)
    (P : CPolynomial F) :
    composeY (primitivePartY Q) P = 0 ↔ composeY Q P = 0 := by
  let : DecidableEq F := instDecidableEqOfLawfulBEq
  have hfactor :
      (composeY Q P).toPoly =
        (yContent Q).toPoly * (composeY (primitivePartY Q) P).toPoly := by
    calc
      _ = (composeY
          ((CPolynomial.C (yContent Q) : CPolynomial (CPolynomial F)) *
            primitivePartY Q) P).toPoly :=
        congrArg (fun equation => (composeY equation P).toPoly)
          (C_yContent_mul_primitivePartY hQ).symm
      _ = _ := by
        rw [GuruswamiSudan.composeY_toPoly, CBivariate.toPoly_mul,
          Polynomial.eval_mul, GuruswamiSudan.composeY_toPoly]
        congr 1
        rw [CBivariate.toPoly_eq_map, CPolynomial.C_toPoly,
          Polynomial.map_C, Polynomial.eval_C]
        exact CPolynomial.ringEquiv_apply (yContent Q)
  have hcontent : (yContent Q).toPoly ≠ 0 :=
    (CPolynomial.toPoly_eq_zero_iff (yContent Q)).not.mpr (yContent_ne_zero hQ)
  rw [← CPolynomial.toPoly_eq_zero_iff, ← CPolynomial.toPoly_eq_zero_iff,
    hfactor, mul_eq_zero, or_iff_right hcontent]

end CompPoly.CBivariate
