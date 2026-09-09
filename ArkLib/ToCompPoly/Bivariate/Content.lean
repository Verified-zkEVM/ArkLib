/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CompPoly.Bivariate.Basic
import CompPoly.Univariate.Roots.Correctness

/-!
# Executable content of a bivariate polynomial

For `Q` represented as `F[X][Y]`, its content in `Y` is the gcd of its
`F[X]` coefficients.  This is the first normalization step in the ordinary
Reed--Solomon decoder.  The construction below folds the executable monic gcd
over the stored coefficient array and proves that the result divides every
coefficient of `Q`.
-/

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

end CompPoly.CBivariate
