/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Differential.TaylorResidual
public import ArkLib.ToMathlib.MvPolynomial.SupportWeightOffset

/-!
# Coefficient-index weight of a universal Taylor residual

In the `j`-th universal jet `universalTaylorJet K j`, the symbolic Taylor coefficient `c_l` occurs
only in the monomial `c_l ξ ^ (l - j)`. Its index `l` therefore exceeds its displacement exponent
by exactly `j`. Give the variable `some l` the weight `l` and the displacement `none` the weight
zero; this is `indexWeight`. Multiplying jets adds these excesses, so every monomial of the
coefficient of `ξ ^ h` in `universalTaylorResidual K a Q` has index weight at most `h` plus the
weighted degree of `Q` in which the jet variable `Y_j` has weight `j`.

For a first-order differential polynomial, that weighted degree of `Q` is its degree in the
derivative variable `Y_1`.

## Main statements

* `PolynomialDifferential.universalTaylorJet_supportWeightOffset`: the `j`-th jet has index-weight
  allowance `j`.
* `PolynomialDifferential.universalTaylorResidual_supportWeightOffset`: the residual has allowance
  `Q.weightedTotalDegree (indexWeight (r + 1))`.
* `PolynomialDifferential.indexWeight_le_of_mem_universalTaylorResidual_coeff`: the resulting
  bound on each monomial of each displacement coefficient.
* `PolynomialDifferential.weightedTotalDegree_indexWeight_eq_jetDegree_one`: the first-order
  case.

## References

* [Dao, Q., Kominers, S. D., and Thaler, J., *Reed–Solomon Codes Beyond Johnson: Efficient
  Decoding and Smaller Cryptographic Proofs*][DKT26], Appendix A.6.
-/

@[expose] public section

namespace PolynomialDifferential

noncomputable section

open MvPolynomial
open scoped BigOperators

/-- The index weight on `Option (Fin n)`: `none` has weight zero and `some l` has weight `l`. -/
abbrev indexWeight (n : ℕ) : Option (Fin n) → ℕ :=
  fun i ↦ i.elim 0 Fin.val

variable {F : Type*} [CommSemiring F]

/-- Every monomial `c_l ξ ^ (l - j)` of the `j`-th universal jet has index weight `l`, which is its
displacement exponent plus `j`. -/
theorem universalTaylorJet_supportWeightOffset (K j : ℕ) :
    SupportWeightOffset (Finsupp.weight (indexWeight K)) (Finsupp.applyAddHom none) j
      (universalTaylorJet (F := F) K j) := by
  classical
  apply SupportWeightOffset.sum
  intro l hl
  apply SupportWeightOffset.monomial
  have hj := (Finset.mem_filter.mp hl).2
  simp only [map_add, Finsupp.weight_single, one_smul, Option.elim_some,
    Option.elim_none, smul_zero, add_zero, Finsupp.applyAddHom_apply,
    Finsupp.single_apply, Option.some_ne_none, ↓reduceIte, zero_add]
  omega

/-- Every monomial of the universal residual has index weight at most its displacement exponent
plus the weighted degree of `Q` in which `Y_j` has weight `j`. -/
theorem universalTaylorResidual_supportWeightOffset {r : ℕ} (K : ℕ) (center : F)
    (Q : DifferentialPolynomial F r) :
    SupportWeightOffset (Finsupp.weight (indexWeight K)) (Finsupp.applyAddHom none)
      (Q.weightedTotalDegree (indexWeight (r + 1)))
      (universalTaylorResidual K center Q) := by
  apply supportWeightOffset_aeval
  intro i
  cases i with
  | none =>
    apply SupportWeightOffset.add
    · exact SupportWeightOffset.C center
    · apply SupportWeightOffset.monomial
      simp [Finsupp.weight_single]
  | some j => exact universalTaylorJet_supportWeightOffset K j.val

/-- Every monomial `m` of the coefficient of `ξ ^ h` in the universal residual satisfies
`∑ l, l * m l ≤ h + Q.weightedTotalDegree (indexWeight (r + 1))`. -/
theorem indexWeight_le_of_mem_universalTaylorResidual_coeff {r : ℕ} (K : ℕ) (center : F)
    (Q : DifferentialPolynomial F r) (h : ℕ) (m : Fin K →₀ ℕ)
    (hm : m ∈ ((optionEquivLeft F (Fin K) (universalTaylorResidual K center Q)).coeff h).support) :
    Finsupp.weight Fin.val m ≤ h + Q.weightedTotalDegree (indexWeight (r + 1)) := by
  have hbound := universalTaylorResidual_supportWeightOffset K center Q (m.optionElim h)
    ((mem_support_coeff_optionEquivLeft F).mp hm)
  rw [Finsupp.weight_apply, Finsupp.sum_option_index] at hbound
  · simpa [Finsupp.weight_apply] using hbound
  · intro i
    simp
  · intro i c d
    exact add_smul c d _

/-- For a first-order differential polynomial, the weighted degree in which `Y_j` has weight `j`
is the degree in the derivative variable `Y_1`. -/
theorem weightedTotalDegree_indexWeight_eq_jetDegree_one (Q : DifferentialPolynomial F 1) :
    Q.weightedTotalDegree (indexWeight 2) = jetDegree Q 1 := by
  have hw : indexWeight 2 = Pi.single (some 1) 1 := by
    funext i
    cases i with
    | none => simp
    | some j => fin_cases j <;> simp
  rw [hw, weightedTotalDegree_piSingle, jetDegree]

end

end PolynomialDifferential
