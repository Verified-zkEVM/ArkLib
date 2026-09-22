/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Differential.JetDegree
public import ArkLib.Data.Polynomial.TaylorPrefix
public import ArkLib.ToMathlib.MvPolynomial.SupportWeight
public import ArkLib.ToMathlib.Polynomial.HasseTaylor.Shift

/-!
# Universal Taylor residuals of differential polynomials

Fix a center `a` and a length `K`. Write a polynomial of degree `< K` around `a` with symbolic
Taylor coefficients `c₀, ..., c_(K-1)`, as `∑ l, c_l (x - a) ^ l`. Its `j`-th Hasse derivative,
in the displacement `ξ = x - a`, is the polynomial `universalTaylorJet K j` in the variables
`none = ξ` and `some l = c_l`. Substituting these jets into a differential polynomial `Q` of
order `r`, together with `x = a + ξ`, gives the universal residual
`universalTaylorResidual K a Q`. The coefficient of `ξ ^ h` in this residual is the order-`h`
Taylor coefficient of `Q` along every such polynomial.

The residual satisfies two support bounds, both without degree or characteristic hypotheses:

* every monomial of the coefficient of `ξ ^ h` has later-coefficient weight
  `∑ l, (l - r) * exponent(c_l)` at most `h`, because `c_l` first occurs in the `j`-th jet at
  order `l - j ≥ l - r`;
* every such coefficient has total degree at most the total jet degree of `Q`, because each jet is
  linear in the coefficient variables.

The first bound gives the separant-denominator budget: a monomial of the coefficient of `ξ ^ h`
that avoids `c_(r+h)` and later coefficients uses at most `2h - 2` powers of the separant when
each `c_l` with `l > r` carries denominator exponent `2(l - r) - 1`.

Specializing the coefficient variables to `c : ℕ → R` recovers the Taylor expansion at `a` of
`differentialSpecialization Q P`, where `P = Polynomial.centeredCoefficientPrefix a c K`.

## Main statements

* `PolynomialDifferential.universalTaylorJet` and `optionEquivLeft_universalTaylorJet`, which
  identifies it with the Hasse derivative of `∑ l, X l * ξ ^ l`.
* `PolynomialDifferential.universalTaylorResidual`.
* `weight_le_of_mem_universalTaylorResidual_coeff`: the Taylor-weight bound.
* `denominator_weight_le_of_mem_universalTaylorResidual_coeff`: the separant-denominator budget.
* `totalDegree_universalTaylorResidual_coeff_le`: the total-degree bound.
* `map_optionEquivLeft_universalTaylorResidual` and `aeval_universalTaylorResidual_coeff`:
  specialization to an explicit centered coefficient prefix.

## References

* [Dao, Q., Kominers, S. D., and Thaler, J., *Reed–Solomon Codes Beyond Johnson: Efficient
  Decoding and Smaller Cryptographic Proofs*][DKT26], Appendix A.6, Lemma A.4 (Regular Taylor
  chart).
-/

@[expose] public section

namespace PolynomialDifferential

noncomputable section

open MvPolynomial
open scoped BigOperators

section CommSemiring

variable {F : Type*} [CommSemiring F]

/-- The `j`-th Hasse derivative of `∑ l < K, c_l ξ ^ l`, as a polynomial in the displacement
`ξ` (variable `none`) and the symbolic coefficients `c_l` (variable `some l`). It is
`∑ l ≥ j, (l choose j) c_l ξ ^ (l - j)`. -/
def universalTaylorJet (K j : ℕ) : MvPolynomial (Option (Fin K)) F :=
  ∑ l ∈ Finset.univ.filter (fun l : Fin K ↦ j ≤ l.val),
    monomial (Finsupp.single (some l) 1 + Finsupp.single none (l.val - j))
      (Nat.choose l.val j : F)

/-- After separating the displacement variable, the universal jet is the Hasse derivative of
`∑ l < K, c_l ξ ^ l`. -/
theorem optionEquivLeft_universalTaylorJet (K j : ℕ) :
    optionEquivLeft F (Fin K) (universalTaylorJet (F := F) K j) =
      Polynomial.hasseDeriv j (∑ l : Fin K, Polynomial.monomial l.val (X l)) := by
  classical
  simp only [universalTaylorJet, map_sum, optionEquivLeft_monomial,
    Polynomial.hasseDeriv_monomial]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro l _
  by_cases hj : j ≤ l.val
  · simp only [hj, ↓reduceIte, Finsupp.add_apply, Finsupp.single_apply,
      Option.some_ne_none, zero_add, Finsupp.some_add,
      Finsupp.some_single_some, Finsupp.some_single_none, add_zero]
    congr 1
    rw [← C_mul_X_eq_monomial, map_natCast]
  · simp [hj, Nat.choose_eq_zero_of_lt (by omega : l.val < j)]

/-- The later-coefficient Taylor weight: the displacement has weight zero and `c_l` has weight
`l - r`, the least displacement order at which `c_l` can occur in a jet of order at most `r`. -/
abbrev taylorWeight (K r : ℕ) : Option (Fin K) → ℕ :=
  fun i ↦ i.elim 0 (fun l ↦ l.val - r)

/-- Every monomial of a jet of order `j ≤ r` has Taylor weight at most its displacement
exponent. The monomial `c_l ξ ^ (l - j)` has weight `l - r ≤ l - j`. -/
theorem universalTaylorJet_mem_supportWeightLE (K j r : ℕ) (hj : j ≤ r) :
    universalTaylorJet (F := F) K j ∈ supportWeightLE
      (Finsupp.weight (taylorWeight K r)) (Finsupp.applyAddHom none) := by
  classical
  apply Subalgebra.sum_mem
  intro l _
  apply monomial_mem_supportWeightLE
  simp only [map_add, Finsupp.weight_single, one_smul, Option.elim_some,
    Option.elim_none, smul_zero, add_zero, Finsupp.applyAddHom_apply,
    Finsupp.single_apply, Option.some_ne_none, ↓reduceIte, zero_add]
  omega

/-- The universal residual of an order-`r` differential polynomial `Q` along a length-`K` Taylor
chart at `center`. The independent variable becomes `center + ξ` and the jet variable `Y_j`
becomes `universalTaylorJet K j`. -/
def universalTaylorResidual {r : ℕ} (K : ℕ) (center : F)
    (Q : DifferentialPolynomial F r) : MvPolynomial (Option (Fin K)) F :=
  aeval (fun i ↦ i.elim (C center + X none) (fun j ↦ universalTaylorJet K j.val)) Q

/-- Every monomial of the universal residual has Taylor weight at most its displacement
exponent. No degree or characteristic hypothesis on `Q` is needed, because each substituted
generator satisfies the inequality and it is preserved by products and sums. -/
theorem universalTaylorResidual_mem_supportWeightLE {r : ℕ} (K : ℕ) (center : F)
    (Q : DifferentialPolynomial F r) :
    universalTaylorResidual K center Q ∈ supportWeightLE
      (Finsupp.weight (taylorWeight K r)) (Finsupp.applyAddHom none) := by
  apply aeval_mem_supportWeightLE
  intro i
  cases i with
  | none =>
    apply Subalgebra.add_mem
    · exact (supportWeightLE _ _).algebraMap_mem center
    · apply monomial_mem_supportWeightLE
      simp [Finsupp.weight_single]
  | some j => exact universalTaylorJet_mem_supportWeightLE K j.val r (by omega)

/-- Every monomial `m` of the coefficient of `ξ ^ h` in the universal residual satisfies
`∑ l, (l - r) * m l ≤ h`. -/
theorem weight_le_of_mem_universalTaylorResidual_coeff {r : ℕ} (K : ℕ) (center : F)
    (Q : DifferentialPolynomial F r) (h : ℕ) (m : Fin K →₀ ℕ)
    (hm : m ∈ ((optionEquivLeft F (Fin K) (universalTaylorResidual K center Q)).coeff h).support) :
    Finsupp.weight (fun l : Fin K ↦ l.val - r) m ≤ h :=
  weight_le_of_mem_coeff_optionEquivLeft _ _
    (universalTaylorResidual_mem_supportWeightLE K center Q) h m hm

/-- Separant-denominator budget. Suppose the chart has length `K ≤ r + h`, so it contains no
coefficient `c_l` with `l - r ≥ h`. If each `c_l` carries denominator exponent `2(l - r) - 1`,
every monomial of the coefficient of `ξ ^ h` has total denominator exponent at most `2h - 2`.

The length hypothesis is needed: at `K = r + h + 1`, the monomial `c_(r+h)` has exponent
`2h - 1`. -/
theorem denominator_weight_le_of_mem_universalTaylorResidual_coeff
    {r K h : ℕ} (hK : K ≤ r + h) (center : F)
    (Q : DifferentialPolynomial F r) (m : Fin K →₀ ℕ)
    (hm : m ∈ ((optionEquivLeft F (Fin K) (universalTaylorResidual K center Q)).coeff h).support) :
    Finsupp.weight (fun l : Fin K ↦ 2 * (l.val - r) - 1) m ≤ 2 * h - 2 :=
  Finsupp.weight_two_mul_sub_one_le (fun l : Fin K ↦ l.val - r) m
    (weight_le_of_mem_universalTaylorResidual_coeff K center Q h m hm)
    (fun l _ ↦ by omega)

/-- Every universal jet has degree at most one in the coefficient variables. -/
theorem weightedTotalDegree_universalTaylorJet_le (K j : ℕ) :
    (universalTaylorJet (F := F) K j).weightedTotalDegree
      (fun i : Option (Fin K) ↦ i.elim 0 (fun _ ↦ 1)) ≤ 1 := by
  classical
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
  apply Submodule.sum_mem
  intro l _
  apply (monomial_mem_restrictWeightedDegree _ _ _ _).mpr
  left
  simp only [map_add, Finsupp.weight_single, Option.elim_some, Option.elim_none,
    smul_zero, add_zero, one_smul, le_refl]

/-- The degree of the universal residual in the coefficient variables is at most the total jet
degree of `Q`. The degree of `Q` in the independent variable does not contribute, since
`center + ξ` has coefficient degree zero. -/
theorem weightedTotalDegree_universalTaylorResidual_le {r : ℕ} (K : ℕ) (center : F)
    (Q : DifferentialPolynomial F r) :
    (universalTaylorResidual K center Q).weightedTotalDegree
        (fun i : Option (Fin K) ↦ i.elim 0 (fun _ ↦ 1)) ≤ jetTotalDegree Q := by
  have hw : (jetDegreeWeight : JetVariable r → ℕ) = fun i ↦ i.elim 0 (fun _ ↦ 1) := by
    funext i
    cases i <;> rfl
  rw [jetTotalDegree, hw]
  apply weightedTotalDegree_aeval_le_of_le
  intro i
  cases i with
  | none =>
    apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
    apply Submodule.add_mem
    · exact C_mem_restrictWeightedDegree _ _ _
    · exact X_mem_restrictWeightedDegree _ _ _ (by simp)
  | some j => exact weightedTotalDegree_universalTaylorJet_le K j.val

/-- Each displacement coefficient of the universal residual has total degree at most the total
jet degree of `Q`. -/
theorem totalDegree_universalTaylorResidual_coeff_le {r : ℕ} (K : ℕ) (center : F)
    (Q : DifferentialPolynomial F r) (h : ℕ) :
    ((optionEquivLeft F (Fin K) (universalTaylorResidual K center Q)).coeff h).totalDegree ≤
      jetTotalDegree Q := by
  rw [← weightedTotalDegree_one]
  exact (weightedTotalDegree_coeff_optionEquivLeft_le _ _ _).trans
    (weightedTotalDegree_universalTaylorResidual_le K center Q)

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R]

/-- Specializing the coefficient variables of the universal residual to `c 0, ..., c (K - 1)`
gives the Taylor expansion at `center` of `Q` specialized at the centered coefficient prefix
`centeredCoefficientPrefix center c K`. -/
theorem map_optionEquivLeft_universalTaylorResidual {r : ℕ} (center : R) (c : ℕ → R) (K : ℕ)
    (Q : DifferentialPolynomial R r) :
    (optionEquivLeft R (Fin K) (universalTaylorResidual K center Q)).map
        (aeval fun i : Fin K ↦ c i.val).toRingHom =
      Polynomial.taylor center
        (differentialSpecialization Q (Polynomial.centeredCoefficientPrefix center c K)) := by
  set φ : MvPolynomial (Option (Fin K)) R →ₐ[R] Polynomial R :=
    (Polynomial.mapAlgHom (aeval fun i : Fin K ↦ c i.val)).comp
      (optionEquivLeft R (Fin K)).toAlgHom with hφ
  set P := Polynomial.centeredCoefficientPrefix center c K
  have hjet (j : ℕ) : φ (universalTaylorJet K j) =
      Polynomial.taylor center (Polynomial.hasseDeriv j P) := by
    rw [hφ, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, optionEquivLeft_universalTaylorJet,
      Polynomial.coe_mapAlgHom, ← Polynomial.hasseDeriv_map, ← Polynomial.hasseDeriv_taylor,
      Polynomial.taylor_centeredCoefficientPrefix]
    simp [Polynomial.map_sum, Polynomial.map_monomial]
  have heq : φ.comp (aeval (fun i : Option (Fin (r + 1)) ↦
        i.elim (C center + X none) (fun j ↦ universalTaylorJet K j.val))) =
      (Polynomial.taylorAlgHom center).comp (differentialSpecializationHom (d := r) P) := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i with
    | none =>
      simp [hφ, differentialSpecializationHom, add_comm]
    | some j =>
      simp only [AlgHom.comp_apply, aeval_X, Option.elim_some, hjet]
      simp [differentialSpecializationHom]
  have h := DFunLike.congr_fun heq Q
  rw [AlgHom.comp_apply, AlgHom.comp_apply] at h
  exact h

/-- Coefficientwise form of `map_optionEquivLeft_universalTaylorResidual`: evaluating the
coefficient of `ξ ^ h` at `c 0, ..., c (K - 1)` gives the `h`-th Taylor coefficient at `center` of
`Q` specialized at `centeredCoefficientPrefix center c K`. -/
theorem aeval_universalTaylorResidual_coeff {r : ℕ} (center : R) (c : ℕ → R) (K h : ℕ)
    (Q : DifferentialPolynomial R r) :
    aeval (fun i : Fin K ↦ c i.val)
        ((optionEquivLeft R (Fin K) (universalTaylorResidual K center Q)).coeff h) =
      (Polynomial.taylor center (differentialSpecialization Q
        (Polynomial.centeredCoefficientPrefix center c K))).coeff h := by
  rw [← map_optionEquivLeft_universalTaylorResidual, Polynomial.coeff_map]
  rfl

end CommRing

end

end PolynomialDifferential
