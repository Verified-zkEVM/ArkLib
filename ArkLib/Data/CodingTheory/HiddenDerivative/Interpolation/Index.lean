/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Kai Zhe Zheng
-/
module

public import ArkLib.Data.Polynomial.Differential.JetDegree
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# The exact finite interpolation space for hidden-derivative list decoding

For ambient degree `D`, agreement threshold `A`, derivative order `d`, multiplicity `m`, first-jet
cap `M`, and higher-jet budget `W`, the exact interpolation space consists of the differential
polynomials `Q(X, Y₀, ..., Y_d)` whose monomials `X^a Y₀^b₀ ⋯ Y_d^b_d` satisfy

```text
b₁ ≤ M,
sum_{j=2}^d (j - 1) b_j ≤ W,
a + D b₀ + (D - 1) b₁ + ... + (D - d) b_d < m A.
```

The last expression is the `differentialWeight D` weight of the exponent, the same weight that
bounds the degree of a specialization `Q(X, P, P', ...)` for `deg P ≤ D`.

The hypothesis `d < D` is necessary for finiteness: it gives every jet variable weight at least
`D - d > 0`, which bounds the total jet degree by `⌊(mA - 1)/(D - d)⌋`. At `D = d` the variable
`Y_d` has weight zero and all of its powers are eligible. The space is therefore indexed by a
proof of `d < D`, and its canonical monomial basis gives finite coefficient coordinates, the
columns of the local constraint systems.

## Main statements

* `exactInterpolationExponentSet_finite`: the eligible exponents form a finite set when `d < D`.
* `exactInterpolationSpace` with its basis, coordinates, and
  `exactInterpolationCoefficientEvaluator`, which turns a linear map on differential polynomials
  into a map on coefficient columns.
* `differentialWeightedDegree_lt_of_mem_exactInterpolationSpace`,
  `jetTotalDegree_le_floor_of_mem_exactInterpolationSpace`, and
  `jetDegree_le_floor_of_mem_exactInterpolationSpace`: degree bounds for members of the space.
* `finrank_exactInterpolationSpace_eq_card`: its dimension is the number of eligible exponents.

## References

* [Brakensiek, J., Chen, Y., Putterman, A., Zhang, Z., and Zheng, K. Z., *Algorithmic List
  Decoding of Reed–Solomon Codes up to Capacity in the Low-Rate Regime*][BCPZZ26].
* [Dao, Q., Kominers, S. D., and Thaler, J., *Reed–Solomon Codes Beyond Johnson: Efficient
  Decoding and Smaller Cryptographic Proofs*][DKT26], Section 6.1, the support (70).
-/

@[expose] public section

open PolynomialDifferential

namespace ReedSolomon.HiddenDerivative

noncomputable section

variable {R V : Type*} {d D A m M W : ℕ}

/-! ### Jet weights -/

/-- The weight counting the exponent of `Y₁`. It is zero on every variable when `d = 0`. -/
def jetFirstWeight : JetVariable d → ℕ
  | none => 0
  | some j => if j.val = 1 then 1 else 0

/-- The anisotropic higher-jet weight: `X`, `Y₀`, and `Y₁` have weight zero and `Y_j` has
weight `j - 1`. -/
def jetHigherWeight : JetVariable d → ℕ
  | none => 0
  | some j => j.val - 1

/-- The exponent of `Y₁` in a monomial. -/
def firstJetExponent (u : JetVariable d →₀ ℕ) : ℕ :=
  Finsupp.weight jetFirstWeight u

/-- The higher-jet weight `∑_{j ≥ 2} (j - 1) b_j` of a monomial. -/
def fullHigherJetWeight (u : JetVariable d →₀ ℕ) : ℕ :=
  Finsupp.weight jetHigherWeight u

/-- The degree of an exponent splits into the `X` exponent and the total jet degree. -/
theorem degree_eq_add_totalJetDegree (u : JetVariable d →₀ ℕ) :
    u.degree = u none + totalJetDegree u := by
  classical
  simp [Finsupp.degree_eq_sum, totalJetDegree_eq_sum, Fintype.sum_option]

/-- The specialization weight written out: `a + ∑_j (D - j) b_j`. -/
theorem weight_differentialWeight_eq (D : ℕ) (u : JetVariable d →₀ ℕ) :
    Finsupp.weight (differentialWeight D) u =
      u none + ∑ j : Fin (d + 1), (D - j.val) * u (some j) := by
  classical
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, Fintype.sum_option, differentialWeight,
    mul_comm]

/-- If `d < D`, the total jet degree times the gap `D - d` is at most the specialization weight,
since every jet variable has weight at least `D - d`. -/
theorem sub_mul_totalJetDegree_le_weight (hdD : d < D) (u : JetVariable d →₀ ℕ) :
    (D - d) * totalJetDegree u ≤ Finsupp.weight (differentialWeight D) u := by
  rw [weight_differentialWeight_eq, totalJetDegree_eq_sum, Finset.mul_sum]
  refine le_trans (Finset.sum_le_sum fun j _ => ?_) (Nat.le_add_left _ _)
  rw [mul_comm (D - d), mul_comm (D - j.val)]
  have hj : j.val ≤ d := Nat.le_of_lt_succ j.isLt
  exact Nat.mul_le_mul_left _ (by omega)

/-! ### Eligible exponents -/

/-- Eligibility of one exponent: at most `M` copies of `Y₁`, higher-jet weight at most `W`, and
specialization weight strictly below `m * A`. -/
def ExactInterpolationEligibleExponent (D A d m M W : ℕ) (u : JetVariable d →₀ ℕ) : Prop :=
  firstJetExponent u ≤ M ∧ fullHigherJetWeight u ≤ W ∧
    Finsupp.weight (differentialWeight D) u < m * A

/-- The set of eligible exponents. -/
def exactInterpolationExponentSet (D A d m M W : ℕ) : Set (JetVariable d →₀ ℕ) :=
  {u | ExactInterpolationEligibleExponent D A d m M W u}

/-- The floor `⌊(mA - 1)/(D - d)⌋`, which bounds the total jet degree of eligible exponents. -/
def exactInterpolationJetDegreeFloor (D A d m : ℕ) : ℕ :=
  (m * A - 1) / (D - d)

/-- If `d < D`, an exponent of specialization weight below `m * A` has total jet degree at most
`⌊(mA - 1)/(D - d)⌋`. -/
theorem totalJetDegree_le_floor_of_weight_lt (hdD : d < D) {u : JetVariable d →₀ ℕ}
    (hu : Finsupp.weight (differentialWeight D) u < m * A) :
    totalJetDegree u ≤ exactInterpolationJetDegreeFloor D A d m := by
  rw [exactInterpolationJetDegreeFloor, Nat.le_div_iff_mul_le (by omega), mul_comm]
  have := sub_mul_totalJetDegree_le_weight hdD u
  omega

/-- The `X` exponent of an eligible exponent is at most `mA - 1`, whatever `D` and `d` are. -/
theorem xExponent_le_pred_of_exact_eligible {u : JetVariable d →₀ ℕ}
    (hu : ExactInterpolationEligibleExponent D A d m M W u) :
    u none ≤ m * A - 1 := by
  have := hu.2.2
  rw [weight_differentialWeight_eq] at this
  omega

/-- If `d < D`, there are finitely many eligible exponents. The hypothesis is necessary: at
`D = d`, `Y_d` has weight zero, so every power of `Y_d` is eligible when `0 < m * A` and `Y_d`
is neither `Y₁` nor a higher jet of positive weight (for example when `d = 0`). -/
theorem exactInterpolationExponentSet_finite (hdD : d < D) :
    (exactInterpolationExponentSet D A d m M W).Finite := by
  refine (Finsupp.finite_of_degree_le
    ((m * A - 1) + exactInterpolationJetDegreeFloor D A d m)).subset fun u hu => ?_
  change u.degree ≤ _
  rw [degree_eq_add_totalJetDegree]
  exact Nat.add_le_add (xExponent_le_pred_of_exact_eligible hu)
    (totalJetDegree_le_floor_of_weight_lt hdD hu.2.2)

/-- The finite set of eligible exponents. It is specified through `Set.Finite.toFinset`, so it is
not an executable enumeration. -/
def exactInterpolationExponents (D A d m M W : ℕ) (hdD : d < D) :
    Finset (JetVariable d →₀ ℕ) :=
  (exactInterpolationExponentSet_finite (A := A) (m := m) (M := M) (W := W) hdD).toFinset

/-- Membership in `exactInterpolationExponents` is `ExactInterpolationEligibleExponent`. -/
@[simp]
theorem mem_exactInterpolationExponents {hdD : d < D} {u : JetVariable d →₀ ℕ} :
    u ∈ exactInterpolationExponents D A d m M W hdD ↔
      ExactInterpolationEligibleExponent D A d m M W u := by
  simp [exactInterpolationExponents, exactInterpolationExponentSet]

/-- The canonical finite column type of the exact interpolation system. -/
abbrev ExactInterpolationIndex (D A d m M W : ℕ) (hdD : d < D) :=
  ↥(exactInterpolationExponents D A d m M W hdD)

/-! ### Space, basis, and coefficient coordinates -/

/-- Differential polynomials supported on eligible exponents. -/
def exactInterpolationSpace (R : Type*) [CommSemiring R] (D A d m M W : ℕ) (hdD : d < D) :
    Submodule R (DifferentialPolynomial R d) :=
  MvPolynomial.restrictSupport R
    (↑(exactInterpolationExponents D A d m M W hdD) : Set (JetVariable d →₀ ℕ))

/-- Membership in the exact space is eligibility of every support exponent. -/
theorem mem_exactInterpolationSpace_iff [CommSemiring R] {hdD : d < D}
    {Q : DifferentialPolynomial R d} :
    Q ∈ exactInterpolationSpace R D A d m M W hdD ↔
      ∀ u ∈ Q.support, ExactInterpolationEligibleExponent D A d m M W u := by
  rw [exactInterpolationSpace, MvPolynomial.mem_restrictSupport_iff]
  simp only [Set.subset_def, Finset.mem_coe, mem_exactInterpolationExponents]

/-- A monomial lies in the exact space exactly when its exponent is eligible, unless its
coefficient is zero. -/
@[simp]
theorem monomial_mem_exactInterpolationSpace [CommSemiring R] {hdD : d < D}
    {u : JetVariable d →₀ ℕ} {a : R} :
    MvPolynomial.monomial u a ∈ exactInterpolationSpace R D A d m M W hdD ↔
      ExactInterpolationEligibleExponent D A d m M W u ∨ a = 0 := by
  simp [exactInterpolationSpace]

/-- The monomial basis of the exact interpolation space. -/
def exactInterpolationSpaceBasis (R : Type*) [CommSemiring R] (D A d m M W : ℕ) (hdD : d < D) :
    Module.Basis (ExactInterpolationIndex D A d m M W hdD) R
      (exactInterpolationSpace R D A d m M W hdD) :=
  MvPolynomial.basisRestrictSupport (R := R)
    (↑(exactInterpolationExponents D A d m M W hdD) : Set (JetVariable d →₀ ℕ))

/-- The exact interpolation space is a finite module, since its monomial basis is finite. -/
instance exactInterpolationSpace.finite [CommSemiring R] (hdD : d < D) :
    Module.Finite R (exactInterpolationSpace R D A d m M W hdD) :=
  Module.Finite.of_basis (exactInterpolationSpaceBasis R D A d m M W hdD)

/-- Finitely supported coefficient vectors indexed by the interpolation columns. -/
abbrev ExactInterpolationCoefficients (R : Type*) [Zero R] (D A d m M W : ℕ) (hdD : d < D) :=
  ExactInterpolationIndex D A d m M W hdD →₀ R

/-- Coordinates of an exact interpolation polynomial in the monomial basis. -/
def exactInterpolationRepr [CommSemiring R] (hdD : d < D) :
    exactInterpolationSpace R D A d m M W hdD ≃ₗ[R]
      ExactInterpolationCoefficients R D A d m M W hdD :=
  (exactInterpolationSpaceBasis R D A d m M W hdD).repr

/-- The exact interpolation polynomial with prescribed coefficients. -/
def exactInterpolationPolynomial [CommSemiring R] (hdD : d < D) :
    ExactInterpolationCoefficients R D A d m M W hdD ≃ₗ[R]
      exactInterpolationSpace R D A d m M W hdD :=
  (exactInterpolationRepr hdD).symm

/-- Basis coordinates are ordinary coefficients. -/
@[simp]
theorem exactInterpolationRepr_apply [CommSemiring R] (hdD : d < D)
    (Q : exactInterpolationSpace R D A d m M W hdD)
    (u : ExactInterpolationIndex D A d m M W hdD) :
    exactInterpolationRepr hdD Q u = Q.1.coeff u.1 :=
  rfl

/-- A single coefficient reconstructs the corresponding monomial. -/
@[simp]
theorem exactInterpolationPolynomial_single [CommSemiring R] (hdD : d < D)
    (u : ExactInterpolationIndex D A d m M W hdD) (a : R) :
    (exactInterpolationPolynomial hdD (Finsupp.single u a) : DifferentialPolynomial R d) =
      MvPolynomial.monomial u.1 a := by
  change AddMonoidAlgebra.ofCoeff
      (↑((Finsupp.supportedEquivFinsupp
        (↑(exactInterpolationExponents D A d m M W hdD) :
          Set (JetVariable d →₀ ℕ))).symm (Finsupp.single u a))) =
    MvPolynomial.monomial u.1 a
  rw [Finsupp.supportedEquivFinsupp_symm_single]
  rfl

/-- A linear map on differential polynomials, read on coefficient columns: the image of a
coefficient vector is the image of the polynomial it defines. -/
def exactInterpolationCoefficientEvaluator [CommSemiring R] [AddCommMonoid V] [Module R V]
    (hdD : d < D) (eval : DifferentialPolynomial R d →ₗ[R] V) :
    ExactInterpolationCoefficients R D A d m M W hdD →ₗ[R] V :=
  (eval.domRestrict (exactInterpolationSpace R D A d m M W hdD)).comp
    (exactInterpolationPolynomial hdD).toLinearMap

/-- A single column evaluates to the image of its monomial. -/
@[simp]
theorem exactInterpolationCoefficientEvaluator_single [CommSemiring R] [AddCommMonoid V]
    [Module R V] (hdD : d < D) (eval : DifferentialPolynomial R d →ₗ[R] V)
    (u : ExactInterpolationIndex D A d m M W hdD) (a : R) :
    exactInterpolationCoefficientEvaluator hdD eval (Finsupp.single u a) =
      eval (MvPolynomial.monomial u.1 a) := by
  simp [exactInterpolationCoefficientEvaluator]

/-! ### Degree bounds -/

/-- Every member of the exact space has specialization-weighted degree below `m * A`. The
hypothesis `0 < m * A` is needed for the zero polynomial, whose weighted degree is `0`. -/
theorem differentialWeightedDegree_lt_of_mem_exactInterpolationSpace [CommSemiring R]
    (hbudget : 0 < m * A) (hdD : d < D) {Q : DifferentialPolynomial R d}
    (hQ : Q ∈ exactInterpolationSpace R D A d m M W hdD) :
    differentialWeightedDegree D Q < m * A := by
  rw [differentialWeightedDegree, MvPolynomial.weightedTotalDegree, Finset.sup_lt_iff hbudget]
  exact fun u hu => (mem_exactInterpolationSpace_iff.mp hQ u hu).2.2

/-- Every member of the exact space has total jet degree at most `⌊(mA - 1)/(D - d)⌋`. -/
theorem jetTotalDegree_le_floor_of_mem_exactInterpolationSpace [CommSemiring R] (hdD : d < D)
    {Q : DifferentialPolynomial R d} (hQ : Q ∈ exactInterpolationSpace R D A d m M W hdD) :
    jetTotalDegree Q ≤ exactInterpolationJetDegreeFloor D A d m :=
  (jetTotalDegree_le_iff Q _).mpr fun u hu =>
    totalJetDegree_le_floor_of_weight_lt hdD (mem_exactInterpolationSpace_iff.mp hQ u hu).2.2

/-- Every individual jet degree of a member of the exact space is at most
`⌊(mA - 1)/(D - d)⌋`. -/
theorem jetDegree_le_floor_of_mem_exactInterpolationSpace [CommSemiring R] (hdD : d < D)
    {Q : DifferentialPolynomial R d} (hQ : Q ∈ exactInterpolationSpace R D A d m M W hdD)
    (j : Fin (d + 1)) :
    jetDegree Q j ≤ exactInterpolationJetDegreeFloor D A d m :=
  (jetDegree_le_total Q j).trans (jetTotalDegree_le_floor_of_mem_exactInterpolationSpace hdD hQ)

/-- The dimension of the exact space over a field is the number of eligible exponents. -/
theorem finrank_exactInterpolationSpace_eq_card [Field R] (hdD : d < D) :
    Module.finrank R (exactInterpolationSpace R D A d m M W hdD) =
      (exactInterpolationExponents D A d m M W hdD).card := by
  rw [Module.finrank_eq_card_basis (exactInterpolationSpaceBasis R D A d m M W hdD)]
  exact Fintype.card_coe _

end

end ReedSolomon.HiddenDerivative
