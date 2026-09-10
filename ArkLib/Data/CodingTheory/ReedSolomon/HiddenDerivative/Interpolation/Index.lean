/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Differential.Basic
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Space


/-!
# Exact finite indices for hidden-derivative interpolation

This file packages the cap-free interpolation space used by the all-rate analysis.  For ambient
degree `D`, agreement threshold `A`, derivative order `d`, multiplicity `m`, first-jet cap `M`,
and higher-jet budget `W`, its monomials satisfy

```text
b₁ ≤ M,
sum_{j=2}^d (j - 1)b_j ≤ W,
a + D b₀ + (D - 1)b₁ + ... + (D - d)b_d < m A.
```

The last expression is `exactInterpolationMonomialWeight`.  The strict boundary `d < D` is
load-bearing: it makes every jet weight positive and hence makes the space finite without an
extra total-jet-degree cap.  At `D = d`, arbitrary powers of `Y_d` have weight zero.

The module exposes both a canonical monomial basis and its finitely supported coefficient space.
This is the coordinate API consumed by the local constraint map and by nonzero-kernel extraction.
It is deliberately separate from the older support-first rectangular space in
`InterpolationSpace.lean`; that space is retained for the coarse finite-cover route.

## References

* [Brakensiek, Chen, Putterman, Zhang, and Zheng, *Algorithmic List Decoding of Reed--Solomon
  Codes up to Capacity in the Low-Rate Regime*][BCPZZ26], ECCC TR26-164.
* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding and Mutual Correlated Agreement
  up to Capacity*][DKTZ26], Section 3 (local interpolation).
-/

@[expose] public section

open PolynomialDifferential


namespace ReedSolomon
namespace HiddenDerivative

noncomputable section

open scoped BigOperators

variable {F V : Type*} {d D A m M W K B C : ℕ}

/-! ### Coordinates for the landed support-first space -/

/-- Canonical finite column type for the landed support-first interpolation space.  Its
finiteness comes from the complete `GlobalEligibleExponent` predicate, including the separate
total-jet cap `B`; it does not come from the high-jet weight alone. -/
abbrev InterpolationIndex (d m A K B W C : ℕ) :=
  ↥(globalEligibleExponents d m A K B W C)

/-- Finitely supported canonical coefficients for the landed support-first space. -/
abbrev InterpolationCoefficients (F : Type*) [Zero F] (d m A K B W C : ℕ) :=
  InterpolationIndex d m A K B W C →₀ F

/-- Canonical monomial coordinates of a support-first interpolation polynomial. -/
def interpolationRepr [CommSemiring F] :
    interpolationSpace F d m A K B W C ≃ₗ[F]
      InterpolationCoefficients F d m A K B W C :=
  (interpolationSpaceBasis F d m A K B W C).repr

/-- Reconstruct a support-first interpolation polynomial from canonical coefficients. -/
def interpolationPolynomial [CommSemiring F] :
    InterpolationCoefficients F d m A K B W C ≃ₗ[F]
      interpolationSpace F d m A K B W C :=
  (interpolationRepr (F := F) (d := d) (m := m) (A := A) (K := K) (B := B)
    (W := W) (C := C)).symm

/-- Coordinates in the support-first basis are ordinary multivariate coefficients. -/
@[simp]
theorem interpolationRepr_apply [CommSemiring F]
    (Q : interpolationSpace F d m A K B W C)
    (u : InterpolationIndex d m A K B W C) :
    interpolationRepr Q u = MvPolynomial.coeff u.1 Q.1 :=
  rfl

/-- A singleton support-first coefficient vector reconstructs its indexed monomial. -/
@[simp]
theorem interpolationPolynomial_single [CommSemiring F]
    (u : InterpolationIndex d m A K B W C) (a : F) :
    (interpolationPolynomial (F := F) (d := d) (m := m) (A := A) (K := K) (B := B)
      (W := W) (C := C) (Finsupp.single u a) : DifferentialPolynomial F d) =
      MvPolynomial.monomial u.1 a := by
  change AddMonoidAlgebra.ofCoeff
      (↑((Finsupp.supportedEquivFinsupp
        (↑(globalEligibleExponents d m A K B W C) : Set (JetVariable d →₀ ℕ))).symm
          (Finsupp.single u a))) = MvPolynomial.monomial u.1 a
  rw [Finsupp.supportedEquivFinsupp_symm_single]
  rfl

/-- Coefficient projection at one support-first interpolation column. -/
def interpolationCoeff [CommSemiring F]
    (u : InterpolationIndex d m A K B W C) :
    interpolationSpace F d m A K B W C →ₗ[F] F :=
  MvPolynomial.lcoeff F u.1 ∘ₗ Submodule.subtype _

@[simp]
theorem interpolationCoeff_apply [CommSemiring F]
    (u : InterpolationIndex d m A K B W C)
    (Q : interpolationSpace F d m A K B W C) :
    interpolationCoeff u Q = MvPolynomial.coeff u.1 Q.1 :=
  rfl

/-- Lift a linear evaluator to the support-first coefficient columns. -/
def interpolationCoefficientEvaluator [CommSemiring F] [AddCommMonoid V] [Module F V]
    (eval : DifferentialPolynomial F d →ₗ[F] V) :
    InterpolationCoefficients F d m A K B W C →ₗ[F] V :=
  (eval.domRestrict (interpolationSpace F d m A K B W C)).comp
    (interpolationPolynomial (F := F) (d := d) (m := m) (A := A) (K := K) (B := B)
      (W := W) (C := C)).toLinearMap

/-- Evaluating a singleton support-first column agrees with evaluating its monomial. -/
@[simp]
theorem interpolationCoefficientEvaluator_single [CommSemiring F]
    [AddCommMonoid V] [Module F V]
    (eval : DifferentialPolynomial F d →ₗ[F] V)
    (u : InterpolationIndex d m A K B W C) (a : F) :
    interpolationCoefficientEvaluator (m := m) (A := A) (K := K) (B := B) (W := W)
      (C := C) eval (Finsupp.single u a) = eval (MvPolynomial.monomial u.1 a) := by
  simp [interpolationCoefficientEvaluator]

/-! ### Exact support predicate -/

/-- The exact `(1,D,D-1,...,D-d)` weight of one differential monomial. -/
def exactInterpolationMonomialWeight (D : ℕ) (u : JetVariable d →₀ ℕ) : ℕ :=
  Finsupp.weight (differentialWeight D) u

/-- Expanded paper formula for the exact interpolation weight. -/
theorem exactInterpolationMonomialWeight_eq (D : ℕ) (u : JetVariable d →₀ ℕ) :
    exactInterpolationMonomialWeight D u =
      u none + Finsupp.weight (fun j : Fin (d + 1) ↦ D - j.val) u.some := by
  classical
  simp [exactInterpolationMonomialWeight, Finsupp.weight_apply,
    Finsupp.sum_fintype, Fintype.sum_option, differentialWeight, mul_comm]

/-- The exact weight is bounded by the coarse interpolation weight, which charges every
jet variable by `D`. -/
theorem exactInterpolationMonomialWeight_le_coarse (D : ℕ)
    (u : JetVariable d →₀ ℕ) :
    exactInterpolationMonomialWeight D u ≤ u none + D * totalJetDegree u := by
  rw [exactInterpolationMonomialWeight_eq]
  apply Nat.add_le_add_left
  rw [totalJetDegree, Finsupp.degree_eq_sum, Finset.mul_sum,
    Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  apply Finset.sum_le_sum
  intro j hj
  simp only [nsmul_eq_mul]
  simpa [mul_comm] using Nat.mul_le_mul_left (u.some j) (Nat.sub_le D j.val)

/-- Cap-free eligibility from the exact certificate: a cap on `Y₁`, the anisotropic high-jet
budget, and the strict paper weighted-degree inequality. -/
def ExactInterpolationEligibleExponent (D A d m M W : ℕ)
    (u : JetVariable d →₀ ℕ) : Prop :=
  firstJetExponent u ≤ M ∧
    fullHigherJetWeight u ≤ W ∧
    exactInterpolationMonomialWeight D u < m * A

/-- The underlying set of exact eligible exponents. -/
def exactInterpolationExponentSet (D A d m M W : ℕ) : Set (JetVariable d →₀ ℕ) :=
  {u | ExactInterpolationEligibleExponent D A d m M W u}

/-- Exact integer floor `floor((mA-1)/(D-d))` controlling total jet degree. -/
def exactInterpolationJetDegreeFloor (D A d m : ℕ) : ℕ :=
  (m * A - 1) / (D - d)

/-- A strict natural weighted-degree inequality implies a weak inequality against the
predecessor. -/
theorem exactInterpolationMonomialWeight_le_pred_of_lt {u : JetVariable d →₀ ℕ}
    (hu : exactInterpolationMonomialWeight D u < m * A) :
    exactInterpolationMonomialWeight D u ≤ m * A - 1 := by
  omega

/-- For a positive budget, the strict inequality is exactly the predecessor weak inequality.
This is the integer rounding behind the paper's `mA - 1` formulas. -/
theorem exactInterpolationMonomialWeight_lt_iff_le_pred (hbudget : 0 < m * A)
    {u : JetVariable d →₀ ℕ} :
    exactInterpolationMonomialWeight D u < m * A ↔
      exactInterpolationMonomialWeight D u ≤ m * A - 1 := by
  omega

/-- Every jet variable has weight at least `D-d` when `d < D`. -/
theorem differentialWeight_some_ge_gap (hdD : d < D) (j : Fin (d + 1)) :
    D - d ≤ differentialWeight D (some j) := by
  rw [differentialWeight_some]
  have hj : j.val ≤ d := Nat.le_of_lt_succ j.isLt
  omega

/-- The minimum jet weight times total jet degree is at most the exact monomial weight. -/
theorem gap_mul_totalJetDegree_le_exactInterpolationMonomialWeight
    (hdD : d < D) (u : JetVariable d →₀ ℕ) :
    (D - d) * totalJetDegree u ≤ exactInterpolationMonomialWeight D u := by
  rw [exactInterpolationMonomialWeight_eq]
  apply le_trans ?_ (Nat.le_add_left _ _)
  rw [totalJetDegree, Finsupp.degree_eq_sum, Finset.mul_sum,
    Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  apply Finset.sum_le_sum
  intro j hj
  simp only [nsmul_eq_mul]
  simpa [mul_comm] using
    Nat.mul_le_mul_left (u.some j) (differentialWeight_some_ge_gap hdD j)

/-- Exact floor bound on the total jet degree.  Natural-number division is the floor of
`(mA-1)/(D-d)`; the positive denominator follows precisely from `d < D`. -/
theorem totalJetDegree_le_floor_of_exact_weight_lt (hdD : d < D)
    {u : JetVariable d →₀ ℕ} (hu : exactInterpolationMonomialWeight D u < m * A) :
    totalJetDegree u ≤ exactInterpolationJetDegreeFloor D A d m := by
  rw [exactInterpolationJetDegreeFloor]
  apply (Nat.le_div_iff_mul_le (by omega : 0 < D - d)).2
  calc
    totalJetDegree u * (D - d) = (D - d) * totalJetDegree u := Nat.mul_comm _ _
    _ ≤ exactInterpolationMonomialWeight D u :=
      gap_mul_totalJetDegree_le_exactInterpolationMonomialWeight hdD u
    _ ≤ m * A - 1 := exactInterpolationMonomialWeight_le_pred_of_lt hu

/-- Exact floor bound on total jet degree for every eligible exponent. -/
theorem totalJetDegree_le_floor_of_exact_eligible (hdD : d < D)
    {u : JetVariable d →₀ ℕ} (hu : ExactInterpolationEligibleExponent D A d m M W u) :
    totalJetDegree u ≤ exactInterpolationJetDegreeFloor D A d m :=
  totalJetDegree_le_floor_of_exact_weight_lt hdD hu.2.2

/-- The exponent of `X` is at most `mA-1` for every eligible exponent. -/
theorem xExponent_le_pred_of_exact_eligible
    {u : JetVariable d →₀ ℕ} (hu : ExactInterpolationEligibleExponent D A d m M W u) :
    u none ≤ m * A - 1 := by
  apply le_trans ?_ (exactInterpolationMonomialWeight_le_pred_of_lt hu.2.2)
  rw [exactInterpolationMonomialWeight_eq]
  exact Nat.le_add_right _ _

/-- The cap-free support is finite under the explicit paper boundary `d < D`.

This proof uses the exact derived floor cap.  It never invokes the positive-weight finrank theorem
with a weight that vanishes on `X`, `Y₀`, or `Y₁`. -/
theorem exactInterpolationExponentSet_finite (hdD : d < D) :
    (exactInterpolationExponentSet D A d m M W).Finite := by
  apply (Finsupp.finite_of_degree_le
    ((m * A - 1) + exactInterpolationJetDegreeFloor D A d m)).subset
  intro u hu
  change Finsupp.degree u ≤ (m * A - 1) + exactInterpolationJetDegreeFloor D A d m
  rw [exponentDegree_eq_x_add_totalJetDegree]
  exact Nat.add_le_add (xExponent_le_pred_of_exact_eligible hu)
    (totalJetDegree_le_floor_of_exact_eligible hdD hu)

/-- Finite set of exact cap-free interpolation exponents.  The proof argument records the
load-bearing boundary `d < D` in every downstream index type.

This `Set.Finite.toFinset` construction specifies the finite index set noncomputably;
it does not assert an executable enumeration. -/
def exactInterpolationExponents (D A d m M W : ℕ) (hdD : d < D) :
    Finset (JetVariable d →₀ ℕ) :=
  (exactInterpolationExponentSet_finite (D := D) (A := A) (m := m) (M := M) (W := W)
    hdD).toFinset

@[simp]
theorem mem_exactInterpolationExponents {hdD : d < D} {u : JetVariable d →₀ ℕ} :
    u ∈ exactInterpolationExponents D A d m M W hdD ↔
      ExactInterpolationEligibleExponent D A d m M W u := by
  simp [exactInterpolationExponents, exactInterpolationExponentSet]

/-- Every exponent from the landed source's coarse support belongs to the exact cap-free support.
The ambient dimension is written `D+1`, so its coarse jet weight is exactly `D`. -/
theorem GlobalEligibleExponent.toExactInterpolationEligibleExponent
    {B C : ℕ} {u : JetVariable d →₀ ℕ}
    (hu : GlobalEligibleExponent d m A (D + 1) B W C u) :
    ExactInterpolationEligibleExponent D A d m m W u := by
  refine ⟨hu.1, hu.2.2.2.1, ?_⟩
  exact (exactInterpolationMonomialWeight_le_coarse D u).trans_lt (by simpa using hu.2.2.1)

/-- Canonical finite column type of the exact interpolation system. -/
abbrev ExactInterpolationIndex (D A d m M W : ℕ) (hdD : d < D) :=
  ↥(exactInterpolationExponents D A d m M W hdD)

/-! ### Space, basis, and coefficient coordinates -/

/-- Differential polynomials supported on the exact cap-free interpolation band. -/
def exactInterpolationSpace (F : Type*) [CommSemiring F]
    (D A d m M W : ℕ) (hdD : d < D) :
    Submodule F (DifferentialPolynomial F d) :=
  MvPolynomial.restrictSupport F
    (↑(exactInterpolationExponents D A d m M W hdD) : Set (JetVariable d →₀ ℕ))

/-- Membership in the exact space is pointwise cap-free eligibility of the support. -/
theorem mem_exactInterpolationSpace_iff [CommSemiring F] {hdD : d < D}
    {Q : DifferentialPolynomial F d} :
    Q ∈ exactInterpolationSpace F D A d m M W hdD ↔
      ∀ u ∈ Q.support, ExactInterpolationEligibleExponent D A d m M W u := by
  rw [exactInterpolationSpace, MvPolynomial.mem_restrictSupport_iff]
  simp only [Set.subset_def, Finset.mem_coe, mem_exactInterpolationExponents]

/-- The source's coarse support-first space embeds in the exact cap-free space.  This adapter lets
the already-landed rectangular lower bound feed the exact paper interface without identifying the
two spaces. -/
theorem interpolationSpace_le_exactInterpolationSpace [CommSemiring F]
    {B C : ℕ} (hdD : d < D) :
    interpolationSpace F d m A (D + 1) B W C ≤
      exactInterpolationSpace F D A d m m W hdD := by
  intro Q hQ
  rw [mem_exactInterpolationSpace_iff]
  intro u hu
  exact (mem_interpolationSpace_iff.mp hQ u hu).toExactInterpolationEligibleExponent

/-- A monomial is in the exact space precisely when its exponent is eligible, unless its
coefficient is zero. -/
@[simp]
theorem monomial_mem_exactInterpolationSpace [CommSemiring F] {hdD : d < D}
    {u : JetVariable d →₀ ℕ} {a : F} :
    MvPolynomial.monomial u a ∈ exactInterpolationSpace F D A d m M W hdD ↔
      ExactInterpolationEligibleExponent D A d m M W u ∨ a = 0 := by
  simp [exactInterpolationSpace]

/-- Canonical monomial basis of the exact interpolation space. -/
def exactInterpolationSpaceBasis (F : Type*) [CommSemiring F]
    (D A d m M W : ℕ) (hdD : d < D) :=
  MvPolynomial.basisRestrictSupport (R := F)
    (↑(exactInterpolationExponents D A d m M W hdD) : Set (JetVariable d →₀ ℕ))

/-- Finitely supported coefficient vectors in the canonical interpolation columns. -/
abbrev ExactInterpolationCoefficients (F : Type*) [Zero F]
    (D A d m M W : ℕ) (hdD : d < D) :=
  ExactInterpolationIndex D A d m M W hdD →₀ F

/-- Canonical coordinates of an exact interpolation polynomial. -/
def exactInterpolationRepr [CommSemiring F] (hdD : d < D) :
    exactInterpolationSpace F D A d m M W hdD ≃ₗ[F]
      ExactInterpolationCoefficients F D A d m M W hdD :=
  (exactInterpolationSpaceBasis F D A d m M W hdD).repr

/-- Reconstruct an exact interpolation polynomial from its finite coefficient vector. -/
def exactInterpolationPolynomial [CommSemiring F] (hdD : d < D) :
    ExactInterpolationCoefficients F D A d m M W hdD ≃ₗ[F]
      exactInterpolationSpace F D A d m M W hdD :=
  (exactInterpolationRepr (F := F) (D := D) (A := A) (d := d) (m := m) (M := M)
    (W := W) hdD).symm

/-- Basis coordinates are the ordinary multivariate coefficients. -/
@[simp]
theorem exactInterpolationRepr_apply [CommSemiring F] (hdD : d < D)
    (Q : exactInterpolationSpace F D A d m M W hdD)
    (u : ExactInterpolationIndex D A d m M W hdD) :
    exactInterpolationRepr hdD Q u = MvPolynomial.coeff u.1 Q.1 :=
  rfl

/-- A singleton coefficient vector reconstructs the corresponding monomial. -/
@[simp]
theorem exactInterpolationPolynomial_single [CommSemiring F] (hdD : d < D)
    (u : ExactInterpolationIndex D A d m M W hdD) (a : F) :
    (exactInterpolationPolynomial hdD (Finsupp.single u a) : DifferentialPolynomial F d) =
      MvPolynomial.monomial u.1 a := by
  change AddMonoidAlgebra.ofCoeff
      (↑((Finsupp.supportedEquivFinsupp
        (↑(exactInterpolationExponents D A d m M W hdD) :
          Set (JetVariable d →₀ ℕ))).symm (Finsupp.single u a))) =
    MvPolynomial.monomial u.1 a
  rw [Finsupp.supportedEquivFinsupp_symm_single]
  rfl

/-- Coefficient projection at one canonical interpolation column. -/
def exactInterpolationCoeff [CommSemiring F] (hdD : d < D)
    (u : ExactInterpolationIndex D A d m M W hdD) :
    exactInterpolationSpace F D A d m M W hdD →ₗ[F] F :=
  MvPolynomial.lcoeff F u.1 ∘ₗ Submodule.subtype _

@[simp]
theorem exactInterpolationCoeff_apply [CommSemiring F] (hdD : d < D)
    (u : ExactInterpolationIndex D A d m M W hdD)
    (Q : exactInterpolationSpace F D A d m M W hdD) :
    exactInterpolationCoeff hdD u Q = MvPolynomial.coeff u.1 Q.1 :=
  rfl

/-- Lift a linear evaluator on differential polynomials to canonical finite coefficient
coordinates.  This is the matrix-column interface used by local constraints. -/
def exactInterpolationCoefficientEvaluator [CommSemiring F] [AddCommMonoid V] [Module F V]
    (hdD : d < D) (eval : DifferentialPolynomial F d →ₗ[F] V) :
    ExactInterpolationCoefficients F D A d m M W hdD →ₗ[F] V :=
  (eval.domRestrict (exactInterpolationSpace F D A d m M W hdD)).comp
    (exactInterpolationPolynomial hdD).toLinearMap

/-- Evaluating a singleton column agrees with evaluating its paper monomial. -/
@[simp]
theorem exactInterpolationCoefficientEvaluator_single [CommSemiring F]
    [AddCommMonoid V] [Module F V] (hdD : d < D)
    (eval : DifferentialPolynomial F d →ₗ[F] V)
    (u : ExactInterpolationIndex D A d m M W hdD) (a : F) :
    exactInterpolationCoefficientEvaluator hdD eval (Finsupp.single u a) =
      eval (MvPolynomial.monomial u.1 a) := by
  simp [exactInterpolationCoefficientEvaluator]

/-! ### Exact paper degree consequences -/

/-- Every polynomial in the exact interpolation space has strict paper weighted degree `< mA`.
The positivity hypothesis handles the zero polynomial under a strict natural bound. -/
theorem differentialWeightedDegree_lt_of_mem_exactInterpolationSpace [CommSemiring F]
    (hbudget : 0 < m * A) (hdD : d < D) {Q : DifferentialPolynomial F d}
    (hQ : Q ∈ exactInterpolationSpace F D A d m M W hdD) :
    differentialWeightedDegree D Q < m * A := by
  rw [differentialWeightedDegree, MvPolynomial.weightedTotalDegree,
    Finset.sup_lt_iff hbudget]
  intro u hu
  exact (mem_exactInterpolationSpace_iff.mp hQ u hu).2.2

/-- Every support monomial has the exact floor bound on total jet degree. -/
theorem support_totalJetDegree_le_floor_of_mem_exactInterpolationSpace [CommSemiring F]
    (hdD : d < D) {Q : DifferentialPolynomial F d}
    (hQ : Q ∈ exactInterpolationSpace F D A d m M W hdD)
    {u : JetVariable d →₀ ℕ} (hu : u ∈ Q.support) :
    totalJetDegree u ≤ exactInterpolationJetDegreeFloor D A d m :=
  totalJetDegree_le_floor_of_exact_eligible hdD
    (mem_exactInterpolationSpace_iff.mp hQ u hu)

/-- Every individual jet degree is bounded by the same exact floor. -/
theorem degreeOf_jet_le_floor_of_mem_exactInterpolationSpace [CommSemiring F]
    (hdD : d < D) {Q : DifferentialPolynomial F d}
    (hQ : Q ∈ exactInterpolationSpace F D A d m M W hdD)
    (j : Fin (d + 1)) :
    Q.degreeOf (some j) ≤ exactInterpolationJetDegreeFloor D A d m := by
  rw [MvPolynomial.degreeOf_le_iff]
  intro u hu
  exact (Finsupp.le_degree j u.some).trans
    (support_totalJetDegree_le_floor_of_mem_exactInterpolationSpace hdD hQ hu)

/-- Finrank is exactly the number of canonical finite interpolation columns. -/
theorem finrank_exactInterpolationSpace_eq_card [Field F] (hdD : d < D) :
    Module.finrank F (exactInterpolationSpace F D A d m M W hdD) =
      (exactInterpolationExponents D A d m M W hdD).card := by
  let b : Module.Basis
      (↑(exactInterpolationExponents D A d m M W hdD) : Set (JetVariable d →₀ ℕ))
      F (exactInterpolationSpace F D A d m M W hdD) :=
    exactInterpolationSpaceBasis F D A d m M W hdD
  rw [Module.finrank_eq_card_basis b]
  exact Fintype.card_coe _

/-- Finrank monotonicity across the source-to-exact support embedding.  This is the precise part of
I0 already discharged by the landed F4 rectangular dimension argument. -/
theorem finrank_interpolationSpace_le_exactInterpolationSpace [Field F]
    {B C : ℕ} (hdD : d < D) :
    Module.finrank F (interpolationSpace F d m A (D + 1) B W C) ≤
      Module.finrank F (exactInterpolationSpace F D A d m m W hdD) := by
  let b := exactInterpolationSpaceBasis F D A d m m W hdD
  let _ : Module.Finite F (exactInterpolationSpace F D A d m m W hdD) :=
    Module.Finite.of_basis b
  exact Submodule.finrank_mono (interpolationSpace_le_exactInterpolationSpace hdD)

end
end HiddenDerivative
end ReedSolomon
