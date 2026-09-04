/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters
import ArkLib.Data.MvPolynomial.WeightedDegree

/-!
# Variables and weights for hidden-derivative interpolation

This file names the variables used by the hidden-derivative interpolation construction and packages
its three weight functions:

* `interpolationWeight` assigns weights `(1, K - 1, ..., K - d - 1)` to
  `(X, Y₀, ..., Y_d)`.
* `highDerivativeWeight` records `omega(c) = sum_{j = 2}^d (j - 1) * c_j` on the interpolation
  variables.
* `localMultiplicityWeight` records the local quantity `i + d * b` on monomials containing
  `T ^ i * E ^ b`.

The support spaces use `MvPolynomial.restrictWeightedDegree`, so their caps are inclusive. In
particular, a source condition written as weighted degree strictly less than `C` should use cap
`C - 1` after establishing `0 < C`. This file leaves those strict-bound side conditions to the
interpolation layer rather than silently mishandling `C = 0`.

## References

* [Brakensiek, Chen, Putterman, Zhang, Zheng, *Algorithmic List Decoding of Reed--Solomon Codes up
  to Capacity in the Low-Rate Regime*][BCPZZ26], Section 3.
-/

noncomputable section

namespace ReedSolomon.HiddenDerivative

variable {derivOrder : ℕ}

/-- Variables of a hidden-derivative interpolant: the evaluation variable `X` and jet variables
`Y₀, ..., Y_d`. -/
inductive InterpolationVar (derivOrder : ℕ)
  | X
  | Y (order : Fin (derivOrder + 1))
  deriving DecidableEq, Repr

private def interpolationVarEquivOption :
    InterpolationVar derivOrder ≃ Option (Fin (derivOrder + 1)) where
  toFun
    | .X => none
    | .Y order => some order
  invFun
    | none => .X
    | some order => .Y order
  left_inv x := by cases x <;> rfl
  right_inv x := by cases x <;> rfl

instance : Fintype (InterpolationVar derivOrder) :=
  Fintype.ofEquiv (Option (Fin (derivOrder + 1))) interpolationVarEquivOption.symm

/-- Variables in the local constraint polynomial. `Yhi j` denotes `Y_(j+1)`, so its indices
enumerate `Y₁, ..., Y_d`. -/
inductive LocalVar (derivOrder : ℕ)
  | T
  | E
  | Yhi (order : Fin derivOrder)
  deriving DecidableEq, Repr

private def localVarEquivOption : LocalVar derivOrder ≃ Option (Option (Fin derivOrder)) where
  toFun
    | .T => none
    | .E => some none
    | .Yhi order => some (some order)
  invFun
    | none => .T
    | some none => .E
    | some (some order) => .Yhi order
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with _ | (_ | _) <;> rfl

instance : Fintype (LocalVar derivOrder) :=
  Fintype.ofEquiv (Option (Option (Fin derivOrder))) localVarEquivOption.symm

/-- The specialization weights `(1, K - 1, ..., K - d - 1)` on `X, Y₀, ..., Y_d`.
Natural-number subtraction is intentional: the highest derivative has weight zero at
`d = K - 1`. -/
def interpolationWeight (designDim : ℕ) : InterpolationVar derivOrder → ℕ
  | .X => 1
  | .Y order => designDim - (order + 1)

@[simp]
theorem interpolationWeight_X (designDim : ℕ) :
    interpolationWeight (derivOrder := derivOrder) designDim .X = 1 :=
  rfl

@[simp]
theorem interpolationWeight_Y (designDim : ℕ) (order : Fin (derivOrder + 1)) :
    interpolationWeight designDim (.Y order) = designDim - (order + 1) :=
  rfl

/-- The high-derivative weight `omega`: `X`, `Y₀`, and `Y₁` have weight zero, while `Y_j` has
weight `j - 1` for `j ≥ 2`. -/
def highDerivativeWeight : InterpolationVar derivOrder → ℕ
  | .X => 0
  | .Y order => order - 1

@[simp]
theorem highDerivativeWeight_X : highDerivativeWeight (.X : InterpolationVar derivOrder) = 0 :=
  rfl

@[simp]
theorem highDerivativeWeight_Y (order : Fin (derivOrder + 1)) :
    highDerivativeWeight (.Y order) = order - 1 :=
  rfl

/-- The local divisibility weight from the constraint `i + d * b < m`: `T` has weight one,
`E` has weight `d`, and derivative variables have weight zero. -/
def localMultiplicityWeight (derivOrder : ℕ) : LocalVar derivOrder → ℕ
  | .T => 1
  | .E => derivOrder
  | .Yhi _ => 0

@[simp]
theorem localMultiplicityWeight_T :
    localMultiplicityWeight derivOrder (.T : LocalVar derivOrder) = 1 :=
  rfl

@[simp]
theorem localMultiplicityWeight_E :
    localMultiplicityWeight derivOrder (.E : LocalVar derivOrder) = derivOrder :=
  rfl

@[simp]
theorem localMultiplicityWeight_Yhi (order : Fin derivOrder) :
    localMultiplicityWeight derivOrder (.Yhi order) = 0 :=
  rfl

/-- The local form of the high-derivative weight: `T`, `E`, and `Y₁` have weight zero, while
`Y_(j+1)` has weight `j`. -/
def localDerivativeWeight : LocalVar derivOrder → ℕ
  | .T => 0
  | .E => 0
  | .Yhi order => order

@[simp]
theorem localDerivativeWeight_T : localDerivativeWeight (.T : LocalVar derivOrder) = 0 :=
  rfl

@[simp]
theorem localDerivativeWeight_E : localDerivativeWeight (.E : LocalVar derivOrder) = 0 :=
  rfl

@[simp]
theorem localDerivativeWeight_Yhi (order : Fin derivOrder) :
    localDerivativeWeight (.Yhi order) = order :=
  rfl

/-- Polynomials in the named interpolation variables. -/
abbrev InterpolationPolynomial (derivOrder : ℕ) (R : Type*) [CommSemiring R] :=
  MvPolynomial (InterpolationVar derivOrder) R

/-- Polynomials in the named local variables. -/
abbrev LocalPolynomial (derivOrder : ℕ) (R : Type*) [CommSemiring R] :=
  MvPolynomial (LocalVar derivOrder) R

/-- Interpolation polynomials with an inclusive specialization-weight cap. -/
def interpolationWeightedSupport (R : Type*) [CommSemiring R]
    (derivOrder designDim degreeCap : ℕ) : Submodule R (InterpolationPolynomial derivOrder R) :=
  MvPolynomial.restrictWeightedDegree (interpolationWeight designDim) degreeCap

/-- Interpolation polynomials with an inclusive high-derivative-weight cap. -/
def highDerivativeWeightedSupport (R : Type*) [CommSemiring R]
    (derivOrder degreeCap : ℕ) : Submodule R (InterpolationPolynomial derivOrder R) :=
  MvPolynomial.restrictWeightedDegree highDerivativeWeight degreeCap

/-- Local polynomials with an inclusive multiplicity-weight cap. -/
def localMultiplicityWeightedSupport (R : Type*) [CommSemiring R]
    (derivOrder degreeCap : ℕ) : Submodule R (LocalPolynomial derivOrder R) :=
  MvPolynomial.restrictWeightedDegree (localMultiplicityWeight derivOrder) degreeCap

/-- Local polynomials with an inclusive high-derivative-weight cap. -/
def localDerivativeWeightedSupport (R : Type*) [CommSemiring R]
    (derivOrder degreeCap : ℕ) : Submodule R (LocalPolynomial derivOrder R) :=
  MvPolynomial.restrictWeightedDegree localDerivativeWeight degreeCap

/-- The configured high-derivative support cap on interpolation polynomials. -/
def Parameters.highDerivativeWeightedSupport (params : Parameters) (R : Type*) [CommSemiring R] :
    Submodule R (InterpolationPolynomial params.derivOrder R) :=
  ReedSolomon.HiddenDerivative.highDerivativeWeightedSupport
    R params.derivOrder params.weightCap

/-- The configured high-derivative support cap after passing to local variables. -/
def Parameters.localDerivativeWeightedSupport (params : Parameters) (R : Type*) [CommSemiring R] :
    Submodule R (LocalPolynomial params.derivOrder R) :=
  ReedSolomon.HiddenDerivative.localDerivativeWeightedSupport
    R params.derivOrder params.weightCap

@[simp]
theorem mem_interpolationWeightedSupport {R : Type*} [CommSemiring R]
    {derivOrder designDim degreeCap : ℕ} {p : InterpolationPolynomial derivOrder R} :
    p ∈ interpolationWeightedSupport R derivOrder designDim degreeCap ↔
      p.weightedTotalDegree (interpolationWeight designDim) ≤ degreeCap :=
  MvPolynomial.mem_restrictWeightedDegree_iff_weightedTotalDegree_le

@[simp]
theorem mem_highDerivativeWeightedSupport {R : Type*} [CommSemiring R]
    {derivOrder degreeCap : ℕ} {p : InterpolationPolynomial derivOrder R} :
    p ∈ highDerivativeWeightedSupport R derivOrder degreeCap ↔
      p.weightedTotalDegree highDerivativeWeight ≤ degreeCap :=
  MvPolynomial.mem_restrictWeightedDegree_iff_weightedTotalDegree_le

@[simp]
theorem mem_localMultiplicityWeightedSupport {R : Type*} [CommSemiring R]
    {derivOrder degreeCap : ℕ} {p : LocalPolynomial derivOrder R} :
    p ∈ localMultiplicityWeightedSupport R derivOrder degreeCap ↔
      p.weightedTotalDegree (localMultiplicityWeight derivOrder) ≤ degreeCap :=
  MvPolynomial.mem_restrictWeightedDegree_iff_weightedTotalDegree_le

@[simp]
theorem mem_localDerivativeWeightedSupport {R : Type*} [CommSemiring R]
    {derivOrder degreeCap : ℕ} {p : LocalPolynomial derivOrder R} :
    p ∈ localDerivativeWeightedSupport R derivOrder degreeCap ↔
      p.weightedTotalDegree localDerivativeWeight ≤ degreeCap :=
  MvPolynomial.mem_restrictWeightedDegree_iff_weightedTotalDegree_le

/-! ### Boundary behavior and mutation canaries -/

/-- At `d = K - 1`, the highest interpolation derivative has weight zero. -/
@[simp]
theorem interpolationWeight_last_eq_zero_of_derivOrder_eq_sub_one
    (designDim derivOrder : ℕ) (h : derivOrder = designDim - 1) :
    interpolationWeight designDim (.Y (Fin.last derivOrder)) = 0 := by
  simp only [interpolationWeight_Y, Fin.val_last]
  omega

/-- The zero boundary is genuine: every power of the highest derivative lies in cap zero when
`d = K - 1`. -/
theorem Y_last_pow_mem_interpolationWeightedSupport_zero {R : Type*} [CommSemiring R]
    (designDim derivOrder : ℕ) (h : derivOrder = designDim - 1) (exponent : ℕ) :
    MvPolynomial.X (.Y (Fin.last derivOrder)) ^ exponent ∈
      interpolationWeightedSupport R derivOrder designDim 0 := by
  exact MvPolynomial.X_pow_mem_restrictWeightedDegree_zero
    (interpolationWeight_last_eq_zero_of_derivOrder_eq_sub_one designDim derivOrder h) exponent

/-- At derivative order one, the local variables are exactly `T`, `E`, and `Y₁`; this canary fixes
all three local weights and the interpolation index origin. -/
theorem weight_derivOrder_one_canary :
    interpolationWeight (derivOrder := 1) 3 .X = 1 ∧
      interpolationWeight (derivOrder := 1) 3 (.Y 0) = 2 ∧
      interpolationWeight (derivOrder := 1) 3 (.Y 1) = 1 ∧
      highDerivativeWeight (.X : InterpolationVar 1) = 0 ∧
      highDerivativeWeight (.Y 0 : InterpolationVar 1) = 0 ∧
      highDerivativeWeight (.Y 1 : InterpolationVar 1) = 0 ∧
      localMultiplicityWeight 1 (.T : LocalVar 1) = 1 ∧
      localMultiplicityWeight 1 (.E : LocalVar 1) = 1 ∧
      localDerivativeWeight (.Yhi 0 : LocalVar 1) = 0 := by
  decide

/-- At derivative order two, this canary fixes both local index shifts: `Yhi 0 = Y₁` has
derivative weight zero and `Yhi 1 = Y₂` has derivative weight one. -/
theorem weight_derivOrder_two_canary :
    interpolationWeight (derivOrder := 2) 5 .X = 1 ∧
      interpolationWeight (derivOrder := 2) 5 (.Y 0) = 4 ∧
      interpolationWeight (derivOrder := 2) 5 (.Y 1) = 3 ∧
      interpolationWeight (derivOrder := 2) 5 (.Y 2) = 2 ∧
      highDerivativeWeight (.Y 0 : InterpolationVar 2) = 0 ∧
      highDerivativeWeight (.Y 1 : InterpolationVar 2) = 0 ∧
      highDerivativeWeight (.Y 2 : InterpolationVar 2) = 1 ∧
      localMultiplicityWeight 2 (.E : LocalVar 2) = 2 ∧
      localDerivativeWeight (.Yhi 0 : LocalVar 2) = 0 ∧
      localDerivativeWeight (.Yhi 1 : LocalVar 2) = 1 := by
  decide

/-- Off-by-one interpolation canary: at `(K, d) = (5, 2)`, `X² Y₁` has exact weight five,
belongs to cap five, and misses cap four. -/
theorem interpolationWeight_offByOne_canary :
    let p : InterpolationPolynomial 2 ℤ := MvPolynomial.monomial
      (Finsupp.single .X 2 + Finsupp.single (.Y ⟨1, by decide⟩) 1) 1
    p.weightedTotalDegree (interpolationWeight 5) = 5 ∧
      p ∈ interpolationWeightedSupport ℤ 2 5 5 ∧
      p ∉ interpolationWeightedSupport ℤ 2 5 4 := by
  dsimp only
  have hdegree :
      MvPolynomial.weightedTotalDegree (interpolationWeight (derivOrder := 2) 5)
        (MvPolynomial.monomial
          (Finsupp.single (.X : InterpolationVar 2) 2 +
            Finsupp.single (InterpolationVar.Y ⟨1, by decide⟩) 1) (1 : ℤ)) = 5 := by
    rw [MvPolynomial.weightedTotalDegree_monomial _ _ _ one_ne_zero,
      map_add, Finsupp.weight_single, Finsupp.weight_single]
    norm_num [interpolationWeight]
  refine ⟨hdegree, ?_, ?_⟩
  · rw [mem_interpolationWeightedSupport, hdegree]
  · rw [mem_interpolationWeightedSupport, hdegree]
    omega

/-- Off-by-one high-derivative canary: for `d = 2`, `Y₂` has exact high-derivative weight one,
so it meets cap one but not cap zero. -/
theorem highDerivativeWeight_offByOne_canary :
    let p : InterpolationPolynomial 2 ℤ := MvPolynomial.monomial
      (Finsupp.single (.Y ⟨2, by decide⟩) 1) 1
    p.weightedTotalDegree highDerivativeWeight = 1 ∧
      p ∈ highDerivativeWeightedSupport ℤ 2 1 ∧
      p ∉ highDerivativeWeightedSupport ℤ 2 0 := by
  dsimp only
  have hdegree :
      MvPolynomial.weightedTotalDegree (highDerivativeWeight (derivOrder := 2))
        (MvPolynomial.monomial
          (Finsupp.single (InterpolationVar.Y ⟨2, by decide⟩) 1) (1 : ℤ)) = 1 := by
    rw [MvPolynomial.weightedTotalDegree_monomial _ _ _ one_ne_zero,
      Finsupp.weight_single]
    norm_num [highDerivativeWeight]
  refine ⟨hdegree, ?_, ?_⟩
  · rw [mem_highDerivativeWeightedSupport, hdegree]
  · rw [mem_highDerivativeWeightedSupport, hdegree]
    omega

/-- Off-by-one local-multiplicity canary: for `d = 2`, `T * E²` has exact multiplicity weight
`1 + 2 * 2 = 5`, so it meets cap five but not cap four. -/
theorem localMultiplicityWeight_offByOne_canary :
    let p : LocalPolynomial 2 ℤ := MvPolynomial.monomial
      (Finsupp.single .T 1 + Finsupp.single .E 2) 1
    p.weightedTotalDegree (localMultiplicityWeight 2) = 5 ∧
      p ∈ localMultiplicityWeightedSupport ℤ 2 5 ∧
      p ∉ localMultiplicityWeightedSupport ℤ 2 4 := by
  dsimp only
  have hdegree :
      MvPolynomial.weightedTotalDegree (localMultiplicityWeight 2)
        (MvPolynomial.monomial
          (Finsupp.single (.T : LocalVar 2) 1 + Finsupp.single (.E : LocalVar 2) 2)
          (1 : ℤ)) = 5 := by
    rw [MvPolynomial.weightedTotalDegree_monomial _ _ _ one_ne_zero,
      map_add, Finsupp.weight_single, Finsupp.weight_single]
    norm_num [localMultiplicityWeight]
  refine ⟨hdegree, ?_, ?_⟩
  · rw [mem_localMultiplicityWeightedSupport, hdegree]
  · rw [mem_localMultiplicityWeightedSupport, hdegree]
    omega

end ReedSolomon.HiddenDerivative
