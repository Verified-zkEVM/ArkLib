/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Variables

/-!
# Structured substitutions for hidden-derivative interpolation

This file separates the two error conventions used in the hidden-derivative argument.

* `unscaledLocalSubstitution` is the local rewrite in Equation (14). Its error variable denotes the
  candidate-derived backward Taylor error, which is divisible by `T ^ derivOrder`, and appears as
  `T * E`.
* `normalizedLocalSubstitution` is the algorithmic rewrite in Equation (25). Its error variable is
  free after dividing out `T ^ derivOrder`, and appears as `T ^ (derivOrder + 1) * E`.

The map `normalizeError` sends `E` to `T ^ derivOrder * E`. The composition theorem below records
that applying it to the unscaled rewrite gives the normalized rewrite. Keeping the maps distinct
prevents the divisibility hypothesis on the unscaled error from being silently lost.

For paper Hasse order `j = 1, ..., derivOrder`, the Taylor-correction coefficient is
`(-1) ^ (j + 1)`. The constructor `Yhi r` is zero-based and represents `Y_(r+1)`, so the same
coefficient simplifies to `(-1) ^ r` in `localCorrection`.

## References

* [Brakensiek, Chen, Putterman, Zhang, Zheng, *Algorithmic List Decoding of Reed--Solomon Codes up
  to Capacity in the Low-Rate Regime*][BCPZZ26], Equations (14) and (25).
-/

noncomputable section

open scoped BigOperators

namespace ReedSolomon.HiddenDerivative

open MvPolynomial

variable {R : Type*} [CommRing R]

/-- The signed Taylor correction
`sum_{j=1}^d (-1)^(j+1) T^j Y_j`, with zero-based local index `r = j - 1`. -/
def localCorrection (derivOrder : ℕ) : LocalPolynomial derivOrder R :=
  ∑ order : Fin derivOrder,
    C ((-1 : R) ^ order.val) *
      X (.T : LocalVar derivOrder) ^ (order.val + 1) * X (.Yhi order)

/-- Generator images for the unscaled local rewrite from Equation (14). -/
def unscaledLocalImage (derivOrder : ℕ) (center received : R) :
    InterpolationVar derivOrder → LocalPolynomial derivOrder R
  | .X => C center + X .T
  | .Y order => Fin.cases
      (C received + localCorrection derivOrder + X .T * X .E)
      (fun highOrder => X (.Yhi highOrder)) order

/-- Equation (14): the error is candidate-derived, is divisible by `T ^ derivOrder`, and occurs
as `T * E`. -/
def unscaledLocalSubstitution (derivOrder : ℕ) (center received : R) :
    InterpolationPolynomial derivOrder R →ₐ[R] LocalPolynomial derivOrder R :=
  bind₁ (unscaledLocalImage derivOrder center received)

@[simp]
theorem unscaledLocalSubstitution_X (derivOrder : ℕ) (center received : R) :
    unscaledLocalSubstitution derivOrder center received (X .X) = C center + X .T := by
  simp [unscaledLocalSubstitution, unscaledLocalImage]

@[simp]
theorem unscaledLocalSubstitution_Y_zero (derivOrder : ℕ) (center received : R) :
    unscaledLocalSubstitution derivOrder center received (X (.Y 0)) =
      C received + localCorrection derivOrder + X .T * X .E := by
  simp [unscaledLocalSubstitution, unscaledLocalImage]

@[simp]
theorem unscaledLocalSubstitution_Y_succ (derivOrder : ℕ) (center received : R)
    (order : Fin derivOrder) :
    unscaledLocalSubstitution derivOrder center received (X (.Y order.succ)) =
      X (.Yhi order) := by
  simp [unscaledLocalSubstitution, unscaledLocalImage]

/-- Rescale the error by `E ↦ T ^ derivOrder * E`, fixing all other local generators. -/
def normalizeError (derivOrder : ℕ) :
    LocalPolynomial derivOrder R →ₐ[R] LocalPolynomial derivOrder R :=
  bind₁ fun
    | .T => X .T
    | .E => X .T ^ derivOrder * X .E
    | .Yhi order => X (.Yhi order)

/-- Source-oriented alias for `normalizeError`: it scales the unnormalized error generator by
`T ^ derivOrder`. -/
abbrev scaleLocalError (derivOrder : ℕ) :
    LocalPolynomial derivOrder R →ₐ[R] LocalPolynomial derivOrder R :=
  normalizeError derivOrder

@[simp]
theorem normalizeError_T (derivOrder : ℕ) :
    normalizeError (R := R) derivOrder (X .T) = X .T := by
  simp [normalizeError]

@[simp]
theorem normalizeError_E (derivOrder : ℕ) :
    normalizeError (R := R) derivOrder (X .E) = X .T ^ derivOrder * X .E := by
  simp [normalizeError]

@[simp]
theorem normalizeError_Yhi (derivOrder : ℕ) (order : Fin derivOrder) :
    normalizeError (R := R) derivOrder (X (.Yhi order)) = X (.Yhi order) := by
  simp [normalizeError]

@[simp]
theorem normalizeError_localCorrection (derivOrder : ℕ) :
    normalizeError (R := R) derivOrder (localCorrection derivOrder) =
      localCorrection derivOrder := by
  simp [localCorrection]

/-- Generator images for Algorithm 1, Equation (25), with a free normalized error. -/
def normalizedLocalImage (derivOrder : ℕ) (center received : R) :
    InterpolationVar derivOrder → LocalPolynomial derivOrder R
  | .X => C center + X .T
  | .Y order => Fin.cases
      (C received + localCorrection derivOrder + X .T ^ (derivOrder + 1) * X .E)
      (fun highOrder => X (.Yhi highOrder)) order

/-- Algorithm 1, Equation (25): the error has already been divided by `T ^ derivOrder` and occurs
as `T ^ (derivOrder + 1) * E`. -/
def normalizedLocalSubstitution (derivOrder : ℕ) (center received : R) :
    InterpolationPolynomial derivOrder R →ₐ[R] LocalPolynomial derivOrder R :=
  bind₁ (normalizedLocalImage derivOrder center received)

@[simp]
theorem normalizedLocalSubstitution_X (derivOrder : ℕ) (center received : R) :
    normalizedLocalSubstitution derivOrder center received (X .X) = C center + X .T := by
  simp [normalizedLocalSubstitution, normalizedLocalImage]

@[simp]
theorem normalizedLocalSubstitution_Y_zero (derivOrder : ℕ) (center received : R) :
    normalizedLocalSubstitution derivOrder center received (X (.Y 0)) =
      C received + localCorrection derivOrder + X .T ^ (derivOrder + 1) * X .E := by
  simp [normalizedLocalSubstitution, normalizedLocalImage]

@[simp]
theorem normalizedLocalSubstitution_Y_succ (derivOrder : ℕ) (center received : R)
    (order : Fin derivOrder) :
    normalizedLocalSubstitution derivOrder center received (X (.Y order.succ)) =
      X (.Yhi order) := by
  simp [normalizedLocalSubstitution, normalizedLocalImage]

/-- Rescaling the divisible error in Equation (14) gives Algorithm 1, Equation (25). -/
theorem normalizedLocalSubstitution_eq_normalizeError_comp_unscaled
    (derivOrder : ℕ) (center received : R) :
    normalizedLocalSubstitution derivOrder center received =
      (normalizeError derivOrder).comp
        (unscaledLocalSubstitution derivOrder center received) := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i with
  | X => simp
  | Y order =>
      refine Fin.cases ?_ (fun highOrder => ?_) order
      · simp only [normalizedLocalSubstitution_Y_zero, AlgHom.coe_comp,
          Function.comp_apply, unscaledLocalSubstitution_Y_zero, map_add, algHom_C,
          algebraMap_eq, normalizeError_localCorrection, map_mul, normalizeError_T,
          normalizeError_E, add_right_inj]
        rw [pow_succ]
        ring
      · simp

/-- The composition diagram under the source-oriented `scaleLocalError` name. -/
theorem normalizedLocalSubstitution_eq_scaleLocalError_comp
    (derivOrder : ℕ) (center received : R) :
    normalizedLocalSubstitution derivOrder center received =
      (scaleLocalError derivOrder).comp
        (unscaledLocalSubstitution derivOrder center received) :=
  normalizedLocalSubstitution_eq_normalizeError_comp_unscaled derivOrder center received

/-- Polynomial-level form of the error-rescaling composition diagram. -/
theorem normalizedLocalSubstitution_apply_eq_scaleLocalError_unscaled
    (derivOrder : ℕ) (center received : R) (p : InterpolationPolynomial derivOrder R) :
    normalizedLocalSubstitution derivOrder center received p =
      scaleLocalError derivOrder (unscaledLocalSubstitution derivOrder center received p) :=
  DFunLike.congr_fun
    (normalizedLocalSubstitution_eq_scaleLocalError_comp derivOrder center received) p

/-- At derivative order zero, error rescaling is the identity. -/
@[simp]
theorem scaleLocalError_zero :
    scaleLocalError (R := R) 0 = AlgHom.id R (LocalPolynomial 0 R) := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i with
  | T => simp
  | E => simp
  | Yhi order => exact Fin.elim0 order

/-- At derivative order zero, the unscaled and normalized rewrites coincide. -/
theorem normalizedLocalSubstitution_zero (center received : R) :
    normalizedLocalSubstitution 0 center received =
      unscaledLocalSubstitution 0 center received := by
  rw [normalizedLocalSubstitution_eq_scaleLocalError_comp, scaleLocalError_zero]
  rfl

/-! ### Natural per-image weighted bounds -/

/-- The target weight that records only powers of `T`. -/
def localTWeight (derivOrder : ℕ) : LocalVar derivOrder → ℕ
  | .T => 1
  | .E | .Yhi _ => 0

@[simp]
theorem localTWeight_T (derivOrder : ℕ) :
    localTWeight derivOrder (.T : LocalVar derivOrder) = 1 :=
  rfl

@[simp]
theorem localTWeight_E (derivOrder : ℕ) :
    localTWeight derivOrder (.E : LocalVar derivOrder) = 0 :=
  rfl

@[simp]
theorem localTWeight_Yhi (derivOrder : ℕ) (order : Fin derivOrder) :
    localTWeight derivOrder (.Yhi order) = 0 :=
  rfl

/-- Source caps natural for both local rewrites: `X` has cap one, `Y₀` has cap `d + 1`, and
each `Y_(j+1)` has cap zero. These are substitution-image caps, not the interpolation weights. -/
def localSubstitutionSourceWeight (derivOrder : ℕ) : InterpolationVar derivOrder → ℕ
  | .X => 1
  | .Y order => Fin.cases (derivOrder + 1) (fun _ => 0) order

@[simp]
theorem localSubstitutionSourceWeight_X (derivOrder : ℕ) :
    localSubstitutionSourceWeight derivOrder .X = 1 :=
  rfl

@[simp]
theorem localSubstitutionSourceWeight_Y_zero (derivOrder : ℕ) :
    localSubstitutionSourceWeight derivOrder (.Y 0) = derivOrder + 1 :=
  rfl

@[simp]
theorem localSubstitutionSourceWeight_Y_succ (derivOrder : ℕ)
    (order : Fin derivOrder) :
    localSubstitutionSourceWeight derivOrder (.Y order.succ) = 0 := by
  simp [localSubstitutionSourceWeight]

/-- The correction has local divisibility weight at most `derivOrder`. -/
theorem localCorrection_mem_multiplicity (derivOrder : ℕ) :
    localCorrection (R := R) derivOrder ∈
      restrictWeightedDegree (R := R) (localMultiplicityWeight derivOrder) derivOrder := by
  apply Submodule.sum_mem
  intro order _
  apply restrictWeightedDegree_mono (d := order.val + 1)
  · omega
  have hpow := pow_mem_restrictWeightedDegree
    (X_mem_restrictWeightedDegree (R := R) (localMultiplicityWeight derivOrder) 1 .T
      (by rfl)) (order.val + 1)
  have hcoeffPow := mul_mem_restrictWeightedDegree
    (C_mem_restrictWeightedDegree (R := R) (localMultiplicityWeight derivOrder) 0
      ((-1 : R) ^ order.val)) hpow
  have hterm := mul_mem_restrictWeightedDegree hcoeffPow
    (X_mem_restrictWeightedDegree (R := R) (localMultiplicityWeight derivOrder) 0
      (.Yhi order) (by rfl))
  simpa using hterm

/-- The correction has `T`-degree at most `derivOrder`. -/
theorem localCorrection_mem_TWeight (derivOrder : ℕ) :
    localCorrection (R := R) derivOrder ∈
      restrictWeightedDegree (R := R) (localTWeight derivOrder) derivOrder := by
  apply Submodule.sum_mem
  intro order _
  apply restrictWeightedDegree_mono (d := order.val + 1)
  · omega
  have hpow := pow_mem_restrictWeightedDegree
    (X_mem_restrictWeightedDegree (R := R) (localTWeight derivOrder) 1 .T (by rfl))
    (order.val + 1)
  have hcoeffPow := mul_mem_restrictWeightedDegree
    (C_mem_restrictWeightedDegree (R := R) (localTWeight derivOrder) 0
      ((-1 : R) ^ order.val)) hpow
  have hterm := mul_mem_restrictWeightedDegree hcoeffPow
    (X_mem_restrictWeightedDegree (R := R) (localTWeight derivOrder) 0
      (.Yhi order) (by rfl))
  simpa using hterm

/-- Every unscaled generator image meets its natural local-divisibility cap. In particular, the
`Y₀` image has cap `derivOrder + 1` because `T * E` has weight `1 + derivOrder`. -/
theorem unscaledLocalImage_mem (derivOrder : ℕ) (center received : R) (i) :
    unscaledLocalImage derivOrder center received i ∈
      restrictWeightedDegree (R := R) (localMultiplicityWeight derivOrder)
        (localSubstitutionSourceWeight derivOrder i) := by
  cases i with
  | X =>
      exact Submodule.add_mem _ (C_mem_restrictWeightedDegree _ _ _)
        (X_mem_restrictWeightedDegree _ _ _ (by rfl))
  | Y order =>
      refine Fin.cases ?_ (fun highOrder => ?_) order
      · simp only [unscaledLocalImage, localSubstitutionSourceWeight]
        apply Submodule.add_mem
        · apply Submodule.add_mem
          · exact C_mem_restrictWeightedDegree _ _ _
          · exact restrictWeightedDegree_mono _ (Nat.le_succ _)
              (localCorrection_mem_multiplicity derivOrder)
        · simpa [Nat.add_comm] using mul_mem_restrictWeightedDegree
            (X_mem_restrictWeightedDegree (R := R) (localMultiplicityWeight derivOrder) 1 .T
              (by rfl))
            (X_mem_restrictWeightedDegree (R := R) (localMultiplicityWeight derivOrder)
              derivOrder .E (by rfl))
      · exact X_mem_restrictWeightedDegree _ _ _ (by rfl)

/-- Every normalized generator image has `T`-degree at most its natural cap. In particular, the
`Y₀` image has cap `derivOrder + 1`, attained by its normalized error term. -/
theorem normalizedLocalImage_mem (derivOrder : ℕ) (center received : R) (i) :
    normalizedLocalImage derivOrder center received i ∈
      restrictWeightedDegree (R := R) (localTWeight derivOrder)
        (localSubstitutionSourceWeight derivOrder i) := by
  cases i with
  | X =>
      exact Submodule.add_mem _ (C_mem_restrictWeightedDegree _ _ _)
        (X_mem_restrictWeightedDegree _ _ _ (by rfl))
  | Y order =>
      refine Fin.cases ?_ (fun highOrder => ?_) order
      · simp only [normalizedLocalImage, localSubstitutionSourceWeight]
        apply Submodule.add_mem
        · apply Submodule.add_mem
          · exact C_mem_restrictWeightedDegree _ _ _
          · exact restrictWeightedDegree_mono _ (Nat.le_succ _)
              (localCorrection_mem_TWeight derivOrder)
        · simpa using mul_mem_restrictWeightedDegree
            (pow_mem_restrictWeightedDegree
              (X_mem_restrictWeightedDegree (R := R) (localTWeight derivOrder) 1 .T (by rfl))
              (derivOrder + 1))
            (X_mem_restrictWeightedDegree (R := R) (localTWeight derivOrder) 0 .E (by rfl))
      · exact X_mem_restrictWeightedDegree _ _ _ (by rfl)

/-- The unscaled structured substitution preserves every bound measured with its natural source
and local-divisibility target weights. -/
theorem unscaledLocalSubstitution_mem {derivOrder : ℕ} {center received : R} {degreeCap}
    {p : InterpolationPolynomial derivOrder R}
    (hp : p ∈ restrictWeightedDegree (R := R)
      (localSubstitutionSourceWeight derivOrder) degreeCap) :
    unscaledLocalSubstitution derivOrder center received p ∈
      restrictWeightedDegree (R := R) (localMultiplicityWeight derivOrder) degreeCap := by
  exact bind₁_mem_restrictWeightedDegree
    (unscaledLocalImage_mem derivOrder center received) hp

/-- The normalized structured substitution preserves every bound measured with its natural source
and `T`-degree target weights. -/
theorem normalizedLocalSubstitution_mem {derivOrder : ℕ} {center received : R} {degreeCap}
    {p : InterpolationPolynomial derivOrder R}
    (hp : p ∈ restrictWeightedDegree (R := R)
      (localSubstitutionSourceWeight derivOrder) degreeCap) :
    normalizedLocalSubstitution derivOrder center received p ∈
      restrictWeightedDegree (R := R) (localTWeight derivOrder) degreeCap := by
  exact bind₁_mem_restrictWeightedDegree
    (normalizedLocalImage_mem derivOrder center received) hp

/-! ### Mutation canaries -/

/-- At derivative order two, the monomial `Y₀ * Y₂` simultaneously fixes the correction
signs, the index shift `Y₂ ↦ Yhi 1`, and the distinct error factors `T` versus `T³`. -/
theorem substitution_order_two_canary :
    let source : InterpolationPolynomial 2 ℤ :=
      X (.Y 0) * X (.Y (Fin.succ (1 : Fin 2)))
    let t : LocalPolynomial 2 ℤ := X .T
    let e : LocalPolynomial 2 ℤ := X .E
    let y₁ : LocalPolynomial 2 ℤ := X (.Yhi 0)
    let y₂ : LocalPolynomial 2 ℤ := X (.Yhi 1)
    unscaledLocalSubstitution 2 2 3 source =
        (C 3 + t * y₁ - t ^ 2 * y₂ + t * e) * y₂ ∧
      normalizedLocalSubstitution 2 2 3 source =
        (C 3 + t * y₁ - t ^ 2 * y₂ + t ^ 3 * e) * y₂ := by
  dsimp only
  constructor
  · rw [map_mul, unscaledLocalSubstitution_Y_zero,
      unscaledLocalSubstitution_Y_succ]
    simp [localCorrection, Fin.sum_univ_two]
    ring
  · rw [map_mul, normalizedLocalSubstitution_Y_zero,
      normalizedLocalSubstitution_Y_succ]
    simp [localCorrection, Fin.sum_univ_two]
    ring

/-- At the boundary `(designDim, derivOrder) = (3, 2)`, `Y₀` has interpolation weight two but
its normalized image has exact `T`-degree three. Thus the normalized rewrite does not preserve the
interpolation cap at `derivOrder = designDim - 1`; the honest enlarged cap is three. -/
theorem normalized_boundary_nonpreservation_canary :
    let source : InterpolationPolynomial 2 ℤ := X (.Y 0)
    source ∈ restrictWeightedDegree (R := ℤ) (interpolationWeight 3) 2 ∧
      normalizedLocalSubstitution 2 0 0 source ∈
        restrictWeightedDegree (R := ℤ) (localTWeight 2) 3 ∧
      normalizedLocalSubstitution 2 0 0 source ∉
        restrictWeightedDegree (R := ℤ) (localTWeight 2) 2 := by
  dsimp only
  have hsource :
      X (.Y 0) ∈ restrictWeightedDegree (R := ℤ)
        (interpolationWeight (derivOrder := 2) 3) 2 := by
    exact X_mem_restrictWeightedDegree _ _ _ (by decide)
  have himageThree :
      normalizedLocalSubstitution (R := ℤ) 2 0 0 (X (.Y 0)) ∈
        restrictWeightedDegree (R := ℤ) (localTWeight 2) 3 := by
    simpa only [normalizedLocalSubstitution, bind₁_X_right,
      localSubstitutionSourceWeight, Fin.cases_zero] using
      normalizedLocalImage_mem (R := ℤ) 2 0 0 (.Y 0)
  refine ⟨hsource, himageThree, ?_⟩
  intro himageTwo
  rw [mem_restrictWeightedDegree] at himageTwo
  let exponent : LocalVar 2 →₀ ℕ :=
    Finsupp.single .T 3 + Finsupp.single .E 1
  have hformula :
      normalizedLocalSubstitution (R := ℤ) 2 0 0 (X (.Y 0)) =
        (X (.T : LocalVar 2) : LocalPolynomial 2 ℤ) * X (.Yhi 0) -
          X .T ^ 2 * X (.Yhi 1) + X .T ^ 3 * X .E := by
    rw [normalizedLocalSubstitution_Y_zero]
    simp [localCorrection, Fin.sum_univ_two]
    simp only [sub_eq_add_neg]
  have hcoeff :
      coeff exponent
        (normalizedLocalSubstitution (R := ℤ) 2 0 0 (X (.Y 0))) = (1 : ℤ) := by
    have hfirst :
        Finsupp.single (.T : LocalVar 2) 1 + Finsupp.single (.Yhi 0) 1 ≠ exponent := by
      intro h
      have := DFunLike.congr_fun h (.Yhi 0)
      simp [exponent] at this
    have hsecond :
        Finsupp.single (.T : LocalVar 2) 1 + Finsupp.single .T 1 +
            Finsupp.single (.Yhi 1) 1 ≠ exponent := by
      intro h
      have := DFunLike.congr_fun h (.Yhi 1)
      simp [exponent] at this
    have hthird :
        Finsupp.single (.T : LocalVar 2) 1 + Finsupp.single .T 1 +
          Finsupp.single .T 1 = Finsupp.single .T 3 := by
      ext i
      cases i <;> simp
    rw [hformula]
    classical
    simp [exponent, X, pow_succ, monomial_mul, hfirst, hsecond, hthird]
  have hexponentSupport :
      exponent ∈
        (normalizedLocalSubstitution (R := ℤ) 2 0 0 (X (.Y 0))).support :=
    mem_support_iff.mpr (by rw [hcoeff]; exact one_ne_zero)
  have hweight := himageTwo exponent hexponentSupport
  have : Finsupp.weight (localTWeight 2) exponent = 3 := by
    simp only [exponent, map_add, Finsupp.weight_single]
    decide
  omega

end ReedSolomon.HiddenDerivative
