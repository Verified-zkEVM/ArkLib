/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Justin Thaler
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.IntermediateSpace
public import ArkLib.ToMathlib.LinearAlgebra.TriangularInjective
public import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Independence of the exhibited kernel slices

View a local polynomial as a polynomial in `T` whose coefficients are polynomials in `U` and the
visible jets. The `T^n` coefficient of `T^r (U - localJetSum d)^h G` vanishes for `n < r`, and for
`n = r` it is `(U - Y₁)^h` times the `T^0` coefficient of `G`, because the constant coefficient of
`localJetSum d` is `Y₁`. If `G` has no `T`, its `T^0` coefficient determines it. So the family
`(G_r)_{r < m} ↦ T^m-truncation of ∑_r T^r (U - localJetSum d)^(h_r) G_r` on `T`-free inputs is
block-lower-triangular with respect to the `T`-coefficients, with injective diagonal over a domain,
and `LinearMap.injective_sum_comp_proj_of_triangular` shows it is injective.

Only the exhibited part of the kernel is counted: no reverse inclusion or rank equality is
proved.

## Main statements

* `localTCoefficient_exhibitedKernelFactor_mul_of_lt`: the `T^n` coefficient of an exhibited
  product vanishes for `n < r`.
* `localTCoefficient_exhibitedKernelFactor_mul_self`: the `T^r` coefficient is
  `(U - Y₁)^h` times the `T^0` coefficient of `G`.
* `finrank_exhibitedKernelFamilySource`: the dimension of the family of bounded slices at the
  canonical thresholds.
* `exhibitedKernelFamilyMap_injective`, `exhibitedKernelFamilyKernelMap_injective`: the family
  injects into the intermediate space and into the kernel of the intermediate constraint map.

## References

* [Brakensiek, J., Chen, Y., Putterman, A., Zhang, Z., and Zheng, K. Z., *Algorithmic List
  Decoding of Reed–Solomon Codes up to Capacity in the Low-Rate Regime*][BCPZZ26], Section 3.
-/

@[expose] public section

open PolynomialDifferential

noncomputable section

namespace ReedSolomon.HiddenDerivative

open MvPolynomial

variable {R : Type*} [CommRing R] {d : ℕ}

/-! ### `T`-coefficients -/

/-- The coefficient of `T^n` of a local polynomial, as a polynomial in `U` and the visible jets
(`none` is `U` and `some j` is `Y_(j+1)`). -/
def localTCoefficient (d n : ℕ) : LocalPolynomial R d →ₗ[R] MvPolynomial (Option (Fin d)) R where
  toFun P := (optionEquivLeft R (Option (Fin d)) P).coeff n
  map_add' P Q := by simp
  map_smul' c P := by simp [smul_eq_C_mul, Polynomial.coeff_C_mul]

/-- The coefficient of `localTCoefficient d n P` at `e` is the coefficient of `P` at the exponent
with `T`-degree `n` and the other degrees given by `e`. -/
theorem coeff_localTCoefficient (n : ℕ) (P : LocalPolynomial R d) (e : Option (Fin d) →₀ ℕ) :
    (localTCoefficient d n P).coeff e = P.coeff (e.optionElim n) :=
  optionEquivLeft_coeff_coeff R P n e

/-- Reduction modulo `T^m` keeps exactly the `T`-coefficients of degree below `m`. -/
theorem localTCoefficient_truncateLocalT (m n : ℕ) (P : LocalPolynomial R d) :
    localTCoefficient d n (truncateLocalT m P) =
      if n < m then localTCoefficient d n P else 0 := by
  ext e
  rw [coeff_localTCoefficient, coeff_truncateLocalT]
  split_ifs <;> simp_all [coeff_localTCoefficient, localT]

/-- A polynomial with no `T` is determined by its `T^0` coefficient. The hypothesis on the support
is needed: `T` itself has zero `T^0` coefficient. -/
theorem eq_zero_of_localTCoefficient_zero_eq_zero {P : LocalPolynomial R d}
    (hfree : ∀ e ∈ P.support, e (localT d) = 0) (hP : localTCoefficient d 0 P = 0) : P = 0 := by
  ext e
  by_cases he : e ∈ P.support
  · have hc := congrArg (fun p : MvPolynomial (Option (Fin d)) R => p.coeff e.some) hP
    have heT : e none = 0 := hfree e he
    simp only [coeff_localTCoefficient, ← heT, Finsupp.optionElim_some] at hc
    simpa using hc
  · simpa using notMem_support_iff.mp he

/-- The `T^n` coefficient of `T^r P` is the `T^(n - r)` coefficient of `P` if `r ≤ n`, and zero
otherwise. -/
@[simp]
theorem localTCoefficient_X_localT_pow_mul (r n : ℕ) (P : LocalPolynomial R d) :
    localTCoefficient d n (X (localT d) ^ r * P) =
      if r ≤ n then localTCoefficient d (n - r) P else 0 := by
  simp [localTCoefficient, localT, Polynomial.coeff_X_pow_mul']

/-- The constant coefficient in `T` of the visible-jet sum is `Y₁`. -/
theorem localTCoefficient_zero_localJetSum (hd : 0 < d) :
    localTCoefficient (R := R) d 0 (localJetSum d) = X (some ⟨0, hd⟩) := by
  rw [localJetSum, map_sum, Finset.sum_eq_single (⟨0, hd⟩ : Fin d)]
  · simp [localTCoefficient, localY]
  · intro j _ hj
    have hj0 : j.val ≠ 0 := fun h => hj (Fin.ext h)
    rw [mul_comm (C _), mul_assoc, localTCoefficient_X_localT_pow_mul, ite_eq_right_iff]
    omega
  · simp

/-- The constant coefficient in `T` of the hidden error `U - localJetSum d` is `U - Y₁`. -/
theorem localTCoefficient_zero_hiddenErrorFactor (hd : 0 < d) :
    localTCoefficient (R := R) d 0 (hiddenErrorFactor d) = X none - X (some ⟨0, hd⟩) := by
  rw [hiddenErrorFactor, map_sub, localTCoefficient_zero_localJetSum hd]
  simp [localTCoefficient, localU, localAux]

/-- Over a nontrivial ring, the constant coefficient in `T` of the hidden error is nonzero: it is
`U - Y₁` for `d > 0` and `U` for `d = 0`. -/
theorem localTCoefficient_zero_hiddenErrorFactor_ne_zero [Nontrivial R] (d : ℕ) :
    localTCoefficient (R := R) d 0 (hiddenErrorFactor d) ≠ 0 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [hiddenErrorFactor, localJetSum, localTCoefficient, localU, localAux]
  rw [localTCoefficient_zero_hiddenErrorFactor hd]
  intro h
  have hc := congrArg
    (fun p : MvPolynomial (Option (Fin d)) R => p.coeff (Finsupp.single none 1)) h
  simp at hc

/-- The `T^n` coefficient of `T^r (U - localJetSum d)^h G` vanishes for `n < r`. -/
theorem localTCoefficient_exhibitedKernelFactor_mul_of_lt {r h n : ℕ} (hnr : n < r)
    (G : LocalPolynomial R d) :
    localTCoefficient d n (exhibitedKernelFactor d r h * G) = 0 := by
  rw [exhibitedKernelFactor, mul_assoc, localTCoefficient_X_localT_pow_mul, ite_eq_right_iff]
  omega

/-- The `T^r` coefficient of `T^r (U - localJetSum d)^h G` is the `h`th power of the constant
coefficient of the hidden error (`U - Y₁` when `d > 0`, by
`localTCoefficient_zero_hiddenErrorFactor`) times the `T^0` coefficient of `G`. -/
theorem localTCoefficient_exhibitedKernelFactor_mul_self (r h : ℕ) (G : LocalPolynomial R d) :
    localTCoefficient d r (exhibitedKernelFactor d r h * G) =
      localTCoefficient d 0 (hiddenErrorFactor d) ^ h * localTCoefficient d 0 G := by
  rw [exhibitedKernelFactor, mul_assoc, localTCoefficient_X_localT_pow_mul]
  simp only [le_refl, ↓reduceIte, Nat.sub_self, localTCoefficient, LinearMap.coe_mk,
    AddHom.coe_mk, map_mul, map_pow, Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.eval_mul, Polynomial.eval_pow]

/-! ### The exhibited family -/

/-- One bounded kernel slice for each `T`-degree `r < m`, at the threshold
`contactThreshold d m r`. -/
abbrev ExhibitedKernelFamilySource (R : Type*) [CommRing R] (d m M W : ℕ) :=
  ∀ r : Fin m, kernelSliceSourceSpace R d r M W (contactThreshold d m r)

/-- For `d > 0` the family has dimension
`∑_{r < m} weightedHigherJetCount d (W + r) * (r + 1 - h_r)(M + 1 - h_r)`. -/
theorem finrank_exhibitedKernelFamilySource {F : Type*} [Field F] (hd : 0 < d) (m M W : ℕ) :
    Module.finrank F (ExhibitedKernelFamilySource F d m M W) =
      ∑ r ∈ Finset.range m,
        weightedHigherJetCount d (W + r) *
          exhibitedKernelContactCount r M (contactThreshold d m r) := by
  have : ∀ r : Fin m, Module.Finite F
      (kernelSliceSourceSpace F d r M W (contactThreshold d m r)) := fun r =>
    kernelSliceSourceSpace_finite hd _ _ _ _
  rw [Module.finrank_pi_fintype]
  simp_rw [finrank_kernelSliceSourceSpace (F := F) hd]
  exact Fin.sum_univ_eq_sum_range
    (fun r => weightedHigherJetCount d (W + r) *
      exhibitedKernelContactCount r M (contactThreshold d m r)) m

/-- The sum over `r < m` of the bounded exhibited maps at the canonical thresholds. -/
def exhibitedKernelFamilyMap (m M W : ℕ) :
    ExhibitedKernelFamilySource R d m M W →ₗ[R] localIntermediateSpace R d m M W :=
  ∑ r : Fin m, (boundedExhibitedKernelMap m r M W _).comp (LinearMap.proj r)

/-- `exhibitedKernelFamilyMap m M W G` is the reduction modulo `T^m` of
`∑_r T^r (U - localJetSum d)^(h_r) G_r`, with `h_r = contactThreshold d m r`. -/
@[simp]
theorem exhibitedKernelFamilyMap_apply (m M W : ℕ) (G : ExhibitedKernelFamilySource R d m M W) :
    (exhibitedKernelFamilyMap m M W G : LocalPolynomial R d) =
      truncateLocalT m (∑ r : Fin m,
        exhibitedKernelFactor d r (contactThreshold d m r) * (G r : LocalPolynomial R d)) := by
  simp [exhibitedKernelFamilyMap]

/-- Over a domain the family map is injective, for every `d`. The slice of index `r` contributes
nothing below `T^r`, and its `T^r` coefficient is a nonzero power (`(U - Y₁)^h`, or `U^h` when
`d = 0`) times the `T^0` coefficient of the slice element, which determines it because it is
`T`-free. -/
theorem exhibitedKernelFamilyMap_injective [IsDomain R] (m M W : ℕ) :
    Function.Injective (exhibitedKernelFamilyMap (R := R) (d := d) m M W) := by
  refine LinearMap.injective_sum_comp_proj_of_triangular _
    (fun n : Fin m => localTCoefficient d n ∘ₗ (localIntermediateSpace R d m M W).subtype)
    (fun i j hij G => ?_) (fun i => ?_)
  · simp only [LinearMap.comp_apply, Submodule.subtype_apply, boundedExhibitedKernelMap_apply,
      localTCoefficient_truncateLocalT, i.isLt, ↓reduceIte]
    exact localTCoefficient_exhibitedKernelFactor_mul_of_lt hij _
  · rw [injective_iff_map_eq_zero]
    intro G hG
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, boundedExhibitedKernelMap_apply,
      localTCoefficient_truncateLocalT, i.isLt, ↓reduceIte,
      localTCoefficient_exhibitedKernelFactor_mul_self] at hG
    have h0 := (mul_eq_zero.mp hG).resolve_left
      (pow_ne_zero _ (localTCoefficient_zero_hiddenErrorFactor_ne_zero d))
    exact Subtype.ext (eq_zero_of_localTCoefficient_zero_eq_zero
      (fun e he => tDegree_eq_zero_of_mem_kernelSliceSourceSpace G.2 he) h0)

/-- The family map, as a map into the kernel of the intermediate constraint map. The hypothesis
`0 < d` is the one of `intermediateConstraintMap_boundedExhibitedKernelMap_eq_zero`. -/
def exhibitedKernelFamilyKernelMap (hd : 0 < d) (m M W : ℕ) :
    ExhibitedKernelFamilySource R d m M W →ₗ[R]
      LinearMap.ker (intermediateConstraintMap (R := R) (d := d) m M W) :=
  (exhibitedKernelFamilyMap m M W).codRestrict _ fun G => by
    rw [LinearMap.mem_ker, exhibitedKernelFamilyMap, LinearMap.sum_apply, map_sum]
    exact Finset.sum_eq_zero fun r _ =>
      intermediateConstraintMap_boundedExhibitedKernelMap_eq_zero hd m r M W (G r)

/-- `exhibitedKernelFamilyKernelMap` agrees with `exhibitedKernelFamilyMap` after forgetting the
kernel membership. -/
@[simp]
theorem exhibitedKernelFamilyKernelMap_apply (hd : 0 < d) (m M W : ℕ)
    (G : ExhibitedKernelFamilySource R d m M W) :
    (exhibitedKernelFamilyKernelMap hd m M W G : localIntermediateSpace R d m M W) =
      exhibitedKernelFamilyMap m M W G :=
  rfl

/-- Over a domain with `d > 0`, the family injects into the kernel of the intermediate
constraint map. -/
theorem exhibitedKernelFamilyKernelMap_injective [IsDomain R] (hd : 0 < d) (m M W : ℕ) :
    Function.Injective (exhibitedKernelFamilyKernelMap (R := R) hd m M W) := fun _ _ hGH =>
  exhibitedKernelFamilyMap_injective m M W (congrArg Subtype.val hGH)

end ReedSolomon.HiddenDerivative
