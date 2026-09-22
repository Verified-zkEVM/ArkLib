/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Justin Thaler
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Counting
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.ConstraintMap

/-!
# Exhibited kernel of the enlarged local constraint map

The rewrite `U = E + localJetSum d` sends the hidden-error factor `U - localJetSum d` to the
error variable `E`. The enlarged local constraint map keeps only monomials of contact order below
`m`, where `T` has contact weight `1` and `E` has contact weight `d`. Hence every multiple of
`T^r (U - localJetSum d)^h` is killed by the enlarged map once `m ≤ r + d h`, and over a domain
multiplication by this factor is injective.

## Main statements

* `rewriteUToE_hiddenErrorFactor`: the rewrite sends `U - localJetSum d` to `E`.
* `exhibitedKernelMultiplier_mem_ker`: multiples of `T^r (U - localJetSum d)^h` lie in the
  kernel of `enlargedLocalConstraintMap m` when `m ≤ r + d h`.
* `exhibitedKernelMultiplier_mem_ker_contactThreshold`: the same at `h = contactThreshold d m r`,
  for `d > 0`.
* `exhibitedKernelMultiplier_injective`: multiplication by the factor is injective over a
  domain.

## References

Ported from
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/Local/ConstraintKernel.lean`
at ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d: `hiddenErrorFactor`, the
`rewriteUToE` evaluation lemmas, `exhibitedKernelFactor`, `rewriteUToE_exhibitedKernelFactor`,
`exhibitedKernelMultiplier`, `exhibitedKernelMultiplier_mem_ker`,
`canonicalExhibitedKernelMultiplier_mem_ker` (here
`exhibitedKernelMultiplier_mem_ker_contactThreshold`, without the source's hypothesis `r < m`),
and `exhibitedKernelMultiplier_injective` (here over a domain instead of a field). The source's
monomial computation `projectLowContact_T_pow_mul_E_pow_mul_eq_zero`, `contactKernelExponent`,
and its private contact-order monotonicity lemma are replaced by
`MvPolynomial.mul_mem_restrictWeightedOrder` and `MvPolynomial.weightedTruncation_eq_zero_iff`;
for the same reason `contactKernelExponent`, its two lemmas, and `T_pow_mul_E_pow_eq_monomial`
are not ported. Nothing else in the source file is deferred.

* Brakensiek, Chen, Putterman, Zhang, and Zheng, *Algorithmic List Decoding of Reed--Solomon
  Codes up to Capacity in the Low-Rate Regime*, ECCC TR26-164, Section 3.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon.HiddenDerivative

open MvPolynomial

variable {R : Type*} [CommRing R] {d : ℕ}

/-- The hidden error written in the translated variables: `U - localJetSum d`. -/
def hiddenErrorFactor (d : ℕ) : LocalPolynomial R d :=
  X (localU d) - localJetSum d

@[simp]
theorem rewriteUToE_X_localT (d : ℕ) :
    rewriteUToE (R := R) d (X (localT d)) = X (localT d) := by
  simp [rewriteUToE, rewriteUToEImage, localT]

@[simp]
theorem rewriteUToE_X_localU (d : ℕ) :
    rewriteUToE (R := R) d (X (localU d)) = X (localE d) + localJetSum d := by
  simp [rewriteUToE, rewriteUToEImage, localU, localE, localAux]

@[simp]
theorem rewriteUToE_X_localY (j : Fin d) :
    rewriteUToE (R := R) d (X (localY j)) = X (localY j) := by
  simp [rewriteUToE, rewriteUToEImage, localY]

/-- The rewrite fixes the visible-jet sum, which involves only `T` and the visible jets. -/
@[simp]
theorem rewriteUToE_localJetSum (d : ℕ) :
    rewriteUToE (R := R) d (localJetSum d) = localJetSum d := by
  simp [localJetSum]

/-- The rewrite sends the hidden-error factor `U - localJetSum d` to the error variable `E`. -/
@[simp]
theorem rewriteUToE_hiddenErrorFactor (d : ℕ) :
    rewriteUToE (R := R) d (hiddenErrorFactor d) = X (localE d) := by
  simp [hiddenErrorFactor]

/-- The factor `T^r (U - localJetSum d)^h`. -/
def exhibitedKernelFactor (d r h : ℕ) : LocalPolynomial R d :=
  X (localT d) ^ r * hiddenErrorFactor d ^ h

/-- The rewrite sends the exhibited factor to the monomial `T^r E^h`. -/
@[simp]
theorem rewriteUToE_exhibitedKernelFactor (d r h : ℕ) :
    rewriteUToE (R := R) d (exhibitedKernelFactor d r h) =
      X (localT d) ^ r * X (localE d) ^ h := by
  simp [exhibitedKernelFactor]

/-- Multiplication by `T^r (U - localJetSum d)^h`, as a linear map. -/
def exhibitedKernelMultiplier (d r h : ℕ) : LocalPolynomial R d →ₗ[R] LocalPolynomial R d :=
  LinearMap.mulLeft R (exhibitedKernelFactor d r h)

@[simp]
theorem exhibitedKernelMultiplier_apply (d r h : ℕ) (G : LocalPolynomial R d) :
    exhibitedKernelMultiplier (R := R) d r h G = exhibitedKernelFactor d r h * G :=
  rfl

/-- Every multiple of `T^r (U - localJetSum d)^h` is killed by the enlarged local constraint map
once `m ≤ r + d h`. After the rewrite the factor becomes `T^r E^h`, of contact order `r + d h`, so
every monomial of the product has contact order at least `m`. For `m > r + d h` the statement
fails over every nontrivial ring already for `G = 1`, whose image keeps the monomial `T^r E^h`. -/
theorem exhibitedKernelMultiplier_mem_ker {m r h : ℕ} (hcontact : m ≤ r + d * h)
    (G : LocalPolynomial R d) :
    exhibitedKernelMultiplier (R := R) d r h G ∈
      LinearMap.ker (enlargedLocalConstraintMap (R := R) (d := d) m) := by
  rw [LinearMap.mem_ker, enlargedLocalConstraintMap, LinearMap.comp_apply,
    exhibitedKernelMultiplier_apply, AlgHom.toLinearMap_apply, map_mul,
    rewriteUToE_exhibitedKernelFactor, projectLowContact, weightedTruncation_eq_zero_iff]
  have hT := pow_mem_restrictWeightedOrder (R := R)
    (X_mem_restrictWeightedOrder (localContactWeight d) (localT d) le_rfl) r
  have hE := pow_mem_restrictWeightedOrder (R := R)
    (X_mem_restrictWeightedOrder (localContactWeight d) (localE d) le_rfl) h
  have hG : rewriteUToE (R := R) d G ∈ restrictWeightedOrder (localContactWeight d) 0 := by
    simp
  refine restrictWeightedOrder_anti _ ?_ (mul_mem_restrictWeightedOrder
    (mul_mem_restrictWeightedOrder hT hE) hG)
  simp only [localContactWeight_T, localContactWeight_E, add_zero]
  linarith

/-- At the threshold `h = contactThreshold d m r` the exhibited factor always lies in the kernel.
The hypothesis `0 < d` is needed because for `d = 0` the threshold is `0` and the factor `T^r`
alone does not reach contact order `m > r`. -/
theorem exhibitedKernelMultiplier_mem_ker_contactThreshold (hd : 0 < d) (m r : ℕ)
    (G : LocalPolynomial R d) :
    exhibitedKernelMultiplier (R := R) d r (contactThreshold d m r) G ∈
      LinearMap.ker (enlargedLocalConstraintMap (R := R) (d := d) m) :=
  exhibitedKernelMultiplier_mem_ker (multiplicity_le_add_mul_contactThreshold hd m r) G

/-- Over a nontrivial ring the exhibited factor is nonzero, because its rewrite `T^r E^h` is. -/
theorem exhibitedKernelFactor_ne_zero [Nontrivial R] (d r h : ℕ) :
    exhibitedKernelFactor (R := R) d r h ≠ 0 := by
  intro hzero
  have himage := congrArg (rewriteUToE (R := R) d) hzero
  rw [rewriteUToE_exhibitedKernelFactor, map_zero] at himage
  simp [X_pow_eq_monomial] at himage

/-- Over a domain, multiplication by `T^r (U - localJetSum d)^h` is injective. -/
theorem exhibitedKernelMultiplier_injective [IsDomain R] (d r h : ℕ) :
    Function.Injective (exhibitedKernelMultiplier (R := R) d r h) := fun _ _ hGH =>
  mul_left_cancel₀ (exhibitedKernelFactor_ne_zero d r h) hGH

end ReedSolomon.HiddenDerivative
