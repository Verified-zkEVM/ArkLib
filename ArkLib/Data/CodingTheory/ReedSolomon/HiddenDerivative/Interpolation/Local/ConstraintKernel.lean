/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Justin Thaler
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Counting
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Local.ConstraintMap


/-!
# Exhibited kernel factors for the enlarged local constraint map

Let

```text
E♯ = U - localJetSum.
```

The point-independent rewrite sends `E♯` to the error variable `E`.  Consequently every
multiple of `T^r (E♯)^h` lies in the kernel of the enlarged low-contact map as soon as
`m ≤ r + d*h`.  This file proves that statement over an arbitrary commutative ring and proves
that multiplication by the displayed factor is injective over a field.

At the canonical threshold `h = contactThreshold d m r`, these maps are the algebraic core of the
paper's exhibited `K_r` spaces. Their bounded ranges and direct-sum independence are established
in `KernelSliceIndependence`; the resulting kernel dimension gives an upper bound on the local
constraint rank, not an assertion that the exhibited kernel is the entire kernel.

## References

* Brakensiek, Chen, Putterman, Zhang, and Zheng, *Algorithmic List Decoding of Reed--Solomon
  Codes up to Capacity in the Low-Rate Regime*, ECCC TR26-164, Section 3.
* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding and Mutual Correlated Agreement
  up to Capacity*][DKTZ26].
-/

@[expose] public section

open PolynomialDifferential


noncomputable section

namespace ReedSolomon.HiddenDerivative

open MvPolynomial

variable {R : Type*} [CommRing R]
variable {d m r h : ℕ}

/-- The source-coordinate expression for the hidden error: `E♯ = U - localJetSum`. -/
def hiddenErrorFactor (d : ℕ) : LocalPolynomial R d :=
  X (localU d) - localJetSum d

@[simp]
theorem rewriteUToE_localT (d : ℕ) :
    rewriteUToE (R := R) d (X (localT d)) = X (localT d) := by
  simp [rewriteUToE, localT]

@[simp]
theorem rewriteUToE_localU (d : ℕ) :
    rewriteUToE (R := R) d (X (localU d)) = X (localE d) + localJetSum d := by
  simp [rewriteUToE, localU, localE, localAux]

@[simp]
theorem rewriteUToE_localY (j : Fin d) :
    rewriteUToE (R := R) d (X (localY j)) = X (localY j) := by
  simp [rewriteUToE, localY]

@[simp]
theorem rewriteUToE_localJetSum (d : ℕ) :
    rewriteUToE (R := R) d (localJetSum d) = localJetSum d := by
  simp [localJetSum]

/-- The triangular rewrite sends the formal hidden error `U - S(T,Y)` to `E`. -/
@[simp]
theorem rewriteUToE_hiddenErrorFactor (d : ℕ) :
    rewriteUToE (R := R) d (hiddenErrorFactor d) = X (localE d) := by
  simp [hiddenErrorFactor]

/-- Exponent of the monomial `T^r E^h`. -/
def contactKernelExponent (d r h : ℕ) : LocalVariable d →₀ ℕ :=
  Finsupp.single (localT d) r + Finsupp.single (localE d) h

@[simp]
theorem contactKernelExponent_T (r h : ℕ) :
    contactKernelExponent d r h (localT d) = r := by
  simp [contactKernelExponent, localT, localE, localAux]

@[simp]
theorem localContactOrder_contactKernelExponent (d r h : ℕ) :
    localContactOrder d (contactKernelExponent d r h) = r + d * h := by
  simp [localContactOrder, contactKernelExponent, Finsupp.weight_single,
    localContactWeight, localT, localE, localAux, mul_comm]

/-- Polynomial factor `T^r (E♯)^h` before the `U`-to-`E` rewrite. -/
def exhibitedKernelFactor (d r h : ℕ) : LocalPolynomial R d :=
  X (localT d) ^ r * hiddenErrorFactor d ^ h

/-- Rewriting the exhibited factor gives the contact monomial `T^r E^h`. -/
@[simp]
theorem rewriteUToE_exhibitedKernelFactor (d r h : ℕ) :
    rewriteUToE (R := R) d (exhibitedKernelFactor d r h) =
      X (localT d) ^ r * X (localE d) ^ h := by
  simp [exhibitedKernelFactor]

/-- The rewritten factor is the monomial with exponent `contactKernelExponent`. -/
theorem T_pow_mul_E_pow_eq_monomial (d r h : ℕ) :
    (X (localT d) ^ r * X (localE d) ^ h : LocalPolynomial R d) =
      monomial (contactKernelExponent d r h) 1 := by
  simp [contactKernelExponent, X_pow_eq_monomial, monomial_mul]

private theorem localContactOrder_mono {a b : LocalVariable d →₀ ℕ}
    (hab : a ≤ b) : localContactOrder d a ≤ localContactOrder d b := by
  classical
  rw [localContactOrder, localContactOrder, Finsupp.weight_apply, Finsupp.weight_apply,
    Finsupp.sum_fintype _ _ (by simp), Finsupp.sum_fintype _ _ (by simp)]
  apply Finset.sum_le_sum
  intro v hv
  simpa [nsmul_eq_mul, mul_comm] using
    Nat.mul_le_mul_left (localContactWeight d v) (hab v)

/-- A multiple of `T^r E^h` has no coefficient below contact order `r + d*h`. -/
theorem projectLowContact_T_pow_mul_E_pow_mul_eq_zero
    (G : LocalPolynomial R d) (hcontact : m ≤ r + d * h) :
    projectLowContact (R := R) (d := d) m
      (X (localT d) ^ r * X (localE d) ^ h * G) = 0 := by
  rw [T_pow_mul_E_pow_eq_monomial, projectLowContact_eq_zero_iff]
  intro e he
  rw [MvPolynomial.coeff_monomial_mul']
  by_cases hle : contactKernelExponent d r h ≤ e
  · have : m ≤ localContactOrder d e := by
      calc
        m ≤ r + d * h := hcontact
        _ = localContactOrder d (contactKernelExponent d r h) := by simp
        _ ≤ localContactOrder d e := localContactOrder_mono hle
    omega
  · simp [hle]

/-- Multiplication by the exhibited factor, viewed as a linear map. -/
def exhibitedKernelMultiplier (d r h : ℕ) :
    LocalPolynomial R d →ₗ[R] LocalPolynomial R d where
  toFun G := exhibitedKernelFactor d r h * G
  map_add' G H := by rw [mul_add]
  map_smul' a G := by
    simp only [RingHom.id_apply, smul_eq_C_mul]
    ring

@[simp]
theorem exhibitedKernelMultiplier_apply (d r h : ℕ) (G : LocalPolynomial R d) :
    exhibitedKernelMultiplier (R := R) d r h G = exhibitedKernelFactor d r h * G :=
  rfl

/-- Every value of the exhibited multiplier lies in the enlarged map's kernel once its contact
threshold reaches `m`. -/
theorem exhibitedKernelMultiplier_mem_ker
    (G : LocalPolynomial R d) (hcontact : m ≤ r + d * h) :
    exhibitedKernelMultiplier (R := R) d r h G ∈
      LinearMap.ker (enlargedLocalConstraintMap (R := R) (d := d) m) := by
  rw [LinearMap.mem_ker, enlargedLocalConstraintMap, LinearMap.comp_apply,
    exhibitedKernelMultiplier_apply]
  change projectLowContact (R := R) (d := d) m
    (rewriteUToE d (exhibitedKernelFactor d r h * G)) = 0
  rw [map_mul, rewriteUToE_exhibitedKernelFactor]
  exact projectLowContact_T_pow_mul_E_pow_mul_eq_zero
    (rewriteUToE d G) hcontact

/-- The factor at the canonical threshold always reaches multiplicity when `d > 0` and `r < m`. -/
theorem canonicalExhibitedKernelMultiplier_mem_ker
    (hd : 0 < d) (hr : r < m) (G : LocalPolynomial R d) :
    exhibitedKernelMultiplier (R := R) d r (contactThreshold d m r) G ∈
      LinearMap.ker (enlargedLocalConstraintMap (R := R) (d := d) m) := by
  exact exhibitedKernelMultiplier_mem_ker G
    (multiplicity_le_add_mul_contactThreshold hd hr)

section Field

variable {F : Type*} [Field F]

private theorem exhibitedKernelFactor_ne_zero (d r h : ℕ) :
    exhibitedKernelFactor (R := F) d r h ≠ 0 := by
  intro hzero
  have himage := congrArg (rewriteUToE (R := F) d) hzero
  rw [rewriteUToE_exhibitedKernelFactor, map_zero, T_pow_mul_E_pow_eq_monomial] at himage
  have hcoeff := congrArg (MvPolynomial.coeff (contactKernelExponent d r h)) himage
  simp at hcoeff

/-- Over a field, multiplication by `T^r (E♯)^h` is injective.  This is the within-`K_r`
independence step; independence between different `r`-slices remains a separate `T`-adic lemma. -/
theorem exhibitedKernelMultiplier_injective (d r h : ℕ) :
    Function.Injective (exhibitedKernelMultiplier (R := F) d r h) := by
  intro G H hGH
  have hmul : exhibitedKernelFactor (R := F) d r h * (G - H) = 0 := by
    rw [mul_sub, sub_eq_zero]
    exact hGH
  rcases mul_eq_zero.mp hmul with hfactor | hdiff
  · exact (exhibitedKernelFactor_ne_zero d r h hfactor).elim
  · exact sub_eq_zero.mp hdiff

end Field

end ReedSolomon.HiddenDerivative
