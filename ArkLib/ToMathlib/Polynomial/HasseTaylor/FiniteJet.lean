/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.RingTheory.Polynomial.DegreeLT

/-!
# Finite Hasse jets of univariate polynomials

This file packages Mathlib's Hasse derivatives into finite coordinate vectors.  The construction is
valid over arbitrary semirings and therefore does not silently introduce factorial denominators or
characteristic assumptions.

The main declarations are:

* `Polynomial.hasseCoeffAt`: the `i`-th Hasse derivative evaluated at a point;
* `Polynomial.hasseJet`: the first `m` Hasse coefficients at a point, as a linear map;
* `Polynomial.hasseDerivDegreeLT`: the degree-lowering Hasse derivative on `degreeLT`;
* `Polynomial.hasseJetEquiv`: over a commutative ring, finite jets give coordinates on
  polynomials of degree strictly less than `m`.
-/

namespace Polynomial

noncomputable section

variable {R : Type*}

section Semiring

variable [Semiring R]

/-- The `i`-th Hasse coefficient of `p` at `r`, packaged as a linear functional.

Equivalently, this is coefficient `i` of `p(X + r)`. -/
def hasseCoeffAt (r : R) (i : ℕ) : R[X] →ₗ[R] R :=
  (leval r).comp (hasseDeriv i)

@[simp]
theorem hasseCoeffAt_apply (r : R) (i : ℕ) (p : R[X]) :
    hasseCoeffAt r i p = (hasseDeriv i p).eval r :=
  rfl

/-- At the origin, Hasse coefficients are ordinary polynomial coefficients. -/
theorem hasseCoeffAt_zero_eq_coeff (i : ℕ) (p : R[X]) :
    hasseCoeffAt (0 : R) i p = p.coeff i := by
  rw [hasseCoeffAt_apply, ← taylor_coeff, taylor_zero]

/-- Hasse derivatives commute with mapping polynomial coefficients along a ring homomorphism. -/
@[simp]
theorem map_hasseDeriv {S : Type*} [Semiring S] (f : R →+* S) (i : ℕ) (p : R[X]) :
    (hasseDeriv i p).map f = hasseDeriv i (p.map f) := by
  ext n
  simp [hasseDeriv_coeff]

/-- Hasse coefficients are natural under coefficient-ring homomorphisms. -/
theorem map_hasseCoeffAt {S : Type*} [Semiring S] (f : R →+* S) (a : R) (i : ℕ)
    (p : R[X]) : f (hasseCoeffAt a i p) = hasseCoeffAt (f a) i (p.map f) := by
  rw [hasseCoeffAt_apply, hasseCoeffAt_apply, ← eval_map_apply, map_hasseDeriv]

/-- The first `m` Hasse coefficients of a polynomial at `r`.

Index `i : Fin m` records `D⁽ⁱ⁾ p(r)`, where `D⁽ⁱ⁾` is the Hasse derivative.  Thus
`m = 0` gives the empty jet and `m = 1` records only evaluation at `r`. -/
def hasseJet (m : ℕ) (r : R) : R[X] →ₗ[R] (Fin m → R) where
  toFun p i := hasseCoeffAt r i p
  map_add' p q := by
    ext i
    simp
  map_smul' c p := by
    ext i
    simp

@[simp]
theorem hasseJet_apply (m : ℕ) (r : R) (p : R[X]) (i : Fin m) :
    hasseJet m r p i = (hasseDeriv i p).eval r :=
  rfl

/-- Finite Hasse jets are natural under coefficient-ring homomorphisms. -/
theorem map_hasseJet {S : Type*} [Semiring S] (f : R →+* S) (m : ℕ) (a : R) (p : R[X]) :
    (fun i ↦ f (hasseJet m a p i)) = hasseJet m (f a) (p.map f) := by
  ext i
  exact map_hasseCoeffAt f a i p

@[simp]
theorem hasseJet_zero_apply (m : ℕ) (r : R) (p : R[X]) :
    hasseJet (m + 1) r p 0 = p.eval r := by
  simp

@[simp]
theorem hasseJet_zero (r : R) (p : R[X]) : hasseJet 0 r p = 0 :=
  Subsingleton.elim _ _

@[simp]
theorem hasseJet_one (r : R) (p : R[X]) : hasseJet 1 r p = fun _ ↦ p.eval r := by
  ext i
  simp [Fin.eq_zero i]

/-- Finite Hasse jets are precisely the initial coefficients of the Taylor shift. -/
theorem hasseJet_eq_taylor_coeff (m : ℕ) (r : R) (p : R[X]) (i : Fin m) :
    hasseJet m r p i = (taylor r p).coeff i := by
  rw [hasseJet_apply, taylor_coeff]

/-- A longer Hasse jet restricts definitionally to every shorter prefix. -/
theorem hasseJet_castLE {m n : ℕ} (h : m ≤ n) (r : R) (p : R[X]) (i : Fin m) :
    hasseJet n r p (Fin.castLE h i) = hasseJet m r p i :=
  rfl

/-- The first `m` entries of the order-`m+1` Hasse jet are the order-`m` jet. -/
theorem hasseJet_castSucc (m : ℕ) (r : R) (p : R[X]) (i : Fin m) :
    hasseJet (m + 1) r p i.castSucc = hasseJet m r p i :=
  rfl

/-- The jet through the natural degree of `p` detects whether `p` is zero.

This finite identity principle works over every semiring: its last coordinate is the leading
coefficient of `p`. -/
theorem hasseJet_natDegree_add_one_eq_zero_iff (r : R) (p : R[X]) :
    hasseJet (p.natDegree + 1) r p = 0 ↔ p = 0 := by
  constructor
  · intro h
    rw [← leadingCoeff_eq_zero]
    have hi := congrFun h ⟨p.natDegree, Nat.lt_add_one _⟩
    simpa [hasseJet_apply, hasseDeriv_natDegree_eq_C] using hi
  · rintro rfl
    exact LinearMap.map_zero _

/-- Taking the `k`-th Hasse derivative lowers a strict degree bound from `n + k` to `n`.

The additive indexing makes the boundary case explicit and avoids truncated-subtraction side
conditions. -/
theorem hasseDeriv_mem_degreeLT_add {n k : ℕ} {p : R[X]}
    (hp : p ∈ degreeLT R (n + k)) : hasseDeriv k p ∈ degreeLT R n := by
  rw [mem_degreeLT, degree_lt_iff_coeff_zero] at hp ⊢
  intro i hi
  rw [hasseDeriv_coeff, hp (i + k) (Nat.add_le_add_right hi k), mul_zero]

/-- Taking the `k`-th Hasse derivative lowers a strict degree bound `d` to `d - k`.

When `d ≤ k`, the target is `degreeLT R 0`, so this theorem also records that every such
derivative is zero. -/
theorem hasseDeriv_mem_degreeLT_sub {d k : ℕ} {p : R[X]} (hp : p ∈ degreeLT R d) :
    hasseDeriv k p ∈ degreeLT R (d - k) := by
  rw [mem_degreeLT, degree_lt_iff_coeff_zero] at hp ⊢
  intro i hi
  rw [hasseDeriv_coeff, hp (i + k) (by omega), mul_zero]

/-- The `k`-th Hasse derivative as a degree-lowering linear map on strict-degree submodules. -/
def hasseDerivDegreeLT (d k : ℕ) : degreeLT R d →ₗ[R] degreeLT R (d - k) :=
  (hasseDeriv k).domRestrict (degreeLT R d) |>.codRestrict
    (degreeLT R (d - k)) fun p ↦ hasseDeriv_mem_degreeLT_sub p.2

@[simp]
theorem hasseDerivDegreeLT_apply_coe (d k : ℕ) (p : degreeLT R d) :
    (hasseDerivDegreeLT d k p : R[X]) = hasseDeriv k p :=
  rfl

end Semiring

section CommSemiring

variable [CommSemiring R]

/-- The product rule for Hasse coefficients, with no characteristic assumptions. -/
theorem hasseCoeffAt_mul (r : R) (n : ℕ) (p q : R[X]) :
    hasseCoeffAt r n (p * q) =
      ∑ ij ∈ Finset.antidiagonal n,
        hasseCoeffAt r ij.1 p * hasseCoeffAt r ij.2 q := by
  simp only [hasseCoeffAt_apply, hasseDeriv_mul, eval_finsetSum, eval_mul]

/-- Iterating Hasse derivatives introduces the expected binomial coefficient. -/
theorem hasseCoeffAt_hasseDeriv (r : R) (i k : ℕ) (p : R[X]) :
    hasseCoeffAt r i (hasseDeriv k p) =
      (Nat.choose (i + k) i : R) * hasseCoeffAt r (i + k) p := by
  change (hasseDeriv i (hasseDeriv k p)).eval r = _
  have h := LinearMap.congr_fun (hasseDeriv_comp (R := R) i k) p
  rw [LinearMap.comp_apply, LinearMap.smul_apply] at h
  rw [h]
  simp

/-- Shifting a polynomial translates the point at which its Hasse jet is evaluated. -/
theorem hasseCoeffAt_taylor (r s : R) (i : ℕ) (p : R[X]) :
    hasseCoeffAt s i (taylor r p) = hasseCoeffAt (s + r) i p := by
  simp only [hasseCoeffAt_apply]
  rw [← taylor_coeff, ← taylor_coeff, taylor_taylor]

/-- Componentwise form of `hasseCoeffAt_taylor` for finite jets. -/
theorem hasseJet_taylor (m : ℕ) (r s : R) (p : R[X]) :
    hasseJet m s (taylor r p) = hasseJet m (s + r) p := by
  ext i
  exact hasseCoeffAt_taylor r s i p

end CommSemiring

section CommRing

variable [CommRing R]

/-- Hasse jets at `r` are linear coordinates on polynomials of degree strictly less than `m`.

This is the usual coefficient equivalence after applying Mathlib's degree-preserving Taylor
automorphism. -/
noncomputable def hasseJetEquiv (m : ℕ) (r : R) : degreeLT R m ≃ₗ[R] (Fin m → R) :=
  (taylorLinearEquiv r m).trans (degreeLTEquiv R m)

@[simp]
theorem hasseJetEquiv_apply (m : ℕ) (r : R) (p : degreeLT R m) (i : Fin m) :
    hasseJetEquiv m r p i = hasseJet m r p i := by
  rw [hasseJet_eq_taylor_coeff]
  change (taylor r (p : R[X])).coeff i = _
  rfl

/-- Two degree-`< m` polynomials with the same order-`m` Hasse jet are equal. -/
theorem hasseJet_injective_on_degreeLT (m : ℕ) (r : R) {p q : degreeLT R m}
    (h : hasseJet m r p = hasseJet m r q) : p = q := by
  apply (hasseJetEquiv m r).injective
  ext i
  simpa using congrFun h i

/-- Every vector of `m` Hasse coefficients occurs for a unique polynomial of degree `< m`. -/
theorem existsUnique_degreeLT_hasseJet (m : ℕ) (r : R) (v : Fin m → R) :
    ∃! p : degreeLT R m, hasseJet m r p = v := by
  let p := (hasseJetEquiv m r).symm v
  refine ⟨p, ?_, ?_⟩
  · ext i
    simpa using congrFun ((hasseJetEquiv m r).apply_symm_apply v) i
  · intro q hq
    exact hasseJet_injective_on_degreeLT m r (hq.trans (by
      ext i
      simpa using congrFun ((hasseJetEquiv m r).apply_symm_apply v).symm i))

end CommRing

end

end Polynomial
