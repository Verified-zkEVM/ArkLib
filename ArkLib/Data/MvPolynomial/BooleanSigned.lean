/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.Data.MvPolynomial.Multilinear
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.Ring

/-!
# Boolean and signed cube coordinates

The coordinate change `s = 2*x - 1`, with inverse `x = (s+1)/2`, transports the Boolean cube
and its multilinear interpolation to the signed cube when two is nonzero. Field equality is
explicit only in the executable inverse from a signed point to its Boolean row label.

Formal substitution in the canonical equality polynomials and table MLE gives the signed
kernel with normalization `2^(-n)`. Polynomial identities are proved by ring and substitution
algebra, rather than inferred from finite-field pointwise equality. The transformed table
polynomial remains multilinear and interpolates the same row labels at signed points.

Coordinate maps and the cube equivalence are executable. `halfShift` is an individually
noncomputable sparse-polynomial view; it does not introduce an interpolation backend. These
comparison results impose no odd-characteristic assumption on the generic Boolean protocols.

## References

* [Haböck, U., *Multivariate lookups based on logarithmic derivatives*][Hab22], Eq. (1) and
  Lemma 1 of the inspected March 31, 2023 author copy. Source-version metadata is recorded in
  `docs/kb/papers/Hab22.md`.
-/

@[expose] public section
open scoped BigOperators
namespace MvPolynomial
variable {σ F : Type*} [Field F]

/-- Change each Boolean coordinate to its signed coordinate by `x ↦ 2*x-1`. -/
def booleanToSigned (x : σ → F) : σ → F := fun i ↦ 2 * x i - 1
/-- Change each signed coordinate to `(s+1)/2`, inverse to the forward map when two is nonzero. -/
def signedToBoolean (s : σ → F) : σ → F := fun i ↦ (s i + 1) / 2

/-- The signed-to-Boolean coordinate change inverts the forward map when two is nonzero. -/
theorem signedToBoolean_booleanToSigned (htwo : (2 : F) ≠ 0) (x : σ → F) :
    signedToBoolean (booleanToSigned x) = x := by
  funext i
  simp only [signedToBoolean, booleanToSigned, sub_add_cancel]
  exact mul_div_cancel_left₀ _ htwo

/-- The forward coordinate change inverts division by two when two is nonzero. -/
theorem booleanToSigned_signedToBoolean (htwo : (2 : F) ≠ 0) (s : σ → F) :
    booleanToSigned (signedToBoolean s) = s := by
  funext i
  simp only [signedToBoolean, booleanToSigned, mul_div_cancel₀ _ htwo, add_sub_cancel_right]

private theorem neg_one_ne_one_of_two_ne_zero (htwo : (2 : F) ≠ 0) : (-1 : F) ≠ 1 := by
  intro h
  apply htwo
  calc
    (2 : F) = 1 - (-1) := by ring
    _ = 0 := by rw [h, sub_self]

/-- Convert Boolean row labels to signed cube points, using explicit field equality to recover
each label. Coordinates keep their original order and no field elements are enumerated. -/
def signedCubeEquiv [DecidableEq F] (htwo : (2 : F) ≠ 0) :
    (σ → Fin 2) ≃ {s : σ → F // ∀ i, s i = -1 ∨ s i = 1} where
  toFun u := ⟨booleanToSigned (u : σ → F), by
    intro i
    change 2 * (u i : F) - 1 = -1 ∨ 2 * (u i : F) - 1 = 1
    generalize u i = b
    fin_cases b <;> norm_num⟩
  invFun s i := if s.val i = -1 then 0 else 1
  left_inv u := by
    funext i
    change (if 2 * (u i : F) - 1 = -1 then 0 else 1) = u i
    generalize u i = b
    fin_cases b
    · norm_num
    · simp [show (2 : F) - 1 = 1 by ring,
        Ne.symm (neg_one_ne_one_of_two_ne_zero htwo)]
  right_inv s := by
    apply Subtype.ext
    funext i
    dsimp only [booleanToSigned]
    by_cases h : s.val i = -1
    · simp [h]
    · have hs : s.val i = 1 := (s.property i).resolve_left h
      rw [ite_eq_right h, hs]
      norm_num

private theorem kernel_half_unit {R : Type*} [CommRing R] (c s t : R) (h : 2 * c = 1) :
    (1 - c * (s + 1)) * (1 - c * (t + 1)) + (c * (s + 1)) * (c * (t + 1)) =
      c * (1 + s * t) := by
  apply sub_eq_zero.mp
  calc
    _ = (2 * c - 1) * (c * (s * t + s + t + 1) - 1) := by ring
    _ = 0 := by rw [sub_eq_zero.mpr h, zero_mul]

private theorem two_mul_C_inv_two (htwo : (2 : F) ≠ 0) :
    (2 : MvPolynomial σ F) * C ((2 : F)⁻¹) = 1 := by
  simpa only [map_mul, map_ofNat, map_one] using
    congrArg (C : F → MvPolynomial σ F) (mul_inv_cancel₀ htwo)

/-- The formal substitution of each variable by `(X_i+1)/2` in the sparse polynomial view. -/
noncomputable def halfShift (i : σ) : MvPolynomial σ F := C ((2 : F)⁻¹) * (X i + 1)

/-- Simultaneous substitution in both variable blocks gives the normalized signed kernel. -/
theorem bind₁_eqPolynomial'_halfShift [Fintype σ] (htwo : (2 : F) ≠ 0) :
    bind₁ (halfShift (F := F)) (eqPolynomial' (R := F) (σ := σ)) =
      C (((2 : F) ^ Fintype.card σ)⁻¹) *
        ∏ i : σ, (1 + X (.inl i) * X (.inr i)) := by
  classical
  simp only [eqPolynomial', map_prod, map_add, map_mul, map_sub, map_one,
    bind₁_X_right, halfShift]
  simp_rw [kernel_half_unit _ _ _ (two_mul_C_inv_two (σ := σ ⊕ σ) htwo)]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, ← map_pow, inv_pow]

/-- The scalar Boolean equality kernel becomes the signed product, including `2^(-n)`. -/
theorem eqTilde_signedToBoolean [Fintype σ] (htwo : (2 : F) ≠ 0) (s t : σ → F) :
    eqTilde (signedToBoolean s) (signedToBoolean t) =
      ((2 : F) ^ Fintype.card σ)⁻¹ * ∏ i, (1 + s i * t i) := by
  have hfactor (a b : F) :
      (a + 1) / 2 * ((b + 1) / 2) + (1 - (a + 1) / 2) * (1 - (b + 1) / 2) =
        (2 : F)⁻¹ * (1 + a * b) := by
    simp only [div_eq_inv_mul]
    rw [_root_.add_comm]
    exact kernel_half_unit _ _ _ (mul_inv_cancel₀ htwo)
  simp only [eqTilde, signedToBoolean, hfactor]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, inv_pow]

/-- Substituting the variable coordinates and converting the fixed point gives the formal
signed kernel with one affine factor per coordinate. -/
theorem bind₁_eqPolynomial_halfShift [Fintype σ] (htwo : (2 : F) ≠ 0) (t : σ → F) :
    bind₁ (halfShift (F := F)) (eqPolynomial (signedToBoolean t)) =
      C (((2 : F) ^ Fintype.card σ)⁻¹) * ∏ i : σ, (1 + C (t i) * X i) := by
  classical
  have hhalf (a : F) : (C ((a + 1) / 2) : MvPolynomial σ F) =
      C ((2 : F)⁻¹) * (C a + 1) := by
    simp only [div_eq_mul_inv, map_mul, map_add, map_one]
    ring
  simp only [eqPolynomial, singleEqPolynomial, signedToBoolean, map_prod, map_add, map_mul,
    map_sub, map_one, bind₁_C_right, bind₁_X_right, halfShift]
  simp_rw [hhalf, kernel_half_unit _ _ _ (two_mul_C_inv_two (σ := σ) htwo)]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, ← map_pow, inv_pow]

/-- Coordinate substitution of a Boolean table MLE is exactly its signed kernel expansion. -/
theorem bind₁_MLE_halfShift [Fintype σ] [DecidableEq σ] (htwo : (2 : F) ≠ 0)
    (rho : (σ → Fin 2) → F) :
    bind₁ (halfShift (F := F)) (MLE rho) =
      ∑ u : σ → Fin 2, C (((2 : F) ^ Fintype.card σ)⁻¹) *
        (∏ i : σ, (1 + C (booleanToSigned (u : σ → F) i) * X i)) * C (rho u) := by
  classical
  simp only [MLE, map_sum, map_mul, bind₁_C_right]
  apply Finset.sum_congr rfl
  intro u _
  have hkernel := bind₁_eqPolynomial_halfShift htwo (booleanToSigned (u : σ → F))
  rw [signedToBoolean_booleanToSigned htwo] at hkernel
  rw [hkernel]

/-- Evaluation commutes with the affine variable substitution in every characteristic. -/
theorem eval_bind₁_halfShift (s : σ → F) (p : MvPolynomial σ F) :
    eval s (bind₁ (halfShift (F := F)) p) = eval (signedToBoolean s) p := by
  change eval₂Hom (RingHom.id F) s (bind₁ (halfShift (F := F)) p) =
    eval₂Hom (RingHom.id F) (signedToBoolean s) p
  rw [eval₂Hom_bind₁]
  apply congrArg (fun point ↦ eval₂Hom (RingHom.id F) point p)
  funext i
  simp [halfShift, signedToBoolean, div_eq_inv_mul]

/-- The transformed polynomial interpolates the original table at its corresponding signed rows. -/
theorem eval_bind₁_halfShift_MLE_signed [Fintype σ] [DecidableEq σ]
    (htwo : (2 : F) ≠ 0) (rho : (σ → Fin 2) → F) (u : σ → Fin 2) :
    eval (booleanToSigned (u : σ → F)) (bind₁ (halfShift (F := F)) (MLE rho)) = rho u := by
  rw [eval_bind₁_halfShift, signedToBoolean_booleanToSigned htwo, MLE_eval_zeroOne]

/-- At any signed-coordinate field point, table interpolation uses the normalized signed kernel. -/
theorem MLE_eval_signedToBoolean [Fintype σ] [DecidableEq σ]
    (htwo : (2 : F) ≠ 0) (rho : (σ → Fin 2) → F) (s : σ → F) :
    eval (signedToBoolean s) (MLE rho) =
      ∑ u : σ → Fin 2, ((2 : F) ^ Fintype.card σ)⁻¹ *
        (∏ i : σ, (1 + booleanToSigned (u : σ → F) i * s i)) * rho u := by
  have h := congrArg (eval s) (bind₁_MLE_halfShift htwo rho)
  simpa only [eval_bind₁_halfShift, map_sum, map_mul, eval_C, map_prod, map_add,
    map_one, eval_X] using h

private theorem degreeOf_signedFactor_le [DecidableEq σ] (t : F) (i j : σ) :
    degreeOf j (1 + C t * X i) ≤ if j = i then 1 else 0 := by
  classical
  apply (degreeOf_add_le j _ _).trans
  apply max_le
  · simp
  · apply (degreeOf_mul_le j _ _).trans
    simp only [degreeOf_C, zero_add]
    by_cases h : j = i
    · simp [h]
    · simpa [h] using le_of_eq (degreeOf_X_of_ne (R := F) h)

private theorem degreeOf_signedProduct_le [Fintype σ] (t : σ → F) (j : σ) :
    degreeOf j (∏ i : σ, (1 + C (t i) * X i)) ≤ 1 := by
  classical
  calc
    _ ≤ ∑ i : σ, degreeOf j (1 + C (t i) * X i) := degreeOf_prod_le j _ _
    _ ≤ ∑ i : σ, if j = i then 1 else 0 :=
      Finset.sum_le_sum (fun i _ ↦ degreeOf_signedFactor_le (t i) i j)
    _ = 1 := by simp

/-- The transformed table polynomial has degree at most one in each coordinate. -/
theorem degreeOf_bind₁_MLE_halfShift_le [Fintype σ] [DecidableEq σ]
    (htwo : (2 : F) ≠ 0) (rho : (σ → Fin 2) → F) (j : σ) :
    degreeOf j (bind₁ (halfShift (F := F)) (MLE rho)) ≤ 1 := by
  classical
  rw [bind₁_MLE_halfShift htwo]
  apply (degreeOf_sum_le j _ _).trans
  apply Finset.sup_le
  intro u _
  have h := degreeOf_mul_le j
    (C (((2 : F) ^ Fintype.card σ)⁻¹) *
      ∏ i : σ, (1 + C (booleanToSigned (u : σ → F) i) * X i)) (C (rho u))
  simp only [degreeOf_C, add_zero] at h
  apply h.trans
  have h' := degreeOf_mul_le j (C (((2 : F) ^ Fintype.card σ)⁻¹))
    (∏ i : σ, (1 + C (booleanToSigned (u : σ → F) i) * X i))
  simp only [degreeOf_C, zero_add] at h'
  exact h'.trans (degreeOf_signedProduct_le _ _)

end MvPolynomial
