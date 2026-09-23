/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/
module

public import ArkLib.ProofSystem.RingSwitching.Packing.Prelude

/-!
# Concrete tensor-coordinate identities for ring switching

The final public multiplier is the batched row decomposition of the equality tensor.
These identities use the actual tensor-product basis, rather than assuming that arbitrary
reconstruction maps provide faithful coordinates.
-/

@[expose] public section

noncomputable section

namespace RingSwitching

open MvPolynomial TensorProduct
open scoped BigOperators

private theorem eqTilde_map {R S : Type*} [CommRing R] [CommRing S]
    {n : ℕ} (f : R →+* S) (x y : Fin n → R) :
    eqTilde (fun i => f (x i)) (fun i => f (y i)) = f (eqTilde x y) := by
  simp only [eqTilde_eq_prod, map_prod, map_add, map_mul, map_sub, map_one]

private theorem eqTilde_interpolate {R : Type*} [CommRing R] {n : ℕ}
    (x y : Fin n → R) :
    eqTilde x y = ∑ b : Fin n → Fin 2, eqTilde (fun i => (b i : R)) y *
      eqTilde x (fun i => (b i : R)) := by
  have h := eq_MLE_of_degreeOf_le_one_of_eval_zeroOne_eq
    (fun b : Fin n → Fin 2 => eqTilde x (fun i => (b i : R)))
    (eqPolynomial x) (eqPolynomial_degreeOf x) (fun _ => rfl)
  change eval y (eqPolynomial x) = _
  rw [h, MLE_eval]

private theorem eqTilde_tensor {K L : Type} [Field K] [Field L] [Algebra K L]
    {n : ℕ} (x y : Fin n → L) :
    eqTilde (fun i => φ₀ L K (x i)) (fun i => φ₁ L K (y i)) =
      ∑ b : Fin n → Fin 2,
        eqTilde x (fun i => (b i : L)) ⊗ₜ[K] eqTilde (fun i => (b i : L)) y := by
  rw [eqTilde_interpolate]
  apply Finset.sum_congr rfl
  intro b _
  have h₀ : (fun i => (b i : TensorAlgebra K L)) =
      (fun i => φ₀ L K (b i : L)) := by
    funext i
    simp only [map_natCast]
  have h₁ : (fun i => (b i : TensorAlgebra K L)) =
      (fun i => φ₁ L K (b i : L)) := by
    funext i
    simp only [map_natCast]
  rw [h₁, eqTilde_map]
  rw [← h₁, h₀, eqTilde_map]
  simp only [φ₀, φ₁, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

private theorem tensor_rows_sum {K L : Type} [Field K] [Field L] [Algebra K L]
    {ι J : Type*} [Fintype J] (β : Module.Basis ι K L)
    (x y : J → L) (i : ι) :
    decompose_tensor_algebra_rows (K := K) (L := L) β (∑ j, x j ⊗ₜ[K] y j) i =
      ∑ j, β.repr (x j) i • y j := by
  let rightAlgebra : Algebra L (L ⊗[K] L) := Algebra.TensorProduct.rightAlgebra
  let := rightAlgebra.toModule
  simp only [decompose_tensor_algebra_rows, map_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro j _
  exact Module.Basis.baseChangeRight_repr_tmul β (x j) (y j) i

/-- For the concrete tensor profile, the final equality check evaluates the public multiplier.
The row coordinates decompose the original-point factor, leaving the sumcheck-point factor
as the scalar multiplying each coordinate. -/
theorem compute_A_MLE_eval_eq_final_eq_value_tensor
    (κ : ℕ) [NeZero κ] (L K : Type) [Field L] [Field K] [Algebra K L]
    (β : Module.Basis (Fin κ → Fin 2) K L)
    (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ'] (h_l : ℓ = ℓ' + κ)
    (r : Fin ℓ → L) (r' : Fin ℓ' → L) (rBatch : Fin κ → L) :
    (compute_A_MLE κ L K (tensorProductProfile κ K L β) ℓ'
      (getEvaluationPointSuffix κ L ℓ ℓ' h_l r) rBatch).val.eval r' =
      compute_final_eq_value κ L K (tensorProductProfile κ K L β)
        ℓ ℓ' h_l r r' rBatch := by
  classical
  let x : Fin ℓ' → L := getEvaluationPointSuffix κ L ℓ ℓ' h_l r
  have hbits (b : Fin ℓ' → Fin 2) :
      (fun i => if b i == 1 then (1 : L) else 0) = (fun i => (b i : L)) := by
    funext i
    generalize b i = z
    fin_cases z <;> simp
  have hTensor :
      compute_final_eq_tensor κ L K (tensorProductProfile κ K L β) ℓ ℓ' h_l r r' =
        ∑ b : Fin ℓ' → Fin 2,
          eqTilde x (fun i => (b i : L)) ⊗ₜ[K] eqTilde (fun i => (b i : L)) r' :=
    eqTilde_tensor x r'
  unfold compute_A_MLE compute_final_eq_value
  rw [MLE_eval, hTensor]
  change (∑ b : Fin ℓ' → Fin 2, eqTilde (fun i => (b i : L)) r' *
    compute_A_func κ L K (tensorProductProfile κ K L β) ℓ' x rBatch b) =
    ∑ u : Fin κ → Fin 2,
      eqTilde (fun i => if u i == 1 then (1 : L) else 0) rBatch *
        decompose_tensor_algebra_rows (K := K) (L := L) β
          (∑ b : Fin ℓ' → Fin 2,
            eqTilde x (fun i => (b i : L)) ⊗ₜ[K]
              eqTilde (fun i => (b i : L)) r') u
  simp_rw [tensor_rows_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  simp only [compute_A_func, hbits, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  simp only [Algebra.smul_def]
  ring

end RingSwitching
