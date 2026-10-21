/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ProofSystem.RingSwitching.Packing.Algebra
public import ArkLib.ProofSystem.RingSwitching.Packing.ProfileCoordinates

/-!
# Algebra for the final packing check

The row coordinates of the final equality tensor evaluate the exact public multiplier used by
the relocation sumcheck. All identities are valid over commutative rings and use the explicit
embeddings.
-/

@[expose] public section

open MvPolynomial Finset

noncomputable section

namespace RingSwitching

variable {κ : ℕ} {L K : Type} [CommRing L] [CommRing K] [Algebra K L]
    (P : RingSwitchingProfile K L κ)

/-- The final equality tensor expands in pure tensors indexed by the Boolean cube. -/
theorem final_tensor_expansion {n : ℕ} (r r' : Fin n → L) :
    eqTilde (fun i => P.φ₀ (r i)) (fun i => P.φ₁ (r' i)) =
      ∑ b : Fin n → Fin 2, P.φ₀ (eqTilde r (b : Fin n → L)) *
        P.φ₁ (eqTilde (b : Fin n → L) r') := by
  classical
  have hpoly := eq_MLE_of_degreeOf_le_one_of_eval_zeroOne_eq
    (fun b : Fin n → Fin 2 => eqTilde (fun i => P.φ₀ (r i)) (b : Fin n → P.A))
    (eqPolynomial (fun i => P.φ₀ (r i)))
    (eqPolynomial_degreeOf _) (fun _ => rfl)
  change MvPolynomial.eval (fun i => P.φ₁ (r' i)) _ = _
  rw [hpoly, MLE_eval]
  apply Finset.sum_congr rfl
  intro b _
  simp only [map_eqTilde, map_natCast]
  ring

/-- The final verifier computes the evaluation of the public sumcheck multiplier. -/
theorem compute_final_eq_value_eq_eval {ℓ ℓ' : ℕ} (h_l : ℓ = ℓ' + κ)
    (r : Fin ℓ → L) (r' : Fin ℓ' → L) (b : Fin κ → L) :
    compute_final_eq_value κ L K P ℓ ℓ' h_l r r' b =
      MvPolynomial.eval r' (compute_A_MLE κ L K P ℓ'
        (getEvaluationPointSuffix κ L ℓ ℓ' h_l r) b).val := by
  classical
  have hbit (z : Fin 2) : (if z == 1 then (1 : L) else 0) = (z : L) := by
    fin_cases z <;> simp
  unfold compute_final_eq_value compute_final_eq_tensor
  rw [final_tensor_expansion]
  dsimp only
  rw [P.decomposeRows_sum]
  simp only [eqWeightedCoordSum, Finset.sum_apply, P.decomposeRows_φ₀_mul_φ₁,
    compute_A_MLE, MLE_eval, compute_A_func, hbit, Algebra.smul_def]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  apply Finset.sum_congr rfl
  intro u _
  unfold getEvaluationPointSuffix
  ring

end RingSwitching
