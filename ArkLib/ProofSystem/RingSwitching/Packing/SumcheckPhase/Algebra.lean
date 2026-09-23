/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/
module

public import ArkLib.ProofSystem.RingSwitching.Packing.CoordinateLaws

/-!
# Algebra for the final packing sumcheck

The coordinate identity is conditional on separately proved coordinate laws. Polynomial
projection itself needs no coordinate assumption.
-/

@[expose] public section

noncomputable section

namespace RingSwitching.SumcheckPhase

open MvPolynomial Sumcheck.Structured
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

private theorem eqTilde_embedded {K L : Type} [CommRing K] [CommRing L] [Algebra K L]
    {κ n : ℕ} (P : RingSwitchingProfile K L κ) (x y : Fin n → L) :
    eqTilde (fun i => P.φ₀ (x i)) (fun i => P.φ₁ (y i)) =
      ∑ b : Fin n → Fin 2,
        P.φ₀ (eqTilde x (fun i => (b i : L))) *
          P.φ₁ (eqTilde (fun i => (b i : L)) y) := by
  rw [eqTilde_interpolate]
  apply Finset.sum_congr rfl
  intro b _
  have h₀ : (fun i => (b i : P.A)) = (fun i => P.φ₀ (b i : L)) := by
    funext i
    simp only [map_natCast]
  have h₁ : (fun i => (b i : P.A)) = (fun i => P.φ₁ (b i : L)) := by
    funext i
    simp only [map_natCast]
  rw [h₁, eqTilde_map]
  rw [← h₁, h₀, eqTilde_map]
  exact mul_comm _ _

private theorem rows_sum {K L : Type} [CommRing K] [CommRing L] [Algebra K L]
    {κ : ℕ} {P : RingSwitchingProfile K L κ} (laws : CoordinateLaws P)
    {J : Type*} (s : Finset J) (f : J → P.A) :
    P.decomposeRows (∑ j ∈ s, f j) = ∑ j ∈ s, P.decomposeRows (f j) := by
  classical
  have hz : P.decomposeRows 0 = 0 := by
    have h := laws.rows_add 0 0
    simpa using (add_left_cancel (show P.decomposeRows 0 + P.decomposeRows 0 =
      P.decomposeRows 0 + 0 by simpa using h.symm))
  induction s using Finset.cons_induction with
  | empty => simpa using hz
  | cons a s ha ih => simp only [Finset.sum_cons, laws.rows_add, ih]

/-- Evaluation of the public multiplier equals the final coordinate expression. -/
theorem compute_A_MLE_eval_eq_final_eq_value
    (κ : ℕ) [NeZero κ] (L K : Type) [CommRing L] [CommRing K] [Algebra K L]
    (P : RingSwitchingProfile K L κ) (laws : CoordinateLaws P)
    (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ'] (h_l : ℓ = ℓ' + κ)
    (r : Fin ℓ → L) (r' : Fin ℓ' → L) (rBatch : Fin κ → L) :
    (compute_A_MLE κ L K P ℓ'
      (getEvaluationPointSuffix κ L ℓ ℓ' h_l r) rBatch).val.eval r' =
      compute_final_eq_value κ L K P ℓ ℓ' h_l r r' rBatch := by
  classical
  let x : Fin ℓ' → L := getEvaluationPointSuffix κ L ℓ ℓ' h_l r
  have hbits (b : Fin ℓ' → Fin 2) :
      (fun i => if b i == 1 then (1 : L) else 0) = (fun i => (b i : L)) := by
    funext i
    generalize b i = z
    fin_cases z <;> simp
  unfold compute_A_MLE compute_final_eq_value compute_final_eq_tensor
  rw [MLE_eval, eqTilde_embedded]
  simp only [eqWeightedCoordSum]
  rw [rows_sum laws]
  simp only [Finset.sum_apply, laws.rows_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  simp only [compute_A_func, hbits, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  simp only [Algebra.smul_def]
  have hsuffix : getEvaluationPointSuffix κ L ℓ ℓ' h_l r =
      (fun i => r ⟨i.val + κ, by omega⟩) := rfl
  rw [hsuffix]
  ring

/-- Fixing every variable leaves evaluation at the fixed point. -/
theorem eval_fixFirstVariables_last {L : Type} [CommRing L] {n : ℕ}
    (H : MvPolynomial (Fin n) L) (r : Fin (Fin.last n : Fin (n + 1)) → L)
    (x : Fin (n - (Fin.last n : Fin (n + 1))) → L) :
    MvPolynomial.eval x (fixFirstVariablesOfMQP n (Fin.last n) H r) =
      MvPolynomial.eval r H := by
  induction H using MvPolynomial.induction_on with
  | C a => simp [fixFirstVariablesOfMQP]
  | add p q hp hq => simpa [fixFirstVariablesOfMQP] using congrArg₂ (· + ·) hp hq
  | mul_X p i hp =>
    simp only [fixFirstVariablesOfMQP, map_mul, rename_X] at hp ⊢
    rw [hp]
    congr 1
    have hi : finSumFinEquiv.symm (Fin.cast (show n = n + (n - n) by omega) i) =
        Sum.inl i := by
      apply finSumFinEquiv.injective
      simp only [Equiv.apply_symm_apply, finSumFinEquiv_apply_left]
      exact Fin.ext rfl
    simp only [Fin.val_last, Equiv.trans_apply, finCongr_apply, Equiv.sumComm_apply]
    rw [hi]
    simp

end RingSwitching.SumcheckPhase
