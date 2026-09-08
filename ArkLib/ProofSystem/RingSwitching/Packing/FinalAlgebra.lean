/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.RingSwitching.Packing.Prelude

/-!
# Algebra for the final packing check

The column coordinates of the final tensor evaluate the exact public multiplier
used by relocation sumcheck. Once all variables have been fixed, the residual
cube sum is the product of that multiplier and the packed polynomial opening.
All identities are valid over commutative rings and use the explicit embeddings.
-/

open MvPolynomial Finset
noncomputable section
namespace RingSwitching
variable {κ : ℕ} {L K : Type} [CommRing L] [CommRing K] [Algebra K L]
    (P : RingSwitchingProfile K L κ)

/-- Column decomposition commutes with finite sums. -/
lemma columns_sum {ι : Type} (s : Finset ι) (f : ι → P.A) :
    P.decomposeColumns (∑ i ∈ s, f i) = ∑ i ∈ s, P.decomposeColumns (f i) := by
  let fcol : P.A →+ ((Fin κ → Fin 2) → L) :=
    { toFun := P.decomposeColumns
      map_zero' := P.decomposeColumns_zero
      map_add' := P.decomposeColumns_add }
  exact map_sum fcol f s

private lemma map_eqTilde {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (f : R →+* S) (x y : Fin n → R) :
    f (eqTilde x y) = eqTilde (fun i => f (x i)) (fun i => f (y i)) := by
  simp [eqTilde_eq_prod, map_prod]

/-- The final equality tensor expands in pure tensors indexed by the Boolean cube. -/
lemma final_tensor_expansion {n : ℕ} (r r' : Fin n → L) :
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
lemma compute_final_eq_value_eq_eval {ℓ ℓ' : ℕ} (h_l : ℓ = ℓ' + κ)
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
  rw [columns_sum]
  simp only [eqWeightedCoordSum, Finset.sum_apply, P.decomposeColumns_mul,
    compute_A_MLE, MLE_eval, compute_A_func, hbit, Algebra.smul_def]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  apply Finset.sum_congr rfl
  intro u _
  ring_nf
  rfl

private lemma eval_fix_last {n : ℕ} (H : MvPolynomial (Fin n) L) (r : Fin n → L)
    (x : Fin (n - (Fin.last n).val) → L) :
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

open Sumcheck.Structured in
/-- The final residual sum is exactly the multiplier times the packed opening value. -/
lemma final_project_sum [Nontrivial L]
    {ℓ ℓ' : ℕ} [NeZero ℓ] [NeZero ℓ'] (h_l : ℓ = ℓ' + κ)
    (ctx : RingSwitchingBaseContext κ L K ℓ P) (t : MultilinearPoly L ℓ')
    (r' : Fin ℓ' → L) :
    (∑ x ∈ (boolDomain L (ℓ' - (Fin.last ℓ').val)).cube,
      MvPolynomial.eval x (projectToMidSumcheckPolyWithParam ℓ'
        (RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l) ctx t (Fin.last ℓ') r').val) =
      compute_final_eq_value κ L K P ℓ ℓ' h_l ctx.t_eval_point r' ctx.r_batching *
        MvPolynomial.eval r' t.val := by
  classical
  have hpoint (x : Fin (ℓ' - (Fin.last ℓ').val) → L) :
      MvPolynomial.eval x (projectToMidSumcheckPolyWithParam ℓ'
        (RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l) ctx t (Fin.last ℓ') r').val =
      compute_final_eq_value κ L K P ℓ ℓ' h_l ctx.t_eval_point r' ctx.r_batching *
        MvPolynomial.eval r' t.val := by
    change MvPolynomial.eval x (fixFirstVariablesOfMQP ℓ' (Fin.last ℓ')
      (computeRoundPoly ℓ' (RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l) ctx t).val r') = _
    rw [eval_fix_last]
    simp only [computeRoundPoly, RingSwitching_SumcheckMultParam, Polynomial.aeval_X,
      map_mul, compute_final_eq_value_eq_eval]
  have hcard : (boolDomain L (ℓ' - (Fin.last ℓ').val)).cube.card = 1 := by
    change (boolDomain L (ℓ' - ℓ')).cube.card = 1
    rw [Nat.sub_self, SumcheckDomain.card_cube]
    simp
  simp only [hpoint, sum_const, hcard, one_nsmul]

open Sumcheck.Structured in
/-- Structural consistency at the last round is the exact final verifier equation. -/
lemma final_consistency [Nontrivial L]
    {ℓ ℓ' : ℕ} [NeZero ℓ] [NeZero ℓ'] (h_l : ℓ = ℓ' + κ)
    (stmt : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) (Fin.last ℓ'))
    (wit : RingSwitching.SumcheckWitness L ℓ' (Fin.last ℓ'))
    (hs : witnessStructuralInvariant κ L K P ℓ ℓ' h_l stmt wit) :
    sumcheckConsistencyProp (boolDomain L _) stmt.sumcheck_target wit.H ↔
      stmt.sumcheck_target = compute_final_eq_value κ L K P ℓ ℓ' h_l
        stmt.ctx.t_eval_point stmt.challenges stmt.ctx.r_batching *
        MvPolynomial.eval stmt.challenges wit.t'.val := by
  unfold witnessStructuralInvariant at hs
  unfold sumcheckConsistencyProp
  rw [hs, final_project_sum]

end RingSwitching
