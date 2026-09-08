/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.RingSwitching.Packing.ProfileLayout
import ArkLib.ProofSystem.RingSwitching.Packing.CheckedObservation

/-!
# Tensor batching in finite packing coordinates

The tensor message, row-coordinate scalar check, and column-coordinate batching target
are instances of finite-coordinate packing. The message and packed witness are preserved:
`CheckedObservation` gives reconstruction, and the structured round-zero relation agrees
with the coordinate sumcheck relation.
-/

noncomputable section

namespace RingSwitching

open Module MvPolynomial Sumcheck.Structured

variable {K L : Type} [CommRing K] [CommRing L] [Algebra K L]
  {κ ℓ ℓ' : ℕ} [NeZero κ] [NeZero ℓ] [NeZero ℓ']
  (P : RingSwitchingProfile K L κ) (h_l : ℓ = ℓ' + κ)

local instance : Algebra (Packing.sameAlgebra P.basis).P L :=
  inferInstanceAs (Algebra L L)

local instance : IsScalarTower K (Packing.sameAlgebra P.basis).P L :=
  inferInstanceAs (IsScalarTower K L L)

private theorem map_eqTilde {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (f : R →+* S) (x y : Fin n → R) :
    f (eqTilde x y) = eqTilde (fun i => f (x i)) (fun i => f (y i)) := by
  simp [eqTilde_eq_prod, map_prod]

omit [NeZero κ] [NeZero ℓ] [NeZero ℓ'] in
/-- The embedded evaluation is a finite tensor observation of the packed Boolean table. -/
theorem embedded_MLP_eval_eq_observation (p : MultilinearPoly L ℓ') (r : Fin ℓ → L) :
    embedded_MLP_eval κ L K P ℓ ℓ' h_l p r =
      ∑ y : Fin ℓ' → Fin 2,
        P.φ₀ (eqTilde (getEvaluationPointSuffix κ L ℓ ℓ' h_l r) (y : Fin ℓ' → L)) *
          P.φ₁ (eval (y : Fin ℓ' → L) p.val) := by
  classical
  have hp : (embedCoeffs P.φ₁ p).val =
      MLE (fun y : Fin ℓ' → Fin 2 => P.φ₁ (eval (y : Fin ℓ' → L) p.val)) := by
    apply eq_MLE_of_degreeOf_le_one_of_eval_zeroOne_eq
    · exact (mem_restrictDegree_iff_degreeOf_le _ _).mp (embedCoeffs P.φ₁ p).property
    · intro y
      have hpt : (y : Fin ℓ' → P.A) = fun i => P.φ₁ ((y : Fin ℓ' → L) i) :=
        funext fun i => (map_natCast P.φ₁ _).symm
      rw [hpt, embedCoeffs_eval]
  change eval (fun i => P.φ₀ (getEvaluationPointSuffix κ L ℓ ℓ' h_l r i))
    (embedCoeffs P.φ₁ p).val = _
  rw [hp, MLE_eval]
  apply Finset.sum_congr rfl
  intro y _
  rw [map_eqTilde]
  simp only [map_natCast]
  exact congrArg (fun x => x * P.φ₁ (eval (y : Fin ℓ' → L) p.val))
    (eqPolynomial_symm _ _)

omit [NeZero κ] [NeZero ℓ] [NeZero ℓ'] in
set_option backward.isDefEq.respectTransparency false in
/-- The embedded evaluation's columns satisfy the packed-slice relation. -/
theorem embedded_MLP_eval_sliceRel (p : MultilinearPoly L ℓ') (r : Fin ℓ → L) :
    (P.decomposeColumns (embedded_MLP_eval κ L K P ℓ ℓ' h_l p r), p) ∈
      (Packing.sameAlgebra P.basis).sliceRel ℓ'
        (getEvaluationPointSuffix κ L ℓ ℓ' h_l r) := by
  rw [embedded_MLP_eval_eq_observation]
  have h := P.columns_observation
    (fun y : Fin ℓ' → Fin 2 => eqTilde (getEvaluationPointSuffix κ L ℓ ℓ' h_l r)
      (y : Fin ℓ' → L)) (fun y => eval (y : Fin ℓ' → L) p.val)
  intro u
  exact congrFun h u

omit [NeZero κ] [NeZero ℓ] [NeZero ℓ'] in
set_option backward.isDefEq.respectTransparency false in
/-- The packed-slice relation characterizes the columns of the embedded evaluation. -/
theorem embedded_MLP_eval_eq_iff_sliceRel (p : MultilinearPoly L ℓ')
    (r : Fin ℓ → L) (z : P.A) :
    embedded_MLP_eval κ L K P ℓ ℓ' h_l p r = z ↔
      (P.decomposeColumns z, p) ∈ (Packing.sameAlgebra P.basis).sliceRel ℓ'
        (getEvaluationPointSuffix κ L ℓ ℓ' h_l r) := by
  constructor
  · rintro rfl
    exact embedded_MLP_eval_sliceRel P h_l p r
  · intro h
    apply P.columnEquiv.injective
    change P.decomposeColumns (embedded_MLP_eval κ L K P ℓ ℓ' h_l p r) = _
    funext u
    exact (embedded_MLP_eval_sliceRel P h_l p r u).trans (h u).symm

omit [NeZero κ] in
set_option backward.isDefEq.respectTransparency false in
/-- Row and column coordinates of a carrier satisfy family consistency. -/
theorem claimConsistent_decomposeRows_decomposeColumns (z : P.A) :
    (Packing.sameAlgebra P.basis).claimConsistent (P.decomposeRows z)
      (P.decomposeColumns z) :=
  ((Packing.sameAlgebra P.basis).claimConsistent_iff_transpose _ _).mpr (P.transpose_rows z)

omit [NeZero κ] [NeZero ℓ] [NeZero ℓ'] in
set_option backward.isDefEq.respectTransparency false in
/--
The embedded evaluation's rows equal the unpacked family evaluation of the same packed
polynomial.
-/
theorem rows_embedded_MLP_eval (p : MultilinearPoly L ℓ') (r : Fin ℓ → L)
    (i : Fin κ → Fin 2) :
    P.decomposeRows (embedded_MLP_eval κ L K P ℓ ℓ' h_l p r) i =
      aeval (getEvaluationPointSuffix κ L ℓ ℓ' h_l r)
        ((Packing.sameAlgebra P.basis).unpack p i).val :=
  (Packing.sameAlgebra P.basis).openingClaimRel_of_claimConsistent
    (claimConsistent_decomposeRows_decomposeColumns P _) (embedded_MLP_eval_sliceRel P h_l p r) i

omit [NeZero κ] [NeZero ℓ] [NeZero ℓ'] in
/-- The coordinate sum equals the sum weighted by Boolean equality polynomials. -/
theorem eqWeightedCoordSum_eq_sum (s : (Fin κ → Fin 2) → L) (r : Fin κ → L) :
    eqWeightedCoordSum κ L s r = ∑ i : Fin κ → Fin 2, eqTilde (i : Fin κ → L) r * s i := by
  have hbit (z : Fin 2) : (if z == 1 then (1 : L) else 0) = (z : L) := by
    fin_cases z <;> simp
  simp only [eqWeightedCoordSum, hbit]

omit [NeZero ℓ'] in
set_option backward.isDefEq.respectTransparency false in
/-- The row-coordinate check reconstructs the original polynomial evaluation. -/
theorem original_claim_eq_readback (t : MultilinearPoly K ℓ) (r : Fin ℓ → L) :
    aeval r t.val = eqWeightedCoordSum κ L
      (P.decomposeRows (embedded_MLP_eval κ L K P ℓ ℓ' h_l
        (packMLE κ L K ℓ ℓ' h_l P.basis t) r))
      (fun i => r ⟨i.val, by omega⟩) := by
  rw [eqWeightedCoordSum_eq_sum]
  simp_rw [rows_embedded_MLP_eval]
  rw [packMLE_eq_packedMLE, (Packing.sameAlgebra P.basis).unpack_packedMLE]
  exact aeval_eq_sum_splitFirst h_l t r

/-- Checked observation from the polynomial pack/unpack equivalence and tensor evaluation. -/
def packingObservation : Packing.CheckedObservation (Fin ℓ → L)
    (MultilinearPoly K ℓ) (MultilinearPoly L ℓ') P.A L where
  witnessEquiv :=
    { toFun := packMLE κ L K ℓ ℓ' h_l P.basis
      invFun := unpackMLE κ L K ℓ ℓ' h_l P.basis
      left_inv := unpackMLE_packMLE h_l P.basis
      right_inv := packMLE_unpackMLE h_l P.basis }
  honestMsg r p := embedded_MLP_eval κ L K P ℓ ℓ' h_l p r
  scalarEval r t := aeval r t.val
  observe r z := eqWeightedCoordSum κ L (P.decomposeRows z)
    (fun i => r ⟨i.val, by omega⟩)
  eval_eq_observe r t := original_claim_eq_readback P h_l t r

omit [NeZero ℓ'] in
/-- A related original claim passes the row-coordinate guard. -/
theorem performCheckOriginalEvaluation_honest [DecidableEq L]
    (t : MultilinearPoly K ℓ) (r : Fin ℓ → L) :
    performCheckOriginalEvaluation κ L K P ℓ ℓ' h_l (aeval r t.val) r
      (embedded_MLP_eval κ L K P ℓ ℓ' h_l (packMLE κ L K ℓ ℓ' h_l P.basis t) r) = true := by
  unfold performCheckOriginalEvaluation
  exact decide_eq_true ((packingObservation P h_l).honest_check (q := r) (w := t) rfl)

omit [NeZero ℓ'] in
/-- A tensor evaluation and an accepted row-coordinate guard imply the original polynomial claim. -/
theorem original_claim_of_check [DecidableEq L] (t : MultilinearPoly K ℓ)
    (r : Fin ℓ → L) (s : L) (z : P.A)
    (hz : embedded_MLP_eval κ L K P ℓ ℓ' h_l (packMLE κ L K ℓ ℓ' h_l P.basis t) r = z)
    (hc : performCheckOriginalEvaluation κ L K P ℓ ℓ' h_l s r z = true) :
    s = aeval r t.val := by
  have h := (packingObservation P h_l).readback (q := r)
    (w := packMLE κ L K ℓ ℓ' h_l P.basis t) (of_decide_eq_true hc) hz.symm
  change s = aeval r (unpackMLE κ L K ℓ ℓ' h_l P.basis
    (packMLE κ L K ℓ ℓ' h_l P.basis t)).val at h
  rw [unpackMLE_packMLE] at h
  exact h

omit [NeZero κ] [NeZero ℓ] [NeZero ℓ'] in
/-- The batching polynomial equals the multilinear coordinate multiplier. -/
theorem compute_A_MLE_eq_multiplier (r : Fin ℓ' → L) (c : Fin κ → L) :
    compute_A_MLE κ L K P ℓ' r c =
      (Packing.sameAlgebra P.basis).multiplier r
        (fun u : Fin κ → Fin 2 => eqTilde (u : Fin κ → L) c) := by
  have hbit (z : Fin 2) : (if z == 1 then (1 : L) else 0) = (z : L) := by
    fin_cases z <;> simp
  apply Subtype.ext
  change MLE _ = MLE _
  congr 1
  funext y
  erw [Packing.PackingData.bridge_apply]
  simp only [compute_A_func, hbit, Packing.sameAlgebra]
  rfl

omit [NeZero κ] [NeZero ℓ] [NeZero ℓ'] in
/-- The batching target is the weighted sum of the column family. -/
theorem compute_s0_eq_sum (z : P.A) (c : Fin κ → L) :
    compute_s0 κ L K P z c =
      ∑ u : Fin κ → Fin 2, eqTilde (u : Fin κ → L) c * P.decomposeColumns z u :=
  eqWeightedCoordSum_eq_sum (P.decomposeColumns z) c

omit [NeZero κ] [NeZero ℓ] [NeZero ℓ'] in
/-- The initial residual polynomial equals the product of the multiplier and packed polynomial. -/
theorem initial_project_val (ctx : RingSwitchingBaseContext κ L K ℓ P)
    (p : MultilinearPoly L ℓ') :
    (projectToMidSumcheckPolyWithParam ℓ'
      (RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l) ctx p 0 Fin.elim0).val =
      ((Packing.sameAlgebra P.basis).multiplier
        (getEvaluationPointSuffix κ L ℓ ℓ' h_l ctx.t_eval_point)
        (fun u : Fin κ → Fin 2 => eqTilde (u : Fin κ → L) ctx.r_batching)).val * p.val := by
  change fixFirstVariablesOfMQP ℓ' 0
    (computeRoundPoly ℓ' (RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l) ctx p).val
    Fin.elim0 = _
  rw [fixFirstVariablesOfMQP_zero]
  simp only [computeRoundPoly, RingSwitching_SumcheckMultParam, Polynomial.aeval_X,
    compute_A_MLE_eq_multiplier]
  rfl

omit [NeZero κ] [NeZero ℓ] [NeZero ℓ'] in
set_option backward.isDefEq.respectTransparency false in
/-- The initial structured cube sum equals the batched packed-polynomial sum. -/
theorem initial_project_sum [Nontrivial L]
    (ctx : RingSwitchingBaseContext κ L K ℓ P) (p : MultilinearPoly L ℓ') :
    (∑ x ∈ (boolDomain L ℓ').cube,
      eval x (projectToMidSumcheckPolyWithParam ℓ'
        (RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l) ctx p 0 Fin.elim0).val) =
      ∑ y : Fin ℓ' → Fin 2,
        eval (y : Fin ℓ' → L) ((Packing.sameAlgebra P.basis).multiplier
          (getEvaluationPointSuffix κ L ℓ ℓ' h_l ctx.t_eval_point)
          (fun u : Fin κ → Fin 2 => eqTilde (u : Fin κ → L) ctx.r_batching)).val *
            eval (y : Fin ℓ' → L) p.val := by
  rw [initial_project_val, SumcheckDomain.sum_cube]
  change (∑ y : Fin ℓ' → Fin 2, eval (fun i => boolEmbedding L (y i)) _) = _
  simp only [boolEmbedding_apply, map_mul]

omit [NeZero κ] [NeZero ℓ] [NeZero ℓ'] in
set_option backward.isDefEq.respectTransparency false in
/-- The batched sum relation is equivalent to consistency of the initial residual. -/
theorem initial_consistency_iff [Nontrivial L]
    (ctx : RingSwitchingBaseContext κ L K ℓ P) (p : MultilinearPoly L ℓ') (target : L) :
    sumcheckConsistencyProp (boolDomain L ℓ') target
      (projectToMidSumcheckPolyWithParam ℓ'
        (RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l) ctx p 0 Fin.elim0) ↔
      (target, p) ∈ (Packing.sameAlgebra P.basis).sumcheckClaimRel ℓ'
        (getEvaluationPointSuffix κ L ℓ ℓ' h_l ctx.t_eval_point)
        (fun u : Fin κ → Fin 2 => eqTilde (u : Fin κ → L) ctx.r_batching) := by
  rw [sumcheckConsistencyProp, initial_project_sum]
  rfl

omit [NeZero κ] [NeZero ℓ] [NeZero ℓ'] in
set_option backward.isDefEq.respectTransparency false in
/-- An honest slice family satisfies the initial residual target equation. -/
theorem initial_consistency_of_slices [Nontrivial L]
    (ctx : RingSwitchingBaseContext κ L K ℓ P) (p : MultilinearPoly L ℓ')
    (hs : (P.decomposeColumns ctx.s_hat, p) ∈ (Packing.sameAlgebra P.basis).sliceRel ℓ'
      (getEvaluationPointSuffix κ L ℓ ℓ' h_l ctx.t_eval_point)) :
    sumcheckConsistencyProp (boolDomain L ℓ') (compute_s0 κ L K P ctx.s_hat ctx.r_batching)
      (projectToMidSumcheckPolyWithParam ℓ'
        (RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l) ctx p 0 Fin.elim0) := by
  apply (initial_consistency_iff P h_l ctx p _).mpr
  rw [compute_s0_eq_sum]
  exact (Packing.sameAlgebra P.basis).sumcheckClaim_of_slices hs
    (fun u : Fin κ → Fin 2 => eqTilde (u : Fin κ → L) ctx.r_batching)

end RingSwitching

end
