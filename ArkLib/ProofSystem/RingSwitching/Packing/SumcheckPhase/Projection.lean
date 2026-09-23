/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/
module

public import ArkLib.ProofSystem.RingSwitching.Packing.Prelude
public import ArkLib.ProofSystem.Binius.BinaryBasefold.Basic.IndexAndSumcheck

/-! # Polynomial projection bridges for packing sumcheck -/

@[expose] public section

namespace RingSwitching.SumcheckPhase

open MvPolynomial Sumcheck.Structured
open scoped Polynomial

section FixFirstBridge
variable {L' : Type} [CommRing L'] {ℓ'' : ℕ}
lemma mvPoly_fixFirst_eq_bbf_fixFirst (v : Fin (ℓ'' + 1))
    (poly : MvPolynomial (Fin ℓ'') L') (challenges : Fin v → L') :
    MvPolynomial.fixFirstVariablesOfMQP ℓ'' v poly challenges =
      Binius.BinaryBasefold.fixFirstVariablesOfMQP ℓ'' v poly challenges := by
  rw [Binius.BinaryBasefold.fixFirstVariablesOfMQP_eq_bind₁]
  let subst : Fin ℓ'' → MvPolynomial (Fin (ℓ'' - v)) L' := fun j =>
    if hj : j.val < v.val then MvPolynomial.C (challenges ⟨j.val, hj⟩)
    else MvPolynomial.X (⟨j.val - v, by omega⟩ : Fin (ℓ'' - v))
  have hX : ∀ j : Fin ℓ'',
      MvPolynomial.fixFirstVariablesOfMQP ℓ'' v (MvPolynomial.X j) challenges =
        MvPolynomial.bind₁ subst (MvPolynomial.X j) := by
    intro j
    rw [MvPolynomial.bind₁_X_right]
    unfold subst MvPolynomial.fixFirstVariablesOfMQP
    dsimp only
    rw [MvPolynomial.rename_X]
    by_cases hj : j.val < v.val
    · have hsym : (finSumFinEquiv (m := ↑v) (n := ℓ'' - ↑v)).symm (Fin.cast (by omega) j)
          = Sum.inl (⟨j.val, hj⟩ : Fin ↑v) := by
        rw [Equiv.symm_apply_eq, finSumFinEquiv_apply_left]; apply Fin.ext; simp
      have hmap : (((finCongr (by omega : ℓ'' = ↑v + (ℓ'' - ↑v))).trans
          ((finSumFinEquiv (m := ↑v) (n := ℓ'' - ↑v)).symm.trans (Equiv.sumComm _ _))) j)
          = Sum.inr (⟨j.val, hj⟩ : Fin ↑v) := by
        simp only [Equiv.trans_apply, finCongr_apply, Equiv.sumComm_apply, hsym, Sum.swap_inl]
      rw [hmap]
      simp only [MvPolynomial.sumAlgEquiv_X_inr, MvPolynomial.map_C,
        MvPolynomial.eval_X, hj, ↓reduceDIte]
    · have hsym : (finSumFinEquiv (m := ↑v) (n := ℓ'' - ↑v)).symm (Fin.cast (by omega) j)
          = Sum.inr (⟨j.val - v, by omega⟩ : Fin (ℓ'' - ↑v)) := by
        rw [Equiv.symm_apply_eq, finSumFinEquiv_apply_right]
        apply Fin.ext; simp only [Fin.natAdd_mk, Fin.val_cast]; omega
      have hmap : (((finCongr (by omega : ℓ'' = ↑v + (ℓ'' - ↑v))).trans
          ((finSumFinEquiv (m := ↑v) (n := ℓ'' - ↑v)).symm.trans (Equiv.sumComm _ _))) j)
          = Sum.inl (⟨j.val - v, by omega⟩ : Fin (ℓ'' - ↑v)) := by
        simp only [Equiv.trans_apply, finCongr_apply, Equiv.sumComm_apply, hsym, Sum.swap_inr]
      rw [hmap]
      simp only [MvPolynomial.sumAlgEquiv_X_inl, MvPolynomial.map_X,
        hj, ↓reduceDIte]
  induction poly using MvPolynomial.induction_on with
  | C a =>
    unfold MvPolynomial.fixFirstVariablesOfMQP
    simp only [MvPolynomial.rename_C, MvPolynomial.sumAlgEquiv_C_inl,
      MvPolynomial.map_C, MvPolynomial.eval_C, MvPolynomial.bind₁_C_right]
  | add p q hp hq =>
    have h_add : MvPolynomial.fixFirstVariablesOfMQP ℓ'' v (p + q) challenges =
        MvPolynomial.fixFirstVariablesOfMQP ℓ'' v p challenges +
          MvPolynomial.fixFirstVariablesOfMQP ℓ'' v q challenges := by
      unfold MvPolynomial.fixFirstVariablesOfMQP; simp only [map_add]
    rw [h_add, hp, hq, map_add]
  | mul_X p j hp =>
    have h_mul : MvPolynomial.fixFirstVariablesOfMQP ℓ'' v (p * MvPolynomial.X j) challenges =
        MvPolynomial.fixFirstVariablesOfMQP ℓ'' v p challenges *
          MvPolynomial.fixFirstVariablesOfMQP ℓ'' v (MvPolynomial.X j) challenges := by
      unfold MvPolynomial.fixFirstVariablesOfMQP; simp only [map_mul]
    rw [h_mul, hp, hX, map_mul]


end FixFirstBridge

lemma getRoundProverFinalOutput_H {L : Type} [CommRing L]
    {n : ℕ} [NeZero n] {Context ι : Type} {OStmt : ι → Type} (i : Fin n)
    (stmt : Statement (L := L) (ℓ := n) Context i.castSucc)
    (oStmt : ∀ j, OStmt j) (wit : SumcheckWitness L n i.castSucc)
    (h : L⦃≤ 2⦄[X]) (r : L) :
    (getRoundProverFinalOutput n Context 2 i (stmt, oStmt, wit, h, r)).2.H.val =
      (Binius.BinaryBasefold.projectToNextSumcheckPoly n i wit.H r).val := by
  unfold getRoundProverFinalOutput Binius.BinaryBasefold.projectToNextSumcheckPoly
  dsimp only
  rw [mvPoly_fixFirst_eq_bbf_fixFirst]
  rfl

variable (κ : ℕ) (L K : Type) [CommRing L] [Nontrivial L] [CommRing K]
  [Algebra K L] (P : RingSwitchingProfile K L κ) (ℓ ℓ' : ℕ) [NeZero ℓ']
  (h_l : ℓ = ℓ' + κ)

omit [Nontrivial L] [NeZero ℓ'] in
lemma projectToMidSumcheckPolyWithParam_succ_ringswitching
    (ctx : RingSwitchingBaseContext κ L K ℓ P) (t : Sumcheck.Structured.MultilinearPoly L ℓ')
    (i : Fin ℓ') (challenges : Fin i.castSucc → L) (r_i' : L) :
    (Binius.BinaryBasefold.projectToNextSumcheckPoly (L := L) (ℓ := ℓ') (i := i)
      (Hᵢ := projectToMidSumcheckPolyWithParam (L := L) (ℓ := ℓ')
        (param := RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l)
        (ctx := ctx) (t := t) (i := i.castSucc) (challenges := challenges)) (rᵢ := r_i')).val =
    (projectToMidSumcheckPolyWithParam (L := L) (ℓ := ℓ')
      (param := RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l)
      (ctx := ctx) (t := t) (i := i.succ)
      (challenges := Fin.snoc challenges r_i')).val := by
  -- `computeRoundPoly` for the ring-switching param (combinator `X`) has value
  -- `(multpoly ctx).val * t.val = (computeInitialSumcheckPoly t (multpoly ctx)).val`.
  set m := (RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l).multpoly ctx with hm
  have h_H0 :
      (Sumcheck.Structured.computeRoundPoly (L := L) (ℓ := ℓ')
        (RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l) ctx t).val =
      (Binius.BinaryBasefold.computeInitialSumcheckPoly (L := L) (ℓ := ℓ') t m).val := by
    simp only [Sumcheck.Structured.computeRoundPoly,
      Binius.BinaryBasefold.computeInitialSumcheckPoly, RingSwitching_SumcheckMultParam,
      Polynomial.aeval_X, hm, mul_comm]
  -- Both `WithParam` projections agree with the identity-combinator `projectToMidSumcheckPoly`
  -- at their respective indices (same `H₀`, same `fixFirstVariablesOfMQP`).
  have h_mid_eq : ∀ (j : Fin (ℓ' + 1)) (ch : Fin j → L),
      (projectToMidSumcheckPolyWithParam (L := L) (ℓ := ℓ')
        (param := RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l)
        (ctx := ctx) (t := t) (i := j) (challenges := ch)).val =
      (Binius.BinaryBasefold.projectToMidSumcheckPoly (L := L) (ℓ := ℓ') t m j ch).val := by
    intro j ch
    change MvPolynomial.fixFirstVariablesOfMQP ℓ' ⟨j.val, by omega⟩
        (Sumcheck.Structured.computeRoundPoly (L := L) (ℓ := ℓ')
          (RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l) ctx t).val ch = _
    rw [mvPoly_fixFirst_eq_bbf_fixFirst, h_H0]
    rfl
  rw [h_mid_eq i.succ (Fin.snoc challenges r_i')]
  rw [show projectToMidSumcheckPolyWithParam ℓ'
      (RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l) ctx t i.castSucc challenges =
      Binius.BinaryBasefold.projectToMidSumcheckPoly ℓ' t m i.castSucc challenges
      from Subtype.ext (h_mid_eq i.castSucc challenges)]
  exact congrArg Subtype.val
    (Binius.BinaryBasefold.projectToMidSumcheckPoly_succ
      (L := L) (ℓ := ℓ') t m i challenges r_i').symm

omit [NeZero ℓ'] in
lemma getSumcheckRoundPoly_bool_eq (i : Fin ℓ')
    (h : L⦃≤ 2⦄[X Fin (ℓ' - ↑i.castSucc)]) :
    Sumcheck.Structured.getSumcheckRoundPoly ℓ' (boolDomain L ℓ') i h =
      Binius.BinaryBasefold.getSumcheckRoundPoly ℓ' (boolEmbedding L) i h := by
  apply Subtype.ext
  simp only [Sumcheck.Structured.getSumcheckRoundPoly,
    Binius.BinaryBasefold.getSumcheckRoundPoly, boolDomain,
    SumcheckDomain.drop_uniform, SumcheckDomain.cube_uniform]
  rfl

end RingSwitching.SumcheckPhase
