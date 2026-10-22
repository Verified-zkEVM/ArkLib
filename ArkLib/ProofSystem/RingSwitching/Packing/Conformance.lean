/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import ArkLib.ProofSystem.RingSwitching.Packing.BatchingPhase
public import ArkLib.ProofSystem.RingSwitching.Packing.SumcheckPhase

/-!
# DP24 conformance to shared packing

These library lemmas express the production DP24 batching relations, verifier checks and final
multiplier through `PackingData` and its prefix claim layout. They cover the shared DP24
construction. Binius reuses its batching verifier; Binius currently has separate sumcheck and
final verifier copies.
-/

@[expose] public section

open Module MvPolynomial RingSwitching Sumcheck.Structured

noncomputable section

namespace RingSwitching.Packing.Conformance

section SharedLayer

variable {K L : Type} [CommRing K] [CommRing L] [Algebra K L] {κ ℓ ℓ' : ℕ}
  (P : RingSwitchingProfile K L κ) (h_l : ℓ = ℓ' + κ)

/-- Prefix claim layout: the `κ` prefix variables are packed along the profile
basis and the `ℓ'` suffix variables are retained. -/
abbrev prefixLayout (ℓ' : ℕ) :
    Packing.ScalarHead.ClaimLayout (Packing.PackingData.ofBasis P.basis) ℓ' :=
  Packing.ScalarHead.packedPrefixLayout (Packing.PackingData.ofBasis P.basis) ℓ' κ (Equiv.refl _)

/-- The layout query of an evaluation point: its packed prefix and its retained suffix. -/
abbrev prefixQuery (r : Fin ℓ → L) : (prefixLayout P ℓ').Query :=
  (fun i => r ⟨i.val, by omega⟩, getEvaluationPointSuffix κ L ℓ ℓ' h_l r)

/-- The batching weights of a batching challenge: the equality weights of the Boolean cube. -/
abbrev batchingWeight (c : Fin κ → L) : (Fin κ → Fin 2) → L :=
  fun u => eqTilde (u : Fin κ → L) c

/-- The rows of a carrier are the shared slices of a packed polynomial exactly when its columns
are the opening values of the components: the row family is the shared transpose of the column
family. -/
theorem sliceRel_iff_openingClaimRel {m : ℕ} (z : P.A)
    (ps : (Fin κ → Fin 2) → K⦃≤ 1⦄[X Fin m]) (x : Fin m → L) :
    (P.decomposeRows z, (Packing.PackingData.ofBasis P.basis).packedMLE ps) ∈
        (Packing.PackingData.ofBasis P.basis).sliceRel m x ↔
      ((P.decomposeColumns z, x), ps) ∈
        (Packing.PackingData.ofBasis P.basis).openingClaimRel m := by
  rw [← P.transpose_decomposeColumns, ← Packing.PackingData.openingClaimRel_iff_sliceRel]

/-- A carrier is the honest tensor evaluation of the packed source exactly when its rows are the
shared slices of the `packedMLE` of the source's prefix-layout components. -/
theorem embedded_MLP_eval_packMLE_eq_iff_sliceRel (t : MultilinearPoly K ℓ) (r : Fin ℓ → L)
    (z : P.A) :
    embedded_MLP_eval κ L K P ℓ ℓ' h_l (packMLE κ L K ℓ ℓ' h_l P.basis t) r = z ↔
      (P.decomposeRows z, (Packing.PackingData.ofBasis P.basis).packedMLE
          ((prefixLayout P ℓ').components (sourceDimensionEquiv h_l t))) ∈
        (Packing.PackingData.ofBasis P.basis).sliceRel ℓ'
          ((prefixLayout P ℓ').point (prefixQuery P h_l r)) := by
  rw [packMLE_eq_packedPrefixLayout]
  exact embedded_MLP_eval_eq_iff_sliceRel P h_l _ r z

/-- A carrier is the honest tensor evaluation of the packed source exactly when its columns are
the opening values of the source's prefix-layout components at the retained point. -/
theorem embedded_MLP_eval_packMLE_eq_iff_openingClaimRel (t : MultilinearPoly K ℓ)
    (r : Fin ℓ → L) (z : P.A) :
    embedded_MLP_eval κ L K P ℓ ℓ' h_l (packMLE κ L K ℓ ℓ' h_l P.basis t) r = z ↔
      ((P.decomposeColumns z, (prefixLayout P ℓ').point (prefixQuery P h_l r)),
          (prefixLayout P ℓ').components (sourceDimensionEquiv h_l t)) ∈
        (Packing.PackingData.ofBasis P.basis).openingClaimRel ℓ' := by
  rw [embedded_MLP_eval_packMLE_eq_iff_sliceRel, sliceRel_iff_openingClaimRel]

/-- The column check says that the claim is the layout-weighted sum of the carrier's column
family. -/
theorem check_iff_layout_weight [DecidableEq L] (s : L) (r : Fin ℓ → L) (z : P.A) :
    performCheckOriginalEvaluation κ L K P ℓ ℓ' h_l s r z = true ↔
      s = ∑ v, (prefixLayout P ℓ').weight (prefixQuery P h_l r) v * P.decomposeColumns z v := by
  unfold performCheckOriginalEvaluation
  rw [decide_eq_true_iff, eqWeightedCoordSum_eq_sum]
  rfl

/-- The input relation through the shared layout: the packed polynomial is the shared
`packedMLE` of the source's prefix-layout components, the claim is the layout's weighted
reconstruction from the component evaluations at the retained point, and the packed polynomial
is compatible with the oracle statement. -/
theorem mem_batchingInputRelation_iff_layout (aOStmtIn : AbstractOStmtIn L ℓ')
    (stmt : BatchingStmtIn L ℓ) (oStmt : ∀ j, aOStmtIn.OStmtIn j) (wit : BatchingWitIn L K ℓ ℓ') :
    ((stmt, oStmt), wit) ∈ BatchingPhase.batchingInputRelation κ L K P ℓ ℓ' h_l aOStmtIn ↔
      wit.t' = (Packing.PackingData.ofBasis P.basis).packedMLE
          ((prefixLayout P ℓ').components (sourceDimensionEquiv h_l wit.t)) ∧
        stmt.original_claim = ∑ v,
          (prefixLayout P ℓ').weight (prefixQuery P h_l stmt.t_eval_point) v *
            aeval ((prefixLayout P ℓ').point (prefixQuery P h_l stmt.t_eval_point))
              ((prefixLayout P ℓ').components (sourceDimensionEquiv h_l wit.t) v).val ∧
        aOStmtIn.initialCompatibility ⟨wit.t', oStmt⟩ := by
  change wit.t' = _ ∧ stmt.original_claim = _ ∧ _ ↔ _
  rw [packMLE_eq_packedPrefixLayout, aeval_eq_sum_splitFirst h_l]
  rfl

/-- The statement the batching verifier outputs when its check accepts the carrier `z` and the
batching challenge is `c`: the accept branch of `BatchingPhase.oracleVerifier`, as
`oracleVerifier_eq_scalarRoundOracleVerifier` states. -/
abbrev acceptedStatement (stmt : BatchingStmtIn L ℓ) (z : P.A) (c : Fin κ → L) :
    Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) 0 :=
  BatchingPhase.batchingStmtOut κ L K P ℓ ℓ' stmt z c

/-- The production batching verifier is the shared check-then-update scalar-round verifier with
the column check and the accepted statement `acceptedStatement`. -/
theorem oracleVerifier_eq_scalarRoundOracleVerifier [DecidableEq L]
    (aOStmtIn : AbstractOStmtIn L ℓ') :
    BatchingPhase.oracleVerifier κ L K P ℓ ℓ' h_l (aOStmtIn := aOStmtIn) =
      scalarRoundOracleVerifier (Msg := P.A) (C := Fin κ → L)
        (fun stmt z => performCheckOriginalEvaluation κ L K P ℓ ℓ' h_l stmt.original_claim
          stmt.t_eval_point z)
        (acceptedStatement P) :=
  rfl

/-- At the accepted statement, the round-zero structural invariant says that the round polynomial
is the shared multiplier at the retained point and the batching weights, times the packed
polynomial. -/
theorem witnessStructuralInvariant_iff (stmt : BatchingStmtIn L ℓ) (z : P.A) (c : Fin κ → L)
    (wit : RingSwitching.SumcheckWitness L ℓ' 0) :
    witnessStructuralInvariant κ L K P ℓ ℓ' h_l (acceptedStatement P stmt z c) wit ↔
      wit.H.val = ((Packing.PackingData.ofBasis P.basis).multiplier
        ((prefixLayout P ℓ').point (prefixQuery P h_l stmt.t_eval_point))
          (batchingWeight c)).val * wit.t'.val := by
  unfold witnessStructuralInvariant
  simp only [projectToMidSumcheckPolyWithParam]
  -- `erw`: the fixed-prefix length is `↑(0 : Fin (ℓ' + 1))`, only definitionally `0`
  erw [fixFirstVariablesOfMQP_zero]
  simp only [computeRoundPoly, RingSwitching_SumcheckMultParam, compute_A_MLE_eq_multiplier,
    Polynomial.aeval_X]
  exact Iff.rfl

/-- For a structured round polynomial, round-zero sumcheck consistency of the accepted target says
that the batched rows of the carrier and the packed polynomial are in the shared
`sumcheckClaimRel` of the shared multiplier. -/
theorem sumcheckConsistencyProp_iff_sumcheckClaimRel [Nontrivial L] (stmt : BatchingStmtIn L ℓ)
    (z : P.A) (c : Fin κ → L) (wit : RingSwitching.SumcheckWitness L ℓ' 0)
    (hH : witnessStructuralInvariant κ L K P ℓ ℓ' h_l (acceptedStatement P stmt z c) wit) :
    sumcheckConsistencyProp (boolDomain L _) (compute_s0 κ L K P z c) wit.H ↔
      (∑ u, batchingWeight c u * P.decomposeRows z u, wit.t') ∈
        (Packing.PackingData.ofBasis P.basis).sumcheckClaimRel ℓ'
          ((prefixLayout P ℓ').point (prefixQuery P h_l stmt.t_eval_point)) (batchingWeight c) := by
  rw [witnessStructuralInvariant_iff] at hH
  unfold sumcheckConsistencyProp
  rw [hH, sum_cube_boolDomain, compute_s0_eq_sum]
  change _ = _ ↔ _ = _
  exact Iff.of_eq (congrArg₂ (· = ·) rfl (Finset.sum_congr rfl fun y _ => MvPolynomial.eval_mul))

/-- The column reconstruction check and round-zero sum-check relation hold exactly when the
packed witness is compatible, its round polynomial is `multiplier * t'`, its batched row value is
the sum-check claim, and its weighted columns reconstruct the original claim. -/
theorem batching_conforms [Nontrivial L] [DecidableEq L] (aOStmtIn : AbstractOStmtIn L ℓ')
    (stmt : BatchingStmtIn L ℓ) (oStmt : ∀ j, aOStmtIn.OStmtIn j)
    (z : P.A) (c : Fin κ → L) (wit : RingSwitching.SumcheckWitness L ℓ' 0) :
    (performCheckOriginalEvaluation κ L K P ℓ ℓ' h_l stmt.original_claim stmt.t_eval_point z =
          true ∧
        ((acceptedStatement P stmt z c, oStmt), wit) ∈
          sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn 0) ↔
      aOStmtIn.initialCompatibility ⟨wit.t', oStmt⟩ ∧
        wit.H.val = ((Packing.PackingData.ofBasis P.basis).multiplier
          ((prefixLayout P ℓ').point (prefixQuery P h_l stmt.t_eval_point))
            (batchingWeight c)).val * wit.t'.val ∧
        (∑ u, batchingWeight c u * P.decomposeRows z u, wit.t') ∈
          (Packing.PackingData.ofBasis P.basis).sumcheckClaimRel ℓ'
            ((prefixLayout P ℓ').point (prefixQuery P h_l stmt.t_eval_point)) (batchingWeight c) ∧
        stmt.original_claim = ∑ v,
          (prefixLayout P ℓ').weight (prefixQuery P h_l stmt.t_eval_point) v *
            P.decomposeColumns z v := by
  rw [check_iff_layout_weight]
  change _ ∧ (True ∧ witnessStructuralInvariant κ L K P ℓ ℓ' h_l _ wit ∧
    sumcheckConsistencyProp _ _ wit.H ∧ aOStmtIn.initialCompatibility ⟨wit.t', oStmt⟩) ↔ _
  rw [← witnessStructuralInvariant_iff]
  constructor
  · rintro ⟨hs, -, hH, hcons, hcomp⟩
    exact ⟨hcomp, hH,
      (sumcheckConsistencyProp_iff_sumcheckClaimRel P h_l stmt z c wit hH).1 hcons, hs⟩
  · rintro ⟨hcomp, hH, hclaim, hs⟩
    exact ⟨hs, trivial, hH,
      (sumcheckConsistencyProp_iff_sumcheckClaimRel P h_l stmt z c wit hH).2 hclaim, hcomp⟩

/-- The final sum-check step's equality value is the shared multiplier, at the same retained
point and batching weights as the batching phase, evaluated at the sum-check challenges. -/
theorem compute_final_eq_value_eq_multiplier (r : Fin ℓ → L) (r' : Fin ℓ' → L)
    (c : Fin κ → L) :
    compute_final_eq_value κ L K P ℓ ℓ' h_l r r' c =
      eval r' ((Packing.PackingData.ofBasis P.basis).multiplier
        ((prefixLayout P ℓ').point (prefixQuery P h_l r)) (batchingWeight c)).val := by
  rw [compute_final_eq_value_eq_eval, compute_A_MLE_eq_multiplier]
  rfl

/-- The final sum-check check of `SumcheckPhase.finalSumcheckVerifier`, through the shared
multiplier: the target is the multiplier at the challenges times the prover's final constant. -/
theorem final_check_iff_multiplier
    (stmt : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) (Fin.last ℓ'))
    (s' : L) :
    stmt.sumcheck_target = compute_final_eq_value κ L K P ℓ ℓ' h_l stmt.ctx.t_eval_point
        stmt.challenges stmt.ctx.r_batching * s' ↔
      stmt.sumcheck_target = eval stmt.challenges ((Packing.PackingData.ofBasis P.basis).multiplier
        ((prefixLayout P ℓ').point (prefixQuery P h_l stmt.ctx.t_eval_point))
          (batchingWeight stmt.ctx.r_batching)).val * s' := by
  rw [compute_final_eq_value_eq_multiplier]

end SharedLayer

end RingSwitching.Packing.Conformance

end
