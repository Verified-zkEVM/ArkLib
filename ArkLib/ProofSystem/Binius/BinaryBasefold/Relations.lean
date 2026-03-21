 /-
 Copyright (c) 2026 ArkLib Contributors. All rights reserved.
 Released under Apache 2.0 license as described in the file LICENSE.
 Authors: Chung Thai Nguyen, Quang Dao
 -/

 import ArkLib.ProofSystem.Binius.BinaryBasefold.Basic

 /-! ## Binary Basefold relations and bad-event layer -/

 noncomputable section
 namespace Binius.BinaryBasefold

 open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
   Binius.BinaryBasefold
 open scoped NNReal
 open ReedSolomon Code BerlekampWelch
 open Finset AdditiveNTT Polynomial MvPolynomial Nat Matrix

 variable {r : ℕ} [NeZero r]
 variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
 variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
   [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
 variable [Algebra 𝔽q L]
 variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
   [h_β₀_eq_1 : Fact (β 0 = 1)]
 variable {ℓ 𝓡 ϑ : ℕ} [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ]
 variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}
 variable {𝓑 : Fin 2 ↪ L}
 variable [hdiv : Fact (ϑ ∣ ℓ)]

 section SecurityRelations
 /-- Helper to get the challenges for folding.
 k is the starting index of the challenge slice. ϑ is the number of steps. -/
 def getFoldingChallenges (i : Fin (ℓ + 1)) (challenges : Fin i → L)
     (k : ℕ) (h : k + ϑ ≤ i) : Fin ϑ → L :=
   fun cId => challenges ⟨k + cId, by omega⟩

 omit [NeZero r] [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
   [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ] hdiv in
 lemma getFoldingChallenges_init_succ_eq (i : Fin ℓ)
     (j : Fin (toOutCodewordsCount ℓ ϑ i.castSucc)) (challenges : Fin i.succ → L)
     (h : ↑j * ϑ + ϑ ≤ ↑i.castSucc) :
     getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ) i.castSucc (Fin.init challenges) (↑j * ϑ)
       (h := by omega) =
     getFoldingChallenges (r := r) (𝓡 := 𝓡) i.succ challenges (↑j * ϑ)
       (h := by simp only [Fin.val_succ]; simp only [Fin.val_castSucc] at h; omega) := by
   unfold getFoldingChallenges
   ext cId
   simp only [Fin.init, Fin.val_castSucc, Fin.castSucc_mk, Fin.val_succ]

 def getNextOracle (i : Fin (ℓ + 1))
     (oStmt : ∀ j, (OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i) j)
     (j : Fin (toOutCodewordsCount ℓ ϑ i)) (hj : j.val + 1 < toOutCodewordsCount ℓ ϑ i)
     {destDomainIdx : Fin r} (h_destDomainIdx : destDomainIdx = j.val * ϑ + ϑ) :
     OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destDomainIdx :=
   let res := oStmt ⟨j.val + 1, hj⟩
   have h : j.val * ϑ + ϑ = (j.val + 1) * ϑ := by rw [Nat.add_mul, one_mul]
   have h_lt : (↑j + 1) * ϑ < r := by omega
   have h_eq : destDomainIdx = ⟨(↑j + 1) * ϑ, h_lt⟩ :=
     Fin.eq_of_val_eq (by simp only; omega)
   fun y => res (cast (by rw [h_eq]) y)

 /-- Folding consistency for round i (where i is the oracleIdx) -/
 def oracleFoldingConsistencyProp (i : Fin (ℓ + 1)) (challenges : Fin i → L)
     (oStmt : ∀ j, (OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i) j) : Prop :=
   (∀ (j : Fin (toOutCodewordsCount ℓ ϑ i)) (hj : j.val + 1 < toOutCodewordsCount ℓ ϑ i),
     have h_k_bound := oracle_block_k_bound (ℓ := ℓ) (ϑ := ϑ) (i := i) (j := j)
     have h_k_next_le_i := oracle_block_k_next_le_i (ℓ := ℓ) (ϑ := ϑ) (i := i) (j := j) (hj := hj)
     let destIdx : Fin r := ⟨oraclePositionToDomainIndex (positionIdx := j) + ϑ, by
       have h_le := oracle_index_add_steps_le_ℓ ℓ ϑ (i := i) (j := j)
       dsimp only [oraclePositionToDomainIndex]
       omega
     ⟩
     isCompliant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
       (i := ⟨oraclePositionToDomainIndex (positionIdx := j), by omega⟩) (steps := ϑ)
       (destIdx := destIdx) (by rfl) (by
         dsimp only [destIdx]; simp only [oracle_index_add_steps_le_ℓ])
       (f_i := oStmt ⟨j.val, by exact j.isLt⟩)
       (f_i_plus_steps := getNextOracle 𝔽q β i oStmt j hj (destDomainIdx := destIdx)
         (h_destDomainIdx := by rfl))
       (challenges := getFoldingChallenges (r := r) (𝓡 := 𝓡) i challenges (k := j.val * ϑ)
         (h := h_k_next_le_i))
   )

 def BBF_eq_multiplier (r : Fin ℓ → L) : MultilinearPoly L ℓ :=
   ⟨MvPolynomial.eqPolynomial r, by simp only [eqPolynomial_mem_restrictDegree]⟩

 def BBF_SumcheckMultiplierParam : SumcheckMultiplierParam L ℓ (SumcheckBaseContext L ℓ) :=
   { multpoly := fun ctx => BBF_eq_multiplier ctx.t_eval_point }

 /-- This condition ensures that the folding witness `f` is properly generated from `t` -/
 def getMidCodewords {i : Fin (ℓ + 1)} (t : L⦃≤ 1⦄[X Fin ℓ])
     (challenges : Fin i → L) : (sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩) → L) :=
   let P₀ : L⦃< 2^ℓ⦄[X] := polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (h_ℓ := by omega)
     (a := fun ω => t.val.eval (bitsOfIndex ω))
   let f₀ : (sDomain 𝔽q β h_ℓ_add_R_rate 0) → L := fun x => P₀.val.eval x.val
   let fᵢ := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
     (i := 0) (steps := i) (destIdx := ⟨i, by omega⟩)
     (h_destIdx := by simp only [Fin.coe_ofNat_eq_mod, zero_mod, zero_add]) (h_destIdx_le := by simp only; omega)
     (f := f₀)
     (r_challenges := challenges)
   fun x => fᵢ x

 lemma getMidCodewords_succ (t : L⦃≤ 1⦄[X Fin ℓ]) (i : Fin ℓ)
     (challenges : Fin i.castSucc → L) (r_i' : L) :
     (getMidCodewords 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
       (i := i.succ) (t := t) (challenges := Fin.snoc challenges r_i')) =
     (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i, by omega⟩) (steps := 1)
       (destIdx := ⟨i.succ, by omega⟩) (h_destIdx := by simp only [Fin.val_succ])
       (h_destIdx_le := by simp only; omega)
       (f := getMidCodewords 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i.castSucc)
       (t := t) (challenges := challenges)) (r_challenges := fun _ => r_i'))
     := by
   sorry

 section FoldStepLogic
 variable {Context : Type} {mp : SumcheckMultiplierParam L ℓ Context}

 def foldPrvState (i : Fin ℓ) : Fin (2 + 1) → Type := fun
   | ⟨0, _⟩ => (Statement (L := L) Context i.castSucc ×
     (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j) ×
     Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
   | ⟨1, _⟩ => Statement (L := L) Context i.castSucc ×
     (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j) ×
     Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc × L⦃≤ 2⦄[X]
   | _ => Statement (L := L) Context i.castSucc ×
     (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j) ×
     Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc × L⦃≤ 2⦄[X] × L

 @[reducible]
 noncomputable def getFoldProverFinalOutput (i : Fin ℓ)
     (finalPrvState : foldPrvState 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
       i 2 (Context := Context)) :
   ((Statement (L := L) Context i.succ × ((j : Fin (toOutCodewordsCount ℓ ϑ i.castSucc)) →
     OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j))
       × Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
   := by
   let (stmtIn, oStmtIn, witIn, h_i, r_i') := finalPrvState
   let newSumcheckTarget : L := h_i.val.eval r_i'
   let stmtOut : Statement (L := L) Context i.succ := {
     ctx := stmtIn.ctx,
     sumcheck_target := newSumcheckTarget,
     challenges := Fin.snoc stmtIn.challenges r_i'
   }
   let currentSumcheckPoly : L⦃≤ 2⦄[X Fin (ℓ - i)] := witIn.H
   let f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
     (domainIdx := ⟨i, by omega⟩) := witIn.f
   let challenges : Fin (1) → L := fun cId => r_i'
   let fᵢ_succ := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
     (i := ⟨i, by omega⟩) (steps := 1) (destIdx := ⟨i.succ, by omega⟩)
     (h_destIdx := by simp only [Fin.val_succ]) (h_destIdx_le := by simp only; omega)
     f_i challenges
   simp only at fᵢ_succ
   let witOut : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i.succ := by
     let projectedH := projectToNextSumcheckPoly (L := L) (ℓ := ℓ)
       (i := i) (Hᵢ := witIn.H) (rᵢ := r_i')
     exact {
       t := witIn.t,
       H := projectedH,
       f := fᵢ_succ
     }
   have h_succ_val : i.succ.val = i.val + 1 := rfl
   let oStmtOut : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
     (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j := oStmtIn
   exact ⟨⟨stmtOut, oStmtOut⟩, witOut⟩

 @[reducible]
 def foldProverComputeMsg (i : Fin ℓ)
     (witIn : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc) :
     L⦃≤ 2⦄[X] :=
   getSumcheckRoundPoly ℓ 𝓑 (i := i) witIn.H

 @[reducible]
 def foldVerifierCheck (i : Fin ℓ)
     (stmtIn : Statement (L := L) Context i.castSucc)
     (msg0 : L⦃≤ 2⦄[X]) : Prop :=
   msg0.val.eval (𝓑 0) + msg0.val.eval (𝓑 1) = stmtIn.sumcheck_target

 @[reducible]
 def foldVerifierStmtOut (i : Fin ℓ)
     (stmtIn : Statement (L := L) Context i.castSucc)
     (msg0 : L⦃≤ 2⦄[X])
     (chal1 : L) :
     Statement (L := L) Context i.succ :=
   {
     ctx := stmtIn.ctx,
     sumcheck_target := msg0.val.eval chal1,
     challenges := Fin.snoc stmtIn.challenges chal1
   }

 end FoldStepLogic

 section SumcheckContextIncluded_Relations
 variable {Context : Type} {mp : SumcheckMultiplierParam L ℓ Context}

 /-- This condition ensures that the witness polynomial `H` has the
 correct structure `eq(...) * t(...)`. At the commitment steps (in commitment rounds),
 wit.f is exactly the same as the last oracle being sent. -/
 def witnessStructuralInvariant {i : Fin (ℓ + 1)} (stmt : Statement (L := L) Context i)
     (wit : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) : Prop :=
   wit.H = projectToMidSumcheckPoly ℓ wit.t (m:=mp.multpoly stmt.ctx) i stmt.challenges ∧
   wit.f = getMidCodewords 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) wit.t
     stmt.challenges

 /-- Sumcheck consistency: the claimed sum equals the actual polynomial evaluation sum -/
 def sumcheckConsistencyProp {k : ℕ} (sumcheckTarget : L) (H : L⦃≤ 2⦄[X Fin (k)]) : Prop :=
   sumcheckTarget = ∑ x ∈ (univ.map 𝓑) ^ᶠ (k), H.val.eval x

 lemma firstOracleWitnessConsistencyProp_unique (t₁ t₂ : MultilinearPoly L ℓ)
     (f₀ : sDomain 𝔽q β h_ℓ_add_R_rate 0 → L)
     (h₁ : firstOracleWitnessConsistencyProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t₁ f₀)
     (h₂ : firstOracleWitnessConsistencyProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t₂ f₀) :
     t₁ = t₂ := by
   sorry

 noncomputable def foldingBadEventAtBlock
     (stmtIdx : Fin (ℓ + 1)) (oracleIdx : OracleFrontierIndex stmtIdx)
     (oStmt : ∀ j, (OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)
       (i := oracleIdx.val) j)) (challenges : Fin stmtIdx → L)
     (j : Fin (toOutCodewordsCount ℓ ϑ oracleIdx.val)) : Prop :=
   have h_ϑ: ϑ > 0 := by exact pos_of_neZero ϑ
   let curOracleDomainIdx : Fin r := ⟨oraclePositionToDomainIndex (positionIdx := j), by omega⟩
   if hj: curOracleDomainIdx + ϑ ≤ stmtIdx.val then
     let f_k := oStmt j
     let destIdx : Fin r := ⟨oraclePositionToDomainIndex (positionIdx := j) + ϑ, by
       have h_le := oracle_index_add_steps_le_ℓ ℓ ϑ (i := oracleIdx.val) (j := j)
       dsimp only [oraclePositionToDomainIndex]
       omega
     ⟩
     Binius.BinaryBasefold.foldingBadEvent 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
       (i := curOracleDomainIdx) (steps := ϑ) (destIdx := destIdx) (by rfl) (by dsimp only [destIdx]; simp only [oracle_index_add_steps_le_ℓ]) (f_i := f_k) (r_challenges :=
         getFoldingChallenges (r := r) (𝓡 := 𝓡) stmtIdx challenges (k := j.val * ϑ) (h := by
         simp only [curOracleDomainIdx] at hj
         exact hj
       ))
   else False

 lemma foldingBadEventAtBlock_snoc_castSucc_eq (i : Fin ℓ)
     (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
       (ϑ := ϑ) (i := i.castSucc) j)
     (challenges : Fin i.castSucc → L) (r_new : L)
     (j : Fin (toOutCodewordsCount ℓ ϑ i.castSucc))
     (hj_le : j.val * ϑ + ϑ ≤ i.castSucc.val) :
     foldingBadEventAtBlock 𝔽q β (stmtIdx := i.succ)
       (oracleIdx := OracleFrontierIndex.mkFromStmtIdxCastSuccOfSucc i)
       (oStmt := oStmt)
       (challenges := Fin.snoc challenges r_new) j =
     foldingBadEventAtBlock 𝔽q β (stmtIdx := i.castSucc)
       (oracleIdx := OracleFrontierIndex.mkFromStmtIdx i.castSucc)
       (oStmt := oStmt)
       (challenges := challenges) j := by
   unfold foldingBadEventAtBlock
   simp only [OracleFrontierIndex.val_mkFromStmtIdxCastSuccOfSucc,
     Fin.val_castSucc, OracleFrontierIndex.val_mkFromStmtIdx,
     Fin.val_succ]
   have h_guard_succ : oraclePositionToDomainIndex (positionIdx := j) + ϑ ≤ i.val + 1 := by
     simp only [Fin.val_castSucc] at ⊢ hj_le
     omega
   have h_guard_cast : oraclePositionToDomainIndex (positionIdx := j) + ϑ ≤ i.val := by
     simp only [Fin.val_castSucc] at ⊢ hj_le
     omega
   simp only [h_guard_succ, h_guard_cast, ↓reduceDIte]
   congr 1
   unfold getFoldingChallenges
   ext cId
   simp only [Fin.snoc]
   split
   · rfl
   · exfalso
     rename_i h_lt
     simp only [not_lt] at h_lt
     simp only at h_guard_cast
     omega

 attribute [irreducible] foldingBadEventAtBlock

 open Classical in
 def blockBadEventExistsProp
     (stmtIdx : Fin (ℓ + 1)) (oracleIdx : OracleFrontierIndex stmtIdx)
     (oStmt : ∀ j, (OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)
       (i := oracleIdx.val) j)) (challenges : Fin stmtIdx → L) : Prop :=
   ∃ j, foldingBadEventAtBlock 𝔽q β (stmtIdx := stmtIdx) (oracleIdx := oracleIdx)
     (oStmt := oStmt) (challenges := challenges) j

 def incrementalBadEventExistsProp
     (stmtIdx : Fin (ℓ + 1)) (oracleIdx : OracleFrontierIndex stmtIdx)
     (oStmt : ∀ j, (OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)
       (i := oracleIdx.val) j)) (challenges : Fin stmtIdx → L) : Prop :=
   ∃ j : Fin (toOutCodewordsCount ℓ ϑ oracleIdx.val),
     let curOracleDomainIdx : Fin r := ⟨oraclePositionToDomainIndex (positionIdx := j), by omega⟩
     let k : ℕ := min ϑ (stmtIdx.val - curOracleDomainIdx.val)
     have h1 := oracle_index_add_steps_le_ℓ ℓ ϑ (i := oracleIdx.val) (j := j)
     have h2 : ℓ + 𝓡 < r := h_ℓ_add_R_rate
     have _ : 𝓡 > 0 := pos_of_neZero 𝓡
     let midIdx : Fin r := ⟨curOracleDomainIdx.val + k, by omega⟩
     let destIdx : Fin r := ⟨curOracleDomainIdx.val + ϑ, by
       dsimp only [oraclePositionToDomainIndex, curOracleDomainIdx]; omega⟩
     Binius.BinaryBasefold.incrementalFoldingBadEvent 𝔽q β
       (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
       (block_start_idx := curOracleDomainIdx) (k := k)
       (h_k_le := Nat.min_le_left ϑ (stmtIdx.val - curOracleDomainIdx.val))
       (midIdx := midIdx) (destIdx := destIdx) (h_midIdx := rfl) (h_destIdx := rfl)
       (h_destIdx_le := oracle_index_add_steps_le_ℓ ℓ ϑ (i := oracleIdx.val) (j := j))
       (f_block_start := oStmt j)
       (r_challenges := fun cId => challenges ⟨curOracleDomainIdx.val + cId.val, by
         have h_k_le_stmt : k ≤ stmtIdx.val - curOracleDomainIdx.val :=
           Nat.min_le_right ϑ (stmtIdx.val - curOracleDomainIdx.val)
         have h_cId_lt_k : cId.val < k := cId.isLt
         omega
       ⟩)

 lemma badEventExistsProp_iff_incrementalBadEventExistsProp_last
     (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
     (challenges : Fin (Fin.last ℓ) → L) :
     blockBadEventExistsProp 𝔽q β
       (stmtIdx := Fin.last ℓ) (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ))
       (oStmt := oStmt) (challenges := challenges) ↔
     incrementalBadEventExistsProp 𝔽q β
       (stmtIdx := Fin.last ℓ) (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ))
       (oStmt := oStmt) (challenges := challenges) := by
   constructor
   · intro h_bad
     rcases h_bad with ⟨j, h_j_bad⟩
     refine ⟨j, ?_⟩
     sorry
   · intro h_inc_bad
     rcases h_inc_bad with ⟨j, h_j_inc_bad⟩
     refine ⟨j, ?_⟩
     sorry

 def badSumcheckEventProp (r_i' : L) (h_i h_star : L⦃≤ 2⦄[X]) :=
   h_i ≠ h_star ∧ h_i.val.eval r_i' = h_star.val.eval r_i'
 section SingleStepRelationPreservationLemmas

 section FoldStepPreservationLemmas
 variable {Context : Type} {mp : SumcheckMultiplierParam L ℓ Context}

 end FoldStepPreservationLemmas

 lemma incrementalBadEventExistsProp_relay_preserved (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i)
     (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)
     (challenges : Fin i.succ → L) :
     incrementalBadEventExistsProp 𝔽q β i.succ (OracleFrontierIndex.mkFromStmtIdxCastSuccOfSucc i)
       oStmt challenges ↔
     incrementalBadEventExistsProp 𝔽q β i.succ (OracleFrontierIndex.mkFromStmtIdx i.succ)
       (mapOStmtOutRelayStep 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR oStmt) challenges := by
   sorry

 lemma oracleFoldingConsistencyProp_relay_preserved (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i)
     (challenges : Fin i.succ.val → L)
     (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j) :
     oracleFoldingConsistencyProp 𝔽q β (i := i.castSucc) (Fin.init challenges) oStmt ↔
     oracleFoldingConsistencyProp 𝔽q β (i := i.succ) challenges
       (mapOStmtOutRelayStep 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR oStmt) := by
   sorry

 section CommitStepPreservationLemmas

 lemma incrementalBadEventExistsProp_commit_step_backward (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i)
     (oStmtIn : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)
     (newOracle : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
       (domainIdx := ⟨i.val + 1, by omega⟩))
     (challenges : Fin i.succ → L) :
     incrementalBadEventExistsProp 𝔽q β i.succ (OracleFrontierIndex.mkFromStmtIdx i.succ)
       (snoc_oracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_destIdx := rfl)
         oStmtIn newOracle) challenges →
     incrementalBadEventExistsProp 𝔽q β i.succ (OracleFrontierIndex.mkFromStmtIdxCastSuccOfSucc i)
       oStmtIn challenges := by
   sorry

 lemma oracleFoldingConsistencyProp_commit_step_backward (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i)
     (challenges : Fin i.succ.val → L)
     (oStmtIn : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)
     (newOracle : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
       (domainIdx := ⟨i.val + 1, by omega⟩)) :
     oracleFoldingConsistencyProp 𝔽q β (i := i.succ) challenges
       (snoc_oracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_destIdx := rfl)
         oStmtIn newOracle) →
     oracleFoldingConsistencyProp 𝔽q β (i := i.castSucc) (Fin.init challenges) oStmtIn := by
   sorry

 end CommitStepPreservationLemmas

 end SingleStepRelationPreservationLemmas
 /-- Before V's challenge of the `i-th` foldStep, we ignore the bad-folding-event
 of the `i-th` oracle if any and enable it after the next V's challenge, i.e. one
 round later. This is for the purpose of reasoning its RBR KS properly.
 -/
 def masterKStateProp (stmtIdx : Fin (ℓ + 1))
     (oracleIdx : OracleFrontierIndex stmtIdx)
     (stmt : Statement (L := L) Context stmtIdx)
     (wit : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtIdx)
     (oStmt : ∀ j, (OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ
       (i := oracleIdx.val) j))
     (localChecks : Prop := True) : Prop :=
   let structural := witnessStructuralInvariant 𝔽q β (mp := mp) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmt wit
   let initial := firstOracleWitnessConsistencyProp 𝔽q β wit.t (getFirstOracle 𝔽q β oStmt)
   let oracleFoldingConsistency: Prop := oracleFoldingConsistencyProp 𝔽q β (i := oracleIdx.val)
     (challenges := Fin.take (m := oracleIdx.val) (v := stmt.challenges)
     (h := by simp only [Fin.val_fin_le, OracleFrontierIndex.val_le_i]))
     (oStmt := oStmt)
   let badEventExists := incrementalBadEventExistsProp 𝔽q β stmtIdx oracleIdx
     (challenges := stmt.challenges) (oStmt := oStmt)
   let good := localChecks ∧ structural ∧ initial ∧ oracleFoldingConsistency
   badEventExists ∨ good

 def roundRelationProp (i : Fin (ℓ + 1))
     (input : (Statement (L := L) Context i ×
       (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i j)) ×
       Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    : Prop :=
   let stmt := input.1.1
   let oStmt := input.1.2
   let wit := input.2
   let sumCheckConsistency: Prop := sumcheckConsistencyProp (𝓑 := 𝓑) stmt.sumcheck_target wit.H
   masterKStateProp (mp := mp) 𝔽q β
     (stmtIdx := i) (oracleIdx := OracleFrontierIndex.mkFromStmtIdx i) stmt wit oStmt
     (localChecks := sumCheckConsistency)

 /-- A modified version of roundRelationProp (i+1) -/
 def foldStepRelOutProp (i : Fin ℓ)
     (input : (Statement (L := L) Context i.succ ×
       (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)) ×
       Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    : Prop :=
   let stmt := input.1.1
   let oStmt := input.1.2
   let wit := input.2
   let sumCheckConsistency: Prop := sumcheckConsistencyProp (𝓑 := 𝓑) stmt.sumcheck_target wit.H
   masterKStateProp (mp := mp) 𝔽q β
     (stmtIdx := i.succ) (oracleIdx := OracleFrontierIndex.mkFromStmtIdxCastSuccOfSucc i)
     stmt wit oStmt
       (localChecks := sumCheckConsistency)

 def finalSumcheckStepOracleConsistencyProp {h_le : ϑ ≤ ℓ}
   (stmtOut : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
   (oStmtOut : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ
     (Fin.last ℓ) j) : Prop :=
     let j := getLastOraclePositionIndex (ℓ := ℓ) (ϑ := ϑ) (Fin.last ℓ)
     let k := j.val * ϑ
     have h_k: k = ℓ - ϑ := by
       dsimp only [k, j]
       rw [getLastOraclePositionIndex_last]
       rw [Nat.sub_mul, Nat.one_mul]
       rw [Nat.div_mul_cancel (hdiv.out)]
     let f_k := oStmtOut j
     let challenges : Fin ϑ → L := fun cId => stmtOut.challenges ⟨k + cId, by
       simp only [Fin.val_last, k, j]
       rw [getLastOraclePositionIndex_last, Nat.sub_mul, Nat.one_mul, Nat.div_mul_cancel (hdiv.out)]
       rw [Nat.sub_add_eq_sub_sub_rev (h1:=by omega) (h2:=by omega)]; omega
     ⟩
     let finalOracleFoldingConsistency: Prop := by
       exact isCompliant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨k, by omega⟩) (steps := ϑ) (destIdx := ⟨k + ϑ, by omega⟩) (by rfl) (by simp only; omega) (f_i := f_k)
         (f_i_plus_steps := fun x => stmtOut.final_constant) (challenges := challenges)
     oracleFoldingConsistencyProp 𝔽q β (i := Fin.last ℓ)
         (challenges := stmtOut.challenges) (oStmt := oStmtOut)
       ∧ finalOracleFoldingConsistency

 /-- This is a special case of nonDoomedFoldingProp for `i = ℓ`, where we support
 the consistency between the last oracle `ℓ - ϑ` and the final constant `c`.
 This definition has form similar to masterKState where there is no localChecks.
 -/
 def finalSumcheckStepFoldingStateProp {h_le : ϑ ≤ ℓ}
     (input : (FinalSumcheckStatementOut (L := L) (ℓ := ℓ) ×
       (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)))
    :
     Prop :=
   let stmtOut := input.1
   let oStmtOut := input.2
   let j := getLastOraclePositionIndex (ℓ := ℓ) (ϑ := ϑ) (Fin.last ℓ)
   let k := j.val * ϑ
   have h_k: k = ℓ - ϑ := by
     dsimp only [k, j]
     rw [getLastOraclePositionIndex_last]
     rw [Nat.sub_mul, Nat.one_mul]
     rw [Nat.div_mul_cancel (hdiv.out)]
   let f_k := oStmtOut j
   let challenges : Fin ϑ → L := fun cId => stmtOut.challenges ⟨k + cId, by
     simp only [Fin.val_last, k, j]
     rw [getLastOraclePositionIndex_last, Nat.sub_mul, Nat.one_mul, Nat.div_mul_cancel (hdiv.out)]
     rw [Nat.sub_add_eq_sub_sub_rev (h1:=by omega) (h2:=by omega)]; omega
   ⟩
   have h_k_add_ϑ: k + ϑ = ℓ := by rw [h_k]; apply Nat.sub_add_cancel; omega
   let oracleFoldingConsistency: Prop :=
     finalSumcheckStepOracleConsistencyProp 𝔽q β (h_le := h_le) (stmtOut := stmtOut)
       (oStmtOut := oStmtOut)
   let foldingBadEventExists : Prop := (blockBadEventExistsProp 𝔽q β (stmtIdx := Fin.last ℓ)
     (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ))
     (oStmt := oStmtOut) (challenges := stmtOut.challenges))
   oracleFoldingConsistency ∨ foldingBadEventExists

 def foldStepRelOut (i : Fin ℓ) :
     Set ((Statement (L := L) Context i.succ ×
       (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)) ×
       Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ) :=
   { input | foldStepRelOutProp (mp := mp) (𝓑 := 𝓑) 𝔽q β i input}

 def roundRelation (i : Fin (ℓ + 1)) :
     Set ((Statement (L := L) Context i ×
       (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i j)) ×
       Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :=
   { input | roundRelationProp (mp := mp) (𝓑 := 𝓑) 𝔽q β i input}

 /-- Relation for final sumcheck step -/
 def finalSumcheckRelOutProp
     (input : ((FinalSumcheckStatementOut (L := L) (ℓ := ℓ) ×
       (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)) ×
       (Unit)))
    : Prop :=
   finalSumcheckStepFoldingStateProp 𝔽q β
     (h_le := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (hdiv.out))
     (input := input.1)

 def finalSumcheckRelOut :
     Set ((FinalSumcheckStatementOut (L := L) (ℓ := ℓ) ×
       (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)) ×
       (Unit)) :=
   { input | finalSumcheckRelOutProp 𝔽q β input }

 def strictOracleFoldingConsistencyProp (t : MultilinearPoly L ℓ) (i : Fin (ℓ + 1))
     (challenges : Fin i → L)
     (oStmt : ∀ j, (OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i) j) : Prop :=
   let P₀: L[X]_(2 ^ ℓ) := polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega)
     (fun ω => t.val.eval (bitsOfIndex ω))
   let f₀ := polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := 0) (P := P₀)
   ∀ (j : Fin (toOutCodewordsCount ℓ ϑ i)),
     let destIdx : Fin r := ⟨oraclePositionToDomainIndex (positionIdx := j), by
       have h_le := oracle_index_le_ℓ (i := i) (j := j); omega
     ⟩
     have h_k_next_le_i := oracle_block_k_le_i (i := i) (j := j);
     let fⱼ : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx := oStmt j
     let folded_func := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
       (i := 0) (steps := j * ϑ) (destIdx := destIdx) (h_destIdx := by
         dsimp only [Fin.coe_ofNat_eq_mod, destIdx]; simp only [zero_mod, zero_add])
       (h_destIdx_le := by have h_le := oracle_index_le_ℓ (i := i) (j := j); omega)
       (f := f₀) (r_challenges := getFoldingChallenges (r := r) (𝓡 := 𝓡) i
         challenges (k := 0) (ϑ := j * ϑ) (h := by omega))
     fⱼ = folded_func

 def strictOracleWitnessConsistency
     (stmtIdx : Fin (ℓ + 1)) (oracleIdx : OracleFrontierIndex stmtIdx)
     (stmt : Statement (L := L) (Context := Context) stmtIdx)
     (wit : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtIdx)
     (oStmt : ∀ j, (OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
       ϑ (i := oracleIdx.val) j)) : Prop :=
   let witnessStructuralInvariant: Prop := witnessStructuralInvariant (i:=stmtIdx) 𝔽q β (mp := mp)
     (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmt wit
   let strictOracleFoldingConsistency: Prop := strictOracleFoldingConsistencyProp 𝔽q β
     (t := wit.t) (i := oracleIdx.val)
     (challenges := Fin.take (m := oracleIdx.val) (v := stmt.challenges)
     (h := by simp only [Fin.val_fin_le, OracleFrontierIndex.val_le_i]))
     (oStmt := oStmt)
   witnessStructuralInvariant ∧ strictOracleFoldingConsistency

 def strictRoundRelationProp (i : Fin (ℓ + 1))
     (input : (Statement (L := L) Context i ×
       (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i j)) ×
       Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) : Prop :=
   let stmt := input.1.1
   let oStmt := input.1.2
   let wit := input.2
   let sumCheckConsistency: Prop := sumcheckConsistencyProp (𝓑 := 𝓑) stmt.sumcheck_target wit.H
   let strictOracleWitnessConsistency: Prop := strictOracleWitnessConsistency 𝔽q β (mp := mp)
     (stmtIdx := i) (oracleIdx := OracleFrontierIndex.mkFromStmtIdx i) stmt wit oStmt
   sumCheckConsistency ∧ strictOracleWitnessConsistency

 def strictFoldStepRelOutProp (i : Fin ℓ)
     (input : (Statement (L := L) Context i.succ ×
       (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)) ×
       Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ) : Prop :=
   let stmt := input.1.1
   let oStmt := input.1.2
   let wit := input.2
   let sumCheckConsistency: Prop := sumcheckConsistencyProp (𝓑 := 𝓑) stmt.sumcheck_target wit.H
   let strictOracleWitnessConsistency: Prop := strictOracleWitnessConsistency 𝔽q β (mp := mp)
     (stmtIdx := i.succ) (oracleIdx := OracleFrontierIndex.mkFromStmtIdxCastSuccOfSucc i)
     stmt wit oStmt
   sumCheckConsistency ∧ strictOracleWitnessConsistency

 def strictfinalSumcheckStepFoldingStateProp (t : MultilinearPoly L ℓ) {h_le : ϑ ≤ ℓ}
     (input : (FinalSumcheckStatementOut (L := L) (ℓ := ℓ) ×
       (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j))) :
     Prop :=
   let stmt := input.1
   let oStmt := input.2
   let strictOracleFoldingConsistency: Prop :=
     strictOracleFoldingConsistencyProp 𝔽q β (t := t) (i := Fin.last ℓ)
       (challenges := stmt.challenges) (oStmt := oStmt)
   let lastDomainIdx := getLastOracleDomainIndex ℓ ϑ (Fin.last ℓ)
   have h_eq := getLastOracleDomainIndex_last (ℓ := ℓ) (ϑ := ϑ)
   let k := lastDomainIdx.val
   have h_k: k = ℓ - ϑ := by
     dsimp only [k, lastDomainIdx]
     rw [getLastOraclePositionIndex_last, Nat.sub_mul, Nat.one_mul, Nat.div_mul_cancel (hdiv.out)]
   let curDomainIdx : Fin r := ⟨k, by omega⟩
   have h_destIdx_eq: curDomainIdx.val = lastDomainIdx.val := rfl
   let f_k : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) curDomainIdx :=
     getLastOracle (h_destIdx := h_destIdx_eq) (oracleFrontierIdx := Fin.last ℓ)
       𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (oStmt := oStmt)
   let finalChallenges : Fin ϑ → L := fun cId => stmt.challenges ⟨k + cId, by
     rw [h_k]
     have h_le : ϑ ≤ ℓ := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (hdiv.out)
     have h_cId : cId.val < ϑ := cId.isLt
     have h_last : (Fin.last ℓ).val = ℓ := rfl
     omega
   ⟩
   let destDomainIdx : Fin r := ⟨k + ϑ, by omega⟩
   let strictFinalConstantConsistency: Prop :=
     (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := curDomainIdx) (steps := ϑ)
       (destIdx := destDomainIdx) (h_destIdx := by rfl)
       (h_destIdx_le := by dsimp only [destDomainIdx]; omega) (f := f_k)
       (r_challenges := finalChallenges) = fun x => stmt.final_constant)
   strictOracleFoldingConsistency ∧ strictFinalConstantConsistency

 def strictRoundRelation (i : Fin (ℓ + 1)) :
     Set ((Statement (L := L) Context i ×
       (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i j)) ×
       Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :=
   { input | strictRoundRelationProp (mp := mp) (𝓑 := 𝓑) 𝔽q β i input}

 def strictFoldStepRelOut (i : Fin ℓ) :
     Set ((Statement (L := L) Context i.succ ×
         (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)) ×
       Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ) :=
   { input | strictFoldStepRelOutProp (mp := mp) (𝓑 := 𝓑) 𝔽q β i input}

 def strictFinalSumcheckRelOutProp
     (input : ((FinalSumcheckStatementOut (L := L) (ℓ := ℓ) ×
       (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)) ×
       (Unit))) : Prop :=
   ∃ (t : MultilinearPoly L ℓ), strictfinalSumcheckStepFoldingStateProp 𝔽q β (t := t)
     (h_le := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (hdiv.out))
     (input := input.1)

 def strictFinalSumcheckRelOut :
     Set ((FinalSumcheckStatementOut (L := L) (ℓ := ℓ) ×
       (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)) ×
       (Unit)) :=
   { input | strictFinalSumcheckRelOutProp 𝔽q β input }

 end SumcheckContextIncluded_Relations
 end SecurityRelations

 end Binius.BinaryBasefold
