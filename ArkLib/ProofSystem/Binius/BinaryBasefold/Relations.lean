/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module


public import ArkLib.ProofSystem.Binius.BinaryBasefold.Basic

/-!
# Binary Basefold relations and bad-event layer

The strict relations describe exact witness encodings and their honest folds, for perfect
completeness. The relaxed relations support knowledge soundness via decoding proximity.
This distinction is consistent with BaseFold [ZCF24]: Definition 8 requires completeness
for honestly generated commitments, whereas Theorem 4 extracts a polynomial with a nearby
encoding and the claimed evaluation. BaseFold's coset-distance condition is not identified
with our UDR predicate, and its theorem is not our round-by-round knowledge-soundness result.

## References

* [Zeilberger, H., Chen, B. and Fisch, B., *BaseFold: Efficient Field-Agnostic Polynomial
  Commitment Schemes from Foldable Codes*][ZCF24]
-/

@[expose] public section




noncomputable section
namespace Binius.BinaryBasefold

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
  Binius.BinaryBasefold
open scoped NNReal
open ReedSolomon Code BerlekampWelch
open Finset AdditiveNTT Polynomial MvPolynomial Nat Matrix

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [hF₂ : Fact (Fintype.card 𝔽q = 2)]
local instance instFactPrimeRingCharRelations [Finite 𝔽q] : Fact (Nat.Prime (ringChar 𝔽q)) :=
  ⟨CharP.prime_ringChar 𝔽q⟩
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

omit [NeZero r] [Field L] [Fintype L] [DecidableEq L]
  [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ] hdiv in
/-- A challenge slice below the last round is unchanged when the final challenge is removed. -/
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

/-- Read the next committed oracle at its transported block endpoint. -/
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
def OracleFoldingConsistent (i : Fin (ℓ + 1)) (challenges : Fin i → L)
    (oStmt : ∀ j, (OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i) j) : Prop :=
  (∀ (j : Fin (toOutCodewordsCount ℓ ϑ i)) (hj : j.val + 1 < toOutCodewordsCount ℓ ϑ i),
    have h_k_bound := oracle_block_k_bound (ℓ := ℓ) (ϑ := ϑ) (i := i) (j := j)
    have h_k_next_le_i := oracle_block_k_next_le_i (ℓ := ℓ) (ϑ := ϑ) (i := i) (j := j) (hj := hj)
    let destIdx : Fin r := ⟨oraclePositionToDomainIndex (positionIdx := j) + ϑ, by
      have h_le := oracle_index_add_steps_le_ℓ ℓ ϑ (i := i) (j := j)
      dsimp only [oraclePositionToDomainIndex]
      omega
    ⟩
    IsCompliant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨oraclePositionToDomainIndex (positionIdx := j), by omega⟩) (steps := ϑ)
      (destIdx := destIdx) (by rfl) (by
        dsimp only [destIdx]; simp only [oracle_index_add_steps_le_ℓ])
      (f_i := oStmt ⟨j.val, by exact j.isLt⟩)
      (f_i_plus_steps := getNextOracle 𝔽q β i oStmt j hj (destDomainIdx := destIdx)
        (h_destDomainIdx := by rfl))
      (challenges := getFoldingChallenges (r := r) (𝓡 := 𝓡) i challenges (k := j.val * ϑ)
        (h := h_k_next_le_i))
  )

/-- The multilinear equality polynomial at the given evaluation point. -/
def eqMultiplier (r : Fin ℓ → L) : MultilinearPoly L ℓ :=
  ⟨MvPolynomial.eqPolynomial r, by simp only [eqPolynomial_mem_restrictDegree]⟩

/-- The Binary Basefold multiplier: `eq(r, X)` at the evaluation point `r` of the context, so that
the sum-check round polynomial is `eq(r, X) · t`. -/
def multiplier (ctx : SumcheckBaseContext L ℓ) : MultilinearPoly L ℓ :=
  eqMultiplier ctx.t_eval_point

/-- Fold the encoded witness polynomial through all challenges of the current round. -/
def getMidCodewords {i : Fin (ℓ + 1)} (t : L⦃≤ 1⦄[X Fin ℓ])
    (challenges : Fin i → L) : (sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩) → L) :=
  let P₀ : L⦃< 2^ℓ⦄[X] := polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (h_ℓ := by omega)
    (a := fun ω => t.val.eval (bitsOfIndex ω))
  let f₀ : (sDomain 𝔽q β h_ℓ_add_R_rate 0) → L := fun x => P₀.val.eval x.val
  let fᵢ := iteratedFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := 0) (steps := i) (destIdx := ⟨i, by omega⟩)
    (h_destIdx := by simp only [Fin.coe_ofNat_eq_mod, zero_mod, zero_add])
    (h_destIdx_le := by simp only; omega)
    (f := f₀)
    (r_challenges := challenges)
  fun x => fᵢ x

omit [DecidableEq 𝔽q] h_β₀_eq_1 [NeZero ℓ] in
/-- Advancing the honest codeword by one round is a single fold at the next challenge. -/
lemma getMidCodewords_succ (t : L⦃≤ 1⦄[X Fin ℓ]) (i : Fin ℓ)
    (challenges : Fin i.castSucc → L) (r_i' : L) :
    (getMidCodewords 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i.succ) (t := t) (challenges := Fin.snoc challenges r_i')) =
    (iteratedFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i, by omega⟩) (steps := 1)
      (destIdx := ⟨i.succ, by omega⟩) (h_destIdx := by simp only [Fin.val_succ])
      (h_destIdx_le := by simp only; omega)
      (f := getMidCodewords 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i.castSucc)
      (t := t) (challenges := challenges)) (r_challenges := fun _ => r_i')) := by
  unfold getMidCodewords
  have h_trans :=
    (iteratedFold_iteratedFold (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := (0 : Fin r)) (midIdx := ⟨i, by omega⟩) (destIdx := ⟨i.succ, by omega⟩)
      (steps₁ := i) (steps₂ := 1)
      (h_midIdx := by simp)
      (h_destIdx := by simp [Fin.val_succ])
      (h_destIdx_le := by simp only; omega)
      (f := fun x =>
        (polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (h_ℓ := by omega)
          (a := fun ω => t.val.eval (bitsOfIndex ω))).val.eval x.val)
      (r_challenges₁ := challenges) (r_challenges₂ := fun _ => r_i')).symm
  rw [Fin.append_right_eq_snoc] at h_trans
  exact h_trans

section FoldStepLogic
variable {Context : Type} {multpoly : Context → MultilinearPoly L ℓ}

/-- The prover state before its message, before the challenge, and after the challenge of a fold. -/
def FoldProverState (i : Fin ℓ) : Fin (2 + 1) → Type := fun
  | ⟨0, _⟩ => (Statement (L := L) Context i.castSucc ×
    (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j) ×
    Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
  | ⟨1, _⟩ => Statement (L := L) Context i.castSucc ×
    (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j) ×
    Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc × L⦃≤ 2⦄[X]
  | _ => Statement (L := L) Context i.castSucc ×
    (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j) ×
    Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc × L⦃≤ 2⦄[X] × L

/-- Advance the sum-check statement, residual polynomial and folded word after a challenge. -/
@[reducible]
noncomputable def getFoldProverFinalOutput (i : Fin ℓ)
    (finalPrvState : FoldProverState 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      i 2 (Context := Context)) :
  ((Statement (L := L) Context i.succ × ((j : Fin (toOutCodewordsCount ℓ ϑ i.castSucc)) →
    OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j))
      × Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ) := by
  let (stmtIn, oStmtIn, witIn, h_i, r_i') := finalPrvState
  let newSumcheckTarget : L := h_i.val.eval r_i'
  let stmtOut : Statement (L := L) Context i.succ := {
    ctx := stmtIn.ctx,
    sumcheck_target := newSumcheckTarget,
    challenges := Fin.snoc stmtIn.challenges r_i'
  }
  let f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (domainIdx := ⟨i, by omega⟩) := witIn.f
  let challenges : Fin (1) → L := fun _ => r_i'
  let fᵢ_succ := iteratedFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := ⟨i, by omega⟩) (steps := 1) (destIdx := ⟨i.succ, by omega⟩)
    (h_destIdx := by simp only [Fin.val_succ]) (h_destIdx_le := by simp only; omega)
    f_i challenges
  let witOut : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i.succ := by
    let projectedH := projectToNextSumcheckPoly (L := L) (ℓ := ℓ)
      (i := i) (Hᵢ := witIn.H) (rᵢ := r_i')
    exact {
      t := witIn.t,
      H := projectedH,
      f := fᵢ_succ
    }
  let oStmtOut : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j := oStmtIn
  exact ⟨⟨stmtOut, oStmtOut⟩, witOut⟩

/-- The univariate round polynomial obtained from the residual witness. -/
@[reducible]
def foldProverComputeMsg (i : Fin ℓ)
    (witIn : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc) :
    L⦃≤ 2⦄[X] :=
  getSumcheckRoundPoly ℓ (SumcheckDomain.uniform 𝓑 ℓ) (i := i) witIn.H

/-- Check that the round polynomial sums to the current sum-check target. -/
@[reducible]
def foldVerifierCheck (i : Fin ℓ)
    (stmtIn : Statement (L := L) Context i.castSucc)
    (msg0 : L⦃≤ 2⦄[X]) : Prop :=
  msg0.val.eval (𝓑 0) + msg0.val.eval (𝓑 1) = stmtIn.sumcheck_target

/-- Append the challenge and evaluate the round polynomial to obtain the next target. -/
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
variable {Context : Type} {multpoly : Context → MultilinearPoly L ℓ}

/-- The witness is structured: its round polynomial `H` is `multpoly ctx · t` with the statement's
challenges substituted for the first variables (the `P · t` sum-check, `MvPolynomial.fixPrefix`),
and its folded word `f` is the honest fold of `t`'s codeword by those challenges. -/
def WitnessStructuralInvariant {i : Fin (ℓ + 1)} (stmt : Statement (L := L) Context i)
    (wit : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) : Prop :=
  wit.H = MvPolynomial.fixPrefix ℓ i
    (computeInitialSumcheckPoly ℓ wit.t (multpoly stmt.ctx)) stmt.challenges ∧
  wit.f = getMidCodewords 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) wit.t
    stmt.challenges

-- `sumcheckConsistencyProp` is the structured sum-check's, over a `SumcheckDomain`; Binary
-- Basefold sums over the uniform domain `SumcheckDomain.uniform 𝓑`.
export Sumcheck.Structured (sumcheckConsistencyProp)

/-- The folding bad event for a committed block that is fully challenged by the current state. -/
noncomputable def FoldingBadEventAtBlock
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
    FoldingBadEvent 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := curOracleDomainIdx) (steps := ϑ) (destIdx := destIdx) (by rfl)
      (by dsimp only [destIdx]; simp only [oracle_index_add_steps_le_ℓ])
      (f_i := f_k) (r_challenges :=
        getFoldingChallenges (r := r) (𝓡 := 𝓡) stmtIdx challenges (k := j.val * ϑ) (h := by
        simp only [curOracleDomainIdx] at hj
        exact hj
      ))
  else False

attribute [irreducible] FoldingBadEventAtBlock

/-- Some completed committed block has a folding bad event. -/
def HasBlockBadEvent
    (stmtIdx : Fin (ℓ + 1)) (oracleIdx : OracleFrontierIndex stmtIdx)
    (oStmt : ∀ j, (OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)
      (i := oracleIdx.val) j)) (challenges : Fin stmtIdx → L) : Prop :=
  ∃ j, FoldingBadEventAtBlock 𝔽q β (stmtIdx := stmtIdx) (oracleIdx := oracleIdx)
    (oStmt := oStmt) (challenges := challenges) j

/-- A committed block has an incremental bad event for the consumed challenge prefix. -/
def IncrementalBadEventAtBlock
    (stmtIdx : Fin (ℓ + 1)) (oracleIdx : OracleFrontierIndex stmtIdx)
    (oStmt : ∀ j, (OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)
      (i := oracleIdx.val) j)) (challenges : Fin stmtIdx → L)
    (j : Fin (toOutCodewordsCount ℓ ϑ oracleIdx.val)) : Prop :=
  let curOracleDomainIdx : Fin r := ⟨oraclePositionToDomainIndex (positionIdx := j), by omega⟩
  let k : ℕ := min ϑ (stmtIdx.val - curOracleDomainIdx.val)
  have h1 := oracle_index_add_steps_le_ℓ ℓ ϑ (i := oracleIdx.val) (j := j)
  let midIdx : Fin r := ⟨curOracleDomainIdx.val + k, by omega⟩
  let destIdx : Fin r := ⟨curOracleDomainIdx.val + ϑ, by
    dsimp only [oraclePositionToDomainIndex, curOracleDomainIdx]; omega⟩
  IncrementalFoldingBadEvent 𝔽q β
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


/-- Some committed block has a bad event for the challenges consumed so far. -/
def HasIncrementalBadEvent
    (stmtIdx : Fin (ℓ + 1)) (oracleIdx : OracleFrontierIndex stmtIdx)
    (oStmt : ∀ j, (OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)
      (i := oracleIdx.val) j)) (challenges : Fin stmtIdx → L) : Prop :=
  ∃ j, IncrementalBadEventAtBlock 𝔽q β stmtIdx oracleIdx oStmt challenges j

/-- The incremental bad event of a fixed block at the final state. -/
def IncrementalBadEventAtLast
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
    (challenges : Fin (Fin.last ℓ) → L)
    (j : Fin (toOutCodewordsCount ℓ ϑ (OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ)).val)) :
    Prop :=
  IncrementalBadEventAtBlock 𝔽q β (Fin.last ℓ)
    (OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ)) oStmt challenges j

omit [NeZero r] [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q] hF₂
  [Algebra 𝔽q L] β hβ_lin_indep h_β₀_eq_1 [NeZero 𝓡] hdiv
  [Field L] [Fintype L] [DecidableEq L] [NeZero ℓ] [NeZero ϑ] in
/-- The two final-round challenge slices agree after transport of their index types. -/
lemma lastRoundChallengeSlice_heq
    (challenges : Fin (Fin.last ℓ) → L)
    (j : Fin (toOutCodewordsCount ℓ ϑ (OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ)).val))
    {k : ℕ} (h : k = ϑ)
    (h_k_le_stmt : k ≤ ℓ - j.val * ϑ)
    (h_le : j.val * ϑ + ϑ ≤ ℓ) :
    HEq
      (fun cId : Fin k => challenges ⟨j.val * ϑ + cId.val, by
        have _h_k_le_stmt' : k ≤ ℓ - j.val * ϑ := h_k_le_stmt
        have h_cId_lt_k : cId.val < k := cId.isLt
        change j.val * ϑ + cId.val < ℓ
        omega⟩)
      (fun cId : Fin ϑ => challenges ⟨j.val * ϑ + cId.val, by
        have _h_le' : j.val * ϑ + ϑ ≤ ℓ := h_le
        change j.val * ϑ + cId.val < ℓ
        omega⟩) := by
  cases h
  apply heq_of_eq
  funext cId
  apply congrArg challenges
  apply Fin.ext
  rfl

omit [DecidableEq 𝔽q] in
/-- At the final state, completed-block and incremental bad events of a block agree. -/
lemma foldingBadEventAtBlock_iff_incrementalBadEvent_last
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
    (challenges : Fin (Fin.last ℓ) → L)
    (j : Fin (toOutCodewordsCount ℓ ϑ (OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ)).val)) :
    FoldingBadEventAtBlock 𝔽q β
      (stmtIdx := Fin.last ℓ) (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ))
      (oStmt := oStmt) (challenges := challenges) j ↔
    IncrementalBadEventAtLast 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (ϑ := ϑ) oStmt challenges j := by
  unfold IncrementalBadEventAtLast IncrementalBadEventAtBlock
  unfold FoldingBadEventAtBlock
  dsimp [oraclePositionToDomainIndex]
  have h_le : j.val * ϑ + ϑ ≤ ℓ := by
    exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := j)
  have hk : min ϑ (ℓ - j.val * ϑ) = ϑ := by
    omega
  simp only [h_le, ↓reduceDIte]
  let blockStartIdx : Fin r := ⟨j.val * ϑ, by
    exact lt_r_of_lt_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ((oraclePositionToDomainIndex (ℓ := ℓ) (ϑ := ϑ) j).isLt)⟩
  let destIdx : Fin r := ⟨j.val * ϑ + ϑ, by
    exact lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_le⟩
  let rChallenges : Fin ϑ → L := fun cId => challenges ⟨j.val * ϑ + cId.val, by
    change j.val * ϑ + cId.val < ℓ
    omega⟩
  convert
      (incrementalFoldingBadEvent_full_iff
        (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (ϑ := ϑ) (block_start_idx := blockStartIdx)
        (midIdx := destIdx) (destIdx := destIdx)
        (h_midIdx := rfl) (h_destIdx := rfl) (h_destIdx_le := h_le)
        (f_block_start := oStmt j)
        (r_challenges := rChallenges)).symm using 2
  · rfl
  · apply Fin.ext
    simp [destIdx, hk]
  · exact
      lastRoundChallengeSlice_heq (r := r) (𝓡 := 𝓡) challenges j hk
        (Nat.min_le_right ϑ (ℓ - j.val * ϑ)) h_le

omit [DecidableEq 𝔽q] in
/-- A completed-block bad event implies its final incremental bad event. -/
lemma foldingBadEventAtBlock_imp_incrementalBadEvent_last
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
    (challenges : Fin (Fin.last ℓ) → L)
    (j : Fin (toOutCodewordsCount ℓ ϑ (OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ)).val)) :
    FoldingBadEventAtBlock 𝔽q β
      (stmtIdx := Fin.last ℓ) (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ))
      (oStmt := oStmt) (challenges := challenges) j →
    IncrementalBadEventAtLast 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (ϑ := ϑ) oStmt challenges j := by
  exact (foldingBadEventAtBlock_iff_incrementalBadEvent_last 𝔽q β oStmt challenges j).mp

omit [DecidableEq 𝔽q] in
/-- A final incremental bad event implies the corresponding completed-block folding bad event. -/
lemma incrementalBadEvent_last_imp_foldingBadEventAtBlock
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
    (challenges : Fin (Fin.last ℓ) → L)
    (j : Fin (toOutCodewordsCount ℓ ϑ (OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ)).val))
    (h_j_inc_bad : IncrementalBadEventAtLast 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (ϑ := ϑ) oStmt challenges j) :
    FoldingBadEventAtBlock 𝔽q β
      (stmtIdx := Fin.last ℓ) (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ))
      (oStmt := oStmt) (challenges := challenges) j := by
  exact (foldingBadEventAtBlock_iff_incrementalBadEvent_last 𝔽q β oStmt challenges j).mpr
    h_j_inc_bad

omit [DecidableEq 𝔽q] in
/-- At the final state, completed-block and incremental bad-event existence are equivalent. -/
lemma blockBadEventExists_iff_incrementalBadEventExists_last
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
    (challenges : Fin (Fin.last ℓ) → L) :
    HasBlockBadEvent 𝔽q β
      (stmtIdx := Fin.last ℓ) (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ))
      (oStmt := oStmt) (challenges := challenges) ↔
    HasIncrementalBadEvent 𝔽q β
      (stmtIdx := Fin.last ℓ) (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ))
      (oStmt := oStmt) (challenges := challenges) := by
  constructor
  · intro h_bad
    rcases h_bad with ⟨j, h_j_bad⟩
    refine ⟨j, ?_⟩
    exact foldingBadEventAtBlock_imp_incrementalBadEvent_last
      (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (ϑ := ϑ) oStmt challenges j h_j_bad
  · intro h_inc_bad
    rcases h_inc_bad with ⟨j, h_j_inc_bad⟩
    refine ⟨j, ?_⟩
    exact incrementalBadEvent_last_imp_foldingBadEventAtBlock
      (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (ϑ := ϑ) oStmt challenges j h_j_inc_bad

/-- Unequal round polynomials collide at the sampled challenge. -/
def BadSumcheckChallenge (r_i' : L) (h_i h_star : L⦃≤ 2⦄[X]) :=
  h_i ≠ h_star ∧ h_i.val.eval r_i' = h_star.val.eval r_i'
section SingleStepRelationPreservationLemmas

omit [DecidableEq 𝔽q] in
/-- A relay preserves the existence of an incremental folding bad event. -/
lemma incrementalBadEventExists_relay_iff (i : Fin ℓ) (hNCR : ¬ IsCommitmentRound ℓ ϑ i)
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)
    (challenges : Fin i.succ → L) :
    HasIncrementalBadEvent 𝔽q β i.succ (OracleFrontierIndex.mkFromStmtIdxCastSuccOfSucc i)
      oStmt challenges ↔
    HasIncrementalBadEvent 𝔽q β i.succ (OracleFrontierIndex.mkFromStmtIdx i.succ)
      (mapOStmtOutRelayStep 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR oStmt) challenges := by
  unfold HasIncrementalBadEvent IncrementalBadEventAtBlock
  have h_count : toOutCodewordsCount ℓ ϑ i.castSucc = toOutCodewordsCount ℓ ϑ i.succ := by
    simp [toOutCodewordsCount_succ_eq, hNCR]
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨Fin.cast h_count j, ?_⟩
    have hj' := hj
    simp only [mapOStmtOutRelayStep, OracleFrontierIndex.val_mkFromStmtIdx,
      OracleFrontierIndex.val_mkFromStmtIdxCastSuccOfSucc] at hj' ⊢
    exact hj'
  · rintro ⟨j, hj⟩
    refine ⟨Fin.cast h_count.symm j, ?_⟩
    have hj' := hj
    simp only [mapOStmtOutRelayStep, OracleFrontierIndex.val_mkFromStmtIdx,
      OracleFrontierIndex.val_mkFromStmtIdxCastSuccOfSucc] at hj' ⊢
    exact hj'

omit [DecidableEq 𝔽q] in
/-- A relay preserves consistency of the committed oracle frontier. -/
lemma oracleFoldingConsistent_relay_iff (i : Fin ℓ) (hNCR : ¬ IsCommitmentRound ℓ ϑ i)
    (challenges : Fin i.succ.val → L)
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j) :
    OracleFoldingConsistent 𝔽q β (i := i.castSucc) (Fin.init challenges) oStmt ↔
    OracleFoldingConsistent 𝔽q β (i := i.succ) challenges
      (mapOStmtOutRelayStep 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR oStmt) := by
  have h_count : toOutCodewordsCount ℓ ϑ i.castSucc = toOutCodewordsCount ℓ ϑ i.succ := by
    simp [toOutCodewordsCount_succ_eq, hNCR]
  constructor
  · intro h j hj
    have hj_cast : (Fin.cast h_count.symm j).val + 1 < toOutCodewordsCount ℓ ϑ i.castSucc := by
      change j.val + 1 < toOutCodewordsCount ℓ ϑ i.castSucc
      rw [h_count]
      exact hj
    have h_old := h (Fin.cast h_count.symm j) hj_cast
    simp only [mapOStmtOutRelayStep] at h_old ⊢
    exact h_old
  · intro h j hj
    have hj_cast : (Fin.cast h_count j).val + 1 < toOutCodewordsCount ℓ ϑ i.succ := by
      change j.val + 1 < toOutCodewordsCount ℓ ϑ i.succ
      rw [← h_count]
      exact hj
    have h_old := h (Fin.cast h_count j) hj_cast
    simp only [mapOStmtOutRelayStep] at h_old ⊢
    exact h_old

section CommitStepPreservationLemmas

omit [DecidableEq 𝔽q] in
/-- An incremental bad event after a commitment already occurred before that commitment. -/
lemma hasIncrementalBadEvent_commit_step_backward (i : Fin ℓ) (hCR : IsCommitmentRound ℓ ϑ i)
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)
    (newOracle : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (domainIdx := ⟨i.val + 1, by omega⟩))
    (challenges : Fin i.succ → L) :
    HasIncrementalBadEvent 𝔽q β i.succ (OracleFrontierIndex.mkFromStmtIdx i.succ)
      (snocOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_destIdx := rfl)
        oStmtIn newOracle) challenges →
    HasIncrementalBadEvent 𝔽q β i.succ (OracleFrontierIndex.mkFromStmtIdxCastSuccOfSucc i)
      oStmtIn challenges := by
  unfold HasIncrementalBadEvent IncrementalBadEventAtBlock
  intro h_bad
  rcases h_bad with ⟨j, hj⟩
  by_cases hj_old : j.val < toOutCodewordsCount ℓ ϑ i.castSucc
  · refine ⟨⟨j.val, hj_old⟩, ?_⟩
    dsimp only at hj ⊢
    have hj_old' := hj
    simp only [snocOracle, hj_old, ↓reduceDIte] at hj_old' ⊢
    exact hj_old'
  · have hj_new := hj
    simp only [snocOracle, hj_old, hCR, ↓reduceDIte] at hj_new
    have h_eq := destIdx_eq_oraclePositionToDomainIndex_of_newOracle (h_ℓ_add_R_rate :=
      h_ℓ_add_R_rate)
      (ℓ := ℓ) (ϑ := ϑ) (destIdx := ⟨i.val + 1, by omega⟩)
      (h_destIdx := rfl) (j := j) (hj := hj_old) (h_commit := hCR)
    have h_block_val : j.val * ϑ = i.val + 1 := by
      have h_vals := congrArg Fin.val h_eq
      dsimp [oraclePositionToDomainIndex] at h_vals
      omega
    have hk0 : min ϑ (i.val + 1 - j.val * ϑ) = 0 := by
      omega
    have h_dest_le : j.val * ϑ + ϑ ≤ ℓ := by
      exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := i.succ) (j := j)
    have h_mid_le : j.val * ϑ + min ϑ (i.val + 1 - j.val * ϑ) ≤ ℓ := by
      omega
    exfalso
    exact
      (not_incrementalFoldingBadEvent_zero
        (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (ϑ := ϑ) (block_start_idx := ⟨j.val * ϑ, by
          exact lt_r_of_lt_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (by
            exact (oraclePositionToDomainIndex (ℓ := ℓ) (ϑ := ϑ) j).isLt)⟩)
        (k := min ϑ (i.val + 1 - j.val * ϑ)) hk0
        (midIdx := ⟨j.val * ϑ + min ϑ (i.val + 1 - j.val * ϑ), by
          exact lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_mid_le⟩)
        (destIdx := ⟨j.val * ϑ + ϑ, by
          exact lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_dest_le⟩)
        (h_midIdx := by
          dsimp
          rw [hk0]
          omega) (h_destIdx := rfl)
        (h_destIdx_le := h_dest_le)
        (f_block_start := fun x => newOracle (cast (by rw [h_eq]) x))
        (r_challenges := fun cId => challenges ⟨j.val * ϑ + cId.val, by
          have h_cId_lt : cId.val < min ϑ (i.val + 1 - j.val * ϑ) := cId.isLt
          change j.val * ϑ + cId.val < i.val + 1
          omega⟩)) hj_new

omit [DecidableEq 𝔽q] in
/-- Consistent committed oracles after a commitment restrict to consistent preceding oracles. -/
lemma oracleFoldingConsistent_commit_step_backward (i : Fin ℓ) (hCR : IsCommitmentRound ℓ ϑ i)
    (challenges : Fin i.succ.val → L)
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)
    (newOracle : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (domainIdx := ⟨i.val + 1, by omega⟩)) :
    OracleFoldingConsistent 𝔽q β (i := i.succ) challenges
      (snocOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_destIdx := rfl)
        oStmtIn newOracle) →
    OracleFoldingConsistent 𝔽q β (i := i.castSucc) (Fin.init challenges) oStmtIn := by
  intro h j hj
  let j' : Fin (toOutCodewordsCount ℓ ϑ i.succ) := ⟨j, by
    exact lt_of_lt_of_le j.isLt (toOutCodewordsCount_castSucc_le_succ (ℓ := ℓ) (ϑ := ϑ) i)⟩
  have hj' : j'.val + 1 < toOutCodewordsCount ℓ ϑ i.succ := by
    dsimp [j']
    have h_count : toOutCodewordsCount ℓ ϑ i.succ = toOutCodewordsCount ℓ ϑ i.castSucc + 1 := by
      simp [toOutCodewordsCount_succ_eq, hCR]
    omega
  have h_old := h j' hj'
  have hj_lt_old : j'.val < toOutCodewordsCount ℓ ϑ i.castSucc := by
    dsimp [j']
    exact j.isLt
  have hj1_lt_old : j'.val + 1 < toOutCodewordsCount ℓ ϑ i.castSucc := by
    change j.val + 1 < toOutCodewordsCount ℓ ϑ i.castSucc
    exact hj
  simp only [getNextOracle, snocOracle, j', hj_lt_old,
    hj1_lt_old, hCR] at h_old ⊢
  exact h_old

end CommitStepPreservationLemmas

end SingleStepRelationPreservationLemmas
/-- A consumed-challenge bad event holds, or all local, structural and oracle invariants hold
at the specified statement and oracle frontiers. -/
def KnowledgeInvariant (stmtIdx : Fin (ℓ + 1))
    (oracleIdx : OracleFrontierIndex stmtIdx)
    (stmt : Statement (L := L) Context stmtIdx)
    (wit : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtIdx)
    (oStmt : ∀ j, (OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ
      (i := oracleIdx.val) j))
    (localChecks : Prop := True) : Prop :=
  let structural := WitnessStructuralInvariant 𝔽q β (multpoly := multpoly)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmt wit
  let initial := FirstOracleWitnessConsistent 𝔽q β wit.t (getFirstOracle 𝔽q β oStmt)
  let oracleFoldingConsistency: Prop := OracleFoldingConsistent 𝔽q β (i := oracleIdx.val)
    (challenges := Fin.take (m := oracleIdx.val) (v := stmt.challenges)
    (h := by simp only [Fin.val_fin_le, OracleFrontierIndex.val_le_i]))
    (oStmt := oStmt)
  let badEventExists := HasIncrementalBadEvent 𝔽q β stmtIdx oracleIdx
    (challenges := stmt.challenges) (oStmt := oStmt)
  let good := localChecks ∧ structural ∧ initial ∧ oracleFoldingConsistency
  badEventExists ∨ good

/-- A round is compatible if a bad event occurred or its sum-check, witness and oracle invariants
hold. -/
def RoundRelated (i : Fin (ℓ + 1))
    (input : (Statement (L := L) Context i ×
      (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i j)) ×
      Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) : Prop :=
  let stmt := input.1.1
  let oStmt := input.1.2
  let wit := input.2
  let sumCheckConsistency: Prop :=
    sumcheckConsistencyProp (SumcheckDomain.uniform 𝓑 _) stmt.sumcheck_target wit.H
  KnowledgeInvariant (multpoly := multpoly) 𝔽q β
    (stmtIdx := i) (oracleIdx := OracleFrontierIndex.mkFromStmtIdx i) stmt wit oStmt
    (localChecks := sumCheckConsistency)

/-- The next sum-check state with the oracle frontier still at the preceding round. -/
def FoldStepRelated (i : Fin ℓ)
    (input : (Statement (L := L) Context i.succ ×
      (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)) ×
      Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ) : Prop :=
  let stmt := input.1.1
  let oStmt := input.1.2
  let wit := input.2
  let sumCheckConsistency: Prop :=
    sumcheckConsistencyProp (SumcheckDomain.uniform 𝓑 _) stmt.sumcheck_target wit.H
  KnowledgeInvariant (multpoly := multpoly) 𝔽q β
    (stmtIdx := i.succ) (oracleIdx := OracleFrontierIndex.mkFromStmtIdxCastSuccOfSucc i)
    stmt wit oStmt
      (localChecks := sumCheckConsistency)

/-- All committed folds are consistent, including the last block with the claimed final constant. -/
def FinalSumcheckOracleConsistent
    (stmtOut : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtOut : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ
      (Fin.last ℓ) j) : Prop :=
    have h_le : ϑ ≤ ℓ := blockSize_le_rounds ℓ ϑ
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
      exact IsCompliant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨k, by omega⟩) (steps := ϑ) (destIdx := ⟨k + ϑ, by omega⟩)
        (by rfl) (by simp only; omega) (f_i := f_k)
        (f_i_plus_steps := fun x => stmtOut.finalConstant) (challenges := challenges)
    OracleFoldingConsistent 𝔽q β (i := Fin.last ℓ)
        (challenges := stmtOut.challenges) (oStmt := oStmtOut)
      ∧ finalOracleFoldingConsistency

/-- The folding state after the final sum-check step: either the oracles are fold-consistent up
to level `ℓ`, including the consistency of the last oracle `ℓ - ϑ` with the final constant `c`,
or a block bad event has occurred. It has the shape of `KnowledgeInvariant` without the local
checks. -/
def FinalSumcheckFoldingState
    (input : (FinalSumcheckStatementOut (L := L) (ℓ := ℓ) ×
      (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j))) : Prop :=
  let stmtOut := input.1
  let oStmtOut := input.2
  let oracleFoldingConsistency: Prop :=
    FinalSumcheckOracleConsistent 𝔽q β  (stmtOut := stmtOut)
      (oStmtOut := oStmtOut)
  let foldingBadEventExists : Prop := (HasBlockBadEvent 𝔽q β (stmtIdx := Fin.last ℓ)
    (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ))
    (oStmt := oStmtOut) (challenges := stmtOut.challenges))
  oracleFoldingConsistency ∨ foldingBadEventExists

/-- The fold output relation before updating the committed-oracle frontier. -/
def foldStepRelOut (i : Fin ℓ) :
    Set ((Statement (L := L) Context i.succ ×
      (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)) ×
      Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ) :=
  { input | FoldStepRelated (multpoly := multpoly) (𝓑 := 𝓑) 𝔽q β i input}

/-- The round relation with sum-check, witness and oracle compatibility, or a folding bad event. -/
def roundRelation (i : Fin (ℓ + 1)) :
    Set ((Statement (L := L) Context i ×
      (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i j)) ×
      Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :=
  { input | RoundRelated (multpoly := multpoly) (𝓑 := 𝓑) 𝔽q β i input}

/-- Final output compatibility: consistent folded oracles, or a completed-block bad event. -/
def FinalSumcheckRelated
    (input : ((FinalSumcheckStatementOut (L := L) (ℓ := ℓ) ×
      (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)) ×
      (Unit))) : Prop :=
  FinalSumcheckFoldingState 𝔽q β
    (input := input.1)

/-- The final compatibility relation on the verifier output and its committed codeword oracles. -/
def finalSumcheckRelOut :
    Set ((FinalSumcheckStatementOut (L := L) (ℓ := ℓ) ×
      (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)) ×
      (Unit)) :=
  { input | FinalSumcheckRelated 𝔽q β input }

/-- Every committed codeword equals the honest fold of the witness polynomial encoding. -/
def StrictOracleFoldingConsistent (t : MultilinearPoly L ℓ) (i : Fin (ℓ + 1))
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
    let folded_func := iteratedFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := 0) (steps := j * ϑ) (destIdx := destIdx) (h_destIdx := by
        dsimp only [Fin.coe_ofNat_eq_mod, destIdx]; simp only [zero_mod, zero_add])
      (h_destIdx_le := by have h_le := oracle_index_le_ℓ (i := i) (j := j); omega)
      (f := f₀) (r_challenges := getFoldingChallenges (r := r) (𝓡 := 𝓡) i
        challenges (k := 0) (ϑ := j * ϑ) (h := by omega))
    fⱼ = folded_func

/-- The witness residual polynomial and all committed codewords have their prescribed honest
forms. -/
def StrictOracleWitnessConsistent
    (stmtIdx : Fin (ℓ + 1)) (oracleIdx : OracleFrontierIndex stmtIdx)
    (stmt : Statement (L := L) (Context := Context) stmtIdx)
    (wit : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtIdx)
    (oStmt : ∀ j, (OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ϑ (i := oracleIdx.val) j)) : Prop :=
  let WitnessStructuralInvariant: Prop :=
    WitnessStructuralInvariant (i:=stmtIdx) 𝔽q β (multpoly := multpoly)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmt wit
  let strictOracleFoldingConsistency: Prop := StrictOracleFoldingConsistent 𝔽q β
    (t := wit.t) (i := oracleIdx.val)
    (challenges := Fin.take (m := oracleIdx.val) (v := stmt.challenges)
    (h := by simp only [Fin.val_fin_le, OracleFrontierIndex.val_le_i]))
    (oStmt := oStmt)
  WitnessStructuralInvariant ∧ strictOracleFoldingConsistency

/-- Sum-check consistency and exact witness/oracle consistency at a round boundary. -/
def StrictRoundRelated (i : Fin (ℓ + 1))
    (input : (Statement (L := L) Context i ×
      (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i j)) ×
      Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) : Prop :=
  let stmt := input.1.1
  let oStmt := input.1.2
  let wit := input.2
  let sumCheckConsistency: Prop :=
    sumcheckConsistencyProp (SumcheckDomain.uniform 𝓑 _) stmt.sumcheck_target wit.H
  let StrictOracleWitnessConsistent: Prop :=
    StrictOracleWitnessConsistent 𝔽q β (multpoly := multpoly)
      (stmtIdx := i) (oracleIdx := OracleFrontierIndex.mkFromStmtIdx i) stmt wit oStmt
  sumCheckConsistency ∧ StrictOracleWitnessConsistent

/-- Exact consistency after a fold, before the committed-oracle frontier is updated. -/
def StrictFoldStepRelated (i : Fin ℓ)
    (input : (Statement (L := L) Context i.succ ×
      (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)) ×
      Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ) : Prop :=
  let stmt := input.1.1
  let oStmt := input.1.2
  let wit := input.2
  let sumCheckConsistency: Prop :=
    sumcheckConsistencyProp (SumcheckDomain.uniform 𝓑 _) stmt.sumcheck_target wit.H
  let StrictOracleWitnessConsistent: Prop :=
    StrictOracleWitnessConsistent 𝔽q β (multpoly := multpoly)
      (stmtIdx := i.succ) (oracleIdx := OracleFrontierIndex.mkFromStmtIdxCastSuccOfSucc i)
      stmt wit oStmt
  sumCheckConsistency ∧ StrictOracleWitnessConsistent

/-- Committed codewords and the final constant equal their honest folded encodings. -/
def StrictFinalSumcheckFoldingState (t : MultilinearPoly L ℓ)
    (input : (FinalSumcheckStatementOut (L := L) (ℓ := ℓ) ×
      (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j))) :
    Prop :=
  have h_le : ϑ ≤ ℓ := blockSize_le_rounds ℓ ϑ
  let stmt := input.1
  let oStmt := input.2
  let strictOracleFoldingConsistency: Prop :=
    StrictOracleFoldingConsistent 𝔽q β (t := t) (i := Fin.last ℓ)
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
    have h_le : ϑ ≤ ℓ := blockSize_le_rounds ℓ ϑ
    have h_cId : cId.val < ϑ := cId.isLt
    have h_last : (Fin.last ℓ).val = ℓ := rfl
    omega
  ⟩
  let destDomainIdx : Fin r := ⟨k + ϑ, by omega⟩
  let strictFinalConstantConsistency: Prop :=
    (iteratedFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := curDomainIdx) (steps := ϑ)
      (destIdx := destDomainIdx) (h_destIdx := by rfl)
      (h_destIdx_le := by dsimp only [destDomainIdx]; omega) (f := f_k)
      (r_challenges := finalChallenges) = fun x => stmt.finalConstant)
  strictOracleFoldingConsistency ∧ strictFinalConstantConsistency

/-- The exact-encoding round relation used for perfect completeness. -/
def strictRoundRelation (i : Fin (ℓ + 1)) :
    Set ((Statement (L := L) Context i ×
      (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i j)) ×
      Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :=
  { input | StrictRoundRelated (multpoly := multpoly) (𝓑 := 𝓑) 𝔽q β i input}

/-- The exact-encoding fold output relation before a frontier update. -/
def strictFoldStepRelOut (i : Fin ℓ) :
    Set ((Statement (L := L) Context i.succ ×
        (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)) ×
      Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ) :=
  { input | StrictFoldStepRelated (multpoly := multpoly) (𝓑 := 𝓑) 𝔽q β i input}

/-- Some polynomial supplies the exact committed encodings and claimed final folded constant. -/
def StrictFinalSumcheckRelated
    (input : ((FinalSumcheckStatementOut (L := L) (ℓ := ℓ) ×
      (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)) ×
      (Unit))) : Prop :=
  ∃ (t : MultilinearPoly L ℓ), StrictFinalSumcheckFoldingState 𝔽q β (t := t)
    (input := input.1)

/-- The final exact-encoding relation used for perfect completeness. -/
def strictFinalSumcheckRelOut :
    Set ((FinalSumcheckStatementOut (L := L) (ℓ := ℓ) ×
      (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)) ×
      (Unit)) :=
  { input | StrictFinalSumcheckRelated 𝔽q β input }

end SumcheckContextIncluded_Relations
end SecurityRelations

end Binius.BinaryBasefold
