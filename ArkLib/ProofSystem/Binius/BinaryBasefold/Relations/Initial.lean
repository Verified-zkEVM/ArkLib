/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Alexander Hicks
-/
module

public import ArkLib.ProofSystem.Binius.BinaryBasefold.Relations

/-!
# Initial Binary Basefold relation

No folding block has completed at the initial frontier. Consequently the initial relaxed
relation requires sum-check consistency, the structural invariant and first-oracle consistency.
-/

@[expose] public section

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial

namespace Binius.BinaryBasefold

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L]
variable (𝔽q : Type) [Field 𝔽q]
local instance [Finite 𝔽q] : Fact (Nat.Prime (ringChar 𝔽q)) := ⟨CharP.prime_ringChar 𝔽q⟩

variable [Fintype 𝔽q] [Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]

variable (β : Fin r → L) [Fact (LinearIndependent 𝔽q β)] [Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}
variable [Fact (ϑ ∣ ℓ)]

/-- An oracle block whose fold has not completed by `stmtIdx` is never a bad block. -/
theorem not_foldingBadEventAtBlock_of_lt
    (stmtIdx : Fin (ℓ + 1)) (oracleIdx : OracleFrontierIndex stmtIdx)
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)
      (i := oracleIdx.val) j) (challenges : Fin stmtIdx → L)
    (j : Fin (toOutCodewordsCount ℓ ϑ oracleIdx.val))
    (hj : stmtIdx.val < oraclePositionToDomainIndex (positionIdx := j) + ϑ) :
    ¬ FoldingBadEventAtBlock 𝔽q β (stmtIdx := stmtIdx) (oracleIdx := oracleIdx)
      (oStmt := oStmt) (challenges := challenges) j := by
  unfold FoldingBadEventAtBlock
  intro h
  simp only at h
  split at h
  · rename_i hle
    exact absurd hle (by simp only [not_le]; exact hj)
  · exact h

/-- At round `0` the incremental bad event is false, for every oracle statement and challenge
vector. -/
theorem not_hasIncrementalBadEvent_zero
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)
      (i := (OracleFrontierIndex.mkFromStmtIdx (0 : Fin (ℓ + 1))).val) j)
    (challenges : Fin (0 : Fin (ℓ + 1)) → L) :
    ¬ HasIncrementalBadEvent 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)
      (stmtIdx := (0 : Fin (ℓ + 1)))
      (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (0 : Fin (ℓ + 1)))
      (oStmt := oStmt) (challenges := challenges) := by
  intro h_bad
  rcases h_bad with ⟨j, hj⟩
  have hj0 : j = 0 := by
    apply Fin.eq_of_val_eq
    have hjlt : j.val < 1 := by
      have h_j_lt := j.isLt
      change j.val < toOutCodewordsCount ℓ ϑ (0 : Fin (ℓ + 1)) at h_j_lt
      rw [toOutCodewordsCount_zero] at h_j_lt
      exact h_j_lt
    exact Nat.lt_one_iff.mp hjlt
  subst hj0
  dsimp [IncrementalBadEventAtBlock, oraclePositionToDomainIndex] at hj
  exact absurd hj (by
    apply not_incrementalFoldingBadEvent_zero (𝔽q := 𝔽q) (β := β)
      (h_k := by simp only [zero_mul, tsub_self, zero_le, inf_of_le_right])
      (h_midIdx := by simp only [zero_mul, tsub_self, zero_le, inf_of_le_right, add_zero]))

variable {𝓑 : Fin 2 ↪ L} {Context : Type} {multpoly : Context → MultilinearPoly L ℓ}

/-- The round relation at `0` is exactly its good conjunction: sum-check consistency, a structured
witness, first-oracle consistency and oracle folding consistency. -/
theorem mem_roundRelation_zero_iff
    (stmt : Statement (L := L) Context (0 : Fin (ℓ + 1)))
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (0 : Fin (ℓ + 1)) j)
    (wit : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin (ℓ + 1))) :
    ((stmt, oStmt), wit) ∈ roundRelation (multpoly := multpoly) (𝓑 := 𝓑) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 ↔
      sumcheckConsistencyProp (SumcheckDomain.uniform 𝓑 _) stmt.sumcheck_target wit.H ∧
      WitnessStructuralInvariant 𝔽q β (multpoly := multpoly) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        stmt wit ∧
      FirstOracleWitnessConsistent 𝔽q β wit.t (getFirstOracle 𝔽q β oStmt) ∧
      OracleFoldingConsistent 𝔽q β (i := (OracleFrontierIndex.mkFromStmtIdx 0).val)
        (challenges := Fin.take (m := (OracleFrontierIndex.mkFromStmtIdx 0).val)
          (v := stmt.challenges)
          (h := by simp only [Fin.val_fin_le, OracleFrontierIndex.val_le_i]))
        (oStmt := oStmt) :=
  or_iff_right (not_hasIncrementalBadEvent_zero 𝔽q β oStmt stmt.challenges)


end Binius.BinaryBasefold
