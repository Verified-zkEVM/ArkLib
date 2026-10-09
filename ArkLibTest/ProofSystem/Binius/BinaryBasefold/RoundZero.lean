/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Alexander Hicks
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Relations

/-!
# Binary Basefold: no bad-event escape at round zero

The Binary Basefold round relations are a disjunction: an incremental folding bad event, or the
good conjunction (sum-check consistency, structured witness, first-oracle consistency and oracle
folding consistency). This test checks that the bad-event disjunct is a genuine event:

* an oracle block whose fold has not completed is never a bad block
  (`not_foldingBadEventAtBlock_of_lt`);
* at round `0` the incremental bad event is false for every oracle statement and every challenge
  vector (`not_incrementalBadEventExistsProp_zero`);
* hence the round relation at `0` is exactly its good conjunction (`mem_roundRelation_zero_iff`).

The round relation at `i` is the fold step's input relation and its knowledge state before the
first message, so at round `0` that state has no bad-event escape. The axioms of all three
statements are pinned with `#guard_msgs`.
-/

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
open Binius.BinaryBasefold

namespace ArkLibTest.Binius.BinaryBasefold

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q]
  [Fact (Nat.Prime (ringChar 𝔽q))] [Fact (Fintype.card 𝔽q = 2)]
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
    ¬ foldingBadEventAtBlock 𝔽q β (stmtIdx := stmtIdx) (oracleIdx := oracleIdx)
      (oStmt := oStmt) (challenges := challenges) j := by
  unfold foldingBadEventAtBlock
  intro h
  simp only at h
  split at h
  · rename_i hle
    exact absurd hle (by simp only [not_le]; exact hj)
  · exact h

/-- At round `0` the incremental bad event is false, for every oracle statement and challenge
vector. -/
theorem not_incrementalBadEventExistsProp_zero
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)
      (i := (OracleFrontierIndex.mkFromStmtIdx (0 : Fin (ℓ + 1))).val) j)
    (challenges : Fin (0 : Fin (ℓ + 1)) → L) :
    ¬ incrementalBadEventExistsProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)
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
      rw [toOutCodewordsCountOf0] at h_j_lt
      exact h_j_lt
    exact Nat.lt_one_iff.mp hjlt
  subst hj0
  dsimp [oraclePositionToDomainIndex] at hj
  exact absurd hj (by
    apply incrementalFoldingBadEvent_of_k_eq_0_is_false (𝔽q := 𝔽q) (β := β)
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
      witnessStructuralInvariant 𝔽q β (multpoly := multpoly) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        stmt wit ∧
      firstOracleWitnessConsistencyProp 𝔽q β wit.t (getFirstOracle 𝔽q β oStmt) ∧
      oracleFoldingConsistencyProp 𝔽q β (i := (OracleFrontierIndex.mkFromStmtIdx 0).val)
        (challenges := Fin.take (m := (OracleFrontierIndex.mkFromStmtIdx 0).val)
          (v := stmt.challenges)
          (h := by simp only [Fin.val_fin_le, OracleFrontierIndex.val_le_i]))
        (oStmt := oStmt) :=
  or_iff_right (not_incrementalBadEventExistsProp_zero 𝔽q β oStmt stmt.challenges)

/--
info: 'ArkLibTest.Binius.BinaryBasefold.not_foldingBadEventAtBlock_of_lt' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms not_foldingBadEventAtBlock_of_lt

/--
info: 'ArkLibTest.Binius.BinaryBasefold.not_incrementalBadEventExistsProp_zero' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms not_incrementalBadEventExistsProp_zero

/--
info: 'ArkLibTest.Binius.BinaryBasefold.mem_roundRelation_zero_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms mem_roundRelation_zero_iff

end ArkLibTest.Binius.BinaryBasefold
