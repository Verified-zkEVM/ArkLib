/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.QuarterGap

/-!
# Acceptance cases for quarter-gap Reed–Solomon list bounds

The examples check concrete half- and quarter-gap lists over `ZMod 3`, a specialization to
`Fin n`, and the zero-coordinate boundary where a strict bound by the block length cannot hold.
-/

open ReedSolomon ReedSolomon.ListDecoding

private def boolDomain : Bool ↪ ZMod 3 where
  toFun b := if b then 1 else 0
  inj' x y h := by
    cases x <;> cases y <;> simp_all

private def emptyDomain : Fin 0 ↪ ZMod 2 where
  toFun i := Fin.elim0 i
  inj' i _ _ := Fin.elim0 i

/-- With two evaluation points, the threshold at gap one quarter is two. -/
example :
    (agreeingPolynomials boolDomain 1 (agreementThreshold (1 / 4) 2 1)
      (fun _ : Bool => 0)).encard < (2 : ℕ∞) := by
  exact agreeingPolynomials_encard_lt_blockLength_of_quarter
    (ι := Bool) (F := ZMod 3) (delta := 1 / 4) (by norm_num) boolDomain
    (by decide) (by decide) (by decide) (fun _ => 0)

/-- At the half-gap threshold, the same two-coordinate list has size at most one. -/
example :
    (agreeingPolynomials boolDomain 1 (agreementThreshold (1 / 2) 2 1)
      (fun _ : Bool => 0)).encard ≤ 1 := by
  exact agreeingPolynomials_encard_le_one_of_half
    (ι := Bool) (F := ZMod 3) (delta := 1 / 2) (by norm_num) boolDomain
    (by decide) (by decide) (fun _ => 0)

/-- The arbitrary finite-coordinate quarter-gap theorem specializes to the `Fin n` statement. -/
example {F : Type*} [Field F] [Finite F] [DecidableEq F] {delta : ℝ} {n k : ℕ}
    (hdelta : (1 / 4 : ℝ) ≤ delta) (domain : Fin n ↪ F) (hn : 0 < n)
    (hk : 0 < k) (hkn : k ≤ n) (received : Fin n → F) :
    (agreeingPolynomials domain k (agreementThreshold delta n k) received).encard <
      (n : ℕ∞) := by
    simpa only [Fintype.card_fin] using
    agreeingPolynomials_encard_lt_blockLength_of_quarter
      (ι := Fin n) (F := F) (delta := delta) hdelta domain
      (by simpa only [Fintype.card_fin] using hn) hk
      (by simpa only [Fintype.card_fin] using hkn) received

/-- At zero coordinates no list can have size strictly less than the block length. -/
example (received : Fin 0 → ZMod 2) :
    ¬ (agreeingPolynomials emptyDomain 0
      (agreementThreshold (1 / 4) 0 0) received).encard < (0 : ℕ∞) := by
  simp
