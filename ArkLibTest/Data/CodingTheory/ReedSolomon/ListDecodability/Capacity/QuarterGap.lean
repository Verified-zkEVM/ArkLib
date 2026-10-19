/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.QuarterGap
import Mathlib.Data.Nat.Prime.Infinite

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

private def finDomain {n q : ℕ} (hnq : n ≤ q) : Fin n ↪ ZMod q where
  toFun i := (i.val : ZMod q)
  inj' i j h := by
    apply Fin.ext
    have hiq : i.val < q := i.isLt.trans_le hnq
    have hjq : j.val < q := j.isLt.trans_le hnq
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hiq, Nat.mod_eq_of_lt hjq]
      using congrArg ZMod.val h

/-- With two evaluation points, the threshold at gap one quarter is two. -/
example :
    (agreeingPolynomials boolDomain 1 (capacityAgreementThreshold (1 / 4) 2 1)
      (fun _ : Bool => 0)).encard < (2 : ℕ∞) := by
  exact agreeingPolynomials_encard_lt_blockLength_of_quarter
    (ι := Bool) (F := ZMod 3) (delta := 1 / 4) (by norm_num) boolDomain
    (by decide) (by decide) (fun _ => 0)

/-- At the half-gap threshold, the same two-coordinate list has size at most one. -/
example :
    (agreeingPolynomials boolDomain 1 (capacityAgreementThreshold (1 / 2) 2 1)
      (fun _ : Bool => 0)).encard ≤ 1 := by
  exact agreeingPolynomials_encard_le_one_of_half
    (ι := Bool) (F := ZMod 3) (delta := 1 / 2) (by norm_num) boolDomain
    (by decide) (by decide) (fun _ => 0)

/-- The arbitrary finite-coordinate quarter-gap theorem specializes to the `Fin n` statement. -/
example {F : Type*} [Field F] [DecidableEq F] {delta : ℝ} {n k : ℕ}
    (hdelta : (1 / 4 : ℝ) ≤ delta) (domain : Fin n ↪ F)
    (hk : 0 < k) (hkn : k ≤ n) (received : Fin n → F) :
    (agreeingPolynomials domain k (capacityAgreementThreshold delta n k) received).encard <
      (n : ℕ∞) := by
    simpa only [Fintype.card_fin] using
    agreeingPolynomials_encard_lt_blockLength_of_quarter
      (ι := Fin n) (F := F) (delta := delta) hdelta domain
      hk (by simpa only [Fintype.card_fin] using hkn) received

/-- The uniform quarter-gap theorem supplies a certificate and strict list bound on an explicit
prime-field evaluation domain. -/
example :
    ∃ n q : ℕ, q.Prime ∧ ∃ domain : Fin n ↪ ZMod q,
      0 < n ∧ n ≤ q ∧
        ∃ certificate : CapacityGapCertificate (1 / 4) domain 1 (4 * q),
          Code.Lambda (ReedSolomon.code domain 1 : Set (Fin n → ZMod q))
              (capacityRadius (1 / 4) n 1) ≤ ((4 * q : ℕ) : ℕ∞) ∧
          (∀ received, (certificate.decoderCertificate.decoder received).card ≤ 4 * q) ∧
          PointwiseListBound (1 / 4) domain 1 (4 * q) (fun _ => 0) ∧
          ∀ received : Fin n → ZMod q,
            (agreeingPolynomials domain 1 (capacityAgreementThreshold (1 / 4) n 1)
              received).encard < ((4 * q : ℕ) : ℕ∞) := by
  obtain ⟨threshold, hThreshold⟩ :=
    quarter_gap_list_bound (1 / 4) (by norm_num) (by norm_num)
  let n := max threshold 2
  have hThresholdLe : threshold ≤ n := le_max_left _ _
  have hTwo : 2 ≤ n := le_max_right _ _
  have hn : 0 < n := lt_of_lt_of_le (by omega) hTwo
  obtain ⟨q, hnq, hq⟩ := Nat.exists_infinite_primes n
  let domain := finDomain hnq
  have hInstance := hThreshold n 1 q hThresholdLe (by norm_num) (by omega) hq hnq domain
  have hConcrete :
      Nonempty (CapacityGapCertificate (1 / 4) domain 1 (4 * q)) ∧
        ((1 / 4 : ℝ) < (1 / 2 : ℝ) →
          ∀ received : Fin n → ZMod q,
            (agreeingPolynomials domain 1 (capacityAgreementThreshold (1 / 4) n 1)
              received).encard < ((4 * q : ℕ) : ℕ∞)) := by
    have hHalf : ¬ (1 / 2 : ℝ) ≤ (1 / 4 : ℝ) := by norm_num
    simpa only [ite_eq_right hHalf] using hInstance
  obtain ⟨⟨certificate⟩, hStrict⟩ := hConcrete
  exact ⟨n, q, hq, domain, hn, hnq, certificate,
    by simpa only [Fintype.card_fin] using certificate.lambda_le,
    certificate.decoderCertificate.card_le,
    certificate.pointwiseListBound _, hStrict (by norm_num)⟩

/-- At zero coordinates no list can have size strictly less than the block length. -/
example (received : Fin 0 → ZMod 2) :
    ¬ (agreeingPolynomials emptyDomain 0
      (capacityAgreementThreshold (1 / 4) 0 0) received).encard < (0 : ℕ∞) := by
  simp
