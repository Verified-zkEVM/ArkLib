/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.OrderZero.DecoderCertificate
public import ArkLib.Data.CodingTheory.ReedSolomon.AgreementList

/-!
# Explicit length-one and length-two order-zero branches

A positive gap makes the length-one threshold impossible. At length two, multiplicity one
has strict finite column surplus and the actual direct attempt succeeds. These are branch
certificates for the outer driver, not an implementation of that driver's runtime branching.
The public N=1 convention is unchanged, and characteristic premises remain explicit.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.OrderZeroDecoderCertificate

noncomputable section

open NonzeroInterpolationMachine PolynomialDifferential

/-- Every positive gap oversizes the length-one threshold for positive message dimension. -/
theorem threshold_one_oversized (delta : ℝ) (hdelta : 0 < delta) (k A : ℕ) (hk : 0 < k)
    (hA : ReedSolomon.agreementThreshold delta 1 k ≤ A) : 1 < A := by
  have h := (ReedSolomon.agreementThreshold_le_iff_real hdelta.le 1 k A).mp hA
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hgt : (1 : ℝ) < A := by push_cast at h; nlinarith
  exact_mod_cast hgt

/-- The exact length-one agreement set is empty, so its outer branch may return an empty list. -/
theorem agreeing_one_empty {F : Type*} [Field F] [DecidableEq F]
    (delta : ℝ) (hdelta : 0 < delta) (k A : ℕ) (hk : 0 < k)
    (hA : ReedSolomon.agreementThreshold delta 1 k ≤ A)
    (domain : Fin 1 ↪ F) (received : Fin 1 → F) :
    ReedSolomon.agreeingPolynomials domain k A received = ∅ := by
  exact ReedSolomon.agreeingPolynomials_eq_empty_of_card_lt
    (by simpa using threshold_one_oversized delta hdelta k A hk hA) received

/-- The exact integer quarter-gap threshold at length two is at least k+1. -/
theorem threshold_two_successor (delta : ℝ) (hdelta : (1 / 4 : ℝ) ≤ delta)
    (k A : ℕ) (hA : ReedSolomon.agreementThreshold delta 2 k ≤ A) : k + 1 ≤ A := by
  have h := zero_threshold_quarter delta hdelta 2 k A hA
  have hgt : (k : ℝ) < A := by push_cast at h; linarith
  have hn : k < A := by exact_mod_cast hgt
  omega

/-- Multiplicity one has strictly more than the two actual local constraints. -/
theorem two_column_surplus (k A : ℕ) (hk : 0 < k) (hA : k + 1 ≤ A) :
    2 < Fintype.card (ZeroInterpolationIndex (k - 1) 1 A) := by
  rw [card_zeroInterpolationIndex]
  simp only [Nat.one_mul, Nat.mul_one]
  rw [zeroStaircaseCount_succ, zeroStaircaseCount_succ]
  simp only [zeroStaircaseCount, Finset.range_zero, Finset.sum_empty, Nat.mul_zero,
    Nat.sub_zero, Nat.zero_add, Nat.mul_one]
  omega

variable {F : Type*} [Field F] [DecidableEq F]

/-- The actual length-two direct attempt has full certification and returned-polynomial bounds. -/
theorem two_attempt (delta : ℝ) (hdelta : (1 / 4 : ℝ) ≤ delta) (k A : ℕ) (hk : 0 < k)
    (hA : ReedSolomon.agreementThreshold delta 2 k ≤ A) (centers values : Fin 2 → F) :
    let D := k - 1
    let received := List.ofFn (fun i ↦ (centers i, values i))
    ∃ out c, run D 0 1 A received = (some out, c) ∧ Certified (d := 0) D 1 A received out ∧
      c ≤ zeroAttemptBudget 1 A 2 ∧
      let P := sourceOutput (d := 0) D 1 A out
      P ≠ 0 ∧ Eligible D 1 A P ∧ jetDegree P 0 < 2 ∧ differentialWeightedDegree D P < A ∧
        ∀ p ∈ received, localConstraintAt 1 p.1 p.2 P = 0 := by
  have hcount := two_column_surplus k A hk (threshold_two_successor delta hdelta k A hA)
  obtain ⟨Q, hne, he, hl⟩ := exists_zero_witness_of_count (k - 1) 1 A centers values
    (by simpa using hcount)
  have hlocal : ∀ p ∈ List.ofFn (fun i ↦ (centers i, values i)),
      localConstraintAt 1 p.1 p.2 Q = 0 := by
    intro p hp
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    exact hl i
  simpa only [List.length_ofFn, Nat.mul_one, Nat.one_mul] using
    direct_of_witness (k - 1) 1 A (List.ofFn (fun i ↦ (centers i, values i))) Q hne he hlocal

/-- Length-two returned output is below characteristic when the characteristic is at least two. -/
theorem two_attempt_characteristic (delta : ℝ) (hdelta : (1 / 4 : ℝ) ≤ delta)
    (k A : ℕ) (hk : 0 < k) (hA : ReedSolomon.agreementThreshold delta 2 k ≤ A)
    (hchar : 2 ≤ ringChar F) (centers values : Fin 2 → F) :
    let D := k - 1
    let received := List.ofFn (fun i ↦ (centers i, values i))
    ∃ out c, run D 0 1 A received = (some out, c) ∧ Certified (d := 0) D 1 A received out ∧
      c ≤ zeroAttemptBudget 1 A 2 ∧
      let P := sourceOutput (d := 0) D 1 A out
      P ≠ 0 ∧ Eligible D 1 A P ∧ jetDegree P 0 < 2 ∧ differentialWeightedDegree D P < A ∧
        (∀ j, jetDegree P j < ringChar F) ∧
        ∀ p ∈ received, localConstraintAt 1 p.1 p.2 P = 0 := by
  obtain ⟨out, c, hr, hc, hcost, hp, he, hj, hw, hl⟩ :=
    two_attempt delta hdelta k A hk hA centers values
  exact ⟨out, c, hr, hc, hcost, hp, he, hj, hw,
    returned_characteristic _ _ _ _ out hc hchar, hl⟩

end
end ReedSolomon.HiddenDerivative.OrderZeroDecoderCertificate
