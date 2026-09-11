/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.FirstOrder.FiniteLengthParameters
public import ArkLib.Data.CodingTheory.ReedSolomon.AgreementList

/-!
# Semantic finite-length first-order list bounds

This module applies the squarefree fixed-word theorem to an actual finite interpolation
certificate.  It gives the complete close-polynomial set, not an assumed list, and retains the
exact positive-characteristic guard `p > max(k - 1, M)`.
-/

@[expose] public section

open Polynomial

namespace ReedSolomon.FirstOrder

open ReedSolomon.HiddenDerivative
open ReedSolomon.HiddenDerivative.SymbolicReceivedInterpolation
open ReedSolomon.FirstOrder.Squarefree

noncomputable section

set_option autoImplicit false

universe u

open Classical in
private theorem mem_closePolynomialSet_iff_isAgreementSolution
    {F : Type*} [Field F] {n k A : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F) (P : F[X]) :
    P ∈ closePolynomialSet domain received k A ↔
      IsAgreementSolution domain received k A P := by
  unfold closePolynomialSet IsAgreementSolution
  constructor
  · intro hP
    refine ⟨hP.1, ?_⟩
    convert hP.2 using 1
    congr 1
  · intro hP
    refine ⟨hP.1, ?_⟩
    convert hP.2 using 1
    congr 1

open Classical in
/-- For message dimension zero or one, elementary agreement incidence gives the same
finite-length envelope without a characteristic hypothesis or an interpolation certificate.
This includes the zero code and the nonempty block-length-one boundary. -/
theorem closePolynomialSet_finite_and_card_le_finiteLength_of_dimension_le_one
    {F : Type u} [Field F] {C eta : ℝ} {n k A : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F)
    (hn : 1 ≤ n) (hk : k ≤ 1) (hkA : k ≤ A)
    (hC : 1 ≤ C) (heta : 0 < eta) (hsOne : finiteLengthSlack eta n ≤ 1) :
    (closePolynomialSet domain received k A).Finite ∧
      ((closePolynomialSet domain received k A).ncard : ℝ) ≤
        7 * C ^ 3 * n / finiteLengthSlack eta n ^ 2 := by
  obtain ⟨list, hlist, hincidence⟩ :=
    exists_closePolynomial_finset_with_incidence_bound domain received hkA
  have hcard : list.card ≤ n := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl | rfl
    · simp only [Nat.choose_zero_right, mul_one] at hincidence
      exact hincidence.trans hn
    · have hA : 1 ≤ A := hkA
      calc
        list.card ≤ list.card * A := Nat.le_mul_of_pos_right _ (by omega)
        _ ≤ n := by simpa using hincidence
  have hfinite : (closePolynomialSet domain received k A).Finite :=
    closePolynomialSet_finite domain received hkA
  refine ⟨hfinite, ?_⟩
  have hfinset : hfinite.toFinset = list := by
    ext P
    rw [hfinite.mem_toFinset]
    exact (hlist P).symm
  rw [Set.ncard_eq_toFinset_card _ hfinite, hfinset]
  have hcardReal : (list.card : ℝ) ≤ n := by exact_mod_cast hcard
  apply hcardReal.trans
  have hs := finiteLengthSlack_pos heta (by omega : 0 < n)
  have hsSq : finiteLengthSlack eta n ^ 2 ≤ 1 :=
    pow_le_one₀ hs.le hsOne
  have hCPow : (1 : ℝ) ≤ C ^ 3 := one_le_pow₀ hC
  rw [le_div_iff₀ (sq_pos_of_pos hs)]
  have hn0 : (0 : ℝ) ≤ n := by positivity
  nlinarith [mul_nonneg hn0 (sub_nonneg.mpr hsSq),
    mul_nonneg hn0 (sub_nonneg.mpr hCPow)]

open Classical in
/-- Simpler inverse-`eta` consequence for dimensions zero and one. -/
theorem closePolynomialSet_finite_and_card_le_inv_eta_of_dimension_le_one
    {F : Type u} [Field F] {C eta : ℝ} {n k A : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F)
    (hn : 1 ≤ n) (hk : k ≤ 1) (hkA : k ≤ A)
    (hC : 1 ≤ C) (heta : 0 < eta) (hsOne : finiteLengthSlack eta n ≤ 1) :
    (closePolynomialSet domain received k A).Finite ∧
      ((closePolynomialSet domain received k A).ncard : ℝ) ≤
        7 * C ^ 3 * n / eta ^ 2 := by
  obtain ⟨hfinite, hcard⟩ :=
    closePolynomialSet_finite_and_card_le_finiteLength_of_dimension_le_one
      domain received hn hk hkA hC heta hsOne
  refine ⟨hfinite, hcard.trans ?_⟩
  exact div_finiteLengthSlack_sq_le_div_eta_sq
    (by positivity : 0 ≤ 7 * C ^ 3 * (n : ℝ)) heta (by omega)

open Classical in
/-- An actual finite first-order certificate whose exact caps are bounded by
`C / (eta + 1/n)` gives a complete squarefree list of size
`7 C³ n / (eta + 1/n)²`.

The theorem covers every `n ≥ 2`, including `k = n` and `A = n`.  The positive derivative-cap
hypothesis identifies the squarefree branch; a zero cap belongs to the ordinary endpoint. -/
theorem closePolynomialSet_finite_and_card_le_finiteLength_of_certificate
    {F : Type u} [Field F] {C eta : ℝ}
    {D A m M mu k h n N : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F)
    (columns : Fin N → SourceColumn 1)
    (cert : FirstOrderSymbolicCertificate.{u, u} (F := F)
      D A m M mu k h domain received (fun _ ↦ 0) columns)
    (hn : 2 ≤ n) (hk : 2 ≤ k) (hkn : k ≤ n) (hkA : k ≤ A) (hAn : A ≤ n)
    (hM : 1 ≤ M) (hMmu : M ≤ mu)
    (hchar : ringChar F = 0 ∨ max (k - 1) M < ringChar F)
    (hC : 1 ≤ C) (heta : 0 < eta) (hsOne : finiteLengthSlack eta n ≤ 1)
    (hlambda : ((n - k + 1 : ℕ) : ℝ) / (A - k + 1 : ℕ) ≤ C)
    (hmu : (mu : ℝ) ≤ C / finiteLengthSlack eta n) :
    (closePolynomialSet domain received k A).Finite ∧
      ((closePolynomialSet domain received k A).ncard : ℝ) ≤
        7 * C ^ 3 * n / finiteLengthSlack eta n ^ 2 := by
  let T := closePolynomialSet domain received k A
  let lambda : ℝ := ((n - k + 1 : ℕ) : ℝ) / (A - k + 1 : ℕ)
  let bound : ℝ := 7 * C ^ 3 * n / finiteLengthSlack eta n ^ 2
  have hlambda0 : 0 ≤ lambda := by
    dsimp only [lambda]
    positivity
  have hsem (S : Finset F[X])
      (hS : ∀ P ∈ S, IsAgreementSolution domain received k A P) :
      (S.card : ℝ) ≤ bound := by
    have hraw := firstOrder_finite_agreement_solutions_card_le_squarefree
      domain received columns cert hk hkn hkA hAn hM hMmu hchar S hS
    apply hraw.trans
    have hnumeric := squarefreeListExpression_le_finiteLength
      hC heta (show 1 ≤ n by omega) hsOne (show 1 ≤ k - 1 by omega)
      (show k - 1 ≤ n by omega) hM hMmu hlambda0 (by simpa only [lambda] using hlambda) hmu
    simpa only [lambda, bound, show k - 1 + 1 = k by omega,
      show 2 * (k - 1) - 1 = 2 * k - 3 by omega, mul_div_assoc] using hnumeric
  have hfinite : T.Finite := closePolynomialSet_finite domain received hkA
  refine ⟨hfinite, ?_⟩
  rw [Set.ncard_eq_toFinset_card _ hfinite]
  exact hsem hfinite.toFinset (fun P hP ↦
    (mem_closePolynomialSet_iff_isAgreementSolution domain received P).mp
      (hfinite.mem_toFinset.mp hP))

open Classical in
/-- Simpler inverse-`eta` consequence of the finite-length complete-list theorem. -/
theorem closePolynomialSet_finite_and_card_le_inv_eta_of_certificate
    {F : Type u} [Field F] {C eta : ℝ}
    {D A m M mu k h n N : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F)
    (columns : Fin N → SourceColumn 1)
    (cert : FirstOrderSymbolicCertificate.{u, u} (F := F)
      D A m M mu k h domain received (fun _ ↦ 0) columns)
    (hn : 2 ≤ n) (hk : 2 ≤ k) (hkn : k ≤ n) (hkA : k ≤ A) (hAn : A ≤ n)
    (hM : 1 ≤ M) (hMmu : M ≤ mu)
    (hchar : ringChar F = 0 ∨ max (k - 1) M < ringChar F)
    (hC : 1 ≤ C) (heta : 0 < eta) (hsOne : finiteLengthSlack eta n ≤ 1)
    (hlambda : ((n - k + 1 : ℕ) : ℝ) / (A - k + 1 : ℕ) ≤ C)
    (hmu : (mu : ℝ) ≤ C / finiteLengthSlack eta n) :
    (closePolynomialSet domain received k A).Finite ∧
      ((closePolynomialSet domain received k A).ncard : ℝ) ≤
        7 * C ^ 3 * n / eta ^ 2 := by
  obtain ⟨hfinite, hcard⟩ :=
    closePolynomialSet_finite_and_card_le_finiteLength_of_certificate
      domain received columns cert hn hk hkn hkA hAn hM hMmu hchar hC heta hsOne
        hlambda hmu
  refine ⟨hfinite, hcard.trans ?_⟩
  exact div_finiteLengthSlack_sq_le_div_eta_sq
    (by positivity : 0 ≤ 7 * C ^ 3 * (n : ℝ)) heta (by omega)

end

end ReedSolomon.FirstOrder
