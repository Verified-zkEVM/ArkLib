/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.GeometricCounting
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Counting.TaylorCharZeroSolutions
public import ArkLib.Data.CodingTheory.ReedSolomon.AgreementList
/-!
# List bounds from a differential equation and the actual agreement gap

An equation of derivative order `d` and total jet degree at most `ν` explains a
finite close family. Taylor reconstruction and geometric counting bound that family
by `ν² (2ν/δ)^d n^d`, provided the actual message/recognition gap is at least `δn`.
The ambient dimension `K` may exceed the message dimension `k`; its role is only
to support interpolation and Taylor reconstruction.

This common consumer has no multiplicity or rate-specific parameter recipe. The
rate constructors prove its equation hypotheses, including characteristic zero.
-/

@[expose] public section

noncomputable section

open Polynomial PolynomialDifferential

namespace ReedSolomon

open HiddenDerivative

/-- The geometric root count with an independent jet cap and exact characteristic guards. -/
theorem finite_list_bound_of_equation {F : Type*} [Field F]
    {n k A K d ν : ℕ} {δ : ℝ}
    (domain : Fin n ↪ F) (received : Fin n → F)
    (Q : DifferentialPolynomial F d) (hQ : Q ≠ 0)
    (hdegree : jetTotalDegree Q ≤ ν)
    (hk : 0 < k) (hkK : k ≤ K) (hdK : d < K) (hKn : K ≤ n)
    (hkA : k ≤ A) (hAn : A ≤ n) (hν : 0 < ν) (hδ : 0 < δ)
    (hgap : (k : ℝ) + δ * n ≤ A)
    (hchar : ringChar F = 0 ∨ max (K - 1) ν < ringChar F)
    (S : Finset F[X])
    (hS : ∀ P ∈ S, IsAgreementSolution domain received k A P)
    (hsound : ∀ P ∈ S, differentialSpecialization Q P = 0) :
    (S.card : ℝ) ≤ (ν : ℝ) ^ 2 * (2 * ν / δ) ^ d * n ^ d := by
  have hn : 0 < n := hk.trans_le (hkK.trans hKn)
  have hK : 0 < K := hk.trans_le hkK
  have hbin : ∀ r, r ≤ d → ∀ i, r < i → i < K → (i.choose r : F) ≠ 0 := by
    intro r _ i hri hi
    apply binomial_pivots_of_characteristic (K := K) ?_ r i hri hi
    apply hchar.imp_right
    intro hc
    have := (Nat.le_max_left (K - 1) ν).trans_lt hc
    omega
  have hcount : (S.card : ℚ) ≤ (ν : ℚ) ^ 2 *
      (((n * (1 + 2 * K * (ν - 1)) : ℕ) : ℚ) / (A - k + 1 : ℕ)) ^ d := by
    rcases hchar with hz | hp
    · have : CharP F 0 := hz ▸ inferInstanceAs (CharP F (ringChar F))
      have : CharZero F := CharP.charP_to_charZero F
      exact finite_agreement_solutions_card_le_charZero Q K k ν hdK hkK hQ hdegree
        domain received hk hkA hAn hbin S hsound hS
    · have hc : IsBelowCharacteristic (k - 1) Q := by
        refine ⟨?_, ?_⟩
        · exact (Nat.sub_le_sub_right hkK 1).trans_lt
            ((Nat.le_max_left _ _).trans_lt hp)
        · intro j
          exact ((jetDegree_le_total Q j).trans hdegree).trans_lt
            ((Nat.le_max_right _ _).trans_lt hp)
      exact finite_agreement_solutions_card_le Q K k ν hdK hkK hQ hc hdegree
        domain received hk hkA hAn hbin S hsound hS
  have hcountR : (S.card : ℝ) ≤ (ν : ℝ) ^ 2 *
      (((n * (1 + 2 * K * (ν - 1)) : ℕ) : ℝ) / (A - k + 1 : ℕ)) ^ d := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hcount
    simpa only [Rat.cast_natCast, Rat.cast_mul, Rat.cast_pow, Rat.cast_div] using hc
  calc
    (S.card : ℝ) ≤ (ν : ℝ) ^ 2 *
        (((n * (1 + 2 * K * (ν - 1)) : ℕ) : ℝ) / (A - k + 1 : ℕ)) ^ d := hcountR
    _ ≤ (ν : ℝ) ^ 2 * ((2 * ν / δ) * n) ^ d := by
      gcongr
      exact geometric_ratio_le hn hν hδ hKn hkA hgap
    _ = (ν : ℝ) ^ 2 * (2 * ν / δ) ^ d * n ^ d := by rw [mul_pow, mul_assoc]

open Classical in
/-- Bounding every close polynomial by one equation bounds the whole list, including zero. -/
theorem close_list_bound_of_equation {F : Type*} [Field F]
    {n k A K d ν : ℕ} {δ : ℝ}
    (domain : Fin n ↪ F) (received : Fin n → F)
    (Q : DifferentialPolynomial F d) (hQ : Q ≠ 0)
    (hdegree : jetTotalDegree Q ≤ ν)
    (hk : 0 < k) (hkK : k ≤ K) (hdK : d < K) (hKn : K ≤ n)
    (hkA : k ≤ A) (hAn : A ≤ n) (hν : 0 < ν) (hδ : 0 < δ)
    (hgap : (k : ℝ) + δ * n ≤ A)
    (hchar : ringChar F = 0 ∨ max (K - 1) ν < ringChar F)
    (hsound : ∀ P, IsAgreementSolution domain received k A P →
      differentialSpecialization Q P = 0) :
    (closePolynomialSet domain received k A).Finite ∧
      ((closePolynomialSet domain received k A).ncard : ℝ) ≤
        (ν : ℝ) ^ 2 * (2 * ν / δ) ^ d * n ^ d := by
  classical
  have hfin := closePolynomialSet_finite domain received hkA
  refine ⟨hfin, ?_⟩
  rw [Set.ncard_eq_toFinset_card _ hfin]
  exact finite_list_bound_of_equation domain received Q hQ hdegree hk hkK hdK hKn
    hkA hAn hν hδ hgap hchar hfin.toFinset
    (fun _ hP ↦ hfin.mem_toFinset.mp hP)
    (fun P hP ↦ hsound P (hfin.mem_toFinset.mp hP))

end ReedSolomon
