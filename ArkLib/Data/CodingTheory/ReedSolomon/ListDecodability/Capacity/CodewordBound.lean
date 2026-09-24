/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.Basic
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.GeometricBound

/-!
# Capacity-radius codeword bounds

This module transfers bounds on Reed–Solomon polynomial agreement lists to the canonical
codeword-list function. It also instantiates that transfer with the prescribed geometric bound.

## Main statements

* `agreeingPolynomials_encard_le_closePolynomialSet`: message polynomials inject into the
  complete close-polynomial set after forgetting the degree proof.
* `lambda_le_ceil_of_closePolynomialSet_bound`: a uniform real-valued close-list bound gives a
  rounded natural-number `Code.Lambda` bound.
* `prescribed_geometric_lambda_bound`: the prescribed field-independent geometric bound for
  `Code.Lambda`.

## References

* [DKTZ26]
-/

@[expose] public section

open PolynomialDifferential

noncomputable section

namespace ReedSolomon

variable {F : Type*} [Field F]

open ListDecoding
open HiddenDerivative
open HiddenDerivative.WeightedSupportParameters

open Classical in
/-- Every agreeing message polynomial determines a polynomial in the complete close list. -/
theorem agreeingPolynomials_encard_le_closePolynomialSet {n k A : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F) :
    (agreeingPolynomials domain k A received).encard ≤
      (closePolynomialSet domain received k A).encard := by
  classical
  apply Set.encard_le_encard_of_injOn (f := fun P : MessagePolynomial F k ↦ P.val)
  · intro P hP
    exact ⟨Polynomial.mem_degreeLT.mp P.property, hP⟩
  · exact Subtype.val_injective.injOn

open Classical in
/-- A uniform real bound on close polynomial lists gives a rounded bound on `Code.Lambda`. -/
theorem lambda_le_ceil_of_closePolynomialSet_bound
    {δ : ℝ} (hδ : 0 ≤ δ) {n k : ℕ} (hn : 0 < n)
    (domain : Fin n ↪ F) (B : ℝ)
    (hB : ∀ received : Fin n → F,
      (closePolynomialSet domain received k (agreementThreshold δ n k)).Finite ∧
        ((closePolynomialSet domain received k (agreementThreshold δ n k)).ncard : ℝ) ≤ B) :
    Code.Lambda (ReedSolomon.code domain k : Set (Fin n → F)) (capacityRadius δ n k) ≤
      (Nat.ceil B : ℕ∞) := by
  classical
  have hBound : ∀ received : Fin n → F,
      (agreeingPolynomials domain k
        (agreementThreshold δ (Fintype.card (Fin n)) k) received).encard ≤
        (Nat.ceil B : ℕ∞) := by
    intro received
    apply (agreeingPolynomials_encard_le_closePolynomialSet
      (A := agreementThreshold δ (Fintype.card (Fin n)) k) domain received).trans
    apply Set.encard_le_coe_iff_finite_ncard_le.mpr
    have hclose := hB received
    refine ⟨?_, ?_⟩
    · simpa only [Fintype.card_fin] using hclose.1
    · have hclose' : ((closePolynomialSet domain received k
          (agreementThreshold δ (Fintype.card (Fin n)) k)).ncard : ℝ) ≤ B := by
        simpa only [Fintype.card_fin] using hclose.2
      exact_mod_cast hclose'.trans (Nat.le_ceil B)
  have hLambda := lambda_le_of_forall_agreeingPolynomials_encard_le hδ
    (by simpa using hn) (domain := domain) (messageDim := k) (Nat.ceil B : ℕ∞) hBound
  simpa only [Fintype.card_fin] using hLambda

open Classical in
/-- The prescribed field-independent geometric bound holds for the canonical Reed–Solomon
codeword-list function. -/
theorem prescribed_geometric_lambda_bound
    (δ : ℝ) (n k : ℕ) (domain : Fin n ↪ F)
    (hδ : 0 < δ) (hδ' : δ < 1 / 4) (hk : 0 < k)
    (hblock :
      let d := Nat.ceil (Real.exp (xi / δ))
      let m := Nat.ceil (100 * (d : ℝ) ^ 2 * harmonic (d - 1))
      8 * m ≤ n)
    (hA : agreementThreshold δ n k ≤ n) (hchar : ringChar F = 0 ∨ n ≤ ringChar F) :
    let d := Nat.ceil (Real.exp (xi / δ))
    let m := Nat.ceil (100 * (d : ℝ) ^ 2 * harmonic (d - 1))
    Code.Lambda (ReedSolomon.code domain k : Set (Fin n → F)) (capacityRadius δ n k) ≤
      (Nat.ceil (4 * (m : ℝ) ^ 2 * (4 * m / δ) ^ d * n ^ d) : ℕ∞) := by
  classical
  have hn := (prescribed_geometric_parameters δ n k hδ hδ' hblock hA).1
  apply lambda_le_ceil_of_closePolynomialSet_bound hδ.le hn domain
  intro received
  exact prescribed_geometric_close_list_bound δ n k domain received hδ hδ' hk hblock hA hchar

end ReedSolomon
