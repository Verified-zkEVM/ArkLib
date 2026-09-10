/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.GeometricBound
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.Radius
/-! # Canonical codeword list cardinality from the geometric polynomial bound -/

@[expose] public section

open PolynomialDifferential


noncomputable section
namespace ReedSolomon
open ReedSolomon.ListDecoding
variable {F : Type*} [Field F]

open Classical in
/-- Forgetting the degree proof injects agreeing message polynomials into the
actual close polynomial set. -/
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
/-- A uniform real polynomial-list bound gives a canonical Lambda bound, rounded
up only when converting its real expression to a natural-number list size. -/
theorem lambda_le_ceil_of_closePolynomialSet_bound
    {δ : ℝ} (hδ : 0 ≤ δ) {n k : ℕ} (hn : 0 < n)
    (domain : Fin n ↪ F) (B : ℝ)
    (hB : ∀ received : Fin n → F,
      (closePolynomialSet domain received k (agreementThreshold δ n k)).Finite ∧
        ((closePolynomialSet domain received k (agreementThreshold δ n k)).ncard : ℝ) ≤ B) :
    Code.Lambda (ReedSolomon.code domain k : Set (Fin n → F)) (capacityRadius δ n k) ≤
      (Nat.ceil B : ℕ∞) := by
  classical
  apply lambda_le_of_forall_agreeingPolynomials_encard_le hδ hn domain
  intro received
  apply (agreeingPolynomials_encard_le_closePolynomialSet domain received).trans
  apply Set.encard_le_coe_iff_finite_ncard_le.mpr
  refine ⟨(hB received).1, ?_⟩
  have h := (hB received).2.trans (Nat.le_ceil B)
  exact_mod_cast h

open Classical in
/-- The canonical Reed--Solomon codeword-list function satisfies the prescribed
field-independent all-rate bound in characteristic zero or at least n. -/
theorem prescribed_geometric_lambda_bound
    (δ : ℝ) (n k : ℕ) (domain : Fin n ↪ F)
    (hδ : 0 < δ) (hδ' : δ < 1 / 4) (hk : 0 < k)
    (hblock : 8 * Nat.ceil
      (100 * (Nat.ceil (Real.exp ((27 / 10) / δ)) : ℝ) ^ 2 *
        harmonicNumber (Nat.ceil (Real.exp ((27 / 10) / δ)) - 1)) ≤ n)
    (hA : agreementThreshold δ n k ≤ n) (hchar : ringChar F = 0 ∨ n ≤ ringChar F) :
    let d := Nat.ceil (Real.exp ((27 / 10) / δ))
    let m := Nat.ceil (100 * (d : ℝ) ^ 2 * harmonicNumber (d - 1))
    Code.Lambda (ReedSolomon.code domain k : Set (Fin n → F)) (capacityRadius δ n k) ≤
      (Nat.ceil (4 * (m : ℝ) ^ 2 * (4 * m / δ) ^ d * n ^ d) : ℕ∞) := by
  classical
  have hn := (prescribed_geometric_parameters δ n k hδ hδ' hk hblock hA).1
  apply lambda_le_ceil_of_closePolynomialSet_bound hδ.le hn domain
  intro received
  exact prescribed_geometric_close_list_bound δ n k domain received hδ hδ' hk hblock hA hchar

end ReedSolomon
