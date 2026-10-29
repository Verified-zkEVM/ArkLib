/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Plonk.Batch.Data

/-! # Plonk quotient domain

The row domain has cardinality `n` and nodal polynomial `X ^ n - 1`. Its nodal evaluation
therefore uses only powering and subtraction.
-/

@[expose] public section

namespace Plonk.Quotient

variable {F : Type} [Field F] [DecidableEq F] {n : ℕ}

/-- The finite row domain has exactly one point for each row. -/
theorem points_card (ω : F) (hω : IsPrimitiveRoot ω n) :
    (Batch.points ω hω).card = n := by
  rw [Batch.points, Finset.card_image_of_injective _
    (EvaluationDomain.primitiveRoot ω hω).injective]
  simp

/-- The row-domain nodal polynomial is the roots-of-unity polynomial. -/
theorem nodal_eq (ω : F) (hω : IsPrimitiveRoot ω n) (hn : 0 < n) :
    Lagrange.nodal (Batch.points ω hω) id = Polynomial.X ^ n - 1 := by
  have hdegree : Polynomial.degree (1 : Polynomial F) <
      Polynomial.degree ((Polynomial.X : Polynomial F) ^ n) := by
    simpa using hn
  apply Polynomial.eq_of_degree_le_of_eval_index_eq
    (v := id) (Batch.points ω hω) Function.injective_id.injOn
  · exact Lagrange.degree_nodal.le
  · rw [Lagrange.degree_nodal, points_card,
      Polynomial.degree_sub_eq_left_of_degree_lt hdegree]
    simp
  · rw [Lagrange.nodal_monic, Polynomial.leadingCoeff_sub_of_degree_lt hdegree,
      Polynomial.monic_X_pow]
  · intro x hx
    rw [Lagrange.eval_nodal_at_node hx]
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    simp only [id_eq, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_one, EvaluationDomain.primitiveRoot_node]
    rw [← pow_mul, Nat.mul_comm, pow_mul, hω.pow_eq_one, one_pow, sub_self]

/-- Nodal evaluation on the row domain is the power expression `z ^ n - 1`. -/
theorem eval_nodal (ω : F) (hω : IsPrimitiveRoot ω n) (hn : 0 < n) (z : F) :
    (Lagrange.nodal (Batch.points ω hω) id).eval z = z ^ n - 1 := by
  rw [nodal_eq ω hω hn]
  simp

end Plonk.Quotient
