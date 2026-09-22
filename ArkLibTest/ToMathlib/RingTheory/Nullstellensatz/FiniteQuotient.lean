/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.RingTheory.Nullstellensatz.FiniteQuotient

/-!
# Acceptance tests for finite-quotient zero-locus bounds

The examples check the source cardinality contract through an ordinary import, including an
infinite variable type, and exercise both boundary coordinate quotients. For the top ideal the
quotient is the zero algebra and its zero locus is empty. With no variables and the bottom ideal,
the quotient is the nontrivial one-dimensional base algebra and the zero locus is the singleton
empty tuple. The Krull-dimension-zero form is applied to maximal ideals in three variables, whose
quotients are fields, and to the unit ideal, whose quotient is the zero ring.
-/

open MvPolynomial

/-- The public API does not require finitely many variables, a proper or radical ideal, or an
algebraically closed coordinate field. -/
example {k K : Type*} [Field k] [Field K] [Algebra k K]
    (I : Ideal (MvPolynomial ℕ k)) [Module.Finite k (MvPolynomial ℕ k ⧸ I)] :
    (zeroLocus K I).Finite ∧
      (zeroLocus K I).ncard ≤ Module.finrank k (MvPolynomial ℕ k ⧸ I) :=
  ⟨finite_zeroLocus_of_finite_quotient I, ncard_zeroLocus_le_finrank_quotient I⟩

/-- For the top ideal, the coordinate quotient is the zero algebra: there are no points and both
sides of the cardinality bound are zero. This checks that no properness hypothesis is needed. -/
example :
    (zeroLocus ℚ (⊤ : Ideal (MvPolynomial ℕ ℚ))).ncard = 0 ∧
      Module.finrank ℚ (MvPolynomial ℕ ℚ ⧸ (⊤ : Ideal (MvPolynomial ℕ ℚ))) = 0 ∧
        (zeroLocus ℚ (⊤ : Ideal (MvPolynomial ℕ ℚ))).Finite ∧
          (zeroLocus ℚ (⊤ : Ideal (MvPolynomial ℕ ℚ))).ncard ≤
            Module.finrank ℚ (MvPolynomial ℕ ℚ ⧸ (⊤ : Ideal (MvPolynomial ℕ ℚ))) := by
  refine ⟨by simp, Module.finrank_eq_zero_of_subsingleton ℚ
    (MvPolynomial ℕ ℚ ⧸ (⊤ : Ideal (MvPolynomial ℕ ℚ))), ?_, ?_⟩
  · exact finite_zeroLocus_of_finite_quotient (K := ℚ) (⊤ : Ideal (MvPolynomial ℕ ℚ))
  · exact ncard_zeroLocus_le_finrank_quotient (K := ℚ) (⊤ : Ideal (MvPolynomial ℕ ℚ))

/-- With no variables and no equations, the only point is the empty tuple. The quotient is the
one-dimensional base algebra, so the bound is attained. -/
example :
    (zeroLocus ℚ (⊥ : Ideal (MvPolynomial Empty ℚ))).ncard = 1 ∧
      Module.finrank ℚ (MvPolynomial Empty ℚ ⧸
        (⊥ : Ideal (MvPolynomial Empty ℚ))) = 1 ∧
        (zeroLocus ℚ (⊥ : Ideal (MvPolynomial Empty ℚ))).Finite ∧
          (zeroLocus ℚ (⊥ : Ideal (MvPolynomial Empty ℚ))).ncard ≤
            Module.finrank ℚ (MvPolynomial Empty ℚ ⧸
              (⊥ : Ideal (MvPolynomial Empty ℚ))) := by
  refine ⟨by simp, ?_, ?_, ?_⟩
  · calc
      Module.finrank ℚ (MvPolynomial Empty ℚ ⧸ (⊥ : Ideal (MvPolynomial Empty ℚ))) =
          Module.finrank ℚ (MvPolynomial Empty ℚ) :=
        LinearEquiv.finrank_eq (AlgEquiv.quotientBot ℚ (MvPolynomial Empty ℚ)).toLinearEquiv
      _ = Module.finrank ℚ ℚ :=
        LinearEquiv.finrank_eq (MvPolynomial.isEmptyAlgEquiv ℚ Empty).toLinearEquiv
      _ = 1 := by simp
  · exact finite_zeroLocus_of_finite_quotient (K := ℚ) (⊥ : Ideal (MvPolynomial Empty ℚ))
  · exact ncard_zeroLocus_le_finrank_quotient (K := ℚ) (⊥ : Ideal (MvPolynomial Empty ℚ))

/-- The Krull-dimension-zero form applies to every maximal ideal in finitely many variables: the
quotient is a field, so it has Krull dimension zero, and the zero locus over any extension is
finite with at most `finrank` points. -/
example {k K : Type*} [Field k] [Field K] [Algebra k K] (I : Ideal (MvPolynomial (Fin 3) k))
    [I.IsMaximal] :
    (zeroLocus K I).Finite ∧
      (zeroLocus K I).ncard ≤ Module.finrank k (MvPolynomial (Fin 3) k ⧸ I) := by
  have : Ring.KrullDimLE 0 (MvPolynomial (Fin 3) k ⧸ I) := by
    let := Ideal.Quotient.field I
    infer_instance
  exact finite_zeroLocus_and_ncard_le_of_krullDimLE_zero I

/-- For the unit ideal the quotient is the zero ring, which has Krull dimension zero vacuously;
both sides of the bound are zero. -/
example {k K : Type*} [Field k] [Field K] [Algebra k K] :
    (zeroLocus K (⊤ : Ideal (MvPolynomial (Fin 2) k))).ncard ≤
      Module.finrank k (MvPolynomial (Fin 2) k ⧸ (⊤ : Ideal (MvPolynomial (Fin 2) k))) :=
  (finite_zeroLocus_and_ncard_le_of_krullDimLE_zero ⊤).2
