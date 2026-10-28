/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.MvPolynomial.Multilinear
public import ArkLib.Data.MvPolynomial.SchwartzZippelCounting

/-!
# Multilinear zero-check

A nonzero multilinear polynomial in `m` variables vanishes at a uniform field point with
probability at most `m / |F|`.
-/

@[expose] public section

namespace ZeroCheck

open MvPolynomial OracleComp
open scoped ENNReal

section Relations

variable (F : Type) (m : ℕ) (Statement : Type) {κ : Type} (OStatement : κ → Type)

/-- The input polynomial is identically zero. -/
def relIn [CommSemiring F]
    (P : Statement → (∀ i, OStatement i) → MvPolynomial (Fin m) F) :
    Set ((Statement × (∀ i, OStatement i)) × Unit) :=
  {p | P p.1.1 p.1.2 = 0}

/-- The polynomial vanishes at the sampled vector. -/
def relOut [CommSemiring F]
    (P : Statement → (∀ i, OStatement i) → MvPolynomial (Fin m) F) :
    Set ((((Fin m → F) × Statement) × (∀ i, OStatement i)) × Unit) :=
  {p | eval p.1.1.1 (P p.1.1.2 p.1.2) = 0}

end Relations

variable {F : Type} [Field F] {m : ℕ}

/-- The zero-check bad event for a polynomial fixed before the challenge. -/
def badEvent (P : MvPolynomial (Fin m) F) (τ : Fin m → F) : Prop :=
  P ≠ 0 ∧ eval τ P = 0

/-- A nonzero multilinear polynomial passes the random zero-check with probability at most
`m / |F|`, including the zero-dimensional case. -/
theorem badEvent_bound [Fintype F] [SampleableType F]
    (P : MvPolynomial (Fin m) F) (hP : ∀ i, degreeOf i P ≤ 1) :
    Pr{let τ ← $ᵗ (Fin m → F)}[badEvent P τ] ≤
      (m : ℝ≥0∞) / Fintype.card F := by
  classical
  unfold badEvent
  by_cases hzero : P = 0
  · simp only [hzero, ne_eq, not_true_eq_false, false_and]
    simp
  · simp only [ne_eq, hzero, not_false_eq_true, true_and]
    apply prob_eval_zero_univ_le_div P hzero
    simpa using totalDegree_le_card_mul_of_mem_restrictDegree P 1
      ((mem_restrictDegree_iff_degreeOf_le _ _).mpr hP)

end ZeroCheck
