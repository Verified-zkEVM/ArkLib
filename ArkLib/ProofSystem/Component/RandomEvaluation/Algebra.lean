/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.MvPolynomial.Multilinear
public import ArkLib.Data.MvPolynomial.SchwartzZippelCounting

/-!
# Random evaluation: relations and the Schwartz–Zippel bound

The claim `P = 0` for a multivariate polynomial `P` in `m` variables is reduced to the claim
`P(τ) = 0` at a uniform point `τ : Fin m → F`. If `P` is nonzero of total degree at most `d`, the
reduced claim holds with probability at most `d / |F|` (Schwartz–Zippel). For multilinear `P` the
total degree is at most `m`, giving the bound `m / |F|`.

The polynomial is a function of the statement and oracle statements, so it may be a virtual
polynomial that no party commits to.
-/

@[expose] public section

namespace RandomEvaluation

open MvPolynomial OracleComp
open scoped ENNReal

section Relations

variable (F : Type) (m : ℕ) (Statement : Type) {κ : Type} (OStatement : κ → Type)

/-- The input polynomial is identically zero. -/
def relIn [CommSemiring F]
    (P : Statement → (∀ i, OStatement i) → MvPolynomial (Fin m) F) :
    Set ((Statement × (∀ i, OStatement i)) × Unit) :=
  {p | P p.1.1 p.1.2 = 0}

/-- The polynomial vanishes at the sampled point. -/
def relOut [CommSemiring F]
    (P : Statement → (∀ i, OStatement i) → MvPolynomial (Fin m) F) :
    Set ((((Fin m → F) × Statement) × (∀ i, OStatement i)) × Unit) :=
  {p | eval p.1.1.1 (P p.1.1.2 p.1.2) = 0}

end Relations

variable {F : Type} [Field F] {m : ℕ}

/-- The bad event for a polynomial fixed before the challenge: it is nonzero but vanishes at
the sampled point. -/
def badEvent (P : MvPolynomial (Fin m) F) (τ : Fin m → F) : Prop :=
  P ≠ 0 ∧ eval τ P = 0

/-- Schwartz–Zippel: a polynomial of total degree at most `d` is nonzero and vanishes at a
uniform point with probability at most `d / |F|`. -/
theorem badEvent_bound [Fintype F] [SampleableType F]
    (P : MvPolynomial (Fin m) F) (d : ℕ) (hP : P.totalDegree ≤ d) :
    Pr{let τ ← $ᵗ (Fin m → F)}[badEvent P τ] ≤ (d : ℝ≥0∞) / Fintype.card F := by
  classical
  unfold badEvent
  by_cases hzero : P = 0
  · simp only [hzero, ne_eq, not_true_eq_false, false_and]
    simp
  · simp only [ne_eq, hzero, not_false_eq_true, true_and]
    exact prob_eval_zero_univ_le_div P hzero hP

/-- A polynomial of degree at most one in each of its `m` variables has total degree at most
`m`. -/
theorem totalDegree_le_of_degreeOf_le_one (P : MvPolynomial (Fin m) F)
    (hP : ∀ i, degreeOf i P ≤ 1) : P.totalDegree ≤ m := by
  simpa using totalDegree_le_card_mul_of_mem_restrictDegree P 1
    ((mem_restrictDegree_iff_degreeOf_le _ _).mpr hP)

/-- The multilinear case of `badEvent_bound`, with error `m / |F|`. -/
theorem badEvent_bound_of_degreeOf_le_one [Fintype F] [SampleableType F]
    (P : MvPolynomial (Fin m) F) (hP : ∀ i, degreeOf i P ≤ 1) :
    Pr{let τ ← $ᵗ (Fin m → F)}[badEvent P τ] ≤ (m : ℝ≥0∞) / Fintype.card F :=
  badEvent_bound P m (totalDegree_le_of_degreeOf_le_one P hP)

end RandomEvaluation
