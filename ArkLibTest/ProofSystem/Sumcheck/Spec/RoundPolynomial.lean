/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/
import ArkLib.ProofSystem.Sumcheck.Spec.RoundPolynomial

/-! # Selected-coordinate degree controls for honest sum-check rounds

The coordinate-line controls of PR #1128 live in `ArkLibTest/Data/MvPolynomial/EvalExcept.lean`.
These examples apply the round-polynomial statements to a last round whose polynomial does not
depend on the round's variable.
-/

namespace Sumcheck.Spec.SingleRound.RoundPolynomialTest

open MvPolynomial

noncomputable section

/-- The polynomial does not depend on coordinate one, despite its global degree cap three. -/
def polynomial : OracleStatement ℤ 2 3 () := ⟨X 0, by
  rw [mem_restrictDegree_iff_degreeOf_le]
  intro i
  simp only [degreeOf_X]
  split <;> omega⟩

/-- A singleton domain is enough for this last-round control. -/
def domain : Fin 1 ↪ ℤ := ⟨fun _ ↦ 0, fun _ _ _ ↦ Subsingleton.elim _ _⟩

/-- A previously fixed coordinate gives a constant polynomial in the last round. -/
theorem last_round_constant :
    (projectedRoundPolynomial ℤ 2 3 domain 1 (fun _ ↦ 5) polynomial).val =
      Polynomial.C 5 := by
  rw [projectedRoundPolynomial_eq_sum_eval₂]
  have h (s : Fin 1 → Polynomial ℤ) :
      Fin.insertNth (α := fun _ : Fin 2 ↦ Polynomial ℤ) 1 Polynomial.X s 0 = s 0 := by
    rw [Fin.insertNth_apply_below (by decide)]
    rfl
  simp [polynomial, roundSuffix, h, Fin.append, Fin.addCases]

/-- The coordinate bound is zero, sharper than the global cap three. -/
theorem last_round_degree_zero :
    (projectedRoundPolynomial ℤ 2 3 domain 1 (fun _ ↦ 5) polynomial).val.natDegree = 0 := by
  apply Nat.eq_zero_of_le_zero
  simpa [polynomial, degreeOf_X] using
    projectedRoundPolynomial_natDegree_le domain (1 : Fin 2) (fun _ ↦ 5) polynomial

end
end Sumcheck.Spec.SingleRound.RoundPolynomialTest
