/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Differential.RegularJetCount
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Acceptance tests for counting regular jets

* For `Y₀ ^ 2 = 1` over `ZMod 3` at depth `0`, the theorem bounds the regular jets at each point
  by `jetDegree = 2`, and the two jets `1` and `2` are regular, so the bound is attained.
* The bound `jetDegree Q s * q ^ (d + 1)` on all regular point-jet pairs follows from
  `natCard_regularJet_le`.
* The zero differential polynomial has no regular jets, as the theorem computes from
  `jetDegree 0 s = 0`.
* Over `ZMod 4`, the equation `2 Y₀ = 0` has the two regular jets `0` and `2` at every point
  while `jetDegree = 1`, so the domain hypothesis is needed.
-/

namespace PolynomialDifferential

noncomputable section

open MvPolynomial Finset

/-- The equation `Y₀ ^ 2 - 1 = 0` over `ZMod 3` at depth `0`. -/
private abbrev squareEquation : DifferentialPolynomial (ZMod 3) 0 :=
  X (some 0) ^ 2 - 1

private theorem jetDegree_squareEquation_le : jetDegree squareEquation 0 ≤ 2 := by
  refine (degreeOf_sub_le _ _ _).trans (max_le ?_ ?_)
  · exact (degreeOf_pow_le _ _ _).trans (by simp)
  · rw [← C_1, degreeOf_C]; exact Nat.zero_le _

private theorem isRegularJet_squareEquation (a c : ZMod 3) (hc : c ^ 2 = 1) (hc0 : c ≠ 0) :
    IsRegularJet squareEquation 0 a ![c] := by
  refine ⟨?_, ?_⟩
  · simp [jetEvaluation_eq_eval, hc]
  · simp only [separant, jetEvaluation_eq_eval, squareEquation, map_sub,
      Derivation.leibniz_pow, pderiv_X_self, Derivation.map_one_eq_zero, sub_zero, smul_eq_mul,
      mul_one, nsmul_eq_mul, map_mul, map_natCast, eval_X, jetAssignment_some,
      Matrix.cons_val_fin_one, Nat.reduceSub, pow_one]
    refine mul_ne_zero (by decide) hc0

/-- At every point, `Y₀ ^ 2 = 1` over `ZMod 3` has exactly `2` regular jets: the theorem gives at
most `jetDegree * 3 ^ 0 ≤ 2`, and the jets `1` and `2` are regular. -/
example (a : ZMod 3) :
    #{jet ∈ Fintype.piFinset (fun _ : Fin 1 ↦ (univ : Finset (ZMod 3))) |
      IsRegularJet squareEquation 0 a jet} = 2 := by
  refine le_antisymm ?_ ?_
  · have h := card_filter_isRegularJet_le squareEquation 0 a univ
    rw [pow_zero, mul_one] at h
    exact h.trans jetDegree_squareEquation_le
  · have hsub : ({![1], ![2]} : Finset (Fin 1 → ZMod 3)) ⊆
        {jet ∈ Fintype.piFinset (fun _ : Fin 1 ↦ (univ : Finset (ZMod 3))) |
          IsRegularJet squareEquation 0 a jet} := by
      intro jet hjet
      simp only [mem_insert, mem_singleton] at hjet
      refine mem_filter.mpr ⟨by simp, ?_⟩
      rcases hjet with rfl | rfl
      · exact isRegularJet_squareEquation a 1 (by decide) (by decide)
      · exact isRegularJet_squareEquation a 2 (by decide) (by decide)
    exact (card_le_card hsub).trans_eq' (by decide)

/-- The bound on all regular point-jet pairs over a finite field, written with the exponent
`d + 1`. -/
example {F : Type*} [Field F] [Finite F] {d : ℕ} (Q : DifferentialPolynomial F d)
    (s : Fin (d + 1)) :
    Nat.card (RegularJet Q s) ≤ jetDegree Q s * Nat.card F ^ (d + 1) := by
  have h := natCard_regularJet_le Q s
  rwa [mul_comm (Nat.card F), mul_assoc, ← pow_succ'] at h

/-- The zero differential polynomial has no regular jets in any finite box: the theorem gives the
bound `jetDegree 0 s * #B ^ d = 0`. -/
example {F : Type*} [CommRing F] [IsDomain F] [DecidableEq F] {d : ℕ} (s : Fin (d + 1)) (a : F)
    (B : Finset F) :
    #{jet ∈ Fintype.piFinset (fun _ : Fin (d + 1) ↦ B) |
      IsRegularJet (0 : DifferentialPolynomial F d) s a jet} = 0 := by
  have h := card_filter_isRegularJet_le (0 : DifferentialPolynomial F d) s a B
  simpa [jetDegree] using h

/-- The equation `2 Y₀ = 0` over `ZMod 4` at depth `0`. -/
private abbrev doubleEquation : DifferentialPolynomial (ZMod 4) 0 :=
  C 2 * X (some 0)

/-- Over `ZMod 4`, the jets `0` and `2` are both regular for `2 Y₀ = 0` at any point, more than
`jetDegree * 4 ^ 0 ≤ 1`: the conclusion of `card_filter_isRegularJet_le` fails without the domain
hypothesis. -/
example (a : ZMod 4) :
    jetDegree doubleEquation 0 * (univ : Finset (ZMod 4)).card ^ 0 <
      #{jet ∈ Fintype.piFinset (fun _ : Fin 1 ↦ (univ : Finset (ZMod 4))) |
        IsRegularJet doubleEquation 0 a jet} := by
  have : Fact (1 < 4) := ⟨by norm_num⟩
  have hdeg : jetDegree doubleEquation 0 ≤ 1 :=
    (degreeOf_C_mul_le _ _ _).trans_eq (degreeOf_X_self _)
  have hsub : ({![0], ![2]} : Finset (Fin 1 → ZMod 4)) ⊆
      {jet ∈ Fintype.piFinset (fun _ : Fin 1 ↦ (univ : Finset (ZMod 4))) |
        IsRegularJet doubleEquation 0 a jet} := by
    intro jet hjet
    simp only [mem_insert, mem_singleton] at hjet
    refine mem_filter.mpr ⟨by simp, ?_, ?_⟩ <;>
      rcases hjet with rfl | rfl <;>
      simp only [separant, jetEvaluation_eq_eval, doubleEquation, map_mul, eval_C, eval_X,
        jetAssignment_some, Matrix.cons_val_fin_one, Derivation.leibniz, pderiv_C, pderiv_X_self,
        smul_eq_mul, mul_one, mul_zero, add_zero] <;> decide
  have hcard := card_le_card hsub
  rw [show ({![0], ![2]} : Finset (Fin 1 → ZMod 4)).card = 2 by decide] at hcard
  rw [pow_zero, mul_one]
  exact (Nat.lt_of_le_of_lt hdeg one_lt_two).trans_le hcard

end

end PolynomialDifferential
