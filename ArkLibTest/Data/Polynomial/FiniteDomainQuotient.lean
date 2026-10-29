/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.FiniteDomainQuotient
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.NormNum

/-!
# Finite-domain quotient acceptance tests

Small-field examples cover empty domains, zero dividends, exact quotient degrees, a false claim
with a nontrivial probability bound, and executable evaluation on a multiplicative subgroup.
-/

open Polynomial
open scoped ENNReal ProbabilityTheory

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

namespace Polynomial

/-- The empty domain leaves the dividend itself as the unique quotient. -/
example (f : (ZMod 5)[X]) :
    ∃! q, f = q * Lagrange.nodal ∅ id ∧ q.natDegree = f.natDegree := by
  simpa using (show ZeroOn ∅ f by simp [ZeroOn]).existsUnique_quotient

/-- The zero dividend remains valid when the domain is larger than the degree budget. -/
example : ∃! q : (ZMod 5)[X], 0 = q * Lagrange.nodal {0, 1} id ∧ q.natDegree ≤ 0 := by
  simpa using (zeroOn_iff_existsUnique_quotient_natDegree_le
    (S := ({0, 1} : Finset (ZMod 5))) (f := 0) (d := 0) (by simp)).mp
    (by simp [ZeroOn])

/-- A quadratic vanishing at two distinct points has a constant quotient. -/
example : ∃! q : (ZMod 5)[X], X * (X - 1) = q * Lagrange.nodal {0, 1} id ∧
    q.natDegree = 0 := by
  have hz : ZeroOn ({0, 1} : Finset (ZMod 5)) (X * (X - 1)) := by
    simp [ZeroOn]
  have hd : (X * (X - 1) : (ZMod 5)[X]).natDegree = 2 := by
    change (X * (X - C (1 : ZMod 5))).natDegree = 2
    rw [natDegree_mul X_ne_zero (X_sub_C_ne_zero (1 : ZMod 5)),
      natDegree_X, natDegree_X_sub_C]
  simpa [hd] using hz.existsUnique_quotient

/-- With a false claim at `1` and the zero quotient, the acceptance bound is `1/5`. -/
example :
    Pr{let x ← $ᵗ (ZMod 5)}[(X : (ZMod 5)[X]).eval x =
      (0 : (ZMod 5)[X]).eval x * (Lagrange.nodal {1} id).eval x] ≤
        (1 / 5 : ℝ≥0∞) := by
  simpa using prob_eval_eq_mul_nodal_le
    (S := ({1} : Finset (ZMod 5))) (f := X) (q := 0) (d := 1)
    (by simp) (by simp [ZeroOn]) (by simp) (by simp)

/-- The same check accepts exactly one of the five possible challenges. -/
example : Pr{let x ← $ᵗ (ZMod 5)}[(X : (ZMod 5)[X]).eval x = 0] =
    (1 / 5 : ℝ≥0∞) := by
  simp only [eval_X]
  rw [SampleableType.prEvent_uniformSample]
  have hc : (Finset.univ.filter (fun x : ZMod 5 => x = 0)).card = 1 := by decide
  rw [hc]
  norm_num

/-- Without the cardinality condition, a constant quotient can leave a residual of degree two. -/
example :
    (1 : (ZMod 5)[X]).natDegree ≤ 0 - ({0, 1} : Finset (ZMod 5)).card ∧
      ¬ (0 - 1 * Lagrange.nodal ({0, 1} : Finset (ZMod 5)) id).natDegree ≤ 0 := by
  simp [Lagrange.natDegree_nodal]

end Polynomial

open scoped Classical in
/-- All nonzero elements of `ZMod 5` form a subgroup with vanishing polynomial `X⁴ - 1`. -/
example :
    Lagrange.nodal ((⊤ : Subgroup (ZMod 5)ˣ) : Set (ZMod 5)ˣ).toFinset
      ((↑) : (ZMod 5)ˣ → ZMod 5) = (X : (ZMod 5)[X]) ^ 4 - 1 := by
  rw [Lagrange.nodal_subgroup_eq_X_pow_card_sub_one]
  congr 2
  rw [← Nat.card_eq_fintype_card, Subgroup.card_top, Nat.card_eq_fintype_card]
  decide

/-- The indexed subgroup nodal polynomial is the same one used by the finite-set zero test. -/
example (H : Subgroup (ZMod 5)ˣ) [Fintype H] :
    Lagrange.nodal ((H : Set (ZMod 5)ˣ).toFinset.image ((↑) : (ZMod 5)ˣ → ZMod 5)) id =
      (X : (ZMod 5)[X]) ^ Fintype.card H - 1 := by
  classical
  simpa only [Lagrange.nodal, Finset.prod_image Units.val_injective.injOn, id_eq] using
    Lagrange.nodal_subgroup_eq_X_pow_card_sub_one H

/-- A computable evaluation expression for the subgroup of all nonzero elements. -/
private def subgroupEval (x : ZMod 5) : ZMod 5 := x ^ 4 - 1

open scoped Classical in
example (x : ZMod 5) :
    (Lagrange.nodal ((⊤ : Subgroup (ZMod 5)ˣ) : Set (ZMod 5)ˣ).toFinset
      ((↑) : (ZMod 5)ˣ → ZMod 5)).eval x = subgroupEval x := by
  rw [Lagrange.eval_nodal_subgroup]
  rw [← Nat.card_eq_fintype_card, Subgroup.card_top, Nat.card_eq_fintype_card]
  have hc : Fintype.card (ZMod 5)ˣ = 4 := by decide
  exact congrArg (fun n => x ^ n - 1) hc

/-- info: [4, 0, 0, 0, 0] -/
#guard_msgs in
#eval ([0, 1, 2, 3, 4] : List (ZMod 5)).map subgroupEval
