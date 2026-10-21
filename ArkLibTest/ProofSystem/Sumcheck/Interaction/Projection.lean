/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ProofSystem.Sumcheck.Interaction.Projection
import Mathlib.Data.ZMod.Basic

/-! # A bivariate input reaches run-derived closing through virtual projection -/

namespace Sumcheck.Interaction.SingleRound.ProjectionTest

open OracleComp OracleSpec MvPolynomial
open _root_.Interaction.Oracle

noncomputable section

instance : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- The bivariate polynomial contains both linear terms and a mixed term. -/
def polynomial : Spec.OracleStatement (ZMod 17) 2 1 () :=
  ⟨1 + C 2 * X 0 + C 3 * X 1 + C 4 * X 0 * X 1, by
    rw [mem_restrictDegree_iff_degreeOf_le]
    intro i
    apply le_trans (degreeOf_add_le _ _ _)
    apply max_le
    · apply le_trans (degreeOf_add_le _ _ _)
      apply max_le
      · apply le_trans (degreeOf_add_le _ _ _)
        apply max_le
        · simp
        · apply le_trans (degreeOf_mul_le _ _ _)
          simp only [degreeOf_C, degreeOf_X, zero_add]
          split <;> omega
      · apply le_trans (degreeOf_mul_le _ _ _)
        simp only [degreeOf_C, degreeOf_X, zero_add]
        split <;> omega
    · apply le_trans (degreeOf_mul_le _ _ _)
      apply le_trans (Nat.add_le_add (degreeOf_mul_le _ _ _) (le_refl _))
      fin_cases i <;> simp [degreeOf_X]⟩

/-- Boolean inputs embedded in the seventeen-element field. -/
def domain : Fin 2 ↪ ZMod 17 where
  toFun := fun i => i.val
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all

theorem domain_points : Finset.univ.map domain = {0, 1} := by
  ext x
  simp only [Finset.mem_map, Finset.mem_univ, true_and, Fin.exists_fin_two,
    Finset.mem_insert, Finset.mem_singleton]
  change ((0 : ZMod 17) = x ∨ 1 = x) ↔ (x = 0 ∨ x = 1)
  simp [eq_comm]

theorem suffix_points : Fintype.piFinset (fun _ : Fin 1 => Finset.univ.map domain) =
    {fun _ => 0, fun _ => 1} := by
  ext f
  simp [domain_points, Fintype.mem_piFinset, Fin.forall_fin_one, funext_iff]

/-- First-round target; the challenge prefix is empty. -/
def statement : Spec.StatementRound (ZMod 17) 2 0 := ⟨1, Fin.elim0⟩

/-- The honest sent polynomial is produced by the existing multivariate projection. -/
def projected : Message (ZMod 17) 1 :=
  Spec.SingleRound.projectedRoundPolynomial (ZMod 17) 2 1 domain 0 statement.challenges polynomial

/-- Input answers are computed by the virtual oracle, not by a supplied univariate polynomial. -/
def derived : QueryImpl (inputSpec (ZMod 17)) Id :=
  projectedInput (ZMod 17) 2 1 domain 0 statement polynomial

theorem derived_eval (x : ZMod 17) : derived x = 5 + 8 * x := by
  classical
  rw [derived, projectedInput_eq]
  change (Spec.SingleRound.projectedRoundPolynomial (ZMod 17) 2 1 domain 0
    statement.challenges polynomial).val.eval x = _
  simp only [Spec.SingleRound.projectedRoundPolynomial, Polynomial.eval_finsetSum]
  simp_rw [← eval_eq_eval_mv_eval_finSuccEquivNth]
  change (∑ f ∈ Fintype.piFinset (fun _ : Fin 1 => Finset.univ.map domain),
    polynomial.val.eval (Fin.insertNth 0 x
      (Spec.SingleRound.roundSuffix (ZMod 17) 1 0 statement.challenges f))) = _
  rw [suffix_points]
  have hne : (fun _ : Fin 1 => (0 : ZMod 17)) ≠ (fun _ => 1) := by
    intro h
    have := congrFun h 0
    norm_num at this
  simp [hne, polynomial, Spec.SingleRound.roundSuffix, statement]
  ring

/-- The original bivariate claim has Boolean-hypercube sum one modulo seventeen. -/
theorem input_sum :
    (∑ x ∈ ({0, 1} : Finset (ZMod 17)), ∑ y ∈ ({0, 1} : Finset (ZMod 17)),
      polynomial.val.eval ![x, y]) = 1 := by
  norm_num [polynomial]
  decide

/-- Agreement transports the computed virtual answer to the honest sent witness. -/
theorem projected_eval (x : ZMod 17) : projected.val.eval x = 5 + 8 * x := by
  have h := derived_eval x
  rw [derived, projectedInput_eq] at h
  exact h

/-- The actual projected witness satisfies the verifier's sum test. -/
theorem projected_sum :
    (((Finset.univ.map domain).toList).map (fun x => projected.val.eval x)).sum = 1 := by
  classical
  change (List.map _ (Multiset.toList (Finset.univ.map domain).val)).sum = _
  rw [Multiset.sum_map_toList]
  change (∑ x ∈ Finset.univ.map domain, projected.val.eval x) = 1
  rw [domain_points]
  norm_num [projected_eval]
  decide

/-- A source signature with real oracle capability, unused by this honest fixed-challenge run. -/
abbrev ambient : OracleSpec Unit := Unit →ₒ Unit

/-- The actual executor uses virtual input answers and closes its own output at target twelve. -/
theorem execute_closed :
    CoreRun.closed <$> executeCore
      (claimReduction (ZMod 17) 1 ambient (Finset.univ.map domain).toList 3)
      derived 1 projected =
      pure (some (ConcreteClaim.toClosed
        (⟨(12, 3), fun _ => projected⟩ : ConcreteClaim ((ZMod 17) × ZMod 17)
          (outputFamily (ZMod 17) 1)))) := by
  rw [derived, projectedInput_eq]
  change CoreRun.closed <$> executeCore
    (claimReduction (ZMod 17) 1 ambient (Finset.univ.map domain).toList 3)
    (inputImpl (ZMod 17) 1 projected) 1 projected = _
  rw [executeCore_closed (ZMod 17) 1 ambient projected _ 1 3 projected_sum]
  congr 2
  unfold honestClaim
  rw [projected_eval]
  norm_num
  have h : (29 : ZMod 17) = 12 := by decide
  rw [h]

/-- The closed relation succeeds after execution using the derived handler. -/
theorem execute_related :
    (fun run => run.closed.map (closedOutputRelation (ZMod 17) 1)) <$>
      executeCore
        (claimReduction (ZMod 17) 1 ambient (Finset.univ.map domain).toList 3)
        derived 1 projected = pure (some True) := by
  exact executeCore_projected (ZMod 17) 2 1 domain ambient 0 statement polynomial 3 projected_sum

end
end Sumcheck.Interaction.SingleRound.ProjectionTest
