/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.Interpolation.Solution.Machine
public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.Interpolation.Solution.Basis
/-!
# Same-run nonzero interpolation and sparse-polynomial correctness

The solver receives the actual matrix kernel witness transported from an existing nonzero eligible
polynomial. Sparse emission has the canonical EvaluationMachine meaning over natural variable
indices, related by an injective rename to [X,Y0,...,Yd]. Parameter search and the strict-cap
eligibility of its chosen witness remain explicit external obligations.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.NonzeroInterpolationMachine

noncomputable section

open PolynomialDifferential
open MvPolynomial
open scoped BigOperators

variable {F : Type*} [Field F] {d : ℕ}

/-- The existing sparse machine's variable order. -/
def variableIndex : JetVariable d → ℕ
  | none => 0
  | some j => j.val + 1

theorem variableIndex_injective : Function.Injective (variableIndex (d := d)) := by
  intro i j h
  cases i with
  | none => cases j <;> simp_all [variableIndex]
  | some i =>
    cases j with
    | none => simp [variableIndex] at h
    | some j => exact congrArg some (Fin.ext (Nat.add_right_cancel h))

/-- The factor loop denotes the ordinary ordered product, without a power primitive in dispatch. -/
theorem factors_ofFn (j n : ℕ) (f : Fin n → ℕ) :
    MvPolynomial.EvaluationMachine.factorsPolynomial (F := F) (factors j (List.ofFn f)).1 =
      ∏ i : Fin n, X (j + i.val) ^ f i := by
  induction n generalizing j with
  | zero => simp [factors, MvPolynomial.EvaluationMachine.factorsPolynomial]
  | succ n ih =>
    rw [List.ofFn_succ, factors]
    simp only [MvPolynomial.EvaluationMachine.factorsPolynomial, ih, Fin.prod_univ_succ,
      Fin.val_zero, Nat.add_zero, Fin.val_succ]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    congr 2
    omega

/-- Source exponent products in the common coordinate order. -/
theorem monomial_exponent (v : List ℕ) :
    monomial (exponent d v) (1 : F) = X none ^ v.getD 0 0 *
      ∏ j : Fin (d + 1), X (some j) ^ v.getD (j.val + 1) 0 := by
  simp only [X_pow_eq_monomial, ← monomial_sum_one, monomial_mul, mul_one, exponent]

/-- Emitted factor pairs have the exact source monomial meaning under an injective rename. -/
theorem factors_source (v : List ℕ) (hv : v.length = d + 2) :
    MvPolynomial.EvaluationMachine.factorsPolynomial (F := F) (factors 0 v).1 =
      rename variableIndex (InterpolationPointBlockMachine.sourceValue d v) := by
  rw [sourceValue_eq_monomial v hv, monomial_exponent]
  cases v with
  | nil => simp at hv
  | cons x xs =>
    have hx : xs.length = d + 1 := by simpa using hv
    have he := InterpolationPointBlockMachine.ofFn_getD xs hx
    conv_lhs => rw [← he]
    simp only [factors, MvPolynomial.EvaluationMachine.factorsPolynomial, factors_ofFn,
      map_mul, map_pow, map_prod, rename_X, variableIndex, List.getD_eq_getElem?_getD,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, Nat.zero_add]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    congr 2
    omega

variable [DecidableEq F]

/-- Actual conversion preserves the canonical source polynomial of the solver vector. -/
theorem emit_polynomial (vs : List (List ℕ)) (cs : List F) (hc : cs.length = vs.length)
    (hv : ∀ v ∈ vs, v.length = d + 2) :
    MvPolynomial.EvaluationMachine.sparsePolynomial (emitSpec vs cs) =
      rename variableIndex (InterpolationPointBlockMachine.sourceCombination d vs
        (fun i => cs.getD i 0)) := by
  induction vs generalizing cs with
  | nil => cases cs <;> simp_all [emitSpec, MvPolynomial.EvaluationMachine.sparsePolynomial,
      InterpolationPointBlockMachine.sourceCombination, InterpolationPointBlockMachine.combine]
  | cons v vs ih =>
    cases cs with
    | nil => simp at hc
    | cons c cs =>
      have hh := factors_source v (hv v (by simp)) (F := F)
      have ht := ih cs (by simpa using hc) (fun v hm => hv v (by simp [hm]))
      by_cases hz : c = 0
      · simp [emitSpec, hz, ht, InterpolationPointBlockMachine.sourceCombination,
          InterpolationPointBlockMachine.combine]
      · simp [emitSpec, hz, MvPolynomial.EvaluationMachine.sparsePolynomial, ht, hh,
          InterpolationPointBlockMachine.sourceCombination, InterpolationPointBlockMachine.combine,
          Algebra.smul_def]

omit [DecidableEq F] in
/-- Distinct support prevents a nonzero solver coordinate from representing the zero polynomial. -/
theorem source_nonzero (D m A : ℕ) (cs : List F)
    (j : ℕ) (hj : j < (ReceivedInterpolationMatrixMachine.support D d m A).length)
    (hc : cs.getD j 0 ≠ 0) :
    InterpolationPointBlockMachine.sourceCombination d
      (ReceivedInterpolationMatrixMachine.support D d m A) (fun i => cs.getD i 0) ≠ 0 := by
  rw [sourceCombination_eq]
  apply (combination_ne_zero_iff _ (support_exponents_nodup D m A) _).mpr
  exact ⟨j, by simpa using hj, hc⟩

omit [DecidableEq F] in
/-- Every source output retains exactly the same strict support eligibility. -/
theorem source_eligible (D m A : ℕ) (w : ℕ → F) :
    Eligible D m A (InterpolationPointBlockMachine.sourceCombination d
      (ReceivedInterpolationMatrixMachine.support D d m A) w) := by
  intro e he
  rw [sourceCombination_eq] at he
  obtain ⟨v, hv, hve⟩ := List.mem_map.mp (combination_support _ w e he)
  rw [← hve, vector_exponent v]
  · exact hv
  · simpa [InterpolationSupportMachine.parameters,
      InterpolationSupportMachine.parametersWithBudget] using
      InterpolationSupportMachine.supportSpec_width _ hv

/-- Monotonicity of the existing polynomial solver budget in its actual row count. -/
theorem kernelBudget_mono (n r R : ℕ) (h : r ≤ R) :
    Matrix.NonzeroKernelMachine.budget r n ≤ Matrix.NonzeroKernelMachine.budget R n := by
  unfold Matrix.NonzeroKernelMachine.budget Matrix.ForwardEchelonMachine.budget
    Matrix.ForwardEchelonMachine.stageBudget
  gcongr

/-- Proof-side bound for all executed components; run uses actual materialized counters. -/
def budget (d m A L n : ℕ) : ℕ :=
  32 * InterpolationSupportMachine.linearFactor (d + 1) (2 * m) * (m * A + 1) +
    ReceivedInterpolationMatrixMachine.budget d m A L n +
    Matrix.NonzeroKernelMachine.budget (InterpolationPointBlockMachine.columnSize d m * L * n) L +
    64 * (d + 4) * (L + 1) + 32

/-- An existing eligible nonzero interpolation witness makes this actual composed run succeed.
The output is a nonzero sparse polynomial with the unchanged support caps and every required
low-contact constraint. No row-count shortage or parameter-search conclusion is assumed. -/
theorem run_refines (D m A : ℕ) (received : List (F × F)) (Q : DifferentialPolynomial F d)
    (he : Eligible D m A Q) (hn : Q ≠ 0)
    (hlocal : ∀ p ∈ received, localConstraintAt m p.1 p.2 Q = 0) :
    ∃ out c, run D d m A received = (some out, c) ∧
      out.coefficients.length = (ReceivedInterpolationMatrixMachine.support D d m A).length ∧
      out.chosen < out.coefficients.length ∧ out.coefficients.getD out.chosen 0 = 1 ∧
      out.terms.length ≤ out.coefficients.length ∧
      (out.terms.map Prod.snd).Nodup ∧ (∀ t ∈ out.terms, t.1 ≠ 0) ∧
      MvPolynomial.EvaluationMachine.sparsePolynomial out.terms =
        rename variableIndex (InterpolationPointBlockMachine.sourceCombination d
          (ReceivedInterpolationMatrixMachine.support D d m A)
          (fun i => out.coefficients.getD i 0)) ∧
      MvPolynomial.EvaluationMachine.sparsePolynomial out.terms ≠ 0 ∧
      Eligible D m A (InterpolationPointBlockMachine.sourceCombination d
        (ReceivedInterpolationMatrixMachine.support D d m A) (fun i => out.coefficients.getD i 0)) ∧
      differentialWeightedDegree D (InterpolationPointBlockMachine.sourceCombination d
        (ReceivedInterpolationMatrixMachine.support D d m A)
        (fun i => out.coefficients.getD i 0)) < m * A ∧
      (∀ p ∈ received, localConstraintAt m p.1 p.2
        (InterpolationPointBlockMachine.sourceCombination d
          (ReceivedInterpolationMatrixMachine.support D d m A)
          (fun i => out.coefficients.getD i 0)) = 0) ∧
      c ≤ budget d m A (ReceivedInterpolationMatrixMachine.support D d m A).length
        received.length := by
  let vs := ReceivedInterpolationMatrixMachine.support D d m A
  obtain ⟨w, hw, hi⟩ := witness_coordinates D m A Q he hn
  obtain ⟨mat, mc, hmat, hcols, _, hcount, _, hshape, hkernel, hrowbound, hmc⟩ :=
    ReceivedInterpolationMatrixMachine.run_refines D d m A received
  have hr : Matrix.ForwardEchelonMachine.Rectangular mat.columns mat.rows :=
    fun r hr => (hshape r hr).1
  have hz : ∀ r ∈ mat.rows, r.2 = 0 := fun r hr => (hshape r hr).2
  have hne : ∃ x : ℕ → F, Matrix.PivotSelectionMachine.Satisfies mat.rows x ∧
      ∃ i < mat.columns, x i ≠ 0 := by
    refine ⟨w, (hkernel w).mpr ?_, ?_⟩
    · simpa only [hw] using hlocal
    · simpa only [hcols] using hi
  obtain ⟨j, cs, kc, hsolve, hlen, hj, hunit, hsol, hkc⟩ :=
    Matrix.NonzeroKernelMachine.evaluation_runFuel mat.columns mat.rows hr hz hne
  have hv : ∀ v ∈ vs, v.length = d + 2 := by
    intro v hv
    simpa [InterpolationSupportMachine.parameters,
      InterpolationSupportMachine.parametersWithBudget] using
      InterpolationSupportMachine.supportSpec_width _ hv
  have hcs : cs.length = vs.length := hlen.trans hcols
  obtain ⟨ec, hem, helen, hec⟩ := emit_correct (d + 2) vs cs hcs
    (fun v hm => (hv v hm).le)
  obtain ⟨sc, hs, hsc⟩ := InterpolationSupportMachine.enumerate_correct D d m A
  have hp := emit_polynomial vs cs hcs hv
  have hpn : InterpolationPointBlockMachine.sourceCombination d vs (fun i => cs.getD i 0) ≠ 0 :=
    source_nonzero D m A cs j (by simpa only [hcols] using hj) (by rw [hunit]; exact one_ne_zero)
  have hsn : MvPolynomial.EvaluationMachine.sparsePolynomial (emitSpec vs cs) ≠ 0 := by
    rw [hp]
    exact fun h => hpn ((rename_eq_zero_iff_of_injective _ variableIndex_injective).mp h)
  have hkeys := emitSpec_nodup vs cs (InterpolationSupportMachine.supportSpec_nodup _)
  have hnz : ∀ t ∈ emitSpec vs cs, t.1 ≠ 0 :=
    fun t ht => (emitSpec_keys vs cs t ht).choose_spec.2.2
  have hdeg := eligible_weightedDegree D m A _ (source_eligible D m A _) hpn
  refine ⟨⟨j, cs, emitSpec vs cs⟩,
    32 + sc + mc + Matrix.NonzeroKernelMachine.totalCost kc + ec,
    ?_, hcs, by simpa only [hlen] using hj, hunit, helen.trans_eq hcs.symm,
    hkeys, hnz, hp, hsn, source_eligible D m A _, hdeg, (hkernel _).mp hsol, ?_⟩
  · have hs' : InterpolationSupportMachine.enumerateWithBudget D d m (2 * m) A =
        (.done vs, sc) := by
      simpa [InterpolationSupportMachine.enumerate, vs,
        ReceivedInterpolationMatrixMachine.support,
        ReceivedInterpolationMatrixMachine.supportWithBudget,
        InterpolationSupportMachine.parameters,
        InterpolationSupportMachine.parametersWithBudget] using hs
    have hmat' : ReceivedInterpolationMatrixMachine.runWithBudget D d m (2 * m) A received =
        (some mat, mc) := by simpa [ReceivedInterpolationMatrixMachine.run] using hmat
    simp only [run, runWithBudget, hs', hmat', hcount, hsolve]
    change ((emit vs cs).1.map (fun ts =>
      (⟨j, cs, ts⟩ : Output F)),
      32 + sc + mc + Matrix.NonzeroKernelMachine.totalCost kc + (emit vs cs).2) = _
    rw [hem]
    rfl
  · have hkbound : Matrix.NonzeroKernelMachine.totalCost kc ≤
        Matrix.NonzeroKernelMachine.budget
          (InterpolationPointBlockMachine.columnSize d m * vs.length * received.length)
          vs.length := by
      apply hkc.trans
      rw [hcols]
      exact kernelBudget_mono _ _ _ (by simpa only [hcount] using hrowbound)
    change _ ≤ budget d m A vs.length received.length
    unfold budget
    change ec ≤ 64 * (d + 4) * (vs.length + 1) at hec
    change mc ≤ ReceivedInterpolationMatrixMachine.budget d m A vs.length received.length at hmc
    omega

omit [DecidableEq F] in
/-- A nonzero coefficient in the explicitly budgeted support gives a nonzero source polynomial. -/
theorem sourceWithBudget_nonzero (D m J A : ℕ) (cs : List F)
    (j : ℕ) (hj : j < (ReceivedInterpolationMatrixMachine.supportWithBudget D d m J A).length)
    (hc : cs.getD j 0 ≠ 0) :
    InterpolationPointBlockMachine.sourceCombination d
      (ReceivedInterpolationMatrixMachine.supportWithBudget D d m J A)
        (fun i => cs.getD i 0) ≠ 0 := by
  rw [sourceCombinationWithBudget_eq]
  apply (combination_ne_zero_iff _ (supportWithBudget_exponents_nodup D m J A) _).mpr
  exact ⟨j, by simpa using hj, hc⟩

omit [DecidableEq F] in
/-- Every source output retains the explicit strict support eligibility. -/
theorem sourceWithBudget_eligible (D m J A : ℕ) (w : ℕ → F) :
    EligibleWithBudget D m J A (InterpolationPointBlockMachine.sourceCombination d
      (ReceivedInterpolationMatrixMachine.supportWithBudget D d m J A) w) := by
  intro e he
  rw [sourceCombinationWithBudget_eq] at he
  obtain ⟨v, hv, hve⟩ := List.mem_map.mp (combination_support _ w e he)
  rw [← hve, vector_exponent v]
  · exact hv
  · simpa [InterpolationSupportMachine.parametersWithBudget] using
      InterpolationSupportMachine.supportSpec_width _ hv

/-- Work budget for nonzero interpolation with strict jet cutoff `J`. -/
def budgetWithBudget (d m J A L n : ℕ) : ℕ :=
  32 * InterpolationSupportMachine.linearFactor (d + 1) J * (m * A + 1) +
    ReceivedInterpolationMatrixMachine.budgetWithBudget d m J A L n +
    Matrix.NonzeroKernelMachine.budget (InterpolationPointBlockMachine.columnSize d m * L * n) L +
    64 * (d + 4) * (L + 1) + 32

/-- A budget-eligible nonzero witness makes the explicitly budgeted run succeed. -/
theorem runWithBudget_refines (D m J A : ℕ) (received : List (F × F))
    (Q : DifferentialPolynomial F d) (he : EligibleWithBudget D m J A Q) (hn : Q ≠ 0)
    (hlocal : ∀ p ∈ received, localConstraintAt m p.1 p.2 Q = 0) :
    ∃ out c, runWithBudget D d m J A received = (some out, c) ∧
      out.coefficients.length =
        (ReceivedInterpolationMatrixMachine.supportWithBudget D d m J A).length ∧
      out.chosen < out.coefficients.length ∧ out.coefficients.getD out.chosen 0 = 1 ∧
      out.terms.length ≤ out.coefficients.length ∧
      (out.terms.map Prod.snd).Nodup ∧ (∀ t ∈ out.terms, t.1 ≠ 0) ∧
      MvPolynomial.EvaluationMachine.sparsePolynomial out.terms =
        rename variableIndex (InterpolationPointBlockMachine.sourceCombination d
          (ReceivedInterpolationMatrixMachine.supportWithBudget D d m J A)
          (fun i => out.coefficients.getD i 0)) ∧
      MvPolynomial.EvaluationMachine.sparsePolynomial out.terms ≠ 0 ∧
      EligibleWithBudget D m J A (InterpolationPointBlockMachine.sourceCombination d
        (ReceivedInterpolationMatrixMachine.supportWithBudget D d m J A)
        (fun i => out.coefficients.getD i 0)) ∧
      differentialWeightedDegree D (InterpolationPointBlockMachine.sourceCombination d
        (ReceivedInterpolationMatrixMachine.supportWithBudget D d m J A)
        (fun i => out.coefficients.getD i 0)) < m * A ∧
      (∀ p ∈ received, localConstraintAt m p.1 p.2
        (InterpolationPointBlockMachine.sourceCombination d
          (ReceivedInterpolationMatrixMachine.supportWithBudget D d m J A)
          (fun i => out.coefficients.getD i 0)) = 0) ∧
      c ≤ budgetWithBudget d m J A
        (ReceivedInterpolationMatrixMachine.supportWithBudget D d m J A).length
        received.length := by
  let vs := ReceivedInterpolationMatrixMachine.supportWithBudget D d m J A
  obtain ⟨w, hw, hi⟩ := witnessWithBudget_coordinates D m J A Q he hn
  obtain ⟨mat, mc, hmat, hcols, _, hcount, _, hshape, hkernel, hrowbound, hmc⟩ :=
    ReceivedInterpolationMatrixMachine.runWithBudget_refines D d m J A received
  have hr : Matrix.ForwardEchelonMachine.Rectangular mat.columns mat.rows :=
    fun r hr => (hshape r hr).1
  have hz : ∀ r ∈ mat.rows, r.2 = 0 := fun r hr => (hshape r hr).2
  have hne : ∃ x : ℕ → F, Matrix.PivotSelectionMachine.Satisfies mat.rows x ∧
      ∃ i < mat.columns, x i ≠ 0 := by
    refine ⟨w, (hkernel w).mpr ?_, ?_⟩
    · simpa only [hw] using hlocal
    · simpa only [hcols] using hi
  obtain ⟨j, cs, kc, hsolve, hlen, hj, hunit, hsol, hkc⟩ :=
    Matrix.NonzeroKernelMachine.evaluation_runFuel mat.columns mat.rows hr hz hne
  have hv : ∀ v ∈ vs, v.length = d + 2 := by
    intro v hv
    simpa [InterpolationSupportMachine.parametersWithBudget] using
      InterpolationSupportMachine.supportSpec_width _ hv
  have hcs : cs.length = vs.length := hlen.trans hcols
  obtain ⟨ec, hem, helen, hec⟩ := emit_correct (d + 2) vs cs hcs
    (fun v hm => (hv v hm).le)
  obtain ⟨sc, hs, hsc⟩ := InterpolationSupportMachine.enumerateWithBudget_correct D d m J A
  have hp := emit_polynomial vs cs hcs hv
  have hpn : InterpolationPointBlockMachine.sourceCombination d vs
      (fun i => cs.getD i 0) ≠ 0 :=
    sourceWithBudget_nonzero D m J A cs j (by simpa only [hcols] using hj)
      (by rw [hunit]; exact one_ne_zero)
  have hsn : MvPolynomial.EvaluationMachine.sparsePolynomial (emitSpec vs cs) ≠ 0 := by
    rw [hp]
    exact fun h => hpn ((rename_eq_zero_iff_of_injective _ variableIndex_injective).mp h)
  have hkeys := emitSpec_nodup vs cs (InterpolationSupportMachine.supportSpec_nodup _)
  have hnz : ∀ t ∈ emitSpec vs cs, t.1 ≠ 0 :=
    fun t ht => (emitSpec_keys vs cs t ht).choose_spec.2.2
  have hdeg := eligibleWithBudget_weightedDegree D m J A _
    (sourceWithBudget_eligible D m J A _) hpn
  refine ⟨⟨j, cs, emitSpec vs cs⟩,
    32 + sc + mc + Matrix.NonzeroKernelMachine.totalCost kc + ec,
    ?_, hcs, by simpa only [hlen] using hj, hunit, helen.trans_eq hcs.symm,
    hkeys, hnz, hp, hsn, sourceWithBudget_eligible D m J A _, hdeg,
    (hkernel _).mp hsol, ?_⟩
  · simp only [runWithBudget, hs, hmat, hcount, hsolve]
    change ((emit vs cs).1.map (fun ts => (⟨j, cs, ts⟩ : Output F)),
      32 + sc + mc + Matrix.NonzeroKernelMachine.totalCost kc + (emit vs cs).2) = _
    rw [hem]
    rfl
  · have hkbound : Matrix.NonzeroKernelMachine.totalCost kc ≤
        Matrix.NonzeroKernelMachine.budget
          (InterpolationPointBlockMachine.columnSize d m * vs.length * received.length)
          vs.length := by
      apply hkc.trans
      rw [hcols]
      exact kernelBudget_mono _ _ _ (by simpa only [hcount] using hrowbound)
    change _ ≤ budgetWithBudget d m J A vs.length received.length
    unfold budgetWithBudget
    change ec ≤ 64 * (d + 4) * (vs.length + 1) at hec
    change mc ≤ ReceivedInterpolationMatrixMachine.budgetWithBudget d m J A vs.length
      received.length at hmc
    omega

end
end ReedSolomon.HiddenDerivative.NonzeroInterpolationMachine
