/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.Interpolation.Solution.Proofs
public import ArkLib.Data.Matrix.NonzeroKernelCompletion
/-!
# Unconditional interpolation attempt completion

Every validly assembled homogeneous matrix terminates at the existing solver fuel. Successful
attempts have the full sparse interpolation meaning; failed attempts are bounded independently
of any supplied witness. This is the total interface required by descending ambient search.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.NonzeroInterpolationMachine

noncomputable section

open PolynomialDifferential
open MvPolynomial

variable {F : Type*} [Field F] [DecidableEq F] {d : ℕ}

/-- The source polynomial associated with the actual returned coefficient vector. -/
def sourceOutput (D m A : ℕ) (out : Output F) : DifferentialPolynomial F d :=
  InterpolationPointBlockMachine.sourceCombination d
    (ReceivedInterpolationMatrixMachine.support D d m A) (fun i => out.coefficients.getD i 0)

/-- Complete semantic certificate for an arbitrary successful attempt. -/
def Certified (D m A : ℕ) (received : List (F × F)) (out : Output F) : Prop :=
  out.coefficients.length = (ReceivedInterpolationMatrixMachine.support D d m A).length ∧
    out.chosen < out.coefficients.length ∧ out.coefficients.getD out.chosen 0 = 1 ∧
    out.terms.length ≤ out.coefficients.length ∧ (out.terms.map Prod.snd).Nodup ∧
    (∀ t ∈ out.terms, t.1 ≠ 0) ∧
    MvPolynomial.EvaluationMachine.sparsePolynomial out.terms = rename variableIndex
      (sourceOutput (d := d) D m A out) ∧
    MvPolynomial.EvaluationMachine.sparsePolynomial out.terms ≠ 0 ∧
    Eligible D m A (sourceOutput (d := d) D m A out) ∧
    differentialWeightedDegree D (sourceOutput (d := d) D m A out) < m * A ∧
    ∀ p ∈ received, localConstraintAt m p.1 p.2 (sourceOutput (d := d) D m A out) = 0

/-- Every attempt returns a bounded actual result, and every possible success is certified. -/
theorem attempt_complete (D m A : ℕ) (received : List (F × F)) :
    ∃ result c, run D d m A received = (result, c) ∧
      c ≤ budget d m A (ReceivedInterpolationMatrixMachine.support D d m A).length
        received.length ∧
      ∀ out, result = some out → Certified (d := d) D m A received out := by
  by_cases hex : ∃ Q : DifferentialPolynomial F d,
      Q ≠ 0 ∧ Eligible D m A Q ∧ ∀ p ∈ received, localConstraintAt m p.1 p.2 Q = 0
  · obtain ⟨Q, hn, he, hl⟩ := hex
    obtain ⟨out, c, hr, hlen, hj, hu, ht, hk, hcoeff, hp, hn', he', hd, hl', hc⟩ :=
      run_refines D m A received Q he hn hl
    refine ⟨some out, c, hr, hc, ?_⟩
    intro out' ho
    cases ho
    exact ⟨hlen, hj, hu, ht, hk, hcoeff, hp, hn', he', hd, hl'⟩
  obtain ⟨mat, mc, hmat, hcols, _, hcount, _, hshape, hkernel, hrowbound, hmc⟩ :=
    ReceivedInterpolationMatrixMachine.run_refines D d m A received
  have hr : Matrix.ForwardEchelonMachine.Rectangular mat.columns mat.rows :=
    fun r hr => (hshape r hr).1
  have hz : ∀ r ∈ mat.rows, r.2 = 0 := fun r hr => (hshape r hr).2
  rcases Matrix.NonzeroKernelMachine.completion_runFuel mat.columns mat.rows hr hz with hs | hf
  · obtain ⟨j, cs, kc, _, hlen, hj, hu, hsol, _⟩ := hs
    exfalso
    apply hex
    refine ⟨InterpolationPointBlockMachine.sourceCombination d
      (ReceivedInterpolationMatrixMachine.support D d m A) (fun i => cs.getD i 0),
      source_nonzero D m A cs j (by simpa only [hcols] using hj) ?_,
      source_eligible D m A _, (hkernel _).mp hsol⟩
    rw [hu]
    exact one_ne_zero
  · obtain ⟨kc, hsolve, hkc, _⟩ := hf
    obtain ⟨sc, hs, hsc⟩ := InterpolationSupportMachine.enumerate_correct D d m A
    refine ⟨none, 32 + sc + mc + Matrix.NonzeroKernelMachine.totalCost kc, ?_, ?_, by simp⟩
    · have hs' : InterpolationSupportMachine.enumerateWithBudget D d m (2 * m) A =
          (.done (ReceivedInterpolationMatrixMachine.support D d m A), sc) := by
        simpa [InterpolationSupportMachine.enumerate,
          ReceivedInterpolationMatrixMachine.support,
          ReceivedInterpolationMatrixMachine.supportWithBudget,
          InterpolationSupportMachine.parameters,
          InterpolationSupportMachine.parametersWithBudget] using hs
      have hmat' : ReceivedInterpolationMatrixMachine.runWithBudget D d m (2 * m) A received =
          (some mat, mc) := by simpa [ReceivedInterpolationMatrixMachine.run] using hmat
      simp only [run, runWithBudget, hs', hmat', hcount, hsolve]
    · have hb := hkc.trans (kernelBudget_mono mat.columns _
        (InterpolationPointBlockMachine.columnSize d m *
          (ReceivedInterpolationMatrixMachine.support D d m A).length * received.length)
        (by simpa only [hcount] using hrowbound))
      rw [hcols] at hb
      unfold budget
      omega

/-- Uniform support-box bound, including zero multiplicity and empty support. -/
def maximumColumns (d m A : ℕ) : ℕ := m * A * (2 * m) ^ (d + 1)

theorem support_length_le (D d m A : ℕ) :
    (ReceivedInterpolationMatrixMachine.support D d m A).length ≤ maximumColumns d m A := by
  exact InterpolationSupportMachine.supportSpec_length_le _

/-- The full component budget is monotone in the support-column count. -/
theorem budget_mono_columns (d m A L M n : ℕ) (h : L ≤ M) :
    budget d m A L n ≤ budget d m A M n := by
  unfold budget ReceivedInterpolationMatrixMachine.budget
    ReceivedInterpolationMatrixMachine.budgetWithBudget
    InterpolationPointBlockMachine.assemblyBudgetWithBudget
    Matrix.NonzeroKernelMachine.budget
    Matrix.ForwardEchelonMachine.budget Matrix.ForwardEchelonMachine.stageBudget
  gcongr

/-- A D-independent bound usable on every candidate, including failed ones. -/
def attemptBudget (d m A n : ℕ) : ℕ := budget d m A (maximumColumns d m A) n

theorem attempt_uniform (D m A : ℕ) (received : List (F × F)) :
    ∃ result c, run D d m A received = (result, c) ∧
      c ≤ attemptBudget d m A received.length ∧
      ∀ out, result = some out → Certified (d := d) D m A received out := by
  obtain ⟨result, c, hr, hc, hs⟩ := attempt_complete D m A received
  exact ⟨result, c, hr,
    hc.trans (budget_mono_columns d m A _ _ _ (support_length_le D d m A)), hs⟩

/-- Failure is absence of a supported nonzero interpolant, not a timeout interpretation. -/
theorem run_none_iff (D m A : ℕ) (received : List (F × F)) :
    (run D d m A received).1 = none ↔
      ¬∃ Q : DifferentialPolynomial F d,
        Q ≠ 0 ∧ Eligible D m A Q ∧ ∀ p ∈ received, localConstraintAt m p.1 p.2 Q = 0 := by
  constructor
  · intro h ⟨Q, hn, he, hl⟩
    obtain ⟨out, c, hr, _⟩ := run_refines D m A received Q he hn hl
    rw [hr] at h
    cases h
  · intro h
    obtain ⟨result, c, hr, _, hs⟩ := attempt_complete D m A received
    rw [hr]
    cases result with
    | none => rfl
    | some out =>
      have hc := hs out rfl
      exfalso
      apply h
      refine ⟨sourceOutput (d := d) D m A out, ?_, hc.2.2.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2.2.2⟩
      intro hz
      have hp := hc.2.2.2.2.2.2.1
      rw [hz, map_zero] at hp
      exact hc.2.2.2.2.2.2.2.1 hp

/-- Source polynomial reconstructed from a result at strict jet cutoff `J`. -/
def sourceOutputWithBudget (D m J A : ℕ) (out : Output F) : DifferentialPolynomial F d :=
  InterpolationPointBlockMachine.sourceCombination d
    (ReceivedInterpolationMatrixMachine.supportWithBudget D d m J A)
    (fun i => out.coefficients.getD i 0)

/-- Semantic certificate for a successful explicitly budgeted attempt. -/
def CertifiedWithBudget (D m J A : ℕ) (received : List (F × F)) (out : Output F) : Prop :=
  out.coefficients.length =
      (ReceivedInterpolationMatrixMachine.supportWithBudget D d m J A).length ∧
    out.chosen < out.coefficients.length ∧ out.coefficients.getD out.chosen 0 = 1 ∧
    out.terms.length ≤ out.coefficients.length ∧ (out.terms.map Prod.snd).Nodup ∧
    (∀ t ∈ out.terms, t.1 ≠ 0) ∧
    MvPolynomial.EvaluationMachine.sparsePolynomial out.terms = rename variableIndex
      (sourceOutputWithBudget (d := d) D m J A out) ∧
    MvPolynomial.EvaluationMachine.sparsePolynomial out.terms ≠ 0 ∧
    EligibleWithBudget D m J A (sourceOutputWithBudget (d := d) D m J A out) ∧
    differentialWeightedDegree D (sourceOutputWithBudget (d := d) D m J A out) < m * A ∧
    ∀ p ∈ received,
      localConstraintAt m p.1 p.2 (sourceOutputWithBudget (d := d) D m J A out) = 0

/-- Every explicitly budgeted attempt terminates, and every success is certified. -/
theorem attemptWithBudget_complete (D m J A : ℕ) (received : List (F × F)) :
    ∃ result c, runWithBudget D d m J A received = (result, c) ∧
      c ≤ budgetWithBudget d m J A
        (ReceivedInterpolationMatrixMachine.supportWithBudget D d m J A).length
        received.length ∧
      ∀ out, result = some out → CertifiedWithBudget (d := d) D m J A received out := by
  by_cases hex : ∃ Q : DifferentialPolynomial F d,
      Q ≠ 0 ∧ EligibleWithBudget D m J A Q ∧
        ∀ p ∈ received, localConstraintAt m p.1 p.2 Q = 0
  · obtain ⟨Q, hn, he, hl⟩ := hex
    obtain ⟨out, c, hr, hlen, hj, hu, ht, hk, hcoeff, hp, hn', he', hd, hl', hc⟩ :=
      runWithBudget_refines D m J A received Q he hn hl
    refine ⟨some out, c, hr, hc, ?_⟩
    intro out' ho
    cases ho
    exact ⟨hlen, hj, hu, ht, hk, hcoeff, hp, hn', he', hd, hl'⟩
  obtain ⟨mat, mc, hmat, hcols, _, hcount, _, hshape, hkernel, hrowbound, hmc⟩ :=
    ReceivedInterpolationMatrixMachine.runWithBudget_refines D d m J A received
  have hr : Matrix.ForwardEchelonMachine.Rectangular mat.columns mat.rows :=
    fun r hr => (hshape r hr).1
  have hz : ∀ r ∈ mat.rows, r.2 = 0 := fun r hr => (hshape r hr).2
  rcases Matrix.NonzeroKernelMachine.completion_runFuel mat.columns mat.rows hr hz with hs | hf
  · obtain ⟨j, cs, kc, _, hlen, hj, hu, hsol, _⟩ := hs
    exfalso
    apply hex
    refine ⟨InterpolationPointBlockMachine.sourceCombination d
      (ReceivedInterpolationMatrixMachine.supportWithBudget D d m J A)
        (fun i => cs.getD i 0),
      sourceWithBudget_nonzero D m J A cs j (by simpa only [hcols] using hj) ?_,
      sourceWithBudget_eligible D m J A _, (hkernel _).mp hsol⟩
    rw [hu]
    exact one_ne_zero
  · obtain ⟨kc, hsolve, hkc, _⟩ := hf
    obtain ⟨sc, hs, hsc⟩ :=
      InterpolationSupportMachine.enumerateWithBudget_correct D d m J A
    refine ⟨none, 32 + sc + mc + Matrix.NonzeroKernelMachine.totalCost kc, ?_, ?_, by simp⟩
    · simp only [runWithBudget, hs, hmat, hcount, hsolve]
    · have hb := hkc.trans (kernelBudget_mono mat.columns _
        (InterpolationPointBlockMachine.columnSize d m *
          (ReceivedInterpolationMatrixMachine.supportWithBudget D d m J A).length *
            received.length)
        (by simpa only [hcount] using hrowbound))
      rw [hcols] at hb
      unfold budgetWithBudget
      omega

/-- Uniform support-box bound with explicit strict jet cutoff `J`. -/
def maximumColumnsWithBudget (d m J A : ℕ) : ℕ := m * A * J ^ (d + 1)

theorem supportWithBudget_length_le (D d m J A : ℕ) :
    (ReceivedInterpolationMatrixMachine.supportWithBudget D d m J A).length ≤
      maximumColumnsWithBudget d m J A := by
  exact InterpolationSupportMachine.supportSpec_length_le _

/-- Monotonicity of the explicitly budgeted component bound in its column count. -/
theorem budgetWithBudget_mono_columns (d m J A L M n : ℕ) (h : L ≤ M) :
    budgetWithBudget d m J A L n ≤ budgetWithBudget d m J A M n := by
  unfold budgetWithBudget ReceivedInterpolationMatrixMachine.budgetWithBudget
    InterpolationPointBlockMachine.assemblyBudgetWithBudget
    Matrix.NonzeroKernelMachine.budget Matrix.ForwardEchelonMachine.budget
    Matrix.ForwardEchelonMachine.stageBudget
  gcongr

/-- A degree-independent budget for every attempt at strict jet cutoff `J`. -/
def attemptBudgetWithBudget (d m J A n : ℕ) : ℕ :=
  budgetWithBudget d m J A (maximumColumnsWithBudget d m J A) n

theorem attemptWithBudget_uniform (D m J A : ℕ) (received : List (F × F)) :
    ∃ result c, runWithBudget D d m J A received = (result, c) ∧
      c ≤ attemptBudgetWithBudget d m J A received.length ∧
      ∀ out, result = some out → CertifiedWithBudget (d := d) D m J A received out := by
  obtain ⟨result, c, hr, hc, hs⟩ := attemptWithBudget_complete D m J A received
  exact ⟨result, c, hr,
    hc.trans (budgetWithBudget_mono_columns d m J A _ _ _
      (supportWithBudget_length_le D d m J A)), hs⟩

/-- Failure is absence of a nonzero interpolant supported by the explicit budget. -/
theorem runWithBudget_none_iff (D m J A : ℕ) (received : List (F × F)) :
    (runWithBudget D d m J A received).1 = none ↔
      ¬∃ Q : DifferentialPolynomial F d,
        Q ≠ 0 ∧ EligibleWithBudget D m J A Q ∧
          ∀ p ∈ received, localConstraintAt m p.1 p.2 Q = 0 := by
  constructor
  · intro h ⟨Q, hn, he, hl⟩
    obtain ⟨out, c, hr, _⟩ := runWithBudget_refines D m J A received Q he hn hl
    rw [hr] at h
    cases h
  · intro h
    obtain ⟨result, c, hr, _, hs⟩ := attemptWithBudget_complete D m J A received
    rw [hr]
    cases result with
    | none => rfl
    | some out =>
      have hc := hs out rfl
      exfalso
      apply h
      refine ⟨sourceOutputWithBudget (d := d) D m J A out, ?_,
        hc.2.2.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2.2.2⟩
      intro hz
      have hp := hc.2.2.2.2.2.2.1
      rw [hz, map_zero] at hp
      exact hc.2.2.2.2.2.2.2.1 hp

end
end ReedSolomon.HiddenDerivative.NonzeroInterpolationMachine
