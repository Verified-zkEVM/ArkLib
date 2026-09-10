/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.OrderZero.AssemblyBounds
public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.Interpolation.Solution.Attempts
/-!
# Polynomial observed cost of order-zero interpolation attempts

The same support, matrix, solver and sparse conversion execute unchanged. The order-zero row
bound replaces the generic exponential estimate, including on genuine no-kernel failures.
These bounds allow growing multiplicity. Success from large-gap parameters still requires an
actual eligible witness; a mathematical list-cardinality bound alone does not supply one.
The missing witness route also needs triangular image/rank counting and the D=0 boundary.
Multiplicity n+1 would not ensure below-characteristic jet degree under q≥n; any large-gap
construction must resolve that requirement without changing the field or block-length regime.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.NonzeroInterpolationMachine

open PolynomialDifferential

noncomputable section

variable {F : Type*} [Field F] [DecidableEq F]

/-- Polynomial order-zero attempt cost at the actual support-column count. -/
def zeroBudget (m A L n : ℕ) : ℕ :=
  32 * InterpolationSupportMachine.linearFactor 1 (2 * m) * (m * A + 1) +
    ReceivedInterpolationMatrixMachine.zeroMatrixBudget m A L n +
    Matrix.NonzeroKernelMachine.budget (m * m * L * n) L + 256 * (L + 1) + 32

/-- The same actual solver completion admits a polynomial charge on both success and failure. -/
theorem run_zero_cost (D m A : ℕ) (received : List (F × F)) :
    ∃ result c, run D 0 m A received = (result, c) ∧
      c ≤ zeroBudget m A (ReceivedInterpolationMatrixMachine.support D 0 m A).length
        received.length := by
  obtain ⟨mat, mc, hmat, hcols, _, hcount, hrows, hmc⟩ :=
    ReceivedInterpolationMatrixMachine.run_zero_bounds D m A received
  have hmatBudget : ReceivedInterpolationMatrixMachine.runWithBudget D 0 m (2 * m) A received =
      (some mat, mc) := by
    simpa [ReceivedInterpolationMatrixMachine.run] using hmat
  obtain ⟨mat', mc', hmat', _, _, _, _, hshape, _, _, _⟩ :=
    ReceivedInterpolationMatrixMachine.run_refines D 0 m A received
  rw [hmat] at hmat'
  cases hmat'
  have hr : Matrix.ForwardEchelonMachine.Rectangular mat.columns mat.rows :=
    fun r hr ↦ (hshape r hr).1
  have hz : ∀ r ∈ mat.rows, r.2 = 0 := fun r hr ↦ (hshape r hr).2
  obtain ⟨sc, hs, hsc⟩ := InterpolationSupportMachine.enumerate_correct D 0 m A
  simp only [Nat.zero_add] at hsc
  have hs' : InterpolationSupportMachine.enumerateWithBudget D 0 m (2 * m) A =
      (.done (InterpolationSupportMachine.supportSpec
        (InterpolationSupportMachine.parametersWithBudget D 0 m (2 * m) A)), sc) := by
    simpa [InterpolationSupportMachine.enumerate, InterpolationSupportMachine.parameters,
      InterpolationSupportMachine.parametersWithBudget] using hs
  rcases Matrix.NonzeroKernelMachine.completion_runFuel mat.columns mat.rows hr hz with hh | hh
  · obtain ⟨j, cs, kc, hsolve, hlen, _, _, _, hkc⟩ := hh
    obtain ⟨ec, hem, _, hec⟩ := emit_correct 2
      (ReceivedInterpolationMatrixMachine.support D 0 m A) cs (hlen.trans hcols) (by
        intro v hv
        exact (InterpolationSupportMachine.supportSpec_width _ hv).le)
    refine ⟨some ⟨j, cs, emitSpec (ReceivedInterpolationMatrixMachine.support D 0 m A) cs⟩,
      32 + sc + mc + Matrix.NonzeroKernelMachine.totalCost kc + ec, ?_, ?_⟩
    · simp only [run, runWithBudget, hs', hmatBudget, hcount, hsolve]
      have hsupport : InterpolationSupportMachine.supportSpec
          (InterpolationSupportMachine.parametersWithBudget D 0 m (2 * m) A) =
          ReceivedInterpolationMatrixMachine.support D 0 m A := by
        simp [ReceivedInterpolationMatrixMachine.support,
          ReceivedInterpolationMatrixMachine.supportWithBudget,
          InterpolationSupportMachine.parametersWithBudget]
      rw [hsupport, hem]
      rfl
    · have hb := hkc.trans (kernelBudget_mono mat.columns _
        (m * m * (ReceivedInterpolationMatrixMachine.support D 0 m A).length * received.length)
        (by simpa only [hcount] using hrows))
      rw [hcols] at hb
      unfold zeroBudget
      omega
  · obtain ⟨kc, hsolve, hkc, _⟩ := hh
    refine ⟨none, 32 + sc + mc + Matrix.NonzeroKernelMachine.totalCost kc, ?_, ?_⟩
    · simp only [run, runWithBudget, hs', hmatBudget, hcount, hsolve]
    · have hb := hkc.trans (kernelBudget_mono mat.columns _
        (m * m * (ReceivedInterpolationMatrixMachine.support D 0 m A).length * received.length)
        (by simpa only [hcount] using hrows))
      rw [hcols] at hb
      unfold zeroBudget
      omega

/-- All actual successes retain their complete certificate under the sharper cost bound. -/
theorem attempt_zero_complete (D m A : ℕ) (received : List (F × F)) :
    ∃ result c, run D 0 m A received = (result, c) ∧
      c ≤ zeroBudget m A (ReceivedInterpolationMatrixMachine.support D 0 m A).length
        received.length ∧
      ∀ out, result = some out → Certified (d := 0) D m A received out := by
  obtain ⟨result, c, hr, hc⟩ := run_zero_cost D m A received
  obtain ⟨result', c', hr', _, hcert⟩ := attempt_complete (d := 0) D m A received
  rw [hr] at hr'
  cases hr'
  exact ⟨result, c, hr, hc, hcert⟩

/-- The polynomial bound is monotone in its support-column parameter. -/
theorem zeroBudget_mono_columns (m A L M n : ℕ) (h : L ≤ M) :
    zeroBudget m A L n ≤ zeroBudget m A M n := by
  unfold zeroBudget ReceivedInterpolationMatrixMachine.zeroMatrixBudget
    InterpolationPointBlockMachine.zeroAssemblyBudget Matrix.NonzeroKernelMachine.budget
    Matrix.ForwardEchelonMachine.budget Matrix.ForwardEchelonMachine.stageBudget
  gcongr

/-- Initial integer sizes bound the support by 2*m²*A; D and visited outputs are absent. -/
def zeroAttemptBudget (m A n : ℕ) : ℕ := zeroBudget m A (m * A * (2 * m)) n

/-- Unconditional polynomial completion with only initial integer sizes in the cost bound. -/
theorem attempt_zero_uniform (D m A : ℕ) (received : List (F × F)) :
    ∃ result c, run D 0 m A received = (result, c) ∧
      c ≤ zeroAttemptBudget m A received.length ∧
      ∀ out, result = some out → Certified (d := 0) D m A received out := by
  obtain ⟨result, c, hr, hc, hcert⟩ := attempt_zero_complete D m A received
  have hl : (ReceivedInterpolationMatrixMachine.support D 0 m A).length ≤ m * A * (2 * m) := by
    simpa only [maximumColumns, Nat.zero_add, pow_one] using support_length_le D 0 m A
  exact ⟨result, c, hr, hc.trans (zeroBudget_mono_columns m A _ _ _ hl), hcert⟩

/-- An actual eligible order-zero witness gives the same certified execution in polynomial work.
This conditional bridge does not assume or claim a large-gap interpolation existence theorem. -/
theorem run_zero_of_witness (D m A : ℕ) (received : List (F × F))
    (Q : DifferentialPolynomial F 0) (hn : Q ≠ 0) (he : Eligible D m A Q)
    (hl : ∀ p ∈ received, localConstraintAt m p.1 p.2 Q = 0) :
    ∃ out c, run D 0 m A received = (some out, c) ∧
      Certified (d := 0) D m A received out ∧ c ≤ zeroAttemptBudget m A received.length := by
  obtain ⟨result, c, hr, hc, hcert⟩ := attempt_zero_uniform D m A received
  cases result with
  | none =>
    have hnone : (run D 0 m A received).1 = none := congrArg Prod.fst hr
    exact ((run_none_iff D m A received).mp hnone ⟨Q, hn, he, hl⟩).elim
  | some out => exact ⟨out, c, hr, hcert out rfl, hc⟩

end
end ReedSolomon.HiddenDerivative.NonzeroInterpolationMachine
