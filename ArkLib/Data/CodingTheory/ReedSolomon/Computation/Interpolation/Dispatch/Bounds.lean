/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.Interpolation.Dispatch.Machine
/-!
# Field-size bounds for the actual interpolation dispatch budget

Positive order uses a quartic attempt majorant and at most n descending attempts, giving degree
five in q with every order/multiplicity dependence confined to the coefficient. Order zero uses
the tighter public matrix budget, so growing multiplicity has an absolute polynomial exponent.
All bounds include failed attempts and empty search intervals; no success premise is required.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.InterpolationDispatch

private theorem polynomial_scale (N q : ℕ) (hq : 0 < q) (cs : Fin (N + 1) → ℕ) :
    (∑ i, cs i * q ^ i.val) ≤ (∑ i, cs i) * q ^ N := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _hi
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hq (by omega))

/-- Coefficients of the public attempt budget with A=n=q. The exceptional dependence on d,m
is entirely inside these constants, including the original redundant row-count bound. -/
private def attemptCoefficients (d m : ℕ) : Fin 5 → ℕ :=
  let s := 32 * InterpolationSupportMachine.linearFactor (d + 1) (2 * m)
  let c := InterpolationPointBlockMachine.columnSize d m
  let l := m * (2 * m) ^ (d + 1)
  let z := d + 4
  let u := 288 * m * (m + 1)
  let v := 288 * (3 * m + 2) * (m + 1) +
    8192 * (m + 2) * (d + 2) ^ (m + 2) * (m * m + 1) + 64
  let t := 512 * z * (c + 1) ^ 2
  let b0 := s + v + t + 224
  let b1 := s * m + u + (v + 64) * l + 2 * t * l + 64 * c * l
  let b2 := u * l + t * l ^ 2
  ![2 * s + b0 + 64 * z + 302,
    2 * s * m + 5062 * l + b0 + b1 + 64 * z * l,
    b1 + b2 + 1136 * c * l + 5000 * l ^ 2,
    b2 + 6020 * c * l ^ 2,
    5000 * c * l ^ 3]

private theorem attempt_expansion (d m q : ℕ) :
    NonzeroInterpolationMachine.attemptBudget d m q q =
      ∑ i : Fin 5, attemptCoefficients d m i * q ^ i.val := by
  simp [attemptCoefficients, Fin.sum_univ_succ, NonzeroInterpolationMachine.attemptBudget,
    NonzeroInterpolationMachine.maximumColumns, NonzeroInterpolationMachine.budget,
    ReceivedInterpolationMatrixMachine.budget,
    ReceivedInterpolationMatrixMachine.budgetWithBudget,
    InterpolationPointBlockMachine.assemblyBudgetWithBudget,
    InterpolationPointBlockMachine.columnBudgetWithBudget, Matrix.NonzeroKernelMachine.budget,
    Matrix.ForwardEchelonMachine.budget, Matrix.ForwardEchelonMachine.stageBudget]
  ring

/-- Actual attempt budgets are quartic in the field-size bound with fixed d,m. -/
theorem attempt_budget_fixed (d m A n q : ℕ) (hq : 0 < q) (hA : A ≤ q) (hn : n ≤ q) :
    NonzeroInterpolationMachine.attemptBudget d m A n ≤
      NonzeroInterpolationMachine.attemptBudget d m 1 1 * q ^ 4 := by
  have hm : NonzeroInterpolationMachine.attemptBudget d m A n ≤
      NonzeroInterpolationMachine.attemptBudget d m q q := by
    unfold NonzeroInterpolationMachine.attemptBudget NonzeroInterpolationMachine.maximumColumns
      NonzeroInterpolationMachine.budget ReceivedInterpolationMatrixMachine.budget
      ReceivedInterpolationMatrixMachine.budgetWithBudget
      InterpolationPointBlockMachine.assemblyBudgetWithBudget
      InterpolationPointBlockMachine.columnBudgetWithBudget
      Matrix.NonzeroKernelMachine.budget Matrix.ForwardEchelonMachine.budget
      Matrix.ForwardEchelonMachine.stageBudget
    gcongr
  have hs := polynomial_scale 4 q hq (attemptCoefficients d m)
  rw [attempt_expansion d m q] at hm
  rw [attempt_expansion d m 1]
  simpa only [one_pow, mul_one] using hm.trans hs

/-- Positive-order dispatch includes every failed search attempt and all fixed overhead.
Only the coefficient depends on d,m; the exponent five is absolute and independent of k. -/
theorem budget_fixed (k d m A n q : ℕ) (hd : 0 < d) (hq : 0 < q)
    (hA : A ≤ n) (hn : n ≤ q) :
    budget k d m A n ≤ (NonzeroInterpolationMachine.attemptBudget d m 1 1 + 192) * q ^ 5 := by
  have ha := attempt_budget_fixed d m A n q hq (hA.trans hn) hn
  have hc : n - max (k - 1) (d + 1) ≤ q := (Nat.sub_le _ _).trans hn
  have hprod := Nat.mul_le_mul ha hc
  have hq5 : q ≤ q ^ 5 := by simpa using Nat.pow_le_pow_right hq (by decide : 1 ≤ 5)
  have hpos : 1 ≤ q ^ 5 := Nat.one_le_pow _ _ hq
  unfold budget AmbientSearchMachine.budget AmbientSearchMachine.searchBudget
  rw [if_neg (by omega : d ≠ 0)]
  nlinarith only [hprod, hn, hc, hq5, hpos]

private def zeroCoefficients : Fin 13 → ℕ :=
  ![6670, 11040, 11840, 33004, 17088, 24192, 50752, 17408, 24576, 40464, 8192, 8192, 40000]

private theorem zero_expansion (q : ℕ) :
    32 + NonzeroInterpolationMachine.zeroAttemptBudget q q q =
      ∑ i : Fin 13, zeroCoefficients i * q ^ i.val := by
  simp [zeroCoefficients, Fin.sum_univ_succ, NonzeroInterpolationMachine.zeroAttemptBudget,
    NonzeroInterpolationMachine.zeroBudget, ReceivedInterpolationMatrixMachine.zeroMatrixBudget,
    InterpolationPointBlockMachine.zeroAssemblyBudget,
    InterpolationPointBlockMachine.zeroColumnBudget,
    InterpolationSupportMachine.linearFactor, Matrix.NonzeroKernelMachine.budget,
    Matrix.ForwardEchelonMachine.budget, Matrix.ForwardEchelonMachine.stageBudget]
  ring

/-- Universal coefficient, exactly the order-zero dispatch diagonal evaluated at one. -/
def zeroCoefficient : ℕ := 293418

/-- The universal coefficient is derived from the literal public budget, not an assumed cost. -/
theorem zeroCoefficient_eq :
    32 + NonzeroInterpolationMachine.zeroAttemptBudget 1 1 1 = zeroCoefficient := by
  decide +kernel

/-- Order-zero dispatch stays polynomial when multiplicity grows, with absolute exponent twelve. -/
theorem budget_zero (k m A n q : ℕ) (hq : 0 < q) (hm : m ≤ n) (hA : A ≤ n) (hn : n ≤ q) :
    budget k 0 m A n ≤ zeroCoefficient * q ^ 12 := by
  have hmq := hm.trans hn
  have hAq := hA.trans hn
  have hmono : NonzeroInterpolationMachine.zeroAttemptBudget m A n ≤
      NonzeroInterpolationMachine.zeroAttemptBudget q q q := by
    unfold NonzeroInterpolationMachine.zeroAttemptBudget NonzeroInterpolationMachine.zeroBudget
      ReceivedInterpolationMatrixMachine.zeroMatrixBudget
      InterpolationPointBlockMachine.zeroAssemblyBudget
      InterpolationPointBlockMachine.zeroColumnBudget
      InterpolationSupportMachine.linearFactor Matrix.NonzeroKernelMachine.budget
      Matrix.ForwardEchelonMachine.budget Matrix.ForwardEchelonMachine.stageBudget
    gcongr
  have hc : (∑ i : Fin 13, zeroCoefficients i) = zeroCoefficient := by decide +kernel
  have hs := polynomial_scale 12 q hq zeroCoefficients
  rw [hc] at hs
  simp only [budget]
  exact (Nat.add_le_add_left hmono 32).trans ((zero_expansion q).trans_le hs)

variable {F : Type*} [Field F] [DecidableEq F]

/-- The observed positive-order dispatch ledger inherits the bound, including actual failures. -/
theorem cost_fixed (k d m A q : ℕ) (rows : List (F × F)) (hd : 0 < d) (hq : 0 < q)
    (hA : A ≤ rows.length) (hn : rows.length ≤ q) :
    (run k d m A rows).2 ≤ (NonzeroInterpolationMachine.attemptBudget d m 1 1 + 192) * q ^ 5 := by
  exact (cost_le k d m A rows).trans (budget_fixed k d m A rows.length q hd hq hA hn)

/-- The observed order-zero ledger inherits the universal bound on either success or failure. -/
theorem cost_zero (k m A q : ℕ) (rows : List (F × F)) (hq : 0 < q)
    (hm : m ≤ rows.length) (hA : A ≤ rows.length) (hn : rows.length ≤ q) :
    (run k 0 m A rows).2 ≤ zeroCoefficient * q ^ 12 := by
  exact (cost_le k 0 m A rows).trans (budget_zero k m A rows.length q hq hm hA hn)

end ReedSolomon.HiddenDerivative.InterpolationDispatch
