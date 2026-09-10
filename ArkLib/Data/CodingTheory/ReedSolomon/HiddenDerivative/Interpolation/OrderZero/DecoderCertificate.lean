/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.OrderZero.Witness
public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.Interpolation.Solution.ZeroBounds
/-!
# Certified actual order-zero interpolation output

The direct attempt includes D=0 and has polynomial observed work even with growing multiplicity.
Every degree and characteristic assertion below concerns the polynomial reconstructed from the
actual returned coefficient vector. The existence witness is used only to force successful
execution. The outer prepared decoder must consume this direct attempt instead of ambient search,
whose lower endpoint excludes D=0; its root solver need not be duplicated.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.OrderZeroDecoderCertificate

noncomputable section

open NonzeroInterpolationMachine PolynomialDifferential

variable {F : Type*} [Field F] [DecidableEq F]

omit [DecidableEq F] in
/-- Semantic bounds for the actual returned source polynomial, derived from its full certificate. -/
theorem returned_bounds (D m A : ℕ) (received : List (F × F)) (out : Output F)
    (hc : Certified (d := 0) D m A received out) :
    let Q := sourceOutput (d := 0) D m A out
    Q ≠ 0 ∧ Eligible D m A Q ∧ jetDegree Q 0 < 2 * m ∧
      differentialWeightedDegree D Q < m * A ∧
      ∀ p ∈ received, localConstraintAt m p.1 p.2 Q = 0 := by
  obtain ⟨_, _, _, _, _, _, hrep, hnonzero, he, hw, hl⟩ := hc
  have hn : sourceOutput (d := 0) D m A out ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hrep
    exact hnonzero hrep
  exact ⟨hn, he, eligible_zero_jetDegree D m A _ hn he, hw, hl⟩

omit [DecidableEq F] in
/-- The characteristic bound belongs to the returned polynomial, not merely an existence witness. -/
theorem returned_characteristic (D m A : ℕ) (received : List (F × F)) (out : Output F)
    (hc : Certified (d := 0) D m A received out) (hchar : 2 * m ≤ ringChar F) :
    ∀ j, jetDegree (sourceOutput (d := 0) D m A out) j < ringChar F := by
  obtain ⟨hn, he, _, _, _⟩ := returned_bounds D m A received out hc
  exact eligible_zero_characteristic D m A _ hn he hchar

/-- Any actual witness forces a direct successful attempt with all returned-output degree bounds. -/
theorem direct_of_witness (D m A : ℕ) (received : List (F × F))
    (Q : DifferentialPolynomial F 0) (hne : Q ≠ 0) (he : Eligible D m A Q)
    (hl : ∀ p ∈ received, localConstraintAt m p.1 p.2 Q = 0) :
    ∃ out c, run D 0 m A received = (some out, c) ∧ Certified (d := 0) D m A received out ∧
      c ≤ zeroAttemptBudget m A received.length ∧
      let P := sourceOutput (d := 0) D m A out
      P ≠ 0 ∧ Eligible D m A P ∧ jetDegree P 0 < 2 * m ∧
        differentialWeightedDegree D P < m * A ∧
        ∀ p ∈ received, localConstraintAt m p.1 p.2 P = 0 := by
  obtain ⟨out, c, hr, hc, hcost⟩ := run_zero_of_witness D m A received Q hne he hl
  exact ⟨out, c, hr, hc, hcost, returned_bounds D m A received out hc⟩

/-- Quarter gaps give an actual direct attempt at k-1, including the constant-message degree zero.
No real parameter, witness polynomial or returned size is an input to the runtime or its budget. -/
theorem quarter_attempt (delta : ℝ) (hdelta : (1 / 4 : ℝ) ≤ delta)
    (n k A : ℕ) (hn : 3 ≤ n) (hk : 0 < k)
    (hA : ReedSolomon.agreementThreshold delta n k ≤ A) (centers values : Fin n → F) :
    let D := k - 1
    let m := n / 2
    let received := List.ofFn (fun i ↦ (centers i, values i))
    ∃ out c, run D 0 m A received = (some out, c) ∧ Certified (d := 0) D m A received out ∧
      c ≤ zeroAttemptBudget m A n ∧
      let P := sourceOutput (d := 0) D m A out
      P ≠ 0 ∧ Eligible D m A P ∧ jetDegree P 0 < 2 * m ∧
        differentialWeightedDegree D P < m * A ∧
        ∀ p ∈ received, localConstraintAt m p.1 p.2 P = 0 := by
  obtain ⟨Q, hne, he, _, _, _, hl⟩ :=
    exists_quarter_zero_witness delta hdelta n k A hn hk hA centers values
  simpa only [List.length_ofFn] using
    direct_of_witness (k - 1) (n / 2) A (List.ofFn (fun i ↦ (centers i, values i))) Q hne he hl

/-- The actual quarter-gap output has all individual jet degrees below characteristic.
The hypothesis is about ring characteristic, so extension-field cardinality is not substituted. -/
theorem quarter_attempt_characteristic (delta : ℝ) (hdelta : (1 / 4 : ℝ) ≤ delta)
    (n k A : ℕ) (hn : 3 ≤ n) (hk : 0 < k)
    (hA : ReedSolomon.agreementThreshold delta n k ≤ A) (hchar : n ≤ ringChar F)
    (centers values : Fin n → F) :
    let D := k - 1
    let m := n / 2
    let received := List.ofFn (fun i ↦ (centers i, values i))
    ∃ out c, run D 0 m A received = (some out, c) ∧ Certified (d := 0) D m A received out ∧
      c ≤ zeroAttemptBudget m A n ∧
      let P := sourceOutput (d := 0) D m A out
      P ≠ 0 ∧ Eligible D m A P ∧ jetDegree P 0 < 2 * m ∧
        differentialWeightedDegree D P < m * A ∧ (∀ j, jetDegree P j < ringChar F) ∧
        ∀ p ∈ received, localConstraintAt m p.1 p.2 P = 0 := by
  obtain ⟨out, c, hr, hc, hcost, hp, he, hj, hw, hl⟩ :=
    quarter_attempt delta hdelta n k A hn hk hA centers values
  have hcap : 2 * (n / 2) ≤ ringChar F := (by omega : 2 * (n / 2) ≤ n).trans hchar
  exact ⟨out, c, hr, hc, hcost, hp, he, hj, hw,
    returned_characteristic _ _ _ _ out hc hcap, hl⟩

end
end ReedSolomon.HiddenDerivative.OrderZeroDecoderCertificate
