/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Selection.GuardInputBounds
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Output.CanonicalOutputSemantics
/-!
# Canonical collector budgets from numerical input bounds

The actual acceptance and collector programs retain their guard, descent, degree, agreement and
allocation charges. Uniform width, equation mass, prefix length and record-count bounds give
polynomial majorants without squaring the number of candidates. Applying these size premises to
the actual generated chain and bounding the outer decoder are separate composition steps.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.CanonicalOutputMachine

namespace Guard
export HiddenDerivative.CanonicalGuardMachine (inputFuel inputWork input_bounds)
end Guard

/-- Candidate fuel is polynomial even when the requested output width is zero. -/
def candidateFuelBound (w n : ℕ) : ℕ := 3 * w + n * (3 * w + 6) + 16

/-- Uniform bound for one existing acceptance call, including its guard prefix. -/
def acceptanceFuelBound (w d M samples n p : ℕ) : ℕ :=
  Guard.inputFuel w d M samples p + candidateFuelBound w n + 4

/-- Uniform work of the same acceptance call, with all child dispatches. -/
def acceptanceWorkBound (w d M samples n p : ℕ) : ℕ :=
  Guard.inputWork w d M samples p + 3 * Guard.inputFuel w d M samples p +
    192 * (w + 1) * (n + 1) + 3 * candidateFuelBound w n + 20

/-- Fuel grows linearly in the number of generated records. -/
def inputFuel (w d M samples n p records : ℕ) : ℕ :=
  (acceptanceFuelBound w d M samples n p + 4) * records + 4

/-- Work grows linearly in the number of records; no quadratic duplicate-removal scan is used. -/
def inputWork (w d M samples n p records : ℕ) : ℕ :=
  (acceptanceWorkBound w d M samples n p +
    3 * acceptanceFuelBound w d M samples n p + 30) * records + 16

theorem candidate_fuel_le (w k n : ℕ) :
    QuadraticCandidateMachine.fuel w k n ≤ candidateFuelBound w n := by
  unfold QuadraticCandidateMachine.fuel CandidateFilterMachine.fuel candidateFuelBound
  omega

variable {F : Type*} [Field F] {a b : F}
variable [Fact (∀ r : F, r ^ 2 ≠ a + b * r)]

/-- Width, equation mass and prefix length bound an actual generated record's acceptance. -/
theorem item_input_bounds (d w k n M p : ℕ) (samples : List (QuadraticAlgebra F a b))
    (r : Record (QuadraticAlgebra F a b)) (hw : r.coefficients.length ≤ w)
    (hs : MvPolynomial.PartialDerivativeMachine.inputMass r.context.separant ≤ M)
    (hp : ∀ q ∈ r.context.previous, MvPolynomial.PartialDerivativeMachine.inputMass q ≤ M)
    (hlen : r.context.previous.length ≤ p) :
    itemFuel d samples w k n r ≤ acceptanceFuelBound w d M samples.length n p ∧
      itemWork d samples w k n r ≤ acceptanceWorkBound w d M samples.length n p := by
  obtain ⟨hf, hb⟩ := Guard.input_bounds (guardInput d samples r) r.context.previous
    w d M p hw le_rfl hs hp hlen
  have hc := candidate_fuel_le w k n
  constructor
  · unfold itemFuel CanonicalAcceptanceMachine.fuel acceptanceFuelBound
    exact Nat.add_le_add_right (Nat.add_le_add hf hc) 4
  · unfold itemWork CanonicalAcceptanceMachine.workBound acceptanceWorkBound
      QuadraticCandidateMachine.workBound
    dsimp only [guardInput] at hf hb ⊢
    omega

/-- The existing collector fuel and work have numerical majorants linear in a record cap. -/
theorem input_bounds (d w k n M p R : ℕ) (samples : List (QuadraticAlgebra F a b))
    (records : List (Record (QuadraticAlgebra F a b)))
    (hw : ∀ r ∈ records, r.coefficients.length ≤ w)
    (hs : ∀ r ∈ records, MvPolynomial.PartialDerivativeMachine.inputMass r.context.separant ≤ M)
    (hp : ∀ r ∈ records, ∀ q ∈ r.context.previous,
      MvPolynomial.PartialDerivativeMachine.inputMass q ≤ M)
    (hlen : ∀ r ∈ records, r.context.previous.length ≤ p) (hR : records.length ≤ R) :
    fuel d samples w k n records ≤ inputFuel w d M samples.length n p R ∧
      workBound d samples w k n records ≤ inputWork w d M samples.length n p R := by
  have hi := fun r hr ↦ item_input_bounds d w k n M p samples r
    (hw r hr) (hs r hr) (hp r hr) (hlen r hr)
  obtain ⟨hf, hb⟩ := scan_bounds d w k n
    (acceptanceFuelBound w d M samples.length n p)
    (acceptanceWorkBound w d M samples.length n p) samples records
    (fun r hr ↦ (hi r hr).1) (fun r hr ↦ (hi r hr).2)
  constructor
  · unfold fuel inputFuel
    have h := Nat.mul_le_mul_left (acceptanceFuelBound w d M samples.length n p + 4) hR
    omega
  · unfold workBound inputWork
    have h := Nat.mul_le_mul_left (acceptanceWorkBound w d M samples.length n p +
      3 * acceptanceFuelBound w d M samples.length n p + 30) hR
    omega

end ReedSolomon.ListDecoding.CanonicalOutputMachine
