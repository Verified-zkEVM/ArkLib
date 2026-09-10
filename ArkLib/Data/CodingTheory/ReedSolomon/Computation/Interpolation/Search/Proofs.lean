/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.Interpolation.Search.Machine
public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.Interpolation.Solution.Attempts
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.WeightedSupport.Eligibility
/-!
# Total search, bounded failed attempts, and prescribed weighted-support success

The generic theorem certifies every returned success and charges every failed attempt. A
separate existence theorem joins the prescribed weighted-support witness to actual execution.
Descending
order ensures the returned degree is at least the prescribed successful degree, preserving
the separant field-size slack rather than weakening it at an earlier ambient candidate.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.AmbientSearchMachine

noncomputable section

open PolynomialDifferential
open NonzeroInterpolationMachine
  (Certified CertifiedWithBudget attemptBudget attemptBudgetWithBudget)
open ReedSolomon ListDecoding

variable {F : Type*} [Field F] [DecidableEq F]

/-- A uniform budget for a finite candidate loop, including its terminal control step. -/
def searchBudget (d m A n count : ℕ) : ℕ := (attemptBudget d m A n + 32) * count + 32

/-- A uniform budget for a finite candidate loop at strict jet cutoff `J`. -/
def searchBudgetWithBudget (d m J A n count : ℕ) : ℕ :=
  (attemptBudgetWithBudget d m J A n + 32) * count + 32

/-- Every explicitly budgeted search is bounded and every success is certified. -/
theorem searchWithBudget_complete (d m J A : ℕ) (received : List (F × F)) (count D : ℕ)
    (hcount : count ≤ D + 1) :
    ∃ result c, searchWithBudget d m J A received count D = (result, c) ∧
      c ≤ searchBudgetWithBudget d m J A received.length count ∧
      ∀ out, result = some out →
        D + 1 - count ≤ out.degree ∧ out.degree ≤ D ∧
          CertifiedWithBudget (d := d) out.degree m J A received out.interpolant := by
  induction count generalizing D with
  | zero => exact ⟨none, 32, rfl, by simp [searchBudgetWithBudget], by simp⟩
  | succ count ih =>
    obtain ⟨result, c, hr, hc, hs⟩ :=
      NonzeroInterpolationMachine.attemptWithBudget_uniform (d := d) D m J A received
    cases result with
    | some interp =>
      refine ⟨some ⟨D, interp⟩, 32 + c, ?_, ?_, ?_⟩
      · simp only [searchWithBudget, hr]
      · unfold searchBudgetWithBudget
        nlinarith
      · intro out ho
        cases ho
        exact ⟨by change D + 1 - (count + 1) ≤ D; omega, le_rfl, hs interp rfl⟩
    | none =>
      obtain ⟨result, c', hr', hc', hs'⟩ := ih (D - 1) (by omega)
      refine ⟨result, 32 + c + c', ?_, ?_, ?_⟩
      · simp only [searchWithBudget, hr, hr']
      · unfold searchBudgetWithBudget at *
        nlinarith
      · intro out ho
        obtain ⟨hl, hu, hcert⟩ := hs' out ho
        refine ⟨?_, by omega, hcert⟩
        omega

/-- A successful budget-eligible candidate forces search success at its degree or above. -/
theorem searchWithBudget_success_of_candidate (d m J A : ℕ) (received : List (F × F))
    (count D good : ℕ) (hcount : count ≤ D + 1)
    (hl : D + 1 - count ≤ good) (hu : good ≤ D)
    (hgood : (NonzeroInterpolationMachine.runWithBudget good d m J A received).1 ≠ none) :
    ∃ out c, searchWithBudget d m J A received count D = (some out, c) ∧
      good ≤ out.degree := by
  induction count generalizing D with
  | zero => omega
  | succ count ih =>
    obtain ⟨result, c, hr, _, _⟩ :=
      NonzeroInterpolationMachine.attemptWithBudget_uniform (d := d) D m J A received
    cases result with
    | some interp =>
      exact ⟨⟨D, interp⟩, 32 + c, by simp only [searchWithBudget, hr], hu⟩
    | none =>
      have hne : good ≠ D := by
        intro he
        apply hgood
        simpa only [he] using congrArg Prod.fst hr
      obtain ⟨out, c', hr', hg⟩ := ih (D - 1) (by omega) (by omega) (by omega)
      exact ⟨out, 32 + c + c', by simp only [searchWithBudget, hr, hr'], hg⟩

/-- Public budget for search with independent strict jet cutoff `J`. -/
def budgetWithBudget (k d m J A n : ℕ) : ℕ :=
  32 + 32 * (n + 1) +
    searchBudgetWithBudget d m J A n (n - max (k - 1) d)

/-- Total correctness for the public explicitly budgeted search. -/
theorem runWithBudget_complete (k d m J A : ℕ) (received : List (F × F)) :
    ∃ result c, runWithBudget k d m J A received = (result, c) ∧
      c ≤ budgetWithBudget k d m J A received.length ∧
      ∀ out, result = some out →
        max (k - 1) d ≤ out.degree ∧ out.degree < received.length ∧
          CertifiedWithBudget (d := d) out.degree m J A received out.interpolant := by
  obtain ⟨result, c, hr, hc, hs⟩ := searchWithBudget_complete d m J A received
    (received.length - max (k - 1) d) (received.length - 1) (by omega)
  refine ⟨result, 32 + 32 * (received.length + 1) + c, ?_, ?_, ?_⟩
  · simp only [runWithBudget, ReceivedInterpolationMatrixMachine.countCells_correct, hr]
  · unfold budgetWithBudget
    omega
  · intro out ho
    obtain ⟨hl, hu, hcert⟩ := hs out ho
    have hn : 0 < received.length := by
      by_contra hn
      have hz : received.length = 0 := by omega
      simp only [hz, Nat.zero_sub, searchWithBudget] at hr
      have he := congrArg Prod.fst hr
      rw [ho] at he
      cases he
    exact ⟨by omega, by omega, hcert⟩

/-- The budgeted integer search succeeds from one budget-eligible interpolation witness. -/
theorem runWithBudget_success_of_witness (k d m J A good : ℕ) (received : List (F × F))
    (hl : max (k - 1) d ≤ good) (hu : good < received.length)
    (Q : DifferentialPolynomial F d) (hn : Q ≠ 0)
    (he : NonzeroInterpolationMachine.EligibleWithBudget good m J A Q)
    (hlocal : ∀ p ∈ received, localConstraintAt m p.1 p.2 Q = 0) :
    ∃ out c, runWithBudget k d m J A received = (some out, c) ∧
      good ≤ out.degree ∧ out.degree < received.length ∧
      CertifiedWithBudget (d := d) out.degree m J A received out.interpolant ∧
      c ≤ budgetWithBudget k d m J A received.length := by
  have hg : (NonzeroInterpolationMachine.runWithBudget good d m J A received).1 ≠ none := by
    intro h
    exact (NonzeroInterpolationMachine.runWithBudget_none_iff good m J A received).mp h
      ⟨Q, hn, he, hlocal⟩
  obtain ⟨out, c, hr, hout⟩ := searchWithBudget_success_of_candidate d m J A received
    (received.length - max (k - 1) d) (received.length - 1) good
    (by omega) (by omega) (by omega) hg
  have hrun : runWithBudget k d m J A received =
      (some out, 32 + 32 * (received.length + 1) + c) := by
    simp only [runWithBudget, ReceivedInterpolationMatrixMachine.countCells_correct, hr]
  obtain ⟨result, c', hr', hc', hs⟩ := runWithBudget_complete k d m J A received
  rw [hrun] at hr'
  cases hr'
  obtain ⟨_, hu', hcert⟩ := hs out rfl
  exact ⟨out, _, hrun, hout, hu', hcert, hc'⟩

/-- Every execution is bounded, and all successes satisfy the exact interpolation certificate. -/
theorem search_complete (d m A : ℕ) (received : List (F × F)) (count D : ℕ)
    (hcount : count ≤ D + 1) :
    ∃ result c, search d m A received count D = (result, c) ∧
      c ≤ searchBudget d m A received.length count ∧
      ∀ out, result = some out →
        D + 1 - count ≤ out.degree ∧ out.degree ≤ D ∧
          Certified (d := d) out.degree m A received out.interpolant := by
  induction count generalizing D with
  | zero => exact ⟨none, 32, rfl, by simp [searchBudget], by simp⟩
  | succ count ih =>
    obtain ⟨result, c, hr, hc, hs⟩ :=
      NonzeroInterpolationMachine.attempt_uniform (d := d) D m A received
    change NonzeroInterpolationMachine.runWithBudget D d m (2 * m) A received =
      (result, c) at hr
    cases result with
    | some interp =>
      refine ⟨some ⟨D, interp⟩, 32 + c, ?_, ?_, ?_⟩
      · simp only [search, searchWithBudget, hr]
      · unfold searchBudget
        nlinarith
      · intro out ho
        cases ho
        exact ⟨by change D + 1 - (count + 1) ≤ D; omega, le_rfl, hs interp rfl⟩
    | none =>
      obtain ⟨result, c', hr', hc', hs'⟩ := ih (D - 1) (by omega)
      change searchWithBudget d m (2 * m) A received count (D - 1) =
        (result, c') at hr'
      refine ⟨result, 32 + c + c', ?_, ?_, ?_⟩
      · simp only [search, searchWithBudget, hr, hr']
      · unfold searchBudget at *
        nlinarith
      · intro out ho
        obtain ⟨hl, hu, hcert⟩ := hs' out ho
        refine ⟨?_, by omega, hcert⟩
        omega

/-- An actual successful candidate forces a success at that degree or a larger one. -/
theorem search_success_of_candidate (d m A : ℕ) (received : List (F × F))
    (count D good : ℕ) (hcount : count ≤ D + 1)
    (hl : D + 1 - count ≤ good) (hu : good ≤ D)
    (hgood : (NonzeroInterpolationMachine.run good d m A received).1 ≠ none) :
    ∃ out c, search d m A received count D = (some out, c) ∧ good ≤ out.degree := by
  induction count generalizing D with
  | zero => omega
  | succ count ih =>
    obtain ⟨result, c, hr, _, _⟩ :=
      NonzeroInterpolationMachine.attempt_uniform (d := d) D m A received
    change NonzeroInterpolationMachine.runWithBudget D d m (2 * m) A received =
      (result, c) at hr
    cases result with
    | some interp =>
      exact ⟨⟨D, interp⟩, 32 + c,
        by simp only [search, searchWithBudget, hr], hu⟩
    | none =>
      have hne : good ≠ D := by
        intro he
        apply hgood
        change (NonzeroInterpolationMachine.runWithBudget good d m (2 * m) A received).1 = none
        simpa only [he] using congrArg Prod.fst hr
      obtain ⟨out, c', hr', hg⟩ := ih (D - 1) (by omega) (by omega) (by omega)
      change searchWithBudget d m (2 * m) A received count (D - 1) =
        (some out, c') at hr'
      exact ⟨out, 32 + c + c',
        by simp only [search, searchWithBudget, hr, hr'], hg⟩

/-- The public budget includes input counting and every possible candidate attempt. -/
def budget (k d m A n : ℕ) : ℕ :=
  32 + 32 * (n + 1) + searchBudget d m A n (n - max (k - 1) (d + 1))

/-- Public total correctness, including empty input and empty candidate intervals. -/
theorem run_complete (k d m A : ℕ) (received : List (F × F)) :
    ∃ result c, run k d m A received = (result, c) ∧
      c ≤ budget k d m A received.length ∧
      ∀ out, result = some out →
        max (k - 1) (d + 1) ≤ out.degree ∧ out.degree < received.length ∧
          Certified (d := d) out.degree m A received out.interpolant := by
  obtain ⟨result, c, hr, hc, hs⟩ := search_complete d m A received
    (received.length - max (k - 1) (d + 1)) (received.length - 1) (by omega)
  refine ⟨result, 32 + 32 * (received.length + 1) + c, ?_, ?_, ?_⟩
  · simp only [run, ReceivedInterpolationMatrixMachine.countCells_correct, hr]
  · unfold budget
    omega
  · intro out ho
    obtain ⟨hl, hu, hcert⟩ := hs out ho
    have hn : 0 < received.length := by
      by_contra hn
      have hz : received.length = 0 := by omega
      simp only [hz, Nat.zero_sub, search, searchWithBudget] at hr
      have he := congrArg Prod.fst hr
      rw [ho] at he
      cases he
    exact ⟨by omega, by omega, hcert⟩

/-- The actual integer search succeeds whenever one candidate has an eligible witness. -/
theorem run_success_of_witness (k d m A good : ℕ) (received : List (F × F))
    (hl : max (k - 1) (d + 1) ≤ good) (hu : good < received.length)
    (Q : DifferentialPolynomial F d) (hn : Q ≠ 0)
    (he : NonzeroInterpolationMachine.Eligible good m A Q)
    (hlocal : ∀ p ∈ received, localConstraintAt m p.1 p.2 Q = 0) :
    ∃ out c, run k d m A received = (some out, c) ∧
      good ≤ out.degree ∧ out.degree < received.length ∧
      Certified (d := d) out.degree m A received out.interpolant ∧
      c ≤ budget k d m A received.length := by
  have hg : (NonzeroInterpolationMachine.run good d m A received).1 ≠ none := by
    intro h
    exact (NonzeroInterpolationMachine.run_none_iff good m A received).mp h ⟨Q, hn, he, hlocal⟩
  obtain ⟨out, c, hr, hout⟩ := search_success_of_candidate d m A received
    (received.length - max (k - 1) (d + 1)) (received.length - 1) good
    (by omega) (by omega) (by omega) hg
  have hrun : run k d m A received =
      (some out, 32 + 32 * (received.length + 1) + c) := by
    simp only [run, ReceivedInterpolationMatrixMachine.countCells_correct, hr]
  obtain ⟨result, c', hr', hc', hs⟩ := run_complete k d m A received
  rw [hrun] at hr'
  cases hr'
  obtain ⟨_, hu', hcert⟩ := hs out rfl
  exact ⟨out, _, hrun, hout, hu', hcert, hc'⟩

/-- Prescribed small-gap weighted-support parameters guarantee actual search success. Delta
appears only in the proof-side choice of d,m; the runtime still receives integers and points. -/
theorem run_prescribed_weightedSupport {q : ℕ} [Fact q.Prime]
    (delta : ℝ) (hdelta : 0 < delta)
    (hquarter : delta < (1 / 4 : ℝ)) (n k A : ℕ)
    (hblock : 8 * weightedSupportMultiplicity delta ≤ n) (hk : 0 < k) (hkn : k ≤ n)
    (hA : ReedSolomon.agreementThreshold delta n k ≤ A) (hAn : A ≤ n)
    (hnq : n ≤ q) (domain : Fin n ↪ ZMod q) (received : Fin n → ZMod q) :
    let d := capacityDerivativeOrder delta
    let m := weightedSupportMultiplicity delta
    let rows := List.ofFn (fun i => (domain i, received i))
    ∃ out c, run k d m A rows = (some out, c) ∧
      weightedSupportAmbientDimension delta n k - 1 ≤ out.degree ∧ out.degree < n ∧
      Certified (d := d) out.degree m A rows out.interpolant ∧
      c ≤ budget k d m A n := by
  obtain ⟨hl, hu, Q, hn, he, hlocal⟩ :=
    prescribed_weightedSupport_eligible_candidate delta hdelta hquarter n k A hblock hk hkn hA
      hAn domain received hnq
  simpa only [List.length_ofFn] using
    run_success_of_witness k _ _ A _ (List.ofFn (fun i => (domain i, received i))) hl
      (by simpa only [List.length_ofFn] using hu) Q hn he hlocal

/-- Descending success preserves the separant field-size inequality at the prescribed degree. -/
theorem separant_slack_mono (m A d prescribed actual bound : ℕ)
    (h : prescribed ≤ actual) (hbound : 2 * (m * A + d - prescribed - 1) ≤ bound) :
    2 * (m * A + d - actual - 1) ≤ bound := by omega

end
end ReedSolomon.HiddenDerivative.AmbientSearchMachine
