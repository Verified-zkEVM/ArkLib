/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.CapacityDecoderExecution
public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.Interpolation.Search.Proofs
/-!
# Executed exact output from an independently budgeted interpolation candidate

A concrete nonzero candidate proves that the existing search succeeds. The actual returned
interpolant, reconstruction, filtering, duplicate removal, and physical coefficient list then
satisfy the existing exact-output contract with the displayed primitive-work bound.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.CapacityDecoderMachine

open HiddenDerivative ReedSolomon PolynomialDifferential
open SeparateSampleFieldExecution (ExactOutput)

/-- An explicit budget-eligible candidate makes the integer decoder return its exact list. -/
theorem runWithBudget_exact_of_candidate {q n k d m J A D : ℕ} [Fact q.Prime]
    (domain : Fin n ↪ ZMod q) (received : Fin n → ZMod q)
    (hd : 0 < d) (hn : 3 ≤ n) (hA : A ≤ n) (hnq : n ≤ q)
    (hL : m * A ≤ q ^ 2) (hJ : J ≤ q) (hDlow : max (k - 1) d ≤ D) (hDhigh : D < n)
    (Q : DifferentialPolynomial (ZMod q) d) (hQ : Q ≠ 0)
    (he : NonzeroInterpolationMachine.EligibleWithBudget D m J A Q)
    (hlocal : ∀ row ∈ List.ofFn (fun i ↦ (domain i, received i)),
      localConstraintAt m row.1 row.2 Q = 0) :
    ∃ (out : List (List (ZMod q))) (cost : ℕ)
      (found : AmbientSearchMachine.Output (ZMod q)),
      runWithBudget n k d m J A (List.ofFn (fun i ↦ (domain i, received i))) =
        (some out, cost) ∧ ExactOutput domain received k A out ∧
      cost ≤ InterpolationDispatch.budgetWithBudget k d m J A n +
        QuadraticAlgebra.SetupMachine.budget q (m * A) +
        QuadraticDecoderMachine.decoderFuelWithBudget d m J q
          (if 2 * (m * A + d - (found.degree + 1)) ≤ q then 1 else 2) +
        16 * q + 152 := by
  let rows := List.ofFn (fun i ↦ (domain i, received i))
  obtain ⟨found, c, hr, hgood, hupper, hcert, hcost⟩ :=
    AmbientSearchMachine.runWithBudget_success_of_witness k d m J A D rows hDlow
      (by simpa only [rows, List.length_ofFn] using hDhigh) Q hQ he hlocal
  have hi : (InterpolationDispatch.runWithBudget k d m J A rows).1 = some found := by
    simp only [InterpolationDispatch.runWithBudget, if_neg (by omega : d ≠ 0), hr]
  have hupper' : found.degree < n := by simpa only [rows, List.length_ofFn] using hupper
  obtain ⟨hchar, hweight⟩ := PreparedDecoderParameters.certifiedWithBudget_contracts
    rows found.interpolant hcert (hupper'.trans_le hnq) hJ
  obtain ⟨out, cost, hout, hexact, hbound⟩ := runWithBudget_exact_of_interpolation
    domain received hd hA hn hnq (by omega : q ≠ 2) hL found hi
    (by omega) (by omega) hupper'.le hchar hweight
  exact ⟨out, cost, found, hout, hexact, hbound⟩

end ReedSolomon.ListDecoding.CapacityDecoderMachine
