/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.GeometricBound
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Output.CapacityOutputBounds
public import
ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Coordinate.CoordinateCapacityExecution
/-!
# Field-independent size of the executed capacity list

The agreement-sensitive geometric count bounds the very same coefficient vectors returned by
the coordinate decoder. No new decoder, output selection or execution is introduced. Polynomial
duplicate freedom turns the geometric finite-set bound into a bound on the physical list length.
Increasing the integer agreement threshold only decreases this list; oversized thresholds give
the empty output.

This refinement improves the list bound, not the running-time bound. The observed primitive work
still obeys its previously proved field-dependent estimate. Full bit complexity remains separate.

## References

* [Dao, Kominers, Thaler, and Zheng, *Reed-Solomon List Decoding up to Capacity at Every
  Rate*][DKTZ26], field-independent list bound and uniform capacity decoding.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.GeometricOutputBounds

open Polynomial JetHornerMachine SeparateSampleFieldExecution ReedSolomon

variable {F : Type*} [Field F] {n k A : ℕ}

open Classical in
/-- A supplied exact output satisfies the field-independent bound, including oversized integer
thresholds. Its length counts the original coefficient vectors, not a deduplicated replacement. -/
theorem exact_output_length_le (delta : ℝ) (hdelta : 0 < delta)
    (hsmall : delta < (1 / 4 : ℝ)) (hk : 0 < k)
    (hblock : 8 * weightedSupportMultiplicity delta ≤ n)
    (hA : ReedSolomon.agreementThreshold delta n k ≤ A)
    (hchar : ringChar F = 0 ∨ n ≤ ringChar F)
    (domain : Fin n ↪ F) (received : Fin n → F) (out : List (List F))
    (he : ExactOutput domain received k A out) :
    let d := capacityDerivativeOrder delta
    let m := weightedSupportMultiplicity delta
    (out.length : ℝ) ≤ 4 * (m : ℝ) ^ 2 * (4 * m / delta) ^ d * n ^ d := by
  classical
  by_cases hos : n < A
  · rw [CapacityOutputBounds.oversized_empty domain received out he hos]
    simp only [List.length_nil, Nat.cast_zero]
    positivity
  · have hAn : A ≤ n := by omega
    have hblock' : 8 * Nat.ceil
        (100 * (Nat.ceil (Real.exp ((27 / 10) / delta)) : ℝ) ^ 2 *
          harmonicNumber (Nat.ceil (Real.exp ((27 / 10) / delta)) - 1)) ≤ n := by
      simpa only [weightedSupportMultiplicity, capacityDerivativeOrder_eq_ceil hsmall]
        using hblock
    have hb := prescribed_geometric_finite_list_bound delta n k domain received
      hdelta hsmall hk hblock' (hA.trans hAn) hchar
      (out.map coefficientPolynomial).toFinset (by
        intro P hP
        have hp := (he.2.2.1 P).mp (List.mem_toFinset.mp hP)
        exact ⟨hp.1, hA.trans hp.2⟩)
    simpa only [List.toFinset_card_of_nodup he.1, List.length_map,
      weightedSupportMultiplicity, capacityDerivativeOrder_eq_ceil hsmall] using hb

open Classical in
/-- The existing coordinate decoder returns a field-independently bounded list, with its
previous same-run primitive-work bound unchanged. This does not claim an improved runtime. -/
theorem coordinate_run_list_bound {q : ℕ} [Fact q.Prime]
    (delta : ℝ) (hdelta : 0 < delta) (hsmall : delta < (1 / 4 : ℝ))
    (hblock : 8 * weightedSupportMultiplicity delta ≤ n)
    (hk : 0 < k) (hkn : k ≤ n) (hnq : n ≤ q)
    (hA : ReedSolomon.agreementThreshold delta n k ≤ A)
    (domain : Fin n ↪ ZMod q) (received : Fin n → ZMod q) :
    let d := capacityDerivativeOrder delta
    let m := weightedSupportMultiplicity delta
    ∃ out work,
      CoordinateCapacityMachine.run n k d m A
        (List.ofFn (fun i ↦ (domain i, received i))) = (some out, work) ∧
      ExactOutput domain received k A out ∧
      (out.length : ℝ) ≤ 4 * (m : ℝ) ^ 2 * (4 * m / delta) ^ d * n ^ d ∧
      work ≤ CoordinateCapacityMachine.workCoefficient d m * q ^ (2 * d + 29) ∧
      (2 * (m * A + d - weightedSupportAmbientDimension delta n k) ≤ q →
        work ≤ CoordinateCapacityMachine.workCoefficient d m * q ^ (d + 29)) := by
  obtain ⟨out, work, hr, he, hw, hlarger⟩ := CoordinateCapacityMachine.run_exact
    delta hdelta n k A (by simpa only [if_neg (not_le_of_gt hsmall)] using hblock)
    hk hkn hnq hA domain received
  refine ⟨out, work, hr, he, ?_, hw, hlarger hsmall⟩
  have hdec : ZMod.decidableEq q =
      (fun a b : ZMod q ↦ Classical.propDecidable (a = b)) := Subsingleton.elim _ _
  rw [hdec] at he
  exact exact_output_length_le delta hdelta hsmall hk hblock hA
    (Or.inr (by simpa only [ZMod.ringChar_zmod_n] using hnq)) domain received out he

end ReedSolomon.ListDecoding.GeometricOutputBounds
