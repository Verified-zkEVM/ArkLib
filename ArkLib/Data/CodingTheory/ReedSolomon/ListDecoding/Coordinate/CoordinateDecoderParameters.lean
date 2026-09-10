/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Coordinate.CoordinateDecoderMachine
public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.QuadraticExtension.QuadraticDecoderParameters
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Prepared.PreparedDecoderParameters
/-!
# Small-gap exact execution at the prescribed capacity parameters

The existing interpolation existence theorem supplies actual success to the closed coordinate
decoder. All-rate and gap-only parameter dependence are retained. Descending ambient search
preserves the reduced larger-field condition and therefore selects the smaller center alphabet
when the paper's condition holds. Both cost bounds concern the same returned list and run.
These are primitive-work bounds, not the unfinished bit-cost refinement.

## References

* [Dao, Kominers, Thaler, and Zheng, *Reed-Solomon List Decoding up to Capacity at Every
  Rate*][DKTZ26], uniform capacity decoding and the reduced separant field-size condition.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.CoordinateDecoderMachine

open HiddenDerivative ReedSolomon QuadraticAlgebra
open SeparateSampleFieldExecution (ExactOutput)

/-- The parameter-only coordinate budget preserves the ordering of the two center regimes. -/
theorem decoderFuel_one_le_two (d m q : ℕ) (hq : 0 < q) :
    CoordinateDecoderCore.fuel d m q 1 ≤ CoordinateDecoderCore.fuel d m q 2 :=
  Nat.mul_le_mul_left _ (QuadraticDecoderMachine.decoderFuel_one_le_two d m q hq)

variable {q : ℕ} [Fact q.Prime]

/-- The prescribed small-gap integers produce an exact executed decoder at every rate.
Proof-only setup preconditions are obtained here, rather than assumed of the instance.
The two primitive-work inequalities apply to the identical observed output and cost. -/
theorem small_gap_run_exact (delta : ℝ) (hdelta : 0 < delta)
    (hquarter : delta < (1 / 4 : ℝ)) (n k A : ℕ)
    (hblock : 8 * weightedSupportMultiplicity delta ≤ n) (hk : 0 < k) (hkn : k ≤ n)
    (hA : ReedSolomon.agreementThreshold delta n k ≤ A) (hAn : A ≤ n) (hnq : n ≤ q)
    (domain : Fin n ↪ ZMod q) (received : Fin n → ZMod q) :
    let d := capacityDerivativeOrder delta
    let m := weightedSupportMultiplicity delta
    ∃ (hodd : q ≠ 2) (hL : m * A ≤ q ^ 2) (out : List (List (ZMod q))) (cost : ℕ),
      run k d m A (List.ofFn (fun i ↦ (domain i, received i))) hodd hL = (some out, cost) ∧
      ExactOutput domain received k A out ∧
      cost ≤ InterpolationDispatch.budget k d m A n + SetupMachine.budget q (m * A) +
        CoordinateDecoderCore.fuel d m q 2 + 45 * q ^ 2 + 16 * q + 168 ∧
      (2 * (m * A + d - weightedSupportAmbientDimension delta n k) ≤ q →
        cost ≤ InterpolationDispatch.budget k d m A n + SetupMachine.budget q (m * A) +
          CoordinateDecoderCore.fuel d m q 1 + 45 * q ^ 2 + 16 * q + 168) := by
  let d := capacityDerivativeOrder delta
  let m := weightedSupportMultiplicity delta
  let rows := List.ofFn (fun i ↦ (domain i, received i))
  have hd : d ≠ 0 := by
    dsimp only [d]
    rw [capacityDerivativeOrder_eq_ceil hquarter]
    exact Nat.ne_of_gt (Nat.ceil_pos.mpr (Real.exp_pos _))
  obtain ⟨found, ic, hi, _hc, hgood, hD, hchar, hweight, hL, hodd, _hic⟩ :=
    PreparedDecoderParameters.prescribed_search delta hdelta hquarter n k A
      hblock hk hkn hA hAn hnq domain received
  change AmbientSearchMachine.run k d m A rows = (some found, ic) at hi
  obtain ⟨result, ic', hi', _hbudget, hs⟩ := AmbientSearchMachine.run_complete k d m A rows
  rw [hi] at hi'
  cases hi'
  obtain ⟨hl, _hu, _hcert⟩ := hs found rfl
  have hdepth : d ≤ found.degree := by omega
  have hdim : k ≤ found.degree + 1 := by omega
  have hdispatch : (InterpolationDispatch.run k d m A rows).1 = some found := by
    simp only [InterpolationDispatch.run, if_neg hd, hi]
  obtain ⟨out, cost, hr, ho, hb⟩ := run_exact_of_interpolation k d m A domain received
    hodd hL found hdispatch hdepth hdim hD.le hnq hAn (by omega) hchar hweight
  refine ⟨hodd, hL, out, cost, hr, ho, ?_, ?_⟩
  · have hmono := decoderFuel_one_le_two d m q (Fact.out : q.Prime).pos
    dsimp only [d, m] at hb hmono ⊢
    split at hb <;> omega
  · intro hlarge
    have hK : 0 < weightedSupportAmbientDimension delta n k := by
      unfold weightedSupportAmbientDimension
      exact hk.trans_le (Nat.le_max_left _ _)
    have hactual : 2 * (m * A + d - (found.degree + 1)) ≤ q := by
      dsimp only [d, m]
      omega
    simpa only [if_pos hactual] using hb

end ReedSolomon.ListDecoding.CoordinateDecoderMachine
