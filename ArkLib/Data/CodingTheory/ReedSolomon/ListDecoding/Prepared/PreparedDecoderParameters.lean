/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Prepared.PreparedDecoderProof
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.WeightedSupport
/-!
# Small-gap parameters for the actual returned interpolant

The certified support bounds every jet exponent strictly below twice the prescribed
multiplicity. Search bounds the actual ambient degree by the block length. These facts give
the characteristic contract at every prime field size at least the original block length.
The integer sample count `m*A` fits the quadratic extension under the original `8*m ≤ n` bound.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.PreparedDecoderParameters

open PolynomialDifferential
open HiddenDerivative ReedSolomon

variable {F : Type*} [Field F] [DecidableEq F]

omit [DecidableEq F] in
/-- Certified support bounds each jet degree of the actual returned source polynomial. -/
theorem certified_jetDegree_lt {D d m A : ℕ} (rows : List (F × F))
    (out : NonzeroInterpolationMachine.Output F)
    (hc : NonzeroInterpolationMachine.Certified (d := d) D m A rows out) (j : Fin (d + 1)) :
    jetDegree (NonzeroInterpolationMachine.sourceOutput (d := d) D m A out) j < 2 * m := by
  let Q := NonzeroInterpolationMachine.sourceOutput (d := d) D m A out
  have hQ : Q ≠ 0 := by
    intro hz
    have hrep := hc.2.2.2.2.2.2.1
    rw [show NonzeroInterpolationMachine.sourceOutput (d := d) D m A out = 0 from hz,
      map_zero] at hrep
    exact hc.2.2.2.2.2.2.2.1 hrep
  obtain ⟨e, he⟩ := MvPolynomial.support_nonempty.mpr hQ
  have helig := hc.2.2.2.2.2.2.2.2.1
  have hp : 0 < 2 * m := Nat.zero_lt_of_lt
    (NonzeroInterpolationMachine.eligible_support_caps D m A Q helig e he).1
  rw [jetDegree, MvPolynomial.degreeOf_lt_iff hp]
  intro u hu
  exact (Finsupp.le_degree j u.some).trans_lt
    (NonzeroInterpolationMachine.eligible_support_caps D m A Q helig u hu).1

omit [DecidableEq F] in
/-- A successful attempt at strict cutoff `J` has every jet degree below `J`. -/
theorem certifiedWithBudget_jetDegree_lt {D d m J A : ℕ} (rows : List (F × F))
    (out : NonzeroInterpolationMachine.Output F)
    (hc : NonzeroInterpolationMachine.CertifiedWithBudget (d := d) D m J A rows out)
    (j : Fin (d + 1)) :
    jetDegree (NonzeroInterpolationMachine.sourceOutputWithBudget (d := d) D m J A out) j < J := by
  let Q := NonzeroInterpolationMachine.sourceOutputWithBudget (d := d) D m J A out
  have hQ : Q ≠ 0 := by
    intro hz
    have hrep := hc.2.2.2.2.2.2.1
    rw [show NonzeroInterpolationMachine.sourceOutputWithBudget (d := d) D m J A out = 0
      from hz, map_zero] at hrep
    exact hc.2.2.2.2.2.2.2.1 hrep
  obtain ⟨e, he⟩ := MvPolynomial.support_nonempty.mpr hQ
  have helig := hc.2.2.2.2.2.2.2.2.1
  have hp : 0 < J := Nat.zero_lt_of_lt
    (NonzeroInterpolationMachine.eligibleWithBudget_support_caps D m J A Q helig e he).1
  rw [jetDegree, MvPolynomial.degreeOf_lt_iff hp]
  intro u hu
  exact (Finsupp.le_degree j u.some).trans_lt
    (NonzeroInterpolationMachine.eligibleWithBudget_support_caps D m J A Q helig u hu).1

/-- Full residual sampling fits the quadratic field with the original small-gap block bound. -/
theorem sample_count_le_square {m A n q : ℕ} (hblock : 8 * m ≤ n) (hA : A ≤ n)
    (hnq : n ≤ q) : m * A ≤ q ^ 2 := by
  have hm : m ≤ q := by omega
  have hAq : A ≤ q := hA.trans hnq
  simpa only [pow_two] using Nat.mul_le_mul hm hAq

/-- Positive small-gap multiplicity and the original block bound exclude characteristic two. -/
theorem field_ne_two {m n q : ℕ} (hm : 0 < m) (hblock : 8 * m ≤ n) (hnq : n ≤ q) :
    q ≠ 2 := by omega

/-- Characteristic and full residual-degree contracts hold for the actual certified output. -/
theorem certified_contracts {q D d m A n : ℕ} [Fact q.Prime]
    (rows : List (ZMod q × ZMod q)) (out : NonzeroInterpolationMachine.Output (ZMod q))
    (hc : NonzeroInterpolationMachine.Certified (d := d) D m A rows out)
    (hD : D < n) (hblock : 8 * m ≤ n) (hnq : n ≤ q) :
    IsBelowCharacteristic D
        (NonzeroInterpolationMachine.sourceOutput (d := d) D m A out) ∧
      differentialWeightedDegree D
        (NonzeroInterpolationMachine.sourceOutput (d := d) D m A out) < m * A := by
  refine ⟨⟨?_, ?_⟩, hc.2.2.2.2.2.2.2.2.2.1⟩
  · simpa only [ZMod.ringChar_zmod_n] using hD.trans_le hnq
  · intro j
    have hj := certified_jetDegree_lt rows out hc j
    have hmq : 2 * m ≤ q := by omega
    simpa only [ZMod.ringChar_zmod_n] using hj.trans_le hmq

/-- Characteristic and residual-degree contracts for an independently budgeted output. -/
theorem certifiedWithBudget_contracts {q D d m J A : ℕ} [Fact q.Prime]
    (rows : List (ZMod q × ZMod q)) (out : NonzeroInterpolationMachine.Output (ZMod q))
    (hc : NonzeroInterpolationMachine.CertifiedWithBudget (d := d) D m J A rows out)
    (hD : D < q) (hJ : J ≤ q) :
    IsBelowCharacteristic D
        (NonzeroInterpolationMachine.sourceOutputWithBudget (d := d) D m J A out) ∧
      differentialWeightedDegree D
        (NonzeroInterpolationMachine.sourceOutputWithBudget (d := d) D m J A out) < m * A := by
  refine ⟨⟨?_, ?_⟩, hc.2.2.2.2.2.2.2.2.2.1⟩
  · simpa only [ZMod.ringChar_zmod_n] using hD
  · intro j
    have hj := certifiedWithBudget_jetDegree_lt rows out hc j
    simpa only [ZMod.ringChar_zmod_n] using hj.trans_le hJ

/-- Prescribed small-gap search certifies its actual output with all root parameter contracts.
The real gap chooses proof-side integers only; the displayed search still runs integer inputs. -/
theorem prescribed_search {q : ℕ} [Fact q.Prime] (delta : ℝ) (hdelta : 0 < delta)
    (hquarter : delta < (1 / 4 : ℝ)) (n k A : ℕ)
    (hblock : 8 * weightedSupportMultiplicity delta ≤ n) (hk : 0 < k) (hkn : k ≤ n)
    (hA : ReedSolomon.agreementThreshold delta n k ≤ A) (hAn : A ≤ n) (hnq : n ≤ q)
    (domain : Fin n ↪ ZMod q) (received : Fin n → ZMod q) :
    let d := capacityDerivativeOrder delta
    let m := weightedSupportMultiplicity delta
    let rows := List.ofFn (fun i ↦ (domain i, received i))
    ∃ found c, AmbientSearchMachine.run k d m A rows = (some found, c) ∧
      NonzeroInterpolationMachine.Certified (d := d) found.degree m A rows found.interpolant ∧
      weightedSupportAmbientDimension delta n k - 1 ≤ found.degree ∧ found.degree < n ∧
      IsBelowCharacteristic found.degree
        (NonzeroInterpolationMachine.sourceOutput (d := d) found.degree m A found.interpolant) ∧
      differentialWeightedDegree found.degree
        (NonzeroInterpolationMachine.sourceOutput (d := d) found.degree m A found.interpolant) <
          m * A ∧ m * A ≤ q ^ 2 ∧ q ≠ 2 ∧
      c ≤ AmbientSearchMachine.budget k d m A n := by
  obtain ⟨found, c, hr, hl, hu, hc, hcost⟩ :=
    AmbientSearchMachine.run_prescribed_weightedSupport delta hdelta hquarter n k A hblock hk hkn
      hA hAn hnq domain received
  obtain ⟨hchar, hweight⟩ := certified_contracts _ found.interpolant hc hu hblock hnq
  exact ⟨found, c, hr, hc, hl, hu, hchar, hweight, sample_count_le_square hblock hAn hnq,
    field_ne_two (weightedSupportMultiplicity_pos hdelta hquarter) hblock hnq, hcost⟩

end ReedSolomon.ListDecoding.PreparedDecoderParameters
