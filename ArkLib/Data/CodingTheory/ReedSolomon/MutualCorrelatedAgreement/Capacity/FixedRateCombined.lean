/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity.RatePartition
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.RatePartition
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.RatePartition.Gate
/-!
# Fixed-rate list capacity and exact mutual correlated agreement

Fix the physical rate bound `R` and a positive exponent slack `epsilon`. For every sufficiently
small capacity gap `delta`, the derivative order is

`d = ceil(exp((c(R) + epsilon) / delta))`, where `c(R) = R * log(40 / (9R))`.

The finite partition parameters depend only on `R`, `delta`, and this order. The theorem chooses
these parameters before the field, block length, evaluation domain, or received words. Above an
explicit length threshold, they give a finite complete list of size `C * n^d` and an exceptional
challenge set of size `C' * n^(d+1)`. Both prefactors are displayed in the statement.

The proof first turns the asymptotic scalar gate into an actual finite partition choice. The
same choice feeds the list bound and the symbolic curve MCA bound. The latter recovers equality
of the full agreement set, not merely a lower bound on the recovered pair's agreements.

This is an eventual small-gap theorem: `epsilon > 0` and the existential `deltaZero` are part of
the guarantee. Reconstruction uses `max k (d + 1)`, so the characteristic guard is the exact
maximum of message degree, derivative order, and jet cap rather than the interpolation dimension.

For the paper's fixed-`R`, fixed-`a`, fixed-`d` row under the literal gate
`1 < ratePartitionGamma R a d`, use `exists_ratePartition_list_bound` and
`exists_ratePartition_lineMCA_parameters`. The theorem here is their derived eventual-small-gap
specialization with a positive exponent slack.

## References

* [Dao, Kominers, and Thaler, *Quantitative Reed--Solomon List Decoding and Mutual
  Correlated Agreement: From Johnson to Capacity*][DKTZ26], fixed-order and fixed-rate bounds.
-/

@[expose] public section

namespace ReedSolomon
open Polynomial HiddenDerivative
universe u

open Classical in
/-- **One fixed-rate parameter choice gives complete lists and exact line MCA.**

For each positive exponent slack, choose a positive gap cutoff. For every smaller positive gap,
choose finite interpolation parameters once, before any code or field data. The same parameters
then bound all complete lists and all received lines over every eligible field.

The first conclusion explicitly asserts complete-list finiteness, including over infinite fields.
In the second conclusion, one exceptional set works for every candidate on the received line;
the exact correlated pair may depend on the challenge and candidate polynomial.
-/
theorem exists_fixedRate_capacity_bounds {R epsilon : ℝ}
    /-

    R bounds the physical dimension ratio k/n. The positive epsilon absorbs
    the finite errors in passing from the asymptotic scalar gate to a partition.
    -/
    (hR : 0 < R)
    (hRone : R < 1)
    (hepsilon : 0 < epsilon) :
    /-

    Exponent slack gives a positive interval of gaps where the finite construction works.
    -/
    ∃ deltaZero : ℝ, 0 < deltaZero ∧
      ∀ delta : ℝ, 0 < delta → delta < deltaZero →
      /-

      c(R) = R log(40/(9R)); the order depends only on the rate and gap.
      -/
      let d := Nat.ceil (Real.exp ((RatePartition.fixedRateCoefficient R + epsilon) / delta))
      /-

      Positive finite surplus supplies p before the field and block length.
      -/
      ∃ p : RatePartitionFiniteParameters R (R + delta) d,
        ∀ (F : Type u) [Field F] (n k A : ℕ),
        ratePartitionMathematicalLength R d p.multiplicity ≤ n →
        0 < k →
        (k : ℝ) ≤ R * n →
        (R + delta) * n ≤ A →
        A ≤ n →
        /-

        Distinct evaluation points turn agreement into a count of distinct polynomial roots.
        -/
        ∀ (domain : Fin n ↪ F),
        (ringChar F = 0 ∨
          max (max (k - 1) d) (ratePartitionJetBound R p.multiplicity) < ringChar F) →
        /-

        With ν = ratePartitionJetBound R p.multiplicity, degree and incidence
        give the prefactor C = ν²(2ν/delta)^d for the complete list.
        -/
        (∀ received : Fin n → F,
          (closePolynomialSet domain received k A).Finite ∧
            ((closePolynomialSet domain received k A).ncard : ℝ) ≤
              (ratePartitionJetBound R p.multiplicity : ℝ) ^ 2 *
                (2 * ratePartitionJetBound R p.multiplicity / delta) ^ d * n ^ d) ∧
        /-

        The finite source/rank ratio determines the symbolic challenge height.
        That height and ν give the explicit MCA prefactor, independent of n.
        -/
        ∀ f g : Fin n → F, ∃ exceptional : Finset F,
          (exceptional.card : ℝ) ≤ polynomialCurveProductMCAConstant delta
            (ratePartitionJetBound R p.multiplicity)
            (ratePartitionHeight (ratePartitionJetBound R p.multiplicity)
              (ratePartitionFiniteRatio R (R + delta) d p.multiplicity)) d *
              (n : ℝ) ^ (d + 1) ∧
          /-

          Choose the exceptional set before quantifying over z and P.
          -/
          ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
            A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
            HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  -- Exponent slack makes the scalar gate hold throughout a positive gap interval.
  obtain ⟨deltaZero, hzero, hsmall⟩ :=
    RatePartition.exists_small_gap_rate_gate hR hRone hepsilon
  refine ⟨deltaZero, hzero, ?_⟩
  intro delta hdelta hdeltaZero
  dsimp only
  let d := Nat.ceil (Real.exp ((RatePartition.fixedRateCoefficient R + epsilon) / delta))
  obtain ⟨haone, hd, hgate⟩ := hsmall delta hdelta hdeltaZero
  have hRa : R < R + delta := lt_add_of_pos_right R hdelta
  -- The scalar gate gives an actual finite parameter witness, not an assumed certificate.
  obtain ⟨p⟩ := exists_ratePartitionFiniteParameters hR (hR.trans hRa)
    (show 0 < d by dsimp [d]; omega) hgate
  refine ⟨p, ?_⟩
  intro F instF n k A hn hk hkR haA hAn domain hchar
  constructor
  · intro received
    simpa only [add_sub_cancel_left] using
      ratePartition_close_list_bound p hR hRa haone hd hn hk hkR haA hAn
        domain received hchar
  · intro f g
    simpa only [add_sub_cancel_left] using
      exists_ratePartition_lineMCA p hR hRa haone hd hn hk hkR haA hAn domain f g hchar
end ReedSolomon
