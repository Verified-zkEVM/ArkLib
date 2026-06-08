/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.GrandChallengeCollapse
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallengeLDThresholdElias
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallengeLattice
import ArkLib.Data.CodingTheory.InterleavedCode
import ArkLib.Data.CodingTheory.ProximityGap.MCABadCount
import ArkLib.Data.CodingTheory.ProximityGap.MCABadCountRatio
import ArkLib.Data.CodingTheory.ProximityGap.MCAEndpointLower
import ArkLib.Data.CodingTheory.ProximityGap.MCASecondMoment
import ArkLib.Data.CodingTheory.ProximityGap.SubsetSumErdosHeilbronn
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallengesLattice.PrizeResolution

/-!
# GrandChallengesLattice — FourRate

Concrete four-rate MCA prize brackets from numeric certificates.

Split from `GrandChallengesLattice.lean` for longFile hygiene (#110).
-/

set_option linter.style.longFile 1500

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false


namespace ProximityGap

open scoped NNReal ProbabilityTheory BigOperators
open Code

namespace GrandChallengesLattice

/-! ## Concrete four-rate MCA prize brackets from named numeric certificates

The combinators above (`mcaPrizeLattice_bracketed_of_witnesses`,
`mcaPrizeLatticeResolved_of_adjacent_witnesses`) take *abstract* per-rate witness families.
The two theorems below are the MCA-side analogue of
`listPrizeLatticeResolved_of_johnson_sq_and_elias_next`: they assemble the four-rate prize
bracket directly from the named BCHKS25 Johnson-range lower certificate and the CS25
complete-CA-breakdown upper certificate, with the exact per-rate side conditions isolated as
hypotheses indexed by the prize rate `j : Fin 4` (each at degree
`k_j := ⌊prizeRates j · n⌋`). This closes the asymmetry flagged in issue #57: the LD side
had a concrete per-rate certificate assembler, the MCA side only had the abstract combinators.
-/

/-- **Four-rate faithful MCA lattice bracket from Johnson(BCHKS25) ⊕ CA-breakdown(CS25).**
For every ABF26 prize rate `j`, the BCHKS25 Johnson-range MCA lower bound at radius `δ_lo j`
and the CS25 complete-CA-breakdown upper bound at radius `δ_hi j` bracket the faithful MCA
lattice threshold of the rate-`j` Reed-Solomon code between the lattice indices `⌊δ_lo j·n⌋`
and `⌊δ_hi j·n⌋`. This is the concrete per-rate instantiation requested in issue #57: the
remaining content is exactly the per-rate Johnson/CS25 numeric inequalities. -/
theorem mcaPrizeLattice_bracketed_ofJohnsonBCHKS25_and_RSBreakdownCS25
    (domain : ι ↪ F)
    (η δ_lo δ_hi : Fin 4 → ℝ≥0)
    (hη : ∀ j : Fin 4, 0 < η j)
    (hδ_johnson : ∀ j : Fin 4,
        (δ_lo j : ℝ) <
          1 - (((⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : ℝ) / Fintype.card ι
              + 1 / Fintype.card ι) ^ ((1 : ℝ) / 2)) - (η j : ℝ))
    (hδlo_le_one : ∀ j : Fin 4, δ_lo j ≤ 1)
    (hBCHKS25 : ∀ j : Fin 4,
      CodingTheory.rs_epsMCA_johnson_range_bchks25 domain
        ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ (η j) (δ_lo j) (hη j) (hδ_johnson j))
    (hle : ∀ j : Fin 4,
        ENNReal.ofReal
            (let n : ℝ := Fintype.card ι
             let ρ_plus : ℝ := (⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : ℝ) / n + 1 / n
             let m : ℝ := max ⌈(ρ_plus ^ ((1 : ℝ) / 2)) / (2 * η j)⌉ 3
             ((2 * (m + 1 / 2) ^ 5 + 3 * (m + 1 / 2) * δ_lo j * ρ_plus) /
                    (3 * ρ_plus ^ ((3 : ℝ) / 2)) *
                  n +
                (m + 1 / 2) / ρ_plus ^ ((1 : ℝ) / 2)) /
               (Fintype.card F : ℝ)) ≤
          (epsStar : ENNReal))
    (hδhi : ∀ j : Fin 4, δ_hi j ≤ 1)
    (hq_ge : ∀ _ : Fin 4, 10 ≤ Fintype.card F)
    (hδ_cs_lo : ∀ j : Fin 4,
        1 - CodingTheory.qEntropy (Fintype.card F) (δ_hi j : ℝ) + 2 / (Fintype.card ι : ℝ)
            + ((CodingTheory.qEntropy (Fintype.card F) (δ_hi j : ℝ) - (δ_hi j : ℝ))
                / (Fintype.card ι : ℝ)) ^ ((1 : ℝ) / 2)
          ≤ (⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : ℝ) / Fintype.card ι)
    (hδ_cs_hi : ∀ j : Fin 4,
        (⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : ℝ) / Fintype.card ι
          ≤ 1 - (δ_hi j : ℝ) - 2 / (Fintype.card ι : ℝ))
    (hCS25 : ∀ j : Fin 4,
      CodingTheory.rs_epsCA_breakdown_cs25 domain
        ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ (δ_hi j)
        (hq_ge j) (hδ_cs_lo j) (hδ_cs_hi j))
    (hε : ∀ _ : Fin 4, (epsStar : ENNReal) < 1) :
    ∀ j : Fin 4,
      let hne := mcaThresholdExists_ofJohnsonBCHKS25 domain
        ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ (η j) (δ_lo j) epsStar
        (hη j) (hδ_johnson j) (hδlo_le_one j) (hBCHKS25 j) (hle j)
      latticeIndexOf (ι := ι) (δ_lo j) (hδlo_le_one j) ≤
          mcaThreshold (ReedSolomon.code domain
            ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F)) epsStar hne ∧
        mcaThreshold (ReedSolomon.code domain
            ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F)) epsStar hne <
          latticeIndexOf (ι := ι) (δ_hi j) (hδhi j) := fun j =>
  mcaThresholdLattice_bracketed_ofJohnsonBCHKS25_and_RSBreakdownCS25
    domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ (η j) (δ_lo j) (δ_hi j) epsStar
    (hη j) (hδ_johnson j) (hδlo_le_one j) (hBCHKS25 j) (hle j)
    (hδhi j) (hq_ge j) (hδ_cs_lo j) (hδ_cs_hi j) (hCS25 j) (hε j)

/-- **Four-rate faithful MCA prize resolution from adjacent Johnson(BCHKS25)/CS25
certificates.** If at every prize rate the CS25 upper lattice index `⌊δ_hi j·n⌋` is exactly
one above the BCHKS25 lower lattice index `⌊δ_lo j·n⌋`, the bracket pins the faithful MCA
lattice threshold to the lower index at each rate, *resolving* the four-rate faithful MCA
prize predicate `mcaPrizeLatticeResolved`. This is the MCA counterpart of
`listPrizeLatticeResolved_of_johnson_sq_and_elias_next`. -/
theorem mcaPrizeLatticeResolved_ofJohnsonBCHKS25_and_RSBreakdownCS25_adjacent
    (domain : ι ↪ F)
    (η δ_lo δ_hi : Fin 4 → ℝ≥0)
    (hη : ∀ j : Fin 4, 0 < η j)
    (hδ_johnson : ∀ j : Fin 4,
        (δ_lo j : ℝ) <
          1 - (((⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : ℝ) / Fintype.card ι
              + 1 / Fintype.card ι) ^ ((1 : ℝ) / 2)) - (η j : ℝ))
    (hδlo_le_one : ∀ j : Fin 4, δ_lo j ≤ 1)
    (hBCHKS25 : ∀ j : Fin 4,
      CodingTheory.rs_epsMCA_johnson_range_bchks25 domain
        ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ (η j) (δ_lo j) (hη j) (hδ_johnson j))
    (hle : ∀ j : Fin 4,
        ENNReal.ofReal
            (let n : ℝ := Fintype.card ι
             let ρ_plus : ℝ := (⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : ℝ) / n + 1 / n
             let m : ℝ := max ⌈(ρ_plus ^ ((1 : ℝ) / 2)) / (2 * η j)⌉ 3
             ((2 * (m + 1 / 2) ^ 5 + 3 * (m + 1 / 2) * δ_lo j * ρ_plus) /
                    (3 * ρ_plus ^ ((3 : ℝ) / 2)) *
                  n +
                (m + 1 / 2) / ρ_plus ^ ((1 : ℝ) / 2)) /
               (Fintype.card F : ℝ)) ≤
          (epsStar : ENNReal))
    (hδhi : ∀ j : Fin 4, δ_hi j ≤ 1)
    (hq_ge : ∀ _ : Fin 4, 10 ≤ Fintype.card F)
    (hδ_cs_lo : ∀ j : Fin 4,
        1 - CodingTheory.qEntropy (Fintype.card F) (δ_hi j : ℝ) + 2 / (Fintype.card ι : ℝ)
            + ((CodingTheory.qEntropy (Fintype.card F) (δ_hi j : ℝ) - (δ_hi j : ℝ))
                / (Fintype.card ι : ℝ)) ^ ((1 : ℝ) / 2)
          ≤ (⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : ℝ) / Fintype.card ι)
    (hδ_cs_hi : ∀ j : Fin 4,
        (⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : ℝ) / Fintype.card ι
          ≤ 1 - (δ_hi j : ℝ) - 2 / (Fintype.card ι : ℝ))
    (hCS25 : ∀ j : Fin 4,
      CodingTheory.rs_epsCA_breakdown_cs25 domain
        ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ (δ_hi j)
        (hq_ge j) (hδ_cs_lo j) (hδ_cs_hi j))
    (hε : ∀ _ : Fin 4, (epsStar : ENNReal) < 1)
    (hadj : ∀ j : Fin 4,
      (latticeIndexOf (ι := ι) (δ_hi j) (hδhi j)).val =
        (latticeIndexOf (ι := ι) (δ_lo j) (hδlo_le_one j)).val + 1) :
    mcaPrizeLatticeResolved domain
      (fun j => latticeIndexOf (ι := ι) (δ_lo j) (hδlo_le_one j)) :=
  mcaPrizeLatticeResolved_of_adjacent_witnesses domain
    (fun j => GrandChallenges.MCALowerWitness.ofJohnsonBCHKS25 domain
      ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ (η j) (δ_lo j) epsStar
      (hη j) (hδ_johnson j) (hδlo_le_one j) (hBCHKS25 j) (hle j))
    (fun j => GrandChallenges.MCAUpperWitness.ofRSBreakdownCS25 domain
      ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ (δ_hi j) epsStar
      (hq_ge j) (hδ_cs_lo j) (hδ_cs_hi j) (hCS25 j) (hε j))
    (fun j => hδhi j)
    (fun j => hadj j)


end GrandChallengesLattice

end ProximityGap

