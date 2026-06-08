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
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallengesLattice.MCAThreshold

/-!
# GrandChallengesLattice — WitnessBridge

Bridging witness framework to MCA lattice threshold.

Split from `GrandChallengesLattice.lean` for longFile hygiene (#110).
-/

set_option linter.style.longFile 2000

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false


namespace ProximityGap

open scoped NNReal ProbabilityTheory BigOperators
open Code

namespace GrandChallengesLattice

/-! ## Bridging the witness framework to the MCA lattice threshold

A `MCALowerWitness` (a real radius `δ ≤ 1` with `ε_mca(C, δ) ≤ ε*`) lands, via the step
structure `epsMCA_eq_of_floor_eq`, on the lattice point `⌊δ·n⌋`, certifying a *lower* bound
on `mcaThreshold`. A `MCAUpperWitness` lands on `⌊δ·n⌋` and certifies an *upper* bound. These
mirror `MCALowerWitness.le_δStar` / `MCAUpperWitness.δStar_le` on the lattice. -/

open GrandChallenges

/-- The lattice index `⌊δ·n⌋` carried by a real radius `δ ≤ 1`, as a `Fin (n+1)`. -/
noncomputable def latticeIndexOf (δ : ℝ≥0) (hδ : δ ≤ 1) : Fin (Fintype.card ι + 1) :=
  ⟨Nat.floor (δ * (Fintype.card ι : ℝ≥0)),
    Nat.lt_succ_of_le (by
      have hle : δ * (Fintype.card ι : ℝ≥0) ≤ (Fintype.card ι : ℝ≥0) := by
        calc δ * (Fintype.card ι : ℝ≥0)
            ≤ 1 * (Fintype.card ι : ℝ≥0) := by gcongr
          _ = (Fintype.card ι : ℝ≥0) := one_mul _
      calc Nat.floor (δ * (Fintype.card ι : ℝ≥0))
          ≤ Nat.floor ((Fintype.card ι : ℝ≥0)) := Nat.floor_le_floor hle
        _ = Fintype.card ι := Nat.floor_natCast _)⟩

@[simp] theorem latticeIndexOf_val (δ : ℝ≥0) (hδ : δ ≤ 1) :
    (latticeIndexOf (ι := ι) δ hδ).val = Nat.floor (δ * (Fintype.card ι : ℝ≥0)) := rfl

/-- Rounding a lattice point back to an index recovers that index. -/
@[simp] theorem latticeIndexOf_mcaLatticePoint (j : Fin (Fintype.card ι + 1)) :
    latticeIndexOf (ι := ι) (mcaLatticePoint (Fintype.card ι) j)
      (mcaLatticePoint_le_one (Fintype.card ι) j) = j := by
  ext
  rw [latticeIndexOf_val, floor_mcaLatticePoint _ Fintype.card_pos]

/-- A uniform per-stack bad-scalar count bound gives an `ε_mca` upper bound.

This is the faithful-lattice-facing form of the finite bad-`γ` counting strategy: to prove a
radius is MCA-good, it is enough to show every word stack has at most `B` bad scalars. -/
theorem epsMCA_le_of_forall_mcaBadCount_le
    (C : Set (ι → F)) (δ : ℝ≥0) {B : ENNReal}
    (hcard : ∀ u : WordStack F (Fin 2) ι,
      (mcaBadCount (F := F) C δ (u 0) (u 1) : ENNReal) ≤ B) :
    epsMCA (F := F) (A := F) C δ ≤
      B / (Fintype.card F : ENNReal) := by
  classical
  rw [epsMCA_eq_iSup_mcaBadCount]
  exact ENNReal.div_le_div_right (iSup_le fun u => hcard u) _

/-- A uniform bad-scalar count bound packaged directly as an MCA lower witness. -/
def MCALowerWitness.ofBadCountLe
    (C : Set (ι → F)) {δ ε_star : ℝ≥0} {B : ENNReal}
    (hδ : δ ≤ 1)
    (hcard : ∀ u : WordStack F (Fin 2) ι,
      (mcaBadCount (F := F) C δ (u 0) (u 1) : ENNReal) ≤ B)
    (hB : B / (Fintype.card F : ENNReal) ≤ (ε_star : ENNReal)) :
    MCALowerWitness C ε_star :=
  MCALowerWitness.ofLe hδ
    (le_trans (epsMCA_le_of_forall_mcaBadCount_le C δ hcard) hB)

/-- Radius-`1/n` bad-count upper bounds, such as the J1 algebraic theorem, packaged as an
MCA lower witness.  The only remaining inputs are the uniform bad-scalar count bound and the
normalisation inequality `B / |F| ≤ ε*`. -/
noncomputable def MCALowerWitness.ofBadCountLe_j1
    (C : Set (ι → F)) {ε_star : ℝ≥0} {B : ENNReal}
    (hcard : ∀ u : WordStack F (Fin 2) ι,
      let j1 : Fin (Fintype.card ι + 1) := ⟨1, by
        have hn : 0 < Fintype.card ι := Fintype.card_pos
        omega⟩
      (mcaBadCount (F := F) C (mcaLatticePoint (Fintype.card ι) j1)
        (u 0) (u 1) : ENNReal) ≤ B)
    (hB : B / (Fintype.card F : ENNReal) ≤ (ε_star : ENNReal)) :
    MCALowerWitness C ε_star := by
  let j1 : Fin (Fintype.card ι + 1) := ⟨1, by
    have hn : 0 < Fintype.card ι := Fintype.card_pos
    omega⟩
  exact MCALowerWitness.ofBadCountLe C
    (mcaLatticePoint_le_one (Fintype.card ι) j1)
    (by simpa [j1] using hcard) hB

/-- `ε_mca` at a real radius equals `ε_mca` at its lattice point `⌊δ·n⌋/n` (step structure):
the radius enters only through `⌊δ·n⌋`. -/
theorem epsMCA_eq_at_latticeIndex (C : Set (ι → F)) (δ : ℝ≥0) (hδ : δ ≤ 1) :
    epsMCA (F := F) (A := F) C δ =
      epsMCA (F := F) (A := F) C
        (mcaLatticePoint (Fintype.card ι) (latticeIndexOf (ι := ι) δ hδ)) := by
  have hn : 0 < Fintype.card ι := Fintype.card_pos
  refine epsMCA_eq_of_floor_eq (F := F) C ?_
  rw [floor_mcaLatticePoint _ hn, latticeIndexOf_val]

/-- **Lower bracket.** An `MCALowerWitness` forces its lattice index `⌊δ·n⌋ ≤ mcaThreshold`:
the certified real radius rounds down to a satisfying lattice point. -/
theorem MCALowerWitness_le_mcaThreshold (C : Set (ι → F)) (ε_star : ℝ≥0)
    (hne : mcaThresholdExists C ε_star) (w : MCALowerWitness C ε_star) :
    latticeIndexOf (ι := ι) w.δ w.le_one ≤ mcaThreshold C ε_star hne := by
  refine le_mcaThreshold C ε_star hne ?_
  unfold mcaSatisfies
  rw [← epsMCA_eq_at_latticeIndex C w.δ w.le_one]
  exact w.bound

/-- A lower MCA witness is already enough to make the faithful lattice threshold exist:
round the certified real radius down to its Hamming lattice point. -/
theorem mcaThresholdExists_of_MCALowerWitness (C : Set (ι → F)) (ε_star : ℝ≥0)
    (w : MCALowerWitness C ε_star) :
    mcaThresholdExists C ε_star :=
  ⟨latticeIndexOf (ι := ι) w.δ w.le_one, by
    unfold mcaSatisfies
    rw [← epsMCA_eq_at_latticeIndex C w.δ w.le_one]
    exact w.bound⟩

/-- Radius-`1/n` bad-count upper bounds directly give the faithful MCA threshold lower
bracket `1 ≤ δ*_C`.  This is the Lean-facing endpoint needed by the J1 route before pairing
with an adjacent upper witness. -/
theorem one_le_mcaThreshold_of_badCountLe_j1
    (C : Set (ι → F)) {ε_star : ℝ≥0} {B : ENNReal}
    (hcard : ∀ u : WordStack F (Fin 2) ι,
      let j1 : Fin (Fintype.card ι + 1) := ⟨1, by
        have hn : 0 < Fintype.card ι := Fintype.card_pos
        omega⟩
      (mcaBadCount (F := F) C (mcaLatticePoint (Fintype.card ι) j1)
        (u 0) (u 1) : ENNReal) ≤ B)
    (hB : B / (Fintype.card F : ENNReal) ≤ (ε_star : ENNReal)) :
    let j1 : Fin (Fintype.card ι + 1) := ⟨1, by
      have hn : 0 < Fintype.card ι := Fintype.card_pos
      omega⟩
    let w : MCALowerWitness C ε_star := MCALowerWitness.ofBadCountLe_j1 C hcard hB
    let hne := mcaThresholdExists_of_MCALowerWitness C ε_star w
    j1 ≤ mcaThreshold C ε_star hne := by
  let j1 : Fin (Fintype.card ι + 1) := ⟨1, by
    have hn : 0 < Fintype.card ι := Fintype.card_pos
    omega⟩
  let w : MCALowerWitness C ε_star := MCALowerWitness.ofBadCountLe_j1 C hcard hB
  let hne := mcaThresholdExists_of_MCALowerWitness C ε_star w
  have hle := MCALowerWitness_le_mcaThreshold C ε_star hne w
  have hidx :
      latticeIndexOf (ι := ι) w.δ w.le_one = j1 := by
    simp [w, MCALowerWitness.ofBadCountLe_j1, MCALowerWitness.ofBadCountLe,
      MCALowerWitness.ofLe, latticeIndexOf_mcaLatticePoint, j1]
  simpa [hidx] using hle

/-- The faithful MCA threshold obtained from a lower witness satisfies the MCA bound. -/
theorem mcaThreshold_spec_of_MCALowerWitness (C : Set (ι → F)) (ε_star : ℝ≥0)
    (w : MCALowerWitness C ε_star) :
    let hne := mcaThresholdExists_of_MCALowerWitness C ε_star w
    mcaSatisfies C ε_star (mcaThreshold C ε_star hne) :=
  mcaThreshold_spec C ε_star (mcaThresholdExists_of_MCALowerWitness C ε_star w)

/-- A repaired line-decoding target that yields an MCA lower witness also makes the faithful
MCA lattice threshold exist. -/
theorem mcaThresholdExists_ofLineDecodingTarget
    (C : ModuleCode ι F F) (δ a ε_star : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hLD : CodingTheory.LineDecodable (F := F) (A := F) (C : Set (ι → F)) δ a
      ((Fintype.card ι : ℝ≥0) + 1))
    (hTarget : CodingTheory.lineDecodable_imp_epsMCA_le_target (F := F) (A := F)
      C δ a hLD)
    (hle : (a : ENNReal) / (Fintype.card F : ENNReal) ≤ (ε_star : ENNReal)) :
    mcaThresholdExists (C : Set (ι → F)) ε_star :=
  mcaThresholdExists_of_MCALowerWitness (C : Set (ι → F)) ε_star
    (MCALowerWitness.ofLineDecodingTarget C δ a ε_star hδ_le_one hLD hTarget hle)

/-- The faithful MCA threshold created from a repaired line-decoding target satisfies the MCA
bound. -/
theorem mcaThreshold_spec_ofLineDecodingTarget
    (C : ModuleCode ι F F) (δ a ε_star : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hLD : CodingTheory.LineDecodable (F := F) (A := F) (C : Set (ι → F)) δ a
      ((Fintype.card ι : ℝ≥0) + 1))
    (hTarget : CodingTheory.lineDecodable_imp_epsMCA_le_target (F := F) (A := F)
      C δ a hLD)
    (hle : (a : ENNReal) / (Fintype.card F : ENNReal) ≤ (ε_star : ENNReal)) :
    let hne := mcaThresholdExists_ofLineDecodingTarget C δ a ε_star hδ_le_one hLD hTarget hle
    mcaSatisfies (C : Set (ι → F)) ε_star
      (mcaThreshold (C : Set (ι → F)) ε_star hne) :=
  mcaThreshold_spec (C : Set (ι → F)) ε_star
    (mcaThresholdExists_ofLineDecodingTarget C δ a ε_star hδ_le_one hLD hTarget hle)

/-- A repaired line-decoding target gives a direct lower bracket on the faithful MCA lattice
threshold at `⌊δ·n⌋`. -/
theorem latticeIndexOf_le_mcaThreshold_ofLineDecodingTarget
    (C : ModuleCode ι F F) (δ a ε_star : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hLD : CodingTheory.LineDecodable (F := F) (A := F) (C : Set (ι → F)) δ a
      ((Fintype.card ι : ℝ≥0) + 1))
    (hTarget : CodingTheory.lineDecodable_imp_epsMCA_le_target (F := F) (A := F)
      C δ a hLD)
    (hle : (a : ENNReal) / (Fintype.card F : ENNReal) ≤ (ε_star : ENNReal)) :
    latticeIndexOf (ι := ι) δ hδ_le_one ≤
      mcaThreshold (C : Set (ι → F)) ε_star
        (mcaThresholdExists_ofLineDecodingTarget C δ a ε_star hδ_le_one hLD hTarget hle) := by
  simpa [mcaThresholdExists_ofLineDecodingTarget, MCALowerWitness.ofLineDecodingTarget]
    using MCALowerWitness_le_mcaThreshold (C : Set (ι → F)) ε_star
      (mcaThresholdExists_ofLineDecodingTarget C δ a ε_star hδ_le_one hLD hTarget hle)
      (MCALowerWitness.ofLineDecodingTarget C δ a ε_star hδ_le_one hLD hTarget hle)

set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.latticeIndexOf_le_mcaThreshold_ofLineDecodingTarget

/-- The GKL24 1.5-Johnson MCA lower bound makes the faithful MCA lattice threshold exist
whenever its explicit right-hand side is below the target `ε_star`. -/
theorem mcaThresholdExists_ofLinearOnePointFiveJohnsonGKL24
    (C : ModuleCode ι F F) (δ_min η δ ε_star : ℝ≥0)
    (h_δ_min : (δ_min : ℝ) = (Code.minDist (C : Set (ι → F)) : ℝ) / Fintype.card ι)
    (hη : 0 < η) (hη_lt_δ_min : η < δ_min)
    (hδ_johnson :
      (δ : ℝ) ≤ 1 - ((1 - (δ_min : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / 3)))
    (hδ_le_one : δ ≤ 1)
    (hGKL24 : CodingTheory.linear_epsMCA_1_5_johnson_gkl24 C δ_min η δ
      h_δ_min hη hη_lt_δ_min hδ_johnson)
    (hle :
      ENNReal.ofReal
        ((((Fintype.card ι : ℝ) + 6) / η
          + 2 / ((η : ℝ) *
              ((1 - (δ_min : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / 3)
                - (1 - (δ_min : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / 2)))
         ) / (Fintype.card F : ℝ)) ≤ (ε_star : ENNReal)) :
    mcaThresholdExists (C : Set (ι → F)) ε_star :=
  mcaThresholdExists_of_MCALowerWitness (C : Set (ι → F)) ε_star
    (MCALowerWitness.ofLinearOnePointFiveJohnsonGKL24 C δ_min η δ ε_star h_δ_min hη
      hη_lt_δ_min hδ_johnson hδ_le_one hGKL24 hle)

/-- The faithful MCA threshold obtained from the GKL24 1.5-Johnson lower bound satisfies
the MCA target. -/
theorem mcaThreshold_spec_ofLinearOnePointFiveJohnsonGKL24
    (C : ModuleCode ι F F) (δ_min η δ ε_star : ℝ≥0)
    (h_δ_min : (δ_min : ℝ) = (Code.minDist (C : Set (ι → F)) : ℝ) / Fintype.card ι)
    (hη : 0 < η) (hη_lt_δ_min : η < δ_min)
    (hδ_johnson :
      (δ : ℝ) ≤ 1 - ((1 - (δ_min : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / 3)))
    (hδ_le_one : δ ≤ 1)
    (hGKL24 : CodingTheory.linear_epsMCA_1_5_johnson_gkl24 C δ_min η δ
      h_δ_min hη hη_lt_δ_min hδ_johnson)
    (hle :
      ENNReal.ofReal
        ((((Fintype.card ι : ℝ) + 6) / η
          + 2 / ((η : ℝ) *
              ((1 - (δ_min : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / 3)
                - (1 - (δ_min : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / 2)))
         ) / (Fintype.card F : ℝ)) ≤ (ε_star : ENNReal)) :
    let hne :=
      mcaThresholdExists_ofLinearOnePointFiveJohnsonGKL24 C δ_min η δ ε_star h_δ_min hη
        hη_lt_δ_min hδ_johnson hδ_le_one hGKL24 hle
    mcaSatisfies (C : Set (ι → F)) ε_star
      (mcaThreshold (C : Set (ι → F)) ε_star hne) :=
  mcaThreshold_spec (C : Set (ι → F)) ε_star
    (mcaThresholdExists_ofLinearOnePointFiveJohnsonGKL24 C δ_min η δ ε_star h_δ_min hη
      hη_lt_δ_min hδ_johnson hδ_le_one hGKL24 hle)

/-- The GKL24 1.5-Johnson MCA lower bound gives a direct lower bracket on the faithful
MCA lattice threshold at `⌊δ·n⌋`. -/
theorem latticeIndexOf_le_mcaThreshold_ofLinearOnePointFiveJohnsonGKL24
    (C : ModuleCode ι F F) (δ_min η δ ε_star : ℝ≥0)
    (h_δ_min : (δ_min : ℝ) = (Code.minDist (C : Set (ι → F)) : ℝ) / Fintype.card ι)
    (hη : 0 < η) (hη_lt_δ_min : η < δ_min)
    (hδ_johnson :
      (δ : ℝ) ≤ 1 - ((1 - (δ_min : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / 3)))
    (hδ_le_one : δ ≤ 1)
    (hGKL24 : CodingTheory.linear_epsMCA_1_5_johnson_gkl24 C δ_min η δ
      h_δ_min hη hη_lt_δ_min hδ_johnson)
    (hle :
      ENNReal.ofReal
        ((((Fintype.card ι : ℝ) + 6) / η
          + 2 / ((η : ℝ) *
              ((1 - (δ_min : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / 3)
                - (1 - (δ_min : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / 2)))
         ) / (Fintype.card F : ℝ)) ≤ (ε_star : ENNReal)) :
    let hne :=
      mcaThresholdExists_ofLinearOnePointFiveJohnsonGKL24 C δ_min η δ ε_star h_δ_min hη
        hη_lt_δ_min hδ_johnson hδ_le_one hGKL24 hle
    latticeIndexOf (ι := ι) δ hδ_le_one ≤
      mcaThreshold (C : Set (ι → F)) ε_star hne := by
  exact MCALowerWitness_le_mcaThreshold (C : Set (ι → F)) ε_star
    (mcaThresholdExists_ofLinearOnePointFiveJohnsonGKL24 C δ_min η δ ε_star h_δ_min hη
      hη_lt_δ_min hδ_johnson hδ_le_one hGKL24 hle)
    (MCALowerWitness.ofLinearOnePointFiveJohnsonGKL24 C δ_min η δ ε_star h_δ_min hη
      hη_lt_δ_min hδ_johnson hδ_le_one hGKL24 hle)

set_option linter.style.longLine false
#print axioms ProximityGap.GrandChallengesLattice.mcaThresholdExists_ofLinearOnePointFiveJohnsonGKL24
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_spec_ofLinearOnePointFiveJohnsonGKL24
#print axioms ProximityGap.GrandChallengesLattice.latticeIndexOf_le_mcaThreshold_ofLinearOnePointFiveJohnsonGKL24

/-- The BCHKS25 Johnson-range MCA lower bound makes the faithful MCA lattice threshold exist
whenever its explicit right-hand side is below the target `ε_star`. -/
theorem mcaThresholdExists_ofJohnsonBCHKS25
    (domain : ι ↪ F) (k : ℕ) (η δ ε_star : ℝ≥0)
    (hη : 0 < η)
    (hδ_johnson :
        (δ : ℝ) <
          1 - (((k : ℝ) / Fintype.card ι + 1 / Fintype.card ι) ^ ((1 : ℝ) / 2)) -
            (η : ℝ))
    (hδ_le_one : δ ≤ 1)
    (hBCHKS25 : CodingTheory.rs_epsMCA_johnson_range_bchks25 domain k η δ hη hδ_johnson)
    (hle :
        ENNReal.ofReal
            (let n : ℝ := Fintype.card ι
             let ρ_plus : ℝ := k / n + 1 / n
             let m : ℝ := max ⌈(ρ_plus ^ ((1 : ℝ) / 2)) / (2 * η)⌉ 3
             ((2 * (m + 1 / 2) ^ 5 + 3 * (m + 1 / 2) * δ * ρ_plus) /
                    (3 * ρ_plus ^ ((3 : ℝ) / 2)) *
                  n +
                (m + 1 / 2) / ρ_plus ^ ((1 : ℝ) / 2)) /
               (Fintype.card F : ℝ)) ≤
          (ε_star : ENNReal)) :
    mcaThresholdExists (ReedSolomon.code domain k : Set (ι → F)) ε_star :=
  mcaThresholdExists_of_MCALowerWitness (ReedSolomon.code domain k : Set (ι → F)) ε_star
    (MCALowerWitness.ofJohnsonBCHKS25 domain k η δ ε_star hη hδ_johnson hδ_le_one
      hBCHKS25 hle)

/-- The faithful MCA threshold obtained from the BCHKS25 Johnson-range lower bound satisfies
the MCA target. -/
theorem mcaThreshold_spec_ofJohnsonBCHKS25
    (domain : ι ↪ F) (k : ℕ) (η δ ε_star : ℝ≥0)
    (hη : 0 < η)
    (hδ_johnson :
        (δ : ℝ) <
          1 - (((k : ℝ) / Fintype.card ι + 1 / Fintype.card ι) ^ ((1 : ℝ) / 2)) -
            (η : ℝ))
    (hδ_le_one : δ ≤ 1)
    (hBCHKS25 : CodingTheory.rs_epsMCA_johnson_range_bchks25 domain k η δ hη hδ_johnson)
    (hle :
        ENNReal.ofReal
            (let n : ℝ := Fintype.card ι
             let ρ_plus : ℝ := k / n + 1 / n
             let m : ℝ := max ⌈(ρ_plus ^ ((1 : ℝ) / 2)) / (2 * η)⌉ 3
             ((2 * (m + 1 / 2) ^ 5 + 3 * (m + 1 / 2) * δ * ρ_plus) /
                    (3 * ρ_plus ^ ((3 : ℝ) / 2)) *
                  n +
                (m + 1 / 2) / ρ_plus ^ ((1 : ℝ) / 2)) /
               (Fintype.card F : ℝ)) ≤
          (ε_star : ENNReal)) :
    let hne :=
      mcaThresholdExists_ofJohnsonBCHKS25 domain k η δ ε_star hη hδ_johnson hδ_le_one
        hBCHKS25 hle
    mcaSatisfies (ReedSolomon.code domain k : Set (ι → F)) ε_star
      (mcaThreshold (ReedSolomon.code domain k : Set (ι → F)) ε_star hne) :=
  mcaThreshold_spec (ReedSolomon.code domain k : Set (ι → F)) ε_star
    (mcaThresholdExists_ofJohnsonBCHKS25 domain k η δ ε_star hη hδ_johnson hδ_le_one
      hBCHKS25 hle)

/-- The BCHKS25 Johnson-range MCA lower bound gives a direct lower bracket on the faithful
MCA lattice threshold at `⌊δ·n⌋`. -/
theorem latticeIndexOf_le_mcaThreshold_ofJohnsonBCHKS25
    (domain : ι ↪ F) (k : ℕ) (η δ ε_star : ℝ≥0)
    (hη : 0 < η)
    (hδ_johnson :
        (δ : ℝ) <
          1 - (((k : ℝ) / Fintype.card ι + 1 / Fintype.card ι) ^ ((1 : ℝ) / 2)) -
            (η : ℝ))
    (hδ_le_one : δ ≤ 1)
    (hBCHKS25 : CodingTheory.rs_epsMCA_johnson_range_bchks25 domain k η δ hη hδ_johnson)
    (hle :
        ENNReal.ofReal
            (let n : ℝ := Fintype.card ι
             let ρ_plus : ℝ := k / n + 1 / n
             let m : ℝ := max ⌈(ρ_plus ^ ((1 : ℝ) / 2)) / (2 * η)⌉ 3
             ((2 * (m + 1 / 2) ^ 5 + 3 * (m + 1 / 2) * δ * ρ_plus) /
                    (3 * ρ_plus ^ ((3 : ℝ) / 2)) *
                  n +
                (m + 1 / 2) / ρ_plus ^ ((1 : ℝ) / 2)) /
               (Fintype.card F : ℝ)) ≤
          (ε_star : ENNReal)) :
    let hne :=
      mcaThresholdExists_ofJohnsonBCHKS25 domain k η δ ε_star hη hδ_johnson hδ_le_one
        hBCHKS25 hle
    latticeIndexOf (ι := ι) δ hδ_le_one ≤
      mcaThreshold (ReedSolomon.code domain k : Set (ι → F)) ε_star hne := by
  exact MCALowerWitness_le_mcaThreshold
    (ReedSolomon.code domain k : Set (ι → F)) ε_star
    (mcaThresholdExists_ofJohnsonBCHKS25 domain k η δ ε_star hη hδ_johnson hδ_le_one
      hBCHKS25 hle)
    (MCALowerWitness.ofJohnsonBCHKS25 domain k η δ ε_star hη hδ_johnson hδ_le_one
      hBCHKS25 hle)

#print axioms ProximityGap.GrandChallengesLattice.latticeIndexOf_le_mcaThreshold_ofJohnsonBCHKS25

/-- Under the draft-source §4.5 MCA conjecture, the conjectural lower-witness link also makes the
faithful MCA lattice threshold exist. The consumed `mcaConjecture` is faithful to an ignored ABF26
`.tex` block rather than the rendered paper; use
`mcaThresholdExists_of_ignoredSource_mcaConjecture` at exported API boundaries where that caveat
should be visible in the declaration name. -/
theorem mcaThresholdExists_of_mcaConjecture (h : mcaConjecture) :
    ∃ c₁ c₂ c₃ : ℝ,
      ∀ {ιC : Type} [Fintype ιC] [Nonempty ιC] [DecidableEq ιC]
        {FC : Type} [Field FC] [Fintype FC] [DecidableEq FC]
        (domain : ιC ↪ FC) (k : ℕ) (ε_star δ : ℝ≥0),
        0 < k →
        (δ : ℝ) < 1 - (k : ℝ) / Fintype.card ιC → δ ≤ 1 →
        ENNReal.ofReal
            (mcaConjectureBound (Fintype.card ιC) (Fintype.card FC) k δ c₁ c₂ c₃) ≤
          (ε_star : ENNReal) →
        mcaThresholdExists (ReedSolomon.code domain k : Set (ιC → FC)) ε_star := by
  obtain ⟨c₁, c₂, c₃, hw⟩ := nonempty_mcaLowerWitness_of_mcaConjecture h
  refine ⟨c₁, c₂, c₃, ?_⟩
  intro ιC _ _ _ FC _ _ _ domain k ε_star δ hk hδ hδ1 hle
  rcases hw domain k ε_star δ hk hδ hδ1 hle with ⟨w⟩
  exact mcaThresholdExists_of_MCALowerWitness
    (ReedSolomon.code domain k : Set (ιC → FC)) ε_star w

/-- Under the draft-source §4.5 MCA conjecture, the faithful lattice threshold obtained from the
conjectural lower-witness link satisfies the MCA bound. Use
`mcaThreshold_spec_of_ignoredSource_mcaConjecture` at exported API boundaries where the
ignored-source caveat should be visible in the declaration name. -/
theorem mcaThreshold_spec_of_mcaConjecture (h : mcaConjecture) :
    ∃ c₁ c₂ c₃ : ℝ,
      ∀ {ιC : Type} [Fintype ιC] [Nonempty ιC] [DecidableEq ιC]
        {FC : Type} [Field FC] [Fintype FC] [DecidableEq FC]
        (domain : ιC ↪ FC) (k : ℕ) (ε_star δ : ℝ≥0),
        0 < k →
        (δ : ℝ) < 1 - (k : ℝ) / Fintype.card ιC → δ ≤ 1 →
        ENNReal.ofReal
            (mcaConjectureBound (Fintype.card ιC) (Fintype.card FC) k δ c₁ c₂ c₃) ≤
          (ε_star : ENNReal) →
        ∃ hne : mcaThresholdExists (ReedSolomon.code domain k : Set (ιC → FC)) ε_star,
          mcaSatisfies (ReedSolomon.code domain k : Set (ιC → FC)) ε_star
            (mcaThreshold (ReedSolomon.code domain k : Set (ιC → FC)) ε_star hne) := by
  classical
  rcases mcaThresholdExists_of_mcaConjecture h with ⟨c₁, c₂, c₃, hExists⟩
  refine ⟨c₁, c₂, c₃, ?_⟩
  intro ιC _ _ _ FC _ _ _ domain k ε_star δ hk hδ hδ1 hle
  let hne := hExists domain k ε_star δ hk hδ hδ1 hle
  exact ⟨hne, mcaThreshold_spec (ReedSolomon.code domain k : Set (ιC → FC)) ε_star hne⟩

/-- Name-explicit alias for `mcaThresholdExists_of_mcaConjecture`. The theorem statement is
unchanged, but the exported name records that `mcaConjecture` is sourced from an ignored ABF26
`.tex` block rather than the rendered paper. -/
theorem mcaThresholdExists_of_ignoredSource_mcaConjecture (h : mcaConjecture) :
    ∃ c₁ c₂ c₃ : ℝ,
      ∀ {ιC : Type} [Fintype ιC] [Nonempty ιC] [DecidableEq ιC]
        {FC : Type} [Field FC] [Fintype FC] [DecidableEq FC]
        (domain : ιC ↪ FC) (k : ℕ) (ε_star δ : ℝ≥0),
        0 < k →
        (δ : ℝ) < 1 - (k : ℝ) / Fintype.card ιC → δ ≤ 1 →
        ENNReal.ofReal
            (mcaConjectureBound (Fintype.card ιC) (Fintype.card FC) k δ c₁ c₂ c₃) ≤
          (ε_star : ENNReal) →
        mcaThresholdExists (ReedSolomon.code domain k : Set (ιC → FC)) ε_star :=
  mcaThresholdExists_of_mcaConjecture h

/-- Name-explicit alias for `mcaThreshold_spec_of_mcaConjecture`. The theorem statement is
unchanged, but the exported name makes the ignored-source status of `mcaConjecture` hard to miss in
downstream lattice-threshold composition. -/
theorem mcaThreshold_spec_of_ignoredSource_mcaConjecture (h : mcaConjecture) :
    ∃ c₁ c₂ c₃ : ℝ,
      ∀ {ιC : Type} [Fintype ιC] [Nonempty ιC] [DecidableEq ιC]
        {FC : Type} [Field FC] [Fintype FC] [DecidableEq FC]
        (domain : ιC ↪ FC) (k : ℕ) (ε_star δ : ℝ≥0),
        0 < k →
        (δ : ℝ) < 1 - (k : ℝ) / Fintype.card ιC → δ ≤ 1 →
        ENNReal.ofReal
            (mcaConjectureBound (Fintype.card ιC) (Fintype.card FC) k δ c₁ c₂ c₃) ≤
          (ε_star : ENNReal) →
        ∃ hne : mcaThresholdExists (ReedSolomon.code domain k : Set (ιC → FC)) ε_star,
          mcaSatisfies (ReedSolomon.code domain k : Set (ιC → FC)) ε_star
            (mcaThreshold (ReedSolomon.code domain k : Set (ιC → FC)) ε_star hne) :=
  mcaThreshold_spec_of_mcaConjecture h

/-- Prize-rate specialization of `mcaThresholdExists_of_ignoredSource_mcaConjecture`.
The conjecture remains an explicit ignored-source hypothesis; this only fixes
`ε* = epsStar` and the four ABF26 prize-rate dimensions. -/
theorem mcaThresholdExists_prize_of_ignoredSource_mcaConjecture (h : mcaConjecture) :
    ∃ c₁ c₂ c₃ : ℝ,
      ∀ {ιC : Type} [Fintype ιC] [Nonempty ιC] [DecidableEq ιC]
        {FC : Type} [Field FC] [Fintype FC] [DecidableEq FC]
        (domain : ιC ↪ FC) (j : Fin 4) (δ : ℝ≥0),
        let k : ℕ := ⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊
        0 < k →
        (δ : ℝ) < 1 - (k : ℝ) / Fintype.card ιC → δ ≤ 1 →
        ENNReal.ofReal
            (mcaConjectureBound (Fintype.card ιC) (Fintype.card FC) k δ c₁ c₂ c₃) ≤
          (epsStar : ENNReal) →
        mcaThresholdExists (ReedSolomon.code domain k : Set (ιC → FC)) epsStar := by
  obtain ⟨c₁, c₂, c₃, hExists⟩ := mcaThresholdExists_of_ignoredSource_mcaConjecture h
  refine ⟨c₁, c₂, c₃, ?_⟩
  intro ιC _ _ _ FC _ _ _ domain j δ
  dsimp only
  exact hExists (domain := domain)
    (k := ⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊) (ε_star := epsStar) (δ := δ)

/-- Prize-rate specialization of `mcaThreshold_spec_of_ignoredSource_mcaConjecture`.
This gives the faithful lattice threshold and its specification for the ABF26 prize-rate family
under the explicit ignored-source `mcaConjecture` hypothesis. -/
theorem mcaThreshold_spec_prize_of_ignoredSource_mcaConjecture (h : mcaConjecture) :
    ∃ c₁ c₂ c₃ : ℝ,
      ∀ {ιC : Type} [Fintype ιC] [Nonempty ιC] [DecidableEq ιC]
        {FC : Type} [Field FC] [Fintype FC] [DecidableEq FC]
        (domain : ιC ↪ FC) (j : Fin 4) (δ : ℝ≥0),
        let k : ℕ := ⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊
        0 < k →
        (δ : ℝ) < 1 - (k : ℝ) / Fintype.card ιC → δ ≤ 1 →
        ENNReal.ofReal
            (mcaConjectureBound (Fintype.card ιC) (Fintype.card FC) k δ c₁ c₂ c₃) ≤
          (epsStar : ENNReal) →
        ∃ hne : mcaThresholdExists (ReedSolomon.code domain k : Set (ιC → FC)) epsStar,
          mcaSatisfies (ReedSolomon.code domain k : Set (ιC → FC)) epsStar
            (mcaThreshold (ReedSolomon.code domain k : Set (ιC → FC)) epsStar hne) := by
  obtain ⟨c₁, c₂, c₃, hSpec⟩ := mcaThreshold_spec_of_ignoredSource_mcaConjecture h
  refine ⟨c₁, c₂, c₃, ?_⟩
  intro ιC _ _ _ FC _ _ _ domain j δ
  dsimp only
  exact hSpec (domain := domain)
    (k := ⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊) (ε_star := epsStar) (δ := δ)

set_option linter.style.longLine false
#print axioms ProximityGap.GrandChallengesLattice.mcaThresholdExists_of_ignoredSource_mcaConjecture
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_spec_of_ignoredSource_mcaConjecture
#print axioms ProximityGap.GrandChallengesLattice.mcaThresholdExists_prize_of_ignoredSource_mcaConjecture
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_spec_prize_of_ignoredSource_mcaConjecture

/-- **Upper bracket.** An `MCAUpperWitness` at a radius `δ ≤ 1` forces
`mcaThreshold < ⌊δ·n⌋`: its lattice point already exceeds `ε*`, so the threshold is strictly
below it. -/
theorem mcaThreshold_lt_MCAUpperWitness (C : Set (ι → F)) (ε_star : ℝ≥0)
    (hne : mcaThresholdExists C ε_star) (w : MCAUpperWitness C ε_star) (hδ : w.δ ≤ 1) :
    mcaThreshold C ε_star hne < latticeIndexOf (ι := ι) w.δ hδ := by
  by_contra h
  push Not at h
  have hsat : mcaSatisfies C ε_star (latticeIndexOf (ι := ι) w.δ hδ) := by
    refine mcaSatisfies_downward_closed C ε_star h ?_
    exact mcaThreshold_spec C ε_star hne
  have : epsMCA (F := F) (A := F) C
      (mcaLatticePoint (Fintype.card ι) (latticeIndexOf (ι := ι) w.δ hδ)) ≤
      (ε_star : ENNReal) := hsat
  rw [← epsMCA_eq_at_latticeIndex C w.δ hδ] at this
  exact absurd this (not_le.mpr w.exceeds)

/-- A capacity-side `ε_ca` lower bound for a linear code gives a lattice upper bracket on the
faithful MCA threshold. -/
theorem mcaThreshold_lt_ofEpsCAGt {MC : Submodule F (ι → F)} {ε_star δ : ℝ≥0}
    (hne : mcaThresholdExists (MC : Set (ι → F)) ε_star)
    (h : epsCA (F := F) (A := F) (MC : Set (ι → F)) δ δ > (ε_star : ENNReal))
    (hδ : δ ≤ 1) :
    mcaThreshold (MC : Set (ι → F)) ε_star hne < latticeIndexOf (ι := ι) δ hδ :=
  mcaThreshold_lt_MCAUpperWitness (MC : Set (ι → F)) ε_star hne
    (MCAUpperWitness.ofEpsCAGt h) hδ

/-- The packaged BCHKS25+KK25 near-capacity CA lower-bound witness gives a direct upper
bracket on the faithful MCA lattice threshold once its explicit lower bound exceeds `ε*`. -/
theorem mcaThreshold_lt_ofLowerCapacityBCHKS25KK25
    (c ρ ε_star : ℝ≥0)
    (W : CodingTheory.RSLowerCapacityWitness c ρ ι F)
    (hne : mcaThresholdExists (ReedSolomon.code W.domain W.k : Set (ι → F)) ε_star)
    (hδle : 1 - ρ - W.slack ≤ 1)
    (hgt :
      (ε_star : ENNReal) <
        ((Fintype.card ι : ENNReal) ^ (c : ℝ)) / (Fintype.card F : ENNReal)) :
    mcaThreshold (ReedSolomon.code W.domain W.k : Set (ι → F)) ε_star hne <
      latticeIndexOf (ι := ι) (1 - ρ - W.slack) hδle :=
  mcaThreshold_lt_MCAUpperWitness
    (ReedSolomon.code W.domain W.k : Set (ι → F)) ε_star hne
    (MCAUpperWitness.ofLowerCapacityBCHKS25KK25 c ρ ε_star W hgt) hδle

#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_lt_ofLowerCapacityBCHKS25KK25

/-- The CS25 complete-CA-breakdown lower bound gives a direct upper bracket on the faithful
MCA lattice threshold. -/
theorem mcaThreshold_lt_ofRSBreakdownCS25
    (domain : ι ↪ F) (k : ℕ) (δ ε_star : ℝ≥0)
    (hne : mcaThresholdExists (ReedSolomon.code domain k : Set (ι → F)) ε_star)
    (hδle : δ ≤ 1)
    (hq_ge : 10 ≤ Fintype.card F)
    (hδ_lo :
        1 - CodingTheory.qEntropy (Fintype.card F) (δ : ℝ) + 2 / (Fintype.card ι : ℝ)
            + ((CodingTheory.qEntropy (Fintype.card F) (δ : ℝ) - (δ : ℝ))
                / (Fintype.card ι : ℝ)) ^ ((1 : ℝ) / 2)
          ≤ (k : ℝ) / Fintype.card ι)
    (hδ_hi : (k : ℝ) / Fintype.card ι ≤ 1 - (δ : ℝ) - 2 / (Fintype.card ι : ℝ))
    (hCS25 : CodingTheory.rs_epsCA_breakdown_cs25 domain k δ hq_ge hδ_lo hδ_hi)
    (hε : (ε_star : ENNReal) < 1) :
    mcaThreshold (ReedSolomon.code domain k : Set (ι → F)) ε_star hne <
      latticeIndexOf (ι := ι) δ hδle :=
  mcaThreshold_lt_MCAUpperWitness (ReedSolomon.code domain k : Set (ι → F)) ε_star hne
    (MCAUpperWitness.ofRSBreakdownCS25 domain k δ ε_star hq_ge hδ_lo hδ_hi hCS25 hε)
    hδle

open Classical in
/-- The CS25 count-budget route to complete CA breakdown gives a direct upper bracket on the
faithful MCA lattice threshold. -/
theorem mcaThreshold_lt_ofRSBreakdownCS25Counts
    (domain : ι ↪ F) (k : ℕ) (δ ε_star : ℝ≥0)
    (hne : mcaThresholdExists (ReedSolomon.code domain k : Set (ι → F)) ε_star)
    (hδle : δ ≤ 1)
    (hq_ge : 10 ≤ Fintype.card F)
    (hδ_lo :
        1 - CodingTheory.qEntropy (Fintype.card F) (δ : ℝ) + 2 / (Fintype.card ι : ℝ)
            + ((CodingTheory.qEntropy (Fintype.card F) (δ : ℝ) - (δ : ℝ))
                / (Fintype.card ι : ℝ)) ^ ((1 : ℝ) / 2)
          ≤ (k : ℝ) / Fintype.card ι)
    (hδ_hi : (k : ℝ) / Fintype.card ι ≤ 1 - (δ : ℝ) - 2 / (Fintype.card ι : ℝ))
    (hsum :
      (∑ u : Code.WordStack F (Fin 2) ι,
          (Finset.univ.filter (fun γ : F =>
            ¬ δᵣ(u 0 + γ • u 1, (ReedSolomon.code domain k : Set (ι → F))) ≤ δ)).card)
        + (Finset.univ.filter (fun u : Code.WordStack F (Fin 2) ι =>
            Code.jointProximity (C := (ReedSolomon.code domain k : Set (ι → F))) (u := u) δ)).card
      < Fintype.card (Code.WordStack F (Fin 2) ι))
    (hε : (ε_star : ENNReal) < 1) :
    mcaThreshold (ReedSolomon.code domain k : Set (ι → F)) ε_star hne <
      latticeIndexOf (ι := ι) δ hδle :=
  mcaThreshold_lt_MCAUpperWitness (ReedSolomon.code domain k : Set (ι → F)) ε_star hne
    (MCAUpperWitness.ofRSBreakdownCS25Counts domain k δ ε_star hq_ge hδ_lo hδ_hi hsum hε)
    hδle

#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_lt_ofRSBreakdownCS25Counts

/-- The DG25 sampling lower bound gives a direct upper bracket on the faithful MCA lattice
threshold once the sampling lower bound is numerically above `ε*`. -/
theorem mcaThreshold_lt_ofSamplingDG25
    (C : LinearCode ι F) (δ δ' ε_star : ℝ≥0)
    (hne : mcaThresholdExists (C : Set (ι → F)) ε_star)
    (hδle : δ ≤ 1)
    (hδ' : (δ' : ENNReal) = ⨆ u : ι → F, δᵣ(u, (C : Set (ι → F))))
    (hδ_pos : 0 < δ) (hδ_lt : δ < δ')
    (hDG25 : CodingTheory.linear_epsCA_ge_sampling_dg25 C δ δ' hδ' hδ_pos hδ_lt)
    (hgt :
      ((Fintype.card F - 1 : ℝ≥0) / Fintype.card F : ENNReal)
          * Pr_{
              let u ← $ᵖ (ι → F)
              }[δᵣ(u, (C : Set (ι → F))) ≤ δ] >
        (ε_star : ENNReal)) :
    mcaThreshold (C : Set (ι → F)) ε_star hne < latticeIndexOf (ι := ι) δ hδle :=
  mcaThreshold_lt_MCAUpperWitness (C : Set (ι → F)) ε_star hne
    (MCAUpperWitness.ofSamplingDG25 C δ δ' ε_star hδ' hδ_pos hδ_lt hDG25 hgt)
    hδle

/-- The fixed BCHKS25 Johnson-jump radius is a valid faithful MCA lattice radius. -/
theorem johnsonJumpRadius_le_one : CodingTheory.johnsonJumpRadius ≤ 1 := by
  rw [CodingTheory.johnsonJumpRadius_eq_three_fourths]
  exact_mod_cast (show (3 / 4 : ℝ) ≤ 1 by norm_num)

/-- The packaged BCHKS25 Johnson-jump witness gives a direct upper bracket on the faithful
MCA lattice threshold at the fixed Johnson radius. -/
theorem mcaThreshold_lt_ofJohnsonJumpBCHKS25AutoRadius [CharP F 2]
    (ε ε_star : ℝ≥0)
    (W : CodingTheory.RSJohnsonJumpWitness (FC := F) ε ι)
    (hne : mcaThresholdExists (ReedSolomon.code W.domain W.k : Set (ι → F)) ε_star)
    (hgt :
      (ε_star : ENNReal) <
        ((Fintype.card ι : ENNReal) ^ (2 * ((1 : ℝ) - ε)))
          / (Fintype.card F : ENNReal)) :
    mcaThreshold (ReedSolomon.code W.domain W.k : Set (ι → F)) ε_star hne <
      latticeIndexOf (ι := ι) CodingTheory.johnsonJumpRadius johnsonJumpRadius_le_one :=
  mcaThreshold_lt_MCAUpperWitness
    (ReedSolomon.code W.domain W.k : Set (ι → F)) ε_star hne
    (MCAUpperWitness.ofJohnsonJumpBCHKS25AutoRadius ε ε_star W hgt)
    johnsonJumpRadius_le_one

#print axioms ProximityGap.GrandChallengesLattice.johnsonJumpRadius_le_one
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_lt_ofJohnsonJumpBCHKS25AutoRadius

/-- The arbitrary-radius spike lower bound gives a direct upper bracket on the faithful MCA
lattice threshold.  Unlike the endpoint floor, this excludes every lattice point at or above
the chosen radius `δ` whenever the spike value `t / |F|` already exceeds the MCA budget. -/
theorem mcaThreshold_lt_ofSpike
    (domain : ι ↪ F) (k t : ℕ) (δ ε_star : ℝ≥0)
    (hne : mcaThresholdExists (ReedSolomon.code domain k : Set (ι → F)) ε_star)
    (hδle : δ ≤ 1)
    (ht_n : t + k ≤ Fintype.card ι) (ht_q : t ≤ Fintype.card F)
    (hδ :
      ((1 - δ) * Fintype.card ι : ℝ≥0) ≤ (Fintype.card ι - t + 1 : ℕ))
    (hgt :
      (ε_star : ENNReal) < (t : ENNReal) / (Fintype.card F : ENNReal)) :
    mcaThreshold (ReedSolomon.code domain k : Set (ι → F)) ε_star hne <
      latticeIndexOf (ι := ι) δ hδle :=
  mcaThreshold_lt_MCAUpperWitness
    (ReedSolomon.code domain k : Set (ι → F)) ε_star hne
    ⟨δ, lt_of_lt_of_le hgt (epsMCA_ge_spike domain k t δ ht_n ht_q hδ)⟩ hδle

/-- A lower MCA witness and the CS25 complete-CA-breakdown lower bound bracket the faithful
MCA lattice threshold directly. -/
theorem mcaThresholdLattice_bracketed_of_lowerWitness_and_RSBreakdownCS25
    (domain : ι ↪ F) (k : ℕ) (δ_hi ε_star : ℝ≥0)
    (wlo : MCALowerWitness (ReedSolomon.code domain k : Set (ι → F)) ε_star)
    (hδhi : δ_hi ≤ 1)
    (hq_ge : 10 ≤ Fintype.card F)
    (hδ_lo :
        1 - CodingTheory.qEntropy (Fintype.card F) (δ_hi : ℝ) + 2 / (Fintype.card ι : ℝ)
            + ((CodingTheory.qEntropy (Fintype.card F) (δ_hi : ℝ) - (δ_hi : ℝ))
                / (Fintype.card ι : ℝ)) ^ ((1 : ℝ) / 2)
          ≤ (k : ℝ) / Fintype.card ι)
    (hδ_hi : (k : ℝ) / Fintype.card ι ≤ 1 - (δ_hi : ℝ) - 2 / (Fintype.card ι : ℝ))
    (hCS25 : CodingTheory.rs_epsCA_breakdown_cs25 domain k δ_hi hq_ge hδ_lo hδ_hi)
    (hε : (ε_star : ENNReal) < 1) :
    let hne := mcaThresholdExists_of_MCALowerWitness
      (ReedSolomon.code domain k : Set (ι → F)) ε_star wlo
    latticeIndexOf (ι := ι) wlo.δ wlo.le_one ≤
        mcaThreshold (ReedSolomon.code domain k : Set (ι → F)) ε_star hne ∧
      mcaThreshold (ReedSolomon.code domain k : Set (ι → F)) ε_star hne <
        latticeIndexOf (ι := ι) δ_hi hδhi :=
  ⟨MCALowerWitness_le_mcaThreshold (ReedSolomon.code domain k : Set (ι → F)) ε_star
      (mcaThresholdExists_of_MCALowerWitness
        (ReedSolomon.code domain k : Set (ι → F)) ε_star wlo) wlo,
    mcaThreshold_lt_ofRSBreakdownCS25 domain k δ_hi ε_star
      (mcaThresholdExists_of_MCALowerWitness
        (ReedSolomon.code domain k : Set (ι → F)) ε_star wlo)
      hδhi hq_ge hδ_lo hδ_hi hCS25 hε⟩

/-- The BCHKS25 Johnson-range MCA lower bound and the CS25 complete-CA-breakdown lower bound
bracket the faithful MCA lattice threshold directly.  This is the end-to-end lattice form of
the common Johnson-lower/capacity-upper workflow for Reed-Solomon codes. -/
theorem mcaThresholdLattice_bracketed_ofJohnsonBCHKS25_and_RSBreakdownCS25
    (domain : ι ↪ F) (k : ℕ) (η δ_lo δ_hi ε_star : ℝ≥0)
    (hη : 0 < η)
    (hδ_johnson :
        (δ_lo : ℝ) <
          1 - (((k : ℝ) / Fintype.card ι + 1 / Fintype.card ι) ^ ((1 : ℝ) / 2)) -
            (η : ℝ))
    (hδlo_le_one : δ_lo ≤ 1)
    (hBCHKS25 : CodingTheory.rs_epsMCA_johnson_range_bchks25 domain k η δ_lo
      hη hδ_johnson)
    (hle :
        ENNReal.ofReal
            (let n : ℝ := Fintype.card ι
             let ρ_plus : ℝ := k / n + 1 / n
             let m : ℝ := max ⌈(ρ_plus ^ ((1 : ℝ) / 2)) / (2 * η)⌉ 3
             ((2 * (m + 1 / 2) ^ 5 + 3 * (m + 1 / 2) * δ_lo * ρ_plus) /
                    (3 * ρ_plus ^ ((3 : ℝ) / 2)) *
                  n +
                (m + 1 / 2) / ρ_plus ^ ((1 : ℝ) / 2)) /
               (Fintype.card F : ℝ)) ≤
          (ε_star : ENNReal))
    (hδhi : δ_hi ≤ 1)
    (hq_ge : 10 ≤ Fintype.card F)
    (hδ_cs_lo :
        1 - CodingTheory.qEntropy (Fintype.card F) (δ_hi : ℝ) + 2 / (Fintype.card ι : ℝ)
            + ((CodingTheory.qEntropy (Fintype.card F) (δ_hi : ℝ) - (δ_hi : ℝ))
                / (Fintype.card ι : ℝ)) ^ ((1 : ℝ) / 2)
          ≤ (k : ℝ) / Fintype.card ι)
    (hδ_cs_hi : (k : ℝ) / Fintype.card ι ≤ 1 - (δ_hi : ℝ) - 2 / (Fintype.card ι : ℝ))
    (hCS25 : CodingTheory.rs_epsCA_breakdown_cs25 domain k δ_hi hq_ge hδ_cs_lo hδ_cs_hi)
    (hε : (ε_star : ENNReal) < 1) :
    let hne := mcaThresholdExists_ofJohnsonBCHKS25 domain k η δ_lo ε_star hη
      hδ_johnson hδlo_le_one hBCHKS25 hle
    latticeIndexOf (ι := ι) δ_lo hδlo_le_one ≤
        mcaThreshold (ReedSolomon.code domain k : Set (ι → F)) ε_star hne ∧
      mcaThreshold (ReedSolomon.code domain k : Set (ι → F)) ε_star hne <
        latticeIndexOf (ι := ι) δ_hi hδhi :=
  let wlo := MCALowerWitness.ofJohnsonBCHKS25 domain k η δ_lo ε_star hη hδ_johnson
    hδlo_le_one hBCHKS25 hle
  ⟨MCALowerWitness_le_mcaThreshold (ReedSolomon.code domain k : Set (ι → F)) ε_star
      (mcaThresholdExists_ofJohnsonBCHKS25 domain k η δ_lo ε_star hη hδ_johnson
        hδlo_le_one hBCHKS25 hle) wlo,
    mcaThreshold_lt_ofRSBreakdownCS25 domain k δ_hi ε_star
      (mcaThresholdExists_ofJohnsonBCHKS25 domain k η δ_lo ε_star hη hδ_johnson
        hδlo_le_one hBCHKS25 hle)
      hδhi hq_ge hδ_cs_lo hδ_cs_hi hCS25 hε⟩

/-- A lower MCA witness and the DG25 sampling lower bound bracket the faithful MCA lattice
threshold directly once the sampling lower bound is numerically above `ε*`. -/
theorem mcaThresholdLattice_bracketed_of_lowerWitness_and_SamplingDG25
    (C : LinearCode ι F) (δ_hi δ' ε_star : ℝ≥0)
    (wlo : MCALowerWitness (C : Set (ι → F)) ε_star)
    (hδhi : δ_hi ≤ 1)
    (hδ' : (δ' : ENNReal) = ⨆ u : ι → F, δᵣ(u, (C : Set (ι → F))))
    (hδ_pos : 0 < δ_hi) (hδ_lt : δ_hi < δ')
    (hDG25 : CodingTheory.linear_epsCA_ge_sampling_dg25 C δ_hi δ' hδ' hδ_pos hδ_lt)
    (hgt :
      ((Fintype.card F - 1 : ℝ≥0) / Fintype.card F : ENNReal)
          * Pr_{
              let u ← $ᵖ (ι → F)
              }[δᵣ(u, (C : Set (ι → F))) ≤ δ_hi] >
        (ε_star : ENNReal)) :
    let hne := mcaThresholdExists_of_MCALowerWitness (C : Set (ι → F)) ε_star wlo
    latticeIndexOf (ι := ι) wlo.δ wlo.le_one ≤
        mcaThreshold (C : Set (ι → F)) ε_star hne ∧
      mcaThreshold (C : Set (ι → F)) ε_star hne <
        latticeIndexOf (ι := ι) δ_hi hδhi :=
  ⟨MCALowerWitness_le_mcaThreshold (C : Set (ι → F)) ε_star
      (mcaThresholdExists_of_MCALowerWitness (C : Set (ι → F)) ε_star wlo) wlo,
    mcaThreshold_lt_ofSamplingDG25 C δ_hi δ' ε_star
      (mcaThresholdExists_of_MCALowerWitness (C : Set (ι → F)) ε_star wlo)
      hδhi hδ' hδ_pos hδ_lt hDG25 hgt⟩

/-- The BCHKS25 Johnson-range MCA lower bound and the DG25 sampling lower bound bracket the
faithful MCA lattice threshold directly for Reed-Solomon codes. -/
theorem mcaThresholdLattice_bracketed_ofJohnsonBCHKS25_and_SamplingDG25
    (domain : ι ↪ F) (k : ℕ) (η δ_lo δ_hi δ' ε_star : ℝ≥0)
    (hη : 0 < η)
    (hδ_johnson :
        (δ_lo : ℝ) <
          1 - (((k : ℝ) / Fintype.card ι + 1 / Fintype.card ι) ^ ((1 : ℝ) / 2)) -
            (η : ℝ))
    (hδlo_le_one : δ_lo ≤ 1)
    (hBCHKS25 : CodingTheory.rs_epsMCA_johnson_range_bchks25 domain k η δ_lo
      hη hδ_johnson)
    (hle :
        ENNReal.ofReal
            (let n : ℝ := Fintype.card ι
             let ρ_plus : ℝ := k / n + 1 / n
             let m : ℝ := max ⌈(ρ_plus ^ ((1 : ℝ) / 2)) / (2 * η)⌉ 3
             ((2 * (m + 1 / 2) ^ 5 + 3 * (m + 1 / 2) * δ_lo * ρ_plus) /
                    (3 * ρ_plus ^ ((3 : ℝ) / 2)) *
                  n +
                (m + 1 / 2) / ρ_plus ^ ((1 : ℝ) / 2)) /
               (Fintype.card F : ℝ)) ≤
          (ε_star : ENNReal))
    (hδhi : δ_hi ≤ 1)
    (hδ' : (δ' : ENNReal) =
      ⨆ u : ι → F, δᵣ(u, (ReedSolomon.code domain k : Set (ι → F))))
    (hδ_pos : 0 < δ_hi) (hδ_lt : δ_hi < δ')
    (hDG25 : CodingTheory.linear_epsCA_ge_sampling_dg25
      (ReedSolomon.code domain k) δ_hi δ' hδ' hδ_pos hδ_lt)
    (hgt :
      ((Fintype.card F - 1 : ℝ≥0) / Fintype.card F : ENNReal)
          * Pr_{
              let u ← $ᵖ (ι → F)
              }[δᵣ(u, (ReedSolomon.code domain k : Set (ι → F))) ≤ δ_hi] >
        (ε_star : ENNReal)) :
    let hne := mcaThresholdExists_ofJohnsonBCHKS25 domain k η δ_lo ε_star hη
      hδ_johnson hδlo_le_one hBCHKS25 hle
    latticeIndexOf (ι := ι) δ_lo hδlo_le_one ≤
        mcaThreshold (ReedSolomon.code domain k : Set (ι → F)) ε_star hne ∧
      mcaThreshold (ReedSolomon.code domain k : Set (ι → F)) ε_star hne <
        latticeIndexOf (ι := ι) δ_hi hδhi :=
  let wlo := MCALowerWitness.ofJohnsonBCHKS25 domain k η δ_lo ε_star hη hδ_johnson
    hδlo_le_one hBCHKS25 hle
  ⟨MCALowerWitness_le_mcaThreshold (ReedSolomon.code domain k : Set (ι → F)) ε_star
      (mcaThresholdExists_ofJohnsonBCHKS25 domain k η δ_lo ε_star hη hδ_johnson
        hδlo_le_one hBCHKS25 hle) wlo,
    mcaThreshold_lt_ofSamplingDG25 (ReedSolomon.code domain k) δ_hi δ' ε_star
      (mcaThresholdExists_ofJohnsonBCHKS25 domain k η δ_lo ε_star hη hδ_johnson
        hδlo_le_one hBCHKS25 hle)
      hδhi hδ' hδ_pos hδ_lt hDG25 hgt⟩

/-- A lower MCA witness and an arbitrary-radius spike certificate bracket the faithful MCA
lattice threshold directly.  This is a middle-radius finite-search certificate: one side can
come from Johnson/GS-style existence, while the other comes from the explicit spike family at
the candidate next lattice radius. -/
theorem mcaThresholdLattice_bracketed_of_lowerWitness_and_Spike
    (domain : ι ↪ F) (k t : ℕ) (δ_hi ε_star : ℝ≥0)
    (wlo : MCALowerWitness (ReedSolomon.code domain k : Set (ι → F)) ε_star)
    (hδhi : δ_hi ≤ 1)
    (ht_n : t + k ≤ Fintype.card ι) (ht_q : t ≤ Fintype.card F)
    (hδ :
      ((1 - δ_hi) * Fintype.card ι : ℝ≥0) ≤ (Fintype.card ι - t + 1 : ℕ))
    (hgt :
      (ε_star : ENNReal) < (t : ENNReal) / (Fintype.card F : ENNReal)) :
    let hne := mcaThresholdExists_of_MCALowerWitness
      (ReedSolomon.code domain k : Set (ι → F)) ε_star wlo
    latticeIndexOf (ι := ι) wlo.δ wlo.le_one ≤
        mcaThreshold (ReedSolomon.code domain k : Set (ι → F)) ε_star hne ∧
      mcaThreshold (ReedSolomon.code domain k : Set (ι → F)) ε_star hne <
        latticeIndexOf (ι := ι) δ_hi hδhi :=
  ⟨MCALowerWitness_le_mcaThreshold (ReedSolomon.code domain k : Set (ι → F)) ε_star
      (mcaThresholdExists_of_MCALowerWitness
        (ReedSolomon.code domain k : Set (ι → F)) ε_star wlo) wlo,
    mcaThreshold_lt_ofSpike domain k t δ_hi ε_star
      (mcaThresholdExists_of_MCALowerWitness
        (ReedSolomon.code domain k : Set (ι → F)) ε_star wlo)
      hδhi ht_n ht_q hδ hgt⟩

/-- A lower MCA witness and a capacity-side `ε_ca` upper witness bracket the faithful lattice
threshold directly. This is the lattice version of the common Johnson-lower/capacity-upper
workflow for linear codes. -/
theorem mcaThresholdLattice_bracketed_of_lowerWitness_and_epsCAGt
    {MC : Submodule F (ι → F)} {ε_star δ_hi : ℝ≥0}
    (wlo : MCALowerWitness (MC : Set (ι → F)) ε_star)
    (hhi : epsCA (F := F) (A := F) (MC : Set (ι → F)) δ_hi δ_hi >
      (ε_star : ENNReal))
    (hδhi : δ_hi ≤ 1) :
    let hne := mcaThresholdExists_of_MCALowerWitness (MC : Set (ι → F)) ε_star wlo
    latticeIndexOf (ι := ι) wlo.δ wlo.le_one ≤
        mcaThreshold (MC : Set (ι → F)) ε_star hne ∧
      mcaThreshold (MC : Set (ι → F)) ε_star hne <
        latticeIndexOf (ι := ι) δ_hi hδhi :=
  ⟨MCALowerWitness_le_mcaThreshold (MC : Set (ι → F)) ε_star
      (mcaThresholdExists_of_MCALowerWitness (MC : Set (ι → F)) ε_star wlo) wlo,
    mcaThreshold_lt_ofEpsCAGt
      (mcaThresholdExists_of_MCALowerWitness (MC : Set (ι → F)) ε_star wlo) hhi hδhi⟩

/-- The BCHKS25 Johnson-range MCA lower bound and any capacity-side `ε_ca` upper witness
bracket the faithful MCA lattice threshold directly for Reed-Solomon codes. -/
theorem mcaThresholdLattice_bracketed_ofJohnsonBCHKS25_and_epsCAGt
    (domain : ι ↪ F) (k : ℕ) (η δ_lo δ_hi ε_star : ℝ≥0)
    (hη : 0 < η)
    (hδ_johnson :
        (δ_lo : ℝ) <
          1 - (((k : ℝ) / Fintype.card ι + 1 / Fintype.card ι) ^ ((1 : ℝ) / 2)) -
            (η : ℝ))
    (hδlo_le_one : δ_lo ≤ 1)
    (hBCHKS25 : CodingTheory.rs_epsMCA_johnson_range_bchks25 domain k η δ_lo
      hη hδ_johnson)
    (hle :
        ENNReal.ofReal
            (let n : ℝ := Fintype.card ι
             let ρ_plus : ℝ := k / n + 1 / n
             let m : ℝ := max ⌈(ρ_plus ^ ((1 : ℝ) / 2)) / (2 * η)⌉ 3
             ((2 * (m + 1 / 2) ^ 5 + 3 * (m + 1 / 2) * δ_lo * ρ_plus) /
                    (3 * ρ_plus ^ ((3 : ℝ) / 2)) *
                  n +
                (m + 1 / 2) / ρ_plus ^ ((1 : ℝ) / 2)) /
               (Fintype.card F : ℝ)) ≤
          (ε_star : ENNReal))
    (hhi :
      epsCA (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F)) δ_hi δ_hi >
        (ε_star : ENNReal))
    (hδhi : δ_hi ≤ 1) :
    let hne := mcaThresholdExists_ofJohnsonBCHKS25 domain k η δ_lo ε_star hη
      hδ_johnson hδlo_le_one hBCHKS25 hle
    latticeIndexOf (ι := ι) δ_lo hδlo_le_one ≤
        mcaThreshold (ReedSolomon.code domain k : Set (ι → F)) ε_star hne ∧
      mcaThreshold (ReedSolomon.code domain k : Set (ι → F)) ε_star hne <
        latticeIndexOf (ι := ι) δ_hi hδhi :=
  let wlo := MCALowerWitness.ofJohnsonBCHKS25 domain k η δ_lo ε_star hη hδ_johnson
    hδlo_le_one hBCHKS25 hle
  ⟨MCALowerWitness_le_mcaThreshold (ReedSolomon.code domain k : Set (ι → F)) ε_star
      (mcaThresholdExists_ofJohnsonBCHKS25 domain k η δ_lo ε_star hη hδ_johnson
        hδlo_le_one hBCHKS25 hle) wlo,
    mcaThreshold_lt_ofEpsCAGt
      (MC := ReedSolomon.code domain k)
      (mcaThresholdExists_ofJohnsonBCHKS25 domain k η δ_lo ε_star hη hδ_johnson
        hδlo_le_one hBCHKS25 hle) hhi hδhi⟩

/-- The second-moment radius-one lower bound gives a direct upper bracket on the faithful
MCA lattice threshold: in the explicit numeric regime where `epsStar < (M' - M'^2/q)/q`,
the top radius `1` already exceeds `epsStar`, so the threshold lies strictly below the
top lattice point. -/
theorem mcaThreshold_lt_one_of_secondMoment
    (domain : ι ↪ F) (k M' : ℕ)
    (hne : mcaThresholdExists (ReedSolomon.code domain k : Set (ι → F)) epsStar)
    (hk : k + 1 ≤ Fintype.card ι)
    (hM' : M' ≤ Nat.choose (Fintype.card ι) (k + 1))
    (hle : M' * M' ≤ M' * Fintype.card F)
    (hnum :
      Fintype.card F * Fintype.card F <
        2 ^ (128 : ℕ) * (M' * Fintype.card F - M' * M')) :
    mcaThreshold (ReedSolomon.code domain k : Set (ι → F)) epsStar hne <
      latticeIndexOf (ι := ι) (1 : ℝ≥0) le_rfl := by
  have hsecond :
      (epsStar : ENNReal) <
        epsMCA (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F)) 1 := by
    exact lt_of_lt_of_le
      (epsStar_lt_second_moment_value
        (M' := M') (q := Fintype.card F) Fintype.card_pos hle hnum)
      (epsMCA_one_ge_second_moment domain hk hM')
  exact mcaThreshold_lt_MCAUpperWitness
    (ReedSolomon.code domain k : Set (ι → F)) epsStar hne
    ⟨1, hsecond⟩ le_rfl

/-- The spike endpoint floor gives a direct upper bracket on the faithful MCA lattice
threshold in the small-field regime where `q < 2^128 · (n-k)`. -/
theorem mcaThreshold_lt_one_of_fieldSmall
    (domain : ι ↪ F) (k : ℕ)
    (hne : mcaThresholdExists (ReedSolomon.code domain k : Set (ι → F)) epsStar)
    (hk : 1 ≤ k) (hn : k + 1 ≤ Fintype.card ι)
    (hsmall : Fintype.card F < 2 ^ (128 : ℕ) * (Fintype.card ι - k)) :
    mcaThreshold (ReedSolomon.code domain k : Set (ι → F)) epsStar hne <
      latticeIndexOf (ι := ι) (1 : ℝ≥0) le_rfl :=
  mcaThreshold_lt_MCAUpperWitness
    (ReedSolomon.code domain k : Set (ι → F)) epsStar hne
    ⟨1, epsStar_lt_epsMCA_one_of_field_small domain k hk hn hsmall⟩ le_rfl

/-- The unconditional subset-sum endpoint floor gives a direct upper bracket on the faithful
MCA lattice threshold when the subset-sum set is numerically large enough. -/
theorem mcaThreshold_lt_one_of_subsetSums
    (domain : ι ↪ F) (k : ℕ)
    (hne : mcaThresholdExists (ReedSolomon.code domain k : Set (ι → F)) epsStar)
    (hk : k + 1 ≤ Fintype.card ι)
    (hsmall : Fintype.card F < 2 ^ (128 : ℕ) * (subsetSumsKplus1 domain k).card) :
    mcaThreshold (ReedSolomon.code domain k : Set (ι → F)) epsStar hne <
      latticeIndexOf (ι := ι) (1 : ℝ≥0) le_rfl :=
  mcaThreshold_lt_MCAUpperWitness
    (ReedSolomon.code domain k : Set (ι → F)) epsStar hne
    ⟨1, epsStar_lt_epsMCA_one_of_subsetSums domain hk hsmall⟩ le_rfl

/-- The Erdős-Heilbronn endpoint floor for `k = 1` gives a direct upper bracket on the
faithful MCA lattice threshold in the prime-characteristic numeric regime. -/
theorem mcaThreshold_lt_one_of_erdosHeilbronn
    (domain : ι ↪ F) {p : ℕ} (hp : p.Prime)
    (hne : mcaThresholdExists (ReedSolomon.code domain 1 : Set (ι → F)) epsStar)
    (hchar : ringChar F = p) (hn : 2 ≤ Fintype.card ι)
    (hsmall : 2 * (Fintype.card ι - 2) < p)
    (hq : Fintype.card F < 2 ^ (128 : ℕ) * (2 * (Fintype.card ι - 2) + 1)) :
    mcaThreshold (ReedSolomon.code domain 1 : Set (ι → F)) epsStar hne <
      latticeIndexOf (ι := ι) (1 : ℝ≥0) le_rfl :=
  mcaThreshold_lt_MCAUpperWitness
    (ReedSolomon.code domain 1 : Set (ι → F)) epsStar hne
    ⟨1, epsStar_lt_epsMCA_one_of_erdos_heilbronn domain hp hchar hn hsmall hq⟩ le_rfl

/-- **Lattice bracketing of the MCA threshold (faithful `mca_threshold_bracketed`).** A
lower witness and an upper witness (at a radius `≤ 1`) bracket the lattice threshold:
`⌊δ_lo·n⌋ ≤ mcaThreshold < ⌊δ_hi·n⌋`. This is the lattice replacement for
`GrandChallenges.mca_threshold_bracketed`, which bracketed the collapse-broken real
threshold of a `GrandMCAResolution`. -/
theorem mcaThresholdLattice_bracketed (C : Set (ι → F)) (ε_star : ℝ≥0)
    (hne : mcaThresholdExists C ε_star)
    (wlo : MCALowerWitness C ε_star)
    (whi : MCAUpperWitness C ε_star) (hδhi : whi.δ ≤ 1) :
    latticeIndexOf (ι := ι) wlo.δ wlo.le_one ≤ mcaThreshold C ε_star hne ∧
      mcaThreshold C ε_star hne < latticeIndexOf (ι := ι) whi.δ hδhi :=
  ⟨MCALowerWitness_le_mcaThreshold C ε_star hne wlo,
    mcaThreshold_lt_MCAUpperWitness C ε_star hne whi hδhi⟩

/-- **Lattice bracketing without a separate existence hypothesis.** The lower witness
both constructs the threshold's nonemptiness proof and supplies the lower bracket. -/
theorem mcaThresholdLattice_bracketed_of_witnesses (C : Set (ι → F)) (ε_star : ℝ≥0)
    (wlo : MCALowerWitness C ε_star)
    (whi : MCAUpperWitness C ε_star) (hδhi : whi.δ ≤ 1) :
    let hne := mcaThresholdExists_of_MCALowerWitness C ε_star wlo
    latticeIndexOf (ι := ι) wlo.δ wlo.le_one ≤ mcaThreshold C ε_star hne ∧
      mcaThreshold C ε_star hne < latticeIndexOf (ι := ι) whi.δ hδhi :=
  mcaThresholdLattice_bracketed C ε_star
    (mcaThresholdExists_of_MCALowerWitness C ε_star wlo) wlo whi hδhi

/-- If a lower MCA witness and an upper MCA witness land on adjacent lattice indices, the
faithful MCA threshold is exactly the lower witness index.  This is the finite-search closing
step: `lo ≤ threshold < lo + 1` pins the threshold. -/
theorem mcaThreshold_eq_latticeIndexOf_lowerWitness_of_adjacent
    (C : Set (ι → F)) (ε_star : ℝ≥0)
    (wlo : MCALowerWitness C ε_star)
    (whi : MCAUpperWitness C ε_star) (hδhi : whi.δ ≤ 1)
    (hadj :
      (latticeIndexOf (ι := ι) whi.δ hδhi).val =
        (latticeIndexOf (ι := ι) wlo.δ wlo.le_one).val + 1) :
    let hne := mcaThresholdExists_of_MCALowerWitness C ε_star wlo
    mcaThreshold C ε_star hne = latticeIndexOf (ι := ι) wlo.δ wlo.le_one := by
  classical
  let hne := mcaThresholdExists_of_MCALowerWitness C ε_star wlo
  let lo := latticeIndexOf (ι := ι) wlo.δ wlo.le_one
  let hi := latticeIndexOf (ι := ι) whi.δ hδhi
  have hbracket :
      lo ≤ mcaThreshold C ε_star hne ∧ mcaThreshold C ε_star hne < hi := by
    simpa [hne, lo, hi] using
      mcaThresholdLattice_bracketed_of_witnesses C ε_star wlo whi hδhi
  have hle : lo.val ≤ (mcaThreshold C ε_star hne).val := by
    exact Fin.le_iff_val_le_val.mp hbracket.1
  have hlt : (mcaThreshold C ε_star hne).val < hi.val := by
    exact Fin.lt_def.mp hbracket.2
  have hval : (mcaThreshold C ε_star hne).val = lo.val := by
    have hadj' : hi.val = lo.val + 1 := by simpa [lo, hi] using hadj
    omega
  ext
  exact hval

/-- Adjacent per-rate MCA lower witnesses and middle-radius spike certificates pin the
faithful MCA lattice thresholds to the lower witness indices.

This is a non-endpoint finite-search closing rule: a Johnson/GS-style lower witness can certify
the candidate lattice point, while the explicit spike family rules out the next one. -/
theorem mcaThreshold_eq_of_lowerWitnesses_and_spike_adjacent
    (domain : ι ↪ F)
    (wlo : ∀ j : Fin 4,
      GrandChallenges.MCALowerWitness
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (t : Fin 4 → ℕ) (δ_hi : Fin 4 → ℝ≥0)
    (hδhi : ∀ j : Fin 4, δ_hi j ≤ 1)
    (ht_n : ∀ j : Fin 4,
      t j + ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ ≤ Fintype.card ι)
    (ht_q : ∀ j : Fin 4, t j ≤ Fintype.card F)
    (hδ : ∀ j : Fin 4,
      ((1 - δ_hi j) * Fintype.card ι : ℝ≥0) ≤
        (Fintype.card ι - t j + 1 : ℕ))
    (hgt : ∀ j : Fin 4,
      (epsStar : ENNReal) < (t j : ENNReal) / (Fintype.card F : ENNReal))
    (hadj : ∀ j : Fin 4,
      (latticeIndexOf (ι := ι) (δ_hi j) (hδhi j)).val =
        (latticeIndexOf (ι := ι) (wlo j).δ (wlo j).le_one).val + 1) :
    ∀ j : Fin 4,
      let C :=
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      let hne := mcaThresholdExists_of_MCALowerWitness C epsStar (wlo j)
      mcaThreshold C epsStar hne =
        latticeIndexOf (ι := ι) (wlo j).δ (wlo j).le_one := by
  intro j
  let C :=
    (ReedSolomon.code domain
      ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
  let whi : GrandChallenges.MCAUpperWitness C epsStar :=
    MCAUpperWitness.ofGt
      (lt_of_lt_of_le (hgt j)
        (epsMCA_ge_spike domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ (t j) (δ_hi j)
          (ht_n j) (ht_q j) (hδ j)))
  let hne := mcaThresholdExists_of_MCALowerWitness C epsStar (wlo j)
  let lo := latticeIndexOf (ι := ι) (wlo j).δ (wlo j).le_one
  let hi := latticeIndexOf (ι := ι) (δ_hi j) (hδhi j)
  have hle : lo.val ≤ (mcaThreshold C epsStar hne).val := by
    exact Fin.le_iff_val_le_val.mp
      (MCALowerWitness_le_mcaThreshold C epsStar hne (wlo j))
  have hlt : (mcaThreshold C epsStar hne).val < hi.val := by
    exact Fin.lt_def.mp (mcaThreshold_lt_MCAUpperWitness C epsStar hne whi (hδhi j))
  have hval : (mcaThreshold C epsStar hne).val = lo.val := by
    have hadj' : hi.val = lo.val + 1 := by simpa [lo, hi] using hadj j
    omega
  exact Fin.ext hval

/-- Adjacent BCHKS25 lower and CS25 upper witnesses determine the faithful MCA lattice
threshold exactly. -/
theorem mcaThreshold_eq_ofJohnsonBCHKS25_and_RSBreakdownCS25_adjacent
    (domain : ι ↪ F) (k : ℕ) (η δ_lo δ_hi ε_star : ℝ≥0)
    (hη : 0 < η)
    (hδ_johnson :
        (δ_lo : ℝ) <
          1 - (((k : ℝ) / Fintype.card ι + 1 / Fintype.card ι) ^ ((1 : ℝ) / 2)) -
            (η : ℝ))
    (hδlo_le_one : δ_lo ≤ 1)
    (hBCHKS25 : CodingTheory.rs_epsMCA_johnson_range_bchks25 domain k η δ_lo
      hη hδ_johnson)
    (hle :
        ENNReal.ofReal
            (let n : ℝ := Fintype.card ι
             let ρ_plus : ℝ := k / n + 1 / n
             let m : ℝ := max ⌈(ρ_plus ^ ((1 : ℝ) / 2)) / (2 * η)⌉ 3
             ((2 * (m + 1 / 2) ^ 5 + 3 * (m + 1 / 2) * δ_lo * ρ_plus) /
                    (3 * ρ_plus ^ ((3 : ℝ) / 2)) *
                  n +
                (m + 1 / 2) / ρ_plus ^ ((1 : ℝ) / 2)) /
               (Fintype.card F : ℝ)) ≤
          (ε_star : ENNReal))
    (hδhi : δ_hi ≤ 1)
    (hq_ge : 10 ≤ Fintype.card F)
    (hδ_cs_lo :
        1 - CodingTheory.qEntropy (Fintype.card F) (δ_hi : ℝ) + 2 / (Fintype.card ι : ℝ)
            + ((CodingTheory.qEntropy (Fintype.card F) (δ_hi : ℝ) - (δ_hi : ℝ))
                / (Fintype.card ι : ℝ)) ^ ((1 : ℝ) / 2)
          ≤ (k : ℝ) / Fintype.card ι)
    (hδ_cs_hi : (k : ℝ) / Fintype.card ι ≤ 1 - (δ_hi : ℝ) - 2 / (Fintype.card ι : ℝ))
    (hCS25 : CodingTheory.rs_epsCA_breakdown_cs25 domain k δ_hi hq_ge hδ_cs_lo hδ_cs_hi)
    (hε : (ε_star : ENNReal) < 1)
    (hadj :
      (latticeIndexOf (ι := ι) δ_hi hδhi).val =
        (latticeIndexOf (ι := ι) δ_lo hδlo_le_one).val + 1) :
    let hne := mcaThresholdExists_ofJohnsonBCHKS25 domain k η δ_lo ε_star hη
      hδ_johnson hδlo_le_one hBCHKS25 hle
    mcaThreshold (ReedSolomon.code domain k : Set (ι → F)) ε_star hne =
      latticeIndexOf (ι := ι) δ_lo hδlo_le_one := by
  let wlo := MCALowerWitness.ofJohnsonBCHKS25 domain k η δ_lo ε_star hη hδ_johnson
    hδlo_le_one hBCHKS25 hle
  let whi := MCAUpperWitness.ofRSBreakdownCS25 domain k δ_hi ε_star hq_ge
    hδ_cs_lo hδ_cs_hi hCS25 hε
  exact mcaThreshold_eq_latticeIndexOf_lowerWitness_of_adjacent
    (ReedSolomon.code domain k : Set (ι → F)) ε_star wlo whi hδhi hadj

/-- Adjacent BCHKS25 lower and DG25 sampling upper witnesses determine the faithful MCA
lattice threshold exactly. -/
theorem mcaThreshold_eq_ofJohnsonBCHKS25_and_SamplingDG25_adjacent
    (domain : ι ↪ F) (k : ℕ) (η δ_lo δ_hi δ' ε_star : ℝ≥0)
    (hη : 0 < η)
    (hδ_johnson :
        (δ_lo : ℝ) <
          1 - (((k : ℝ) / Fintype.card ι + 1 / Fintype.card ι) ^ ((1 : ℝ) / 2)) -
            (η : ℝ))
    (hδlo_le_one : δ_lo ≤ 1)
    (hBCHKS25 : CodingTheory.rs_epsMCA_johnson_range_bchks25 domain k η δ_lo
      hη hδ_johnson)
    (hle :
        ENNReal.ofReal
            (let n : ℝ := Fintype.card ι
             let ρ_plus : ℝ := k / n + 1 / n
             let m : ℝ := max ⌈(ρ_plus ^ ((1 : ℝ) / 2)) / (2 * η)⌉ 3
             ((2 * (m + 1 / 2) ^ 5 + 3 * (m + 1 / 2) * δ_lo * ρ_plus) /
                    (3 * ρ_plus ^ ((3 : ℝ) / 2)) *
                  n +
                (m + 1 / 2) / ρ_plus ^ ((1 : ℝ) / 2)) /
               (Fintype.card F : ℝ)) ≤
          (ε_star : ENNReal))
    (hδhi : δ_hi ≤ 1)
    (hδ' : (δ' : ENNReal) =
      ⨆ u : ι → F, δᵣ(u, (ReedSolomon.code domain k : Set (ι → F))))
    (hδ_pos : 0 < δ_hi) (hδ_lt : δ_hi < δ')
    (hDG25 : CodingTheory.linear_epsCA_ge_sampling_dg25
      (ReedSolomon.code domain k) δ_hi δ' hδ' hδ_pos hδ_lt)
    (hgt :
      ((Fintype.card F - 1 : ℝ≥0) / Fintype.card F : ENNReal)
          * Pr_{
              let u ← $ᵖ (ι → F)
              }[δᵣ(u, (ReedSolomon.code domain k : Set (ι → F))) ≤ δ_hi] >
        (ε_star : ENNReal))
    (hadj :
      (latticeIndexOf (ι := ι) δ_hi hδhi).val =
        (latticeIndexOf (ι := ι) δ_lo hδlo_le_one).val + 1) :
    let hne := mcaThresholdExists_ofJohnsonBCHKS25 domain k η δ_lo ε_star hη
      hδ_johnson hδlo_le_one hBCHKS25 hle
    mcaThreshold (ReedSolomon.code domain k : Set (ι → F)) ε_star hne =
      latticeIndexOf (ι := ι) δ_lo hδlo_le_one := by
  let wlo := MCALowerWitness.ofJohnsonBCHKS25 domain k η δ_lo ε_star hη hδ_johnson
    hδlo_le_one hBCHKS25 hle
  let whi := MCAUpperWitness.ofSamplingDG25 (ReedSolomon.code domain k) δ_hi δ' ε_star
    hδ' hδ_pos hδ_lt hDG25 hgt
  exact mcaThreshold_eq_latticeIndexOf_lowerWitness_of_adjacent
    (ReedSolomon.code domain k : Set (ι → F)) ε_star wlo whi hδhi hadj

/-- Adjacent BCHKS25 lower and generic capacity-side `ε_ca` upper witnesses determine the
faithful MCA lattice threshold exactly. -/
theorem mcaThreshold_eq_ofJohnsonBCHKS25_and_epsCAGt_adjacent
    (domain : ι ↪ F) (k : ℕ) (η δ_lo δ_hi ε_star : ℝ≥0)
    (hη : 0 < η)
    (hδ_johnson :
        (δ_lo : ℝ) <
          1 - (((k : ℝ) / Fintype.card ι + 1 / Fintype.card ι) ^ ((1 : ℝ) / 2)) -
            (η : ℝ))
    (hδlo_le_one : δ_lo ≤ 1)
    (hBCHKS25 : CodingTheory.rs_epsMCA_johnson_range_bchks25 domain k η δ_lo
      hη hδ_johnson)
    (hle :
        ENNReal.ofReal
            (let n : ℝ := Fintype.card ι
             let ρ_plus : ℝ := k / n + 1 / n
             let m : ℝ := max ⌈(ρ_plus ^ ((1 : ℝ) / 2)) / (2 * η)⌉ 3
             ((2 * (m + 1 / 2) ^ 5 + 3 * (m + 1 / 2) * δ_lo * ρ_plus) /
                    (3 * ρ_plus ^ ((3 : ℝ) / 2)) *
                  n +
                (m + 1 / 2) / ρ_plus ^ ((1 : ℝ) / 2)) /
               (Fintype.card F : ℝ)) ≤
          (ε_star : ENNReal))
    (hhi :
      epsCA (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F)) δ_hi δ_hi >
        (ε_star : ENNReal))
    (hδhi : δ_hi ≤ 1)
    (hadj :
      (latticeIndexOf (ι := ι) δ_hi hδhi).val =
        (latticeIndexOf (ι := ι) δ_lo hδlo_le_one).val + 1) :
    let hne := mcaThresholdExists_ofJohnsonBCHKS25 domain k η δ_lo ε_star hη
      hδ_johnson hδlo_le_one hBCHKS25 hle
    mcaThreshold (ReedSolomon.code domain k : Set (ι → F)) ε_star hne =
      latticeIndexOf (ι := ι) δ_lo hδlo_le_one := by
  let wlo := MCALowerWitness.ofJohnsonBCHKS25 domain k η δ_lo ε_star hη hδ_johnson
    hδlo_le_one hBCHKS25 hle
  let whi := MCAUpperWitness.ofEpsCAGt
    (MC := ReedSolomon.code domain k) (ε_star := ε_star) (δ := δ_hi) hhi
  exact mcaThreshold_eq_latticeIndexOf_lowerWitness_of_adjacent
    (ReedSolomon.code domain k : Set (ι → F)) ε_star wlo whi hδhi hadj


end GrandChallengesLattice

end ProximityGap

