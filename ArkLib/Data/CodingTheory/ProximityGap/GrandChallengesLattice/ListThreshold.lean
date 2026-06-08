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
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallengesLattice.WitnessBridge

/-!
# GrandChallengesLattice — ListThreshold

List-decoding lattice threshold mirror of MCA development.

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

/-! ## The list-decoding lattice threshold

The exact mirror of the MCA development, with the maximised list size `Λ(C^⋈m, δ)` (ABF26
D2.8) in place of `ε_mca`, the threshold `ε*·|F|` in place of `ε*`, and `lambda_coe_mono`
in place of `epsMCA_mono`. -/

open ListDecodable

/-- `Λ(C^⋈m, j/n) ≤ ε*·|F|` at the lattice radius `j/n`. -/
def listSatisfies (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0)
    (j : Fin (Fintype.card ι + 1)) : Prop :=
  (Lambda (C^⋈ (Fin m)) ((mcaLatticePoint (Fintype.card ι) j : ℝ≥0) : ℝ) : ENNReal) ≤
    ((ε_star : ENNReal) * (Fintype.card F : ENNReal))

noncomputable instance (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0) :
    DecidablePred (listSatisfies C m ε_star) := fun _ => Classical.propDecidable _

/-- **Downward closure** for list decoding, from `lambda_coe_mono`. -/
theorem listSatisfies_downward_closed (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0)
    {i j : Fin (Fintype.card ι + 1)} (hij : i ≤ j) (hj : listSatisfies C m ε_star j) :
    listSatisfies C m ε_star i :=
  le_trans (GrandChallenges.lambda_coe_mono (mcaLatticePoint_mono _ hij)) hj

/-- The satisfying lattice points for the list-decoding bound. -/
noncomputable def listSatSet (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0) :
    Finset (Fin (Fintype.card ι + 1)) :=
  Finset.univ.filter (listSatisfies C m ε_star)

@[simp] theorem mem_listSatSet (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0)
    {j : Fin (Fintype.card ι + 1)} :
    j ∈ listSatSet C m ε_star ↔ listSatisfies C m ε_star j := by
  simp [listSatSet]

/-- Bridge from the `Fin (n+1)` list lattice encoding to the canonical `Finset ℕ`
encoding in `GrandChallengeLattice.lean`. -/
theorem val_mem_listLatticeSet_iff_listSatisfies
    (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0)
    (j : Fin (Fintype.card ι + 1)) :
    j.val ∈ GrandChallenges.listLatticeSet C m ε_star ↔ listSatisfies C m ε_star j := by
  classical
  rw [GrandChallenges.listLatticeSet, Finset.mem_filter, Finset.mem_range]
  simp [listSatisfies, mcaLatticePoint, j.isLt]

/-- **Existence (nonemptiness) hypothesis** for the list-decoding lattice threshold. -/
def listThresholdExists (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0) : Prop :=
  ∃ j : Fin (Fintype.card ι + 1), listSatisfies C m ε_star j

theorem listSatSet_nonempty_iff_listLatticeSet_nonempty
    (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0) :
    (listSatSet C m ε_star).Nonempty ↔
      (GrandChallenges.listLatticeSet C m ε_star).Nonempty := by
  classical
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨j.val, (val_mem_listLatticeSet_iff_listSatisfies C m ε_star j).mpr
      ((mem_listSatSet C m ε_star).mp hj)⟩
  · rintro ⟨j, hj⟩
    have hj_range : j < Fintype.card ι + 1 := by
      rw [GrandChallenges.listLatticeSet, Finset.mem_filter, Finset.mem_range] at hj
      exact hj.1
    exact ⟨⟨j, hj_range⟩, (mem_listSatSet C m ε_star).mpr
      ((val_mem_listLatticeSet_iff_listSatisfies C m ε_star ⟨j, hj_range⟩).mp hj)⟩

theorem listSatSet_nonempty_iff (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0) :
    (listSatSet C m ε_star).Nonempty ↔ listThresholdExists C m ε_star := by
  constructor
  · rintro ⟨j, hj⟩; exact ⟨j, (mem_listSatSet C m ε_star).mp hj⟩
  · rintro ⟨j, hj⟩; exact ⟨j, (mem_listSatSet C m ε_star).mpr hj⟩

/-- **The faithful list-decoding lattice threshold.** The greatest lattice index whose
radius keeps `Λ(C^⋈m, ·) ≤ ε*·|F|`, under the existence hypothesis. **Determining its value
is the open ABF26 §1 Grand List Decoding Challenge**; the witnesses bracket it. -/
noncomputable def listThreshold (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0)
    (hne : listThresholdExists C m ε_star) : Fin (Fintype.card ι + 1) :=
  (listSatSet C m ε_star).max' ((listSatSet_nonempty_iff C m ε_star).mpr hne)

/-- **Existence half.** The list threshold satisfies the bound. -/
theorem listThreshold_spec (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0)
    (hne : listThresholdExists C m ε_star) :
    listSatisfies C m ε_star (listThreshold C m ε_star hne) := by
  have h := (listSatSet C m ε_star).max'_mem ((listSatSet_nonempty_iff C m ε_star).mpr hne)
  exact (mem_listSatSet C m ε_star).mp h

/-- **Maximality.** Every satisfying lattice point is `≤ listThreshold`. -/
theorem le_listThreshold (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0)
    (hne : listThresholdExists C m ε_star) {j : Fin (Fintype.card ι + 1)}
    (hj : listSatisfies C m ε_star j) :
    j ≤ listThreshold C m ε_star hne :=
  (listSatSet C m ε_star).le_max' j ((mem_listSatSet C m ε_star).mpr hj)

/-- The `Fin (n+1)` list threshold and the canonical `Finset ℕ` list threshold have the
same value under `Fin.val`. -/
theorem listThreshold_val_eq_listLatticeThreshold
    (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0)
    (hne_fin : listThresholdExists C m ε_star)
    (hne_nat : (GrandChallenges.listLatticeSet C m ε_star).Nonempty) :
    (listThreshold C m ε_star hne_fin).val =
      GrandChallenges.listLatticeThreshold C m ε_star hne_nat := by
  classical
  apply le_antisymm
  · have hsat := listThreshold_spec C m ε_star hne_fin
    exact Finset.le_max' (GrandChallenges.listLatticeSet C m ε_star)
      (listThreshold C m ε_star hne_fin).val
      ((val_mem_listLatticeSet_iff_listSatisfies C m ε_star
        (listThreshold C m ε_star hne_fin)).mpr hsat)
  · have hmem :=
      (GrandChallenges.listLatticeSet C m ε_star).max'_mem hne_nat
    have hmem_set :
        GrandChallenges.listLatticeThreshold C m ε_star hne_nat ∈
          GrandChallenges.listLatticeSet C m ε_star := by
      simpa [GrandChallenges.listLatticeThreshold] using hmem
    have hrange : GrandChallenges.listLatticeThreshold C m ε_star hne_nat <
        Fintype.card ι + 1 := by
      have h := hmem_set
      simp [GrandChallenges.listLatticeSet] at h
      exact Nat.lt_succ_of_le h.1
    have hsat :
        listSatisfies C m ε_star
          ⟨GrandChallenges.listLatticeThreshold C m ε_star hne_nat, hrange⟩ :=
      (val_mem_listLatticeSet_iff_listSatisfies C m ε_star
        ⟨GrandChallenges.listLatticeThreshold C m ε_star hne_nat, hrange⟩).mp hmem_set
    exact Fin.le_iff_val_le_val.mp (le_listThreshold C m ε_star hne_fin hsat)

/-- **Strict failure above the threshold.** -/
theorem gt_listThreshold_exceeds (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0)
    (hne : listThresholdExists C m ε_star) {j : Fin (Fintype.card ι + 1)}
    (hj : listThreshold C m ε_star hne < j) :
    (Lambda (C^⋈ (Fin m)) ((mcaLatticePoint (Fintype.card ι) j : ℝ≥0) : ℝ) : ENNReal) >
      ((ε_star : ENNReal) * (Fintype.card F : ENNReal)) := by
  by_contra h
  exact absurd (le_listThreshold C m ε_star hne (not_lt.mp h)) (not_le.mpr hj)

/-- **Uniqueness.** `listThreshold` is the unique maximal satisfying lattice index. -/
theorem listThreshold_unique (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0)
    (hne : listThresholdExists C m ε_star) (j : Fin (Fintype.card ι + 1))
    (hsat : listSatisfies C m ε_star j)
    (hmax : ∀ i : Fin (Fintype.card ι + 1), listSatisfies C m ε_star i → i ≤ j) :
    j = listThreshold C m ε_star hne :=
  le_antisymm (le_listThreshold C m ε_star hne hsat)
    (hmax _ (listThreshold_spec C m ε_star hne))

/-- `Λ` at a real radius equals `Λ` at its lattice point `⌊δ·n⌋/n` (step structure). -/
theorem Lambda_eq_at_latticeIndex (C : Set (ι → F)) (m : ℕ) (δ : ℝ≥0) (hδ : δ ≤ 1) :
    (Lambda (C^⋈ (Fin m)) ((δ : ℝ≥0) : ℝ) : ENNReal) =
      (Lambda (C^⋈ (Fin m))
        ((mcaLatticePoint (Fintype.card ι)
            (latticeIndexOf (ι := ι) δ hδ) : ℝ≥0) : ℝ) : ENNReal) := by
  have hn : 0 < Fintype.card ι := Fintype.card_pos
  congr 1
  refine Lambda_eq_of_floor_eq (C^⋈ (Fin m)) ?_
  rw [floor_mcaLatticePoint _ hn, latticeIndexOf_val]

/-- **Lower bracket.** A `ListLowerWitness` forces `⌊δ·n⌋ ≤ listThreshold`. -/
theorem ListLowerWitness_le_listThreshold (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0)
    (hne : listThresholdExists C m ε_star)
    (w : GrandChallenges.ListLowerWitness C m ε_star) :
    latticeIndexOf (ι := ι) w.δ w.le_one ≤ listThreshold C m ε_star hne := by
  refine le_listThreshold C m ε_star hne ?_
  unfold listSatisfies
  rw [← Lambda_eq_at_latticeIndex C m w.δ w.le_one]
  exact w.bound

/-- A lower list-decoding witness is enough to make the faithful list threshold exist. -/
theorem listThresholdExists_of_ListLowerWitness (C : Set (ι → F)) (m : ℕ)
    (ε_star : ℝ≥0) (w : GrandChallenges.ListLowerWitness C m ε_star) :
    listThresholdExists C m ε_star :=
  ⟨latticeIndexOf (ι := ι) w.δ w.le_one, by
    unfold listSatisfies
    rw [← Lambda_eq_at_latticeIndex C m w.δ w.le_one]
    exact w.bound⟩

/-- The faithful list-decoding threshold obtained from a lower witness satisfies the list
bound. -/
theorem listThreshold_spec_of_ListLowerWitness (C : Set (ι → F)) (m : ℕ)
    (ε_star : ℝ≥0) (w : GrandChallenges.ListLowerWitness C m ε_star) :
    let hne := listThresholdExists_of_ListLowerWitness C m ε_star w
    listSatisfies C m ε_star (listThreshold C m ε_star hne) :=
  listThreshold_spec C m ε_star (listThresholdExists_of_ListLowerWitness C m ε_star w)

/-- **Upper bracket.** A `ListUpperWitness` at a radius `δ ≤ 1` forces
`listThreshold < ⌊δ·n⌋`. -/
theorem listThreshold_lt_ListUpperWitness (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0)
    (hne : listThresholdExists C m ε_star)
    (w : GrandChallenges.ListUpperWitness C m ε_star) (hδ : w.δ ≤ 1) :
    listThreshold C m ε_star hne < latticeIndexOf (ι := ι) w.δ hδ := by
  by_contra h
  push Not at h
  have hsat : listSatisfies C m ε_star (latticeIndexOf (ι := ι) w.δ hδ) :=
    listSatisfies_downward_closed C m ε_star h (listThreshold_spec C m ε_star hne)
  have hb : (Lambda (C^⋈ (Fin m))
          ((mcaLatticePoint (Fintype.card ι) (latticeIndexOf (ι := ι) w.δ hδ) : ℝ≥0) : ℝ) : ENNReal)
      ≤ ((ε_star : ENNReal) * (Fintype.card F : ENNReal)) := hsat
  rw [← Lambda_eq_at_latticeIndex C m w.δ hδ] at hb
  exact absurd hb (not_le.mpr w.exceeds)

/-- A strict `Λ` lower bound gives a lattice upper bracket on the faithful list threshold. -/
theorem listThreshold_lt_ofLambdaGt (C : Set (ι → F)) (m : ℕ) {ε_star δ : ℝ≥0}
    (hne : listThresholdExists C m ε_star)
    (h : (Lambda (C^⋈ (Fin m)) (δ : ℝ) : ENNReal) >
      ((ε_star : ENNReal) * (Fintype.card F : ENNReal)))
    (hδ : δ ≤ 1) :
    listThreshold C m ε_star hne < latticeIndexOf (ι := ι) δ hδ :=
  listThreshold_lt_ListUpperWitness C m ε_star hne
    (GrandChallenges.ListUpperWitness.ofGt h) hδ

/-- A lower list witness and a strict `Λ` upper-side bound bracket the faithful list lattice
threshold directly. -/
theorem listThresholdLattice_bracketed_of_lowerWitness_and_LambdaGt
    (C : Set (ι → F)) (m : ℕ) {ε_star δ_hi : ℝ≥0}
    (wlo : GrandChallenges.ListLowerWitness C m ε_star)
    (hhi : (Lambda (C^⋈ (Fin m)) (δ_hi : ℝ) : ENNReal) >
      ((ε_star : ENNReal) * (Fintype.card F : ENNReal)))
    (hδhi : δ_hi ≤ 1) :
    let hne := listThresholdExists_of_ListLowerWitness C m ε_star wlo
    latticeIndexOf (ι := ι) wlo.δ wlo.le_one ≤ listThreshold C m ε_star hne ∧
      listThreshold C m ε_star hne < latticeIndexOf (ι := ι) δ_hi hδhi :=
  ⟨ListLowerWitness_le_listThreshold C m ε_star
      (listThresholdExists_of_ListLowerWitness C m ε_star wlo) wlo,
    listThreshold_lt_ofLambdaGt C m
      (listThresholdExists_of_ListLowerWitness C m ε_star wlo) hhi hδhi⟩

/-- **Lattice bracketing of the list-decoding threshold (faithful prize-progress edge).**
A lower witness and an upper witness (at a radius `≤ 1`) bracket the lattice threshold:
`⌊δ_lo·n⌋ ≤ listThreshold < ⌊δ_hi·n⌋`. The list-decoding mirror of
`mcaThresholdLattice_bracketed`. -/
theorem listThresholdLattice_bracketed (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0)
    (hne : listThresholdExists C m ε_star)
    (wlo : GrandChallenges.ListLowerWitness C m ε_star)
    (whi : GrandChallenges.ListUpperWitness C m ε_star) (hδhi : whi.δ ≤ 1) :
    latticeIndexOf (ι := ι) wlo.δ wlo.le_one ≤ listThreshold C m ε_star hne ∧
      listThreshold C m ε_star hne < latticeIndexOf (ι := ι) whi.δ hδhi :=
  ⟨ListLowerWitness_le_listThreshold C m ε_star hne wlo,
    listThreshold_lt_ListUpperWitness C m ε_star hne whi hδhi⟩

/-- **List-threshold bracketing without a separate existence hypothesis.** The lower witness
constructs the threshold's nonemptiness proof and supplies the lower bracket. -/
theorem listThresholdLattice_bracketed_of_witnesses (C : Set (ι → F)) (m : ℕ)
    (ε_star : ℝ≥0)
    (wlo : GrandChallenges.ListLowerWitness C m ε_star)
    (whi : GrandChallenges.ListUpperWitness C m ε_star) (hδhi : whi.δ ≤ 1) :
    let hne := listThresholdExists_of_ListLowerWitness C m ε_star wlo
    latticeIndexOf (ι := ι) wlo.δ wlo.le_one ≤ listThreshold C m ε_star hne ∧
      listThreshold C m ε_star hne < latticeIndexOf (ι := ι) whi.δ hδhi :=
  listThresholdLattice_bracketed C m ε_star
    (listThresholdExists_of_ListLowerWitness C m ε_star wlo) wlo whi hδhi

/-- If a lower list witness and an upper list witness land on adjacent lattice indices, the
faithful list-decoding threshold is exactly the lower witness index. -/
theorem listThreshold_eq_latticeIndexOf_lowerWitness_of_adjacent
    (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0)
    (wlo : GrandChallenges.ListLowerWitness C m ε_star)
    (whi : GrandChallenges.ListUpperWitness C m ε_star) (hδhi : whi.δ ≤ 1)
    (hadj :
      (latticeIndexOf (ι := ι) whi.δ hδhi).val =
        (latticeIndexOf (ι := ι) wlo.δ wlo.le_one).val + 1) :
    let hne := listThresholdExists_of_ListLowerWitness C m ε_star wlo
    listThreshold C m ε_star hne = latticeIndexOf (ι := ι) wlo.δ wlo.le_one := by
  classical
  let hne := listThresholdExists_of_ListLowerWitness C m ε_star wlo
  let lo := latticeIndexOf (ι := ι) wlo.δ wlo.le_one
  let hi := latticeIndexOf (ι := ι) whi.δ hδhi
  have hbracket :
      lo ≤ listThreshold C m ε_star hne ∧ listThreshold C m ε_star hne < hi := by
    simpa [hne, lo, hi] using
      listThresholdLattice_bracketed_of_witnesses C m ε_star wlo whi hδhi
  have hle : lo.val ≤ (listThreshold C m ε_star hne).val := by
    exact Fin.le_iff_val_le_val.mp hbracket.1
  have hlt : (listThreshold C m ε_star hne).val < hi.val := by
    exact Fin.lt_def.mp hbracket.2
  have hval : (listThreshold C m ε_star hne).val = lo.val := by
    have hadj' : hi.val = lo.val + 1 := by simpa [lo, hi] using hadj
    omega
  ext
  exact hval

end GrandChallengesLattice

end ProximityGap

