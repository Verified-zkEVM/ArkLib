/-
Direct (paper-style) blueprint for Lemma 4.3: main assembly lemma only.
-/

import ArkLib.Data.CodingTheory.InterleavedCode.Defs
import ArkLib.Data.CodingTheory.Basic
import ArkLib.Data.CodingTheory.InterleavedCode.Lemma43.Aux
import ArkLib.Data.CodingTheory.InterleavedCode.Lemma43.Argmax
import ArkLib.Data.CodingTheory.InterleavedCode.Lemma43.RowFreshCoord
import ArkLib.Data.CodingTheory.InterleavedCode.Lemma43.BadAlpha
import ArkLib.Data.CodingTheory.InterleavedCode.Lemma43.Gate3e
import ArkLib.Data.CodingTheory.InterleavedCode.ProximityToRS.Aux
import Mathlib.Tactic

noncomputable section

open InterleavedCode
open Code
open scoped BigOperators

set_option linter.style.longLine false
set_option linter.unnecessarySimpa false

namespace InterleavedCode
namespace Lemma43

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {κ : Type*} [Fintype κ]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-
Main assembly lemma: if `|F| ≥ e+2`, `3e < d(LC)`, and `Δ(U, MF) > e` with
`MF = matrixSubmoduleOfLinearCode κ LC`, then some row-combination of `U`
is strictly farther than `e` from `LC`.
-/
lemma distInterleavedCodeToCodeLB
  {IC : LawfulInterleavedCode κ ι F} {U : Matrix κ ι F} {e : ℕ}
  (hF : Nat.card F ≥ e.succ.succ)
  (he : 3 * e < Code.minDist (IC.1.LC : Set (ι → F)))
  (hU : e < distToCode U IC.1.MF)
  (hMF : IC.1.MF = matrixSubmoduleOfLinearCode κ IC.1.LC) :
  ∃ v ∈ Matrix.rowSpan U , e < distFromCode v IC.1.LC := by
  classical
  -- Contradiction posture: assume no row-combination is > e far from LC.
  by_contra hnone
  have hAll : ∀ v ∈ Matrix.rowSpan U, distFromCode v IC.1.LC ≤ e := by
    intro v hv; have : ¬ e < distFromCode v IC.1.LC := by exact fun hvgt => hnone ⟨v, hv, hvgt⟩
    simpa using (not_lt.mp this)
  -- Pick v₀ maximizing distance in the row span.
  rcases exists_argmax_dist_in_rowSpan (L := (IC.1.LC : Set (ι → F))) (U := U) with ⟨v0, hv0, hmax⟩
  -- Choose a codeword c₀ within ≤ e of v₀; set E₀ := Err v₀ c₀ and t := |E₀| with t ≤ e.
  have hdist_v0 : distFromCode v0 IC.1.LC ≤ e := hAll v0 hv0
  rcases ProximityToRS.exists_codeword_close_of_dist_le
          (u := v0) (C := (IC.1.LC : Set (ι → F))) (e := e) hdist_v0 with ⟨c0, hc0, hv0c0_le⟩
  let E0 : Finset ι := Err (ι := ι) v0 c0
  let t : ℕ := E0.card
  have hE0_le : t ≤ e := by
    -- t = E0.card = hammingDist v0 c0 ≤ e
    simpa [E0, Err, hammingDist, errset_card_eq_hamming] using hv0c0_le
  -- For each row, choose a codeword within ≤ e (by hAll applied to U i ∈ rowSpan U).
  have hUi_in : ∀ i, (U i) ∈ Matrix.rowSpan U := by
    intro i; exact Submodule.subset_span (by change U i ∈ {U k | k : κ}; simp)
  have hex_row : ∀ i, ∃ ci ∈ (IC.1.LC : Set (ι → F)), hammingDist (U i) ci ≤ e := by
    intro i
    have hdist : distFromCode (U i) IC.1.LC ≤ e := hAll (U i) (hUi_in i)
    simpa using
      (ProximityToRS.exists_codeword_close_of_dist_le
        (u := U i) (C := (IC.1.LC : Set (ι → F))) (e := e) hdist)
  classical
  choose c_row hcrow hrowle using hex_row
  -- Build V' with rows equal to c_row; show V' ∈ MF by hMF
  let V' : Matrix κ ι F := fun i j => c_row i j
  have hV'_in : V' ∈ IC.1.MF := by
    have hrows : ∀ i, V' i ∈ IC.1.LC := by intro i; simpa [V'] using (hcrow i)
    have : V' ∈ matrixSubmoduleOfLinearCode κ IC.1.LC := by
      have : V' ∈ {W : Matrix κ ι F | ∀ i, W i ∈ IC.1.LC} := by simpa [V']
      exact Submodule.subset_span this
    simpa [hMF] using this
  -- Use Δ(U,MF) ≤ distCodewords U V' to conclude many bad columns for V'
  have hDist_le : Δ(U, IC.1.MF) ≤ distCodewords U V' := by
    change sInf {d : ℕ | ∃ W ∈ IC.1.MF, distCodewords U W = d} ≤ distCodewords U V'
    refine Nat.sInf_le ?_
    exact ⟨V', hV'_in, rfl⟩
  -- Therefore |neqCols U V'| > e
  set S := Matrix.neqCols U V' with hSdef
  have hScard_gt : e < S.card := by
    have : Δ(U, IC.1.MF) ≤ distCodewords U V' := hDist_le
    have : e < distCodewords U V' := lt_of_lt_of_le hU this
    simpa [S, hSdef] using this
  -- Pick a fresh column j ∈ S \ E0 and the corresponding row i
  have hnot_subset : ¬ S ⊆ Err (ι := ι) v0 c0 := by
    intro hsubset
    have hmono := Finset.card_mono hsubset
    have : S.card ≤ (Err (ι := ι) v0 c0).card := hmono
    exact (not_lt_of_ge (le_trans this hE0_le)) hScard_gt
  have hsel : ∃ j, j ∈ S ∧ j ∉ Err (ι := ι) v0 c0 := by
    by_contra h
    have : S ⊆ Err (ι := ι) v0 c0 := by
      intro j hj
      by_contra hjmem
      exact h ⟨j, hj, hjmem⟩
    exact hnot_subset this
  rcases hsel with ⟨j, hjS, hjNotE0⟩
  have hx' : ∃ i : κ, V' i j ≠ U i j := by
    simpa [S, hSdef, Matrix.neqCols] using hjS
  rcases hx' with ⟨i, hVU'⟩
  have hjUcr : j ∈ Err (ι := ι) (U i) (c_row i) := by
    have hjuniv : j ∈ (Finset.univ : Finset ι) := by simp
    have : U i j ≠ c_row i j := by simpa [V', ne_comm] using hVU'
    simpa [Err, Finset.mem_filter, hjuniv] using this
  -- j is fresh relative to E0 and differs in row i against c_row i
  -- Choose α ∉ Bad with α ≠ 0; weight increases by ≥ 1 at the fresh coordinate j.
  obtain ⟨α, hα0, hα_not_bad⟩ :=
    exists_good_alpha (ι := ι) (e := e) (hF := hF) (E0 := E0)
      (χ0 := fun j => v0 j - c0 j) (χi := fun j => U i j - c_row i j) (t_le_e := hE0_le)
  have hj_new : (U i j - c_row i j) ≠ 0 := by
    -- j ∈ Err(U i, c_row i) ⇒ difference at j is nonzero
    have : j ∈ Err (U i) (c_row i) := hjUcr
    have : (U i j ≠ c_row i j) := by
      have hjuniv : j ∈ (Finset.univ : Finset ι) := by simp
      simpa [Err, Finset.mem_filter, hjuniv] using this
    simpa [sub_eq_zero] using this
  have hj_old : (v0 j - c0 j) = 0 := by
    -- j ∉ E0 ⇒ v0 j = c0 j
    have hjuniv : j ∈ (Finset.univ : Finset ι) := by simp
    have hmem_iff : j ∈ (Finset.univ.filter fun t : ι => v0 t ≠ c0 t) ↔ v0 j ≠ c0 j := by
      simpa [Finset.mem_filter, hjuniv]
    have : ¬ v0 j ≠ c0 j := by
      have hnotmem : j ∉ (Finset.univ.filter fun t : ι => v0 t ≠ c0 t) := by simpa [E0, Err] using hjNotE0
      have hnotiff : (j ∈ (Finset.univ.filter fun t : ι => v0 t ≠ c0 t)) ↔ (v0 j ≠ c0 j) := hmem_iff
      have : ¬ (v0 j ≠ c0 j) := (not_congr hnotiff).mp hnotmem
      exact this
    exact sub_eq_zero.mpr (Classical.not_not.mp this)
  have h_wt : t.succ ≤ hammingNorm (fun t => (v0 t - c0 t) + α * (U i t - c_row i t)) := by
    have hbase : hammingNorm (fun j => v0 j - c0 j) = t := by
      -- ‖v0 - c0‖₀ = hammingDist v0 c0 = E0.card = t
      have : hammingNorm (fun j => v0 j - c0 j) = hammingDist v0 c0 :=
        hammingNorm_sub_eq_hamming _ _
      simpa [E0, t, Err, hammingDist, errset_card_eq_hamming] using this
    have hw_ineq :=
      (weight_increase_by_one (E0 := E0) (χ0 := fun j => v0 j - c0 j) (χi := fun j => U i j - c_row i j)
        (j := j) (hj_new := hj_new) (hj_old := hj_old) (α := α) (hα := hα_not_bad)
        (hE0 := by
          classical
          ext k; simp [E0, Err, sub_eq_zero]))
    simpa [hbase, Nat.add_comm] using hw_ineq
  -- Gate identity: within radius e, the distance equals the distance to c0 + α·c_row i.
  have hgate_eq :
    distFromCode (fun j => v0 j + α * U i j) (IC.1.LC : Set (ι → F))
      = hammingDist (fun j => v0 j + α * U i j) (fun j => c0 j + α * c_row i j) := by
    -- Use gate_distance_identity_3e with hv, hu and he
    have hv' : hammingDist v0 c0 ≤ e := hv0c0_le
    have hu' : hammingDist (U i) (c_row i) ≤ e := hrowle i
    -- Apply gate
    -- Establish membership of v0 + α • U i in the row span (closure under add/smul).
    have hUi_span : (U i) ∈ Matrix.rowSpan U := hUi_in i
    have hαUi_span : (fun j => α * U i j) ∈ Matrix.rowSpan U := by
      exact (Submodule.smul_mem (Matrix.rowSpan U) α hUi_span)
    have hsum_span : (fun j => v0 j + α * U i j) ∈ Matrix.rowSpan U := by
      exact (Submodule.add_mem (Matrix.rowSpan U) hv0 hαUi_span)
    have := gate_distance_identity_3e (L := IC.1.LC) (e := e) (he := he)
      (hc0 := hc0) (hci := hcrow i) (hv := hv') (hu := hu') (α := α)
      (hsmall := hAll (fun j => v0 j + α * U i j) hsum_span)
    simpa using this
  -- Combine with weight lower bound to obtain a strict inequality vs v0 by maximality
  -- First, lower-bound the distance from code at wα by t+1
  have hge : (t.succ : ℕ∞) ≤ distFromCode (fun j => v0 j + α * U i j) (IC.1.LC : Set (ι → F)) := by
    -- distFromCode equals hamming distance to c0 + α·c_row i
    have :
      distFromCode (fun j => v0 j + α * U i j) (IC.1.LC : Set (ι → F))
        = (hammingDist (fun j => v0 j + α * U i j) (fun j => c0 j + α * c_row i j) : ℕ∞) := by
      simpa using hgate_eq
    -- And that hamming distance equals the Hamming weight of (χ0 + α χi)
    have hdiff_eq :
      (fun j => (v0 j + α * U i j) - (c0 j + α * c_row i j))
        = (fun j => (v0 j - c0 j) + α * (U i j - c_row i j)) := by
      funext j; ring
    have hhd_eq :
      hammingDist (fun j => v0 j + α * U i j) (fun j => c0 j + α * c_row i j)
        = hammingNorm (fun j => (v0 j - c0 j) + α * (U i j - c_row i j)) := by
      -- Step 1: Δ(wα,cα) = ‖(wα) - (cα)‖₀
      have hwteq1 :
        hammingDist (fun j => v0 j + α * U i j) (fun j => c0 j + α * c_row i j)
          = hammingNorm ((fun j => v0 j + α * U i j) - (fun j => c0 j + α * c_row i j)) := by
        simpa using (hammingNorm_sub_eq_hamming (v := (fun j => v0 j + α * U i j)) (c := (fun j => c0 j + α * c_row i j))).symm
      -- Step 2: rewrite difference pointwise to χ0 + α χi
      have hwteq2 :
        hammingNorm ((fun j => v0 j + α * U i j) - (fun j => c0 j + α * c_row i j))
          = hammingNorm (fun j => (v0 j - c0 j) + α * (U i j - c_row i j)) := by
        -- transport equality through hammingNorm by congrArg
        exact congrArg hammingNorm hdiff_eq
      exact hwteq1.trans hwteq2
    -- So the distance-from-code is ≥ t+1 by h_wt
    have hnat : (t.succ : ℕ) ≤ hammingDist (fun j => v0 j + α * U i j) (fun j => c0 j + α * c_row i j) := by
      simpa [hhd_eq] using h_wt
    have : (t.succ : ℕ∞) ≤ (hammingDist (fun j => v0 j + α * U i j)
                                  (fun j => c0 j + α * c_row i j) : ℕ∞) := by
      exact_mod_cast hnat
    simpa [hgate_eq] using this
  -- Also, upper-bound the distance from code at v0 by t using c0 as a witness
  have hv0_le_t : distFromCode v0 (IC.1.LC : Set (ι → F)) ≤ (t : ℕ∞) := by
    -- sInf ≤ distance to c0 and that equals t = hammingDist v0 c0 by definition
    have hmem : (hammingDist v0 c0 : ℕ∞) ∈ {d : ℕ∞ | ∃ z ∈ (IC.1.LC : Set (ι → F)), hammingDist v0 z ≤ d} := by
      exact ⟨c0, hc0, by exact_mod_cast (le_of_eq rfl)⟩
    have hsInf_le := sInf_le hmem
    simpa [Code.distFromCode, t] using hsInf_le
  -- Now: distFromCode v0 ≤ t < t+1 ≤ distFromCode wα gives strict inequality
  have h_mem : (fun j => v0 j + α * U i j) ∈ Matrix.rowSpan U := by
    exact Submodule.add_mem _ hv0 ((Submodule.smul_mem _ α) (hUi_in i))
  have h_lt_tsucc : distFromCode v0 (IC.1.LC : Set (ι → F)) < (t.succ : ℕ∞) := by
    have : (distFromCode v0 (IC.1.LC : Set (ι → F))) ≤ (t : ℕ∞) := hv0_le_t
    have : (distFromCode v0 (IC.1.LC : Set (ι → F))) < (t : ℕ∞) + 1 :=
      lt_of_le_of_lt this (by exact_mod_cast Nat.lt_succ_self t)
    simpa using this
  have h_strict : distFromCode v0 (IC.1.LC : Set (ι → F))
                    < distFromCode (fun j => v0 j + α * U i j) (IC.1.LC : Set (ι → F)) :=
    lt_of_lt_of_le h_lt_tsucc hge
  -- Contradiction with maximality of v0 over the row span
  have h_le_all := hmax (fun j => v0 j + α * U i j) h_mem
  exact (not_lt_of_ge h_le_all) h_strict

end Lemma43
end InterleavedCode
