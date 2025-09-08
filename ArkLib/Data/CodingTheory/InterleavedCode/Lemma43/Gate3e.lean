/-
3e-gate lemmas (uniqueness and identity) used in Lemma 4.3.
-/

import ArkLib.Data.CodingTheory.Basic
import ArkLib.Data.CodingTheory.InterleavedCode.Defs
import ArkLib.Data.CodingTheory.InterleavedCode.Lemma43.Aux
import ArkLib.Data.CodingTheory.InterleavedCode.ProximityToRS.Aux
import Mathlib.Tactic

noncomputable section

open Code

namespace InterleavedCode
namespace Lemma43

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {κ : Type*} [Fintype κ]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/--
3e-gate (uniqueness): if `dist v c0 ≤ e` and `dist u ci ≤ e` with `3e < d(L)`,
then for every `α` any codeword within `≤ e` of `v + α•u` must equal `c0 + α•ci`.
-/
lemma gate_unique_close_codeword_3e
  (L : LinearCode ι F) {e : ℕ}
  (he : 3 * e < Code.minDist (L : Set (ι → F)))
  {v u c0 ci : ι → F} (hc0 : c0 ∈ (L : Set (ι → F))) (hci : ci ∈ (L : Set (ι → F)))
  (hv : hammingDist v c0 ≤ e) (hu : hammingDist u ci ≤ e) :
  ∀ α : F, ∀ c ∈ (L : Set (ι → F)), hammingDist (v + fun j => α * u j) c ≤ e →
    c = fun j => c0 j + α * ci j := by
  classical
  intro α c hcL hclose
  -- Notation
  let wα : ι → F := fun j => v j + α * u j
  let cα : ι → F := fun j => c0 j + α * ci j
  -- cα ∈ L by linearity
  have hcα : cα ∈ (L : Set (ι → F)) := by
    have hc0' : c0 ∈ L := by simpa using hc0
    have hci' : (fun j => α * ci j) ∈ L := by
      simpa [Pi.smul_apply, smul_eq_mul] using (Submodule.smul_mem L α (by simpa using hci))
    simpa [cα, Pi.add_def] using (Submodule.add_mem L (by simpa using hc0') (by simpa using hci'))
  -- Bound Δ(wα, cα) ≤ e + e
  have hΔ_wα_cα_le : hammingDist wα cα ≤ e + e := by
    have hv' : Code.wt (fun j => v j - c0 j) ≤ e := by simpa [LinearCode.hammingDist_eq_wt_sub] using hv
    have hu' : Code.wt (fun j => u j - ci j) ≤ e := by simpa [LinearCode.hammingDist_eq_wt_sub] using hu
    have hsub :=
      (ProximityToRS.wt_add_le (x := fun j => v j - c0 j) (y := fun j => α * (u j - ci j)))
    have hsmul : Code.wt (fun j => α * (u j - ci j)) ≤ Code.wt (fun j => u j - ci j) := by
      by_cases hα : α = 0
      · have hzero : (fun j : ι => α * (u j - ci j)) = 0 := by funext j; simpa [hα]
        have : Code.wt (fun j : ι => α * (u j - ci j)) = 0 := by simp [Code.wt_eq_hammingNorm, hzero]
        simpa [this] using (Nat.zero_le (Code.wt (fun j => u j - ci j)))
      · have : hammingNorm (fun j => α * (u j - ci j)) = hammingNorm (fun j => u j - ci j) :=
          hammingNorm_smul_eq_of_ne_zero α hα (fun j => u j - ci j)
        simpa [Code.wt_eq_hammingNorm] using le_of_eq this
    have : Code.wt (fun j => (v j - c0 j) + α * (u j - ci j)) ≤ e + e :=
      (le_trans hsub (add_le_add hv' (le_trans hsmul hu')))
    -- Convert to Hamming distance bound via difference identity
    have hdiff : (fun j => wα j - cα j) = (fun j => (v j - c0 j) + α * (u j - ci j)) := by
      funext j; simp [wα, cα, add_comm, add_left_comm, add_assoc, sub_eq_add_neg, mul_add]
    have hwt_wαcα : Code.wt (wα - cα) ≤ e + e := by
      simpa [Pi.sub_def, hdiff] using this
    simpa [LinearCode.hammingDist_eq_wt_sub] using hwt_wαcα
  -- Triangle: Δ(c, cα) ≤ Δ(c, wα) + Δ(wα, cα) ≤ 3e
  have hΔ_ccα_lt : hammingDist c cα < Code.minDist (L : Set (ι → F)) := by
    have htri := hammingDist_triangle c wα cα
    have hclose' : hammingDist c wα ≤ e := by simpa [wα, hammingDist_comm] using hclose
    have hbound : hammingDist c cα ≤ e + (e + e) := le_trans htri (by exact add_le_add hclose' hΔ_wα_cα_le)
    have h3e_lt : e + (e + e) < Code.minDist (L : Set (ι → F)) := by
      simpa [Nat.succ_mul, two_mul, add_comm, add_left_comm, add_assoc] using he
    exact lt_of_le_of_lt hbound h3e_lt
  -- Conclude equality
  by_contra hneq
  have hmin_le : Code.minDist (L : Set (ι → F)) ≤ hammingDist c cα := by
    have hwit : ∃ u ∈ (L : Set (ι → F)), ∃ v ∈ (L : Set (ι → F)), u ≠ v ∧ hammingDist u v = hammingDist c cα := by
      exact ⟨c, hcL, cα, hcα, hneq, rfl⟩
    exact Nat.sInf_le (Set.mem_setOf.mpr hwit)
  exact (not_lt_of_ge hmin_le) hΔ_ccα_lt

/--
3e-gate (identity): under the hypotheses of the previous lemma, whenever
`distFromCode (v + α•u) L ≤ e` it must equal the distance to `c0 + α•ci`.
-/
lemma gate_distance_identity_3e
  (L : LinearCode ι F) {e : ℕ}
  (he : 3 * e < Code.minDist (L : Set (ι → F)))
  {v u c0 ci : ι → F} (hc0 : c0 ∈ (L : Set (ι → F))) (hci : ci ∈ (L : Set (ι → F)))
  (hv : hammingDist v c0 ≤ e) (hu : hammingDist u ci ≤ e)
  (α : F)
  (hsmall : distFromCode (v + fun j => α * u j) (L : Set (ι → F)) ≤ e) :
  distFromCode (v + fun j => α * u j) (L : Set (ι → F))
    = hammingDist (v + fun j => α * u j) (fun j => c0 j + α * ci j) := by
  classical
  -- Notation: wα and cα
  let wα : ι → F := fun j => v j + α * u j
  let cα : ι → F := fun j => c0 j + α * ci j
  -- cα ∈ L by linearity
  have hcα : cα ∈ (L : Set (ι → F)) := by
    have hmem_add : (c0 + fun j => α * ci j) ∈ (L : Set (ι → F)) := by
      have hc0' : c0 ∈ L := by simpa using hc0
      have hci' : (fun j => α * ci j) ∈ L := by
        simpa [Pi.smul_apply, smul_eq_mul] using (Submodule.smul_mem L α (by simpa using hci))
      simpa using (Submodule.add_mem L (by simpa using hc0') (by simpa using hci'))
    simpa [cα, Pi.add_def] using hmem_add
  -- Pick a close codeword to wα within radius e
  rcases ProximityToRS.exists_codeword_close_of_dist_le
          (u := wα) (C := (L : Set (ι → F))) (e := e) hsmall
        with ⟨c, hcL, hwαc_le⟩
  -- Bound Δ(wα, cα) ≤ 2e using subadditivity and scaling bound
  have hΔ_wα_cα_le : hammingDist wα cα ≤ e + e := by
    have hv' : Code.wt (fun j => v j - c0 j) ≤ e := by
      simpa [LinearCode.hammingDist_eq_wt_sub] using hv
    have hu' : Code.wt (fun j => u j - ci j) ≤ e := by
      simpa [LinearCode.hammingDist_eq_wt_sub] using hu
    have hsub :
        Code.wt (fun j => (v j - c0 j) + α * (u j - ci j))
          ≤ Code.wt (fun j => v j - c0 j) + Code.wt (fun j => α * (u j - ci j)) := by
      simpa using (ProximityToRS.wt_add_le (x := (fun j => v j - c0 j)) (y := (fun j => α * (u j - ci j))))
    have hsmul : Code.wt (fun j => α * (u j - ci j)) ≤ Code.wt (fun j => u j - ci j) := by
      by_cases hα : α = 0
      · have hzero : (fun j : ι => α * (u j - ci j)) = 0 := by funext j; simpa [hα]
        have : Code.wt (fun j : ι => α * (u j - ci j)) = 0 := by simp [Code.wt_eq_hammingNorm, hzero]
        simpa [this] using (Nat.zero_le (Code.wt (fun j => u j - ci j)))
      · have : hammingNorm (fun j => α * (u j - ci j)) = hammingNorm (fun j => u j - ci j) :=
          hammingNorm_smul_eq_of_ne_zero α hα (fun j => u j - ci j)
        simpa [Code.wt_eq_hammingNorm] using le_of_eq this
    have : Code.wt (fun j => (v j - c0 j) + α * (u j - ci j)) ≤ e + e :=
      (le_trans hsub (add_le_add hv' (le_trans hsmul hu')))
    have hdiff : (fun j => wα j - cα j) = (fun j => (v j - c0 j) + α * (u j - ci j)) := by
      funext j; simp [wα, cα, add_comm, add_left_comm, add_assoc, sub_eq_add_neg, mul_add]
    have hwt_wαcα : Code.wt (wα - cα) ≤ e + e := by
      simpa [Pi.sub_def, hdiff] using this
    simpa [LinearCode.hammingDist_eq_wt_sub] using hwt_wαcα
  -- Show distFromCode equals Δ(wα, v) for a minimizer v ∈ L
  -- Work in the finite set of codewords
  have hCfin : ((L : Set (ι → F)) : Set (ι → F)).Finite := Set.toFinite _
  -- pick a concrete element in L as a seed for min_image
  let w0 := c
  have hw0L : w0 ∈ (L : Set (ι → F)) := hcL
  have hw0mem : w0 ∈ hCfin.toFinset := by simpa using hCfin.mem_toFinset.mpr hw0L
  obtain ⟨vmin, hv_in, hmin⟩ :=
    Finset.exists_min_image (s := hCfin.toFinset)
      (f := fun x : (ι → F) => hammingDist wα x)
      ⟨w0, hw0mem⟩
  have hvL : vmin ∈ (L : Set (ι → F)) := hCfin.mem_toFinset.mp hv_in
  -- distFromCode ≤ Δ(wα, v)
  have h_le : distFromCode wα (L : Set (ι → F)) ≤ (hammingDist wα vmin : ℕ∞) := by
    have hmem : (hammingDist wα vmin : ℕ∞)
        ∈ {d : ℕ∞ | ∃ z ∈ (L : Set (ι → F)), hammingDist wα z ≤ d} := by
      exact ⟨vmin, hvL, by simp⟩
    simpa [Code.distFromCode] using sInf_le hmem
  -- (Δ(wα, v)) ≤ distFromCode via minimality
  have h_ge : (hammingDist wα vmin : ℕ∞) ≤ distFromCode wα (L : Set (ι → F)) := by
    -- Any element of the defining set is ≥ Δ(wα, v)
    have hLB : ∀ d ∈ {d : ℕ∞ | ∃ z ∈ (L : Set (ι → F)), hammingDist wα z ≤ d},
        (hammingDist wα vmin : ℕ∞) ≤ d := by
      intro d hd; rcases hd with ⟨z, hzL, hΔz_le_d⟩
      -- by minimality, Δ(wα, v) ≤ Δ(wα, z)
      have hz_in : z ∈ hCfin.toFinset := hCfin.mem_toFinset.mpr hzL
      have : hammingDist wα vmin ≤ hammingDist wα z := hmin z hz_in
      exact le_trans (by exact_mod_cast this) hΔz_le_d
    -- Apply le_csInf
    have : (hammingDist wα vmin : ℕ∞)
        ≤ sInf {d : ℕ∞ | ∃ z ∈ (L : Set (ι → F)), hammingDist wα z ≤ d} := by
      apply le_csInf
      · refine ⟨(hammingDist wα w0 : ℕ∞), ?_⟩; exact ⟨w0, hw0L, by simp⟩
      · intro d hd; exact hLB d hd
    simpa [Code.distFromCode] using this
  have h_eq_min : distFromCode wα (L : Set (ι → F)) = (hammingDist wα vmin : ℕ∞) :=
    le_antisymm h_le h_ge
  -- Since distFromCode ≤ e, the minimizer v is within radius e and is unique, so v = cα
  have hΔv_le_e : hammingDist wα vmin ≤ e := by
    have hdist_le : distFromCode wα (L : Set (ι → F)) ≤ e := by
      simpa [wα] using hsmall
    have : (hammingDist wα vmin : ℕ∞) ≤ e := by simpa [h_eq_min] using hdist_le
    exact (by exact_mod_cast this)
  have hv_eq : vmin = cα :=
    gate_unique_close_codeword_3e (L := L) (e := e) (he := he) (hc0 := hc0) (hci := hci)
      (hv := hv) (hu := hu) α vmin hvL hΔv_le_e
  -- Conclude the desired identity by rewriting the minimizer to cα and unfolding notation
  have h5 :
      distFromCode (v + fun j => α * u j) (L : Set (ι → F))
        = (hammingDist (v + fun j => α * u j) cα : ℕ∞) := by
    -- combine the minimizer identity and uniqueness (vmin = cα)
    simpa [wα, hv_eq] using h_eq_min
  simpa [cα] using h5

end Lemma43
end InterleavedCode
