/-
Triple-combination zero lemmas used by affine parametrization.
-/

import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.InterleavedCode.ProximityToRS.Lemma44.MinDistHelpers
import ArkLib.Data.CodingTheory.InterleavedCode.ProximityToRS.ThreeClosePoints
import Mathlib.Tactic

noncomputable section

open Code

namespace ProximityToRS

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype F] [DecidableEq ι] in
/-- Appendix A: Under `3*e < minDist(RS)`, the triple combination must be zero. -/
lemma triple_combo_is_zero
  (RS : LinearCode ι F) {e : ℕ}
  (he : 3 * e < Code.minDist (RS : Set (ι → F)))
  {a b c : F} {fa fb fc : ι → F}
  (hfa : fa ∈ (RS : Set (ι → F))) (hfb : fb ∈ (RS : Set (ι → F))) (hfc : fc ∈ (RS : Set (ι → F)))
  (hwt : Code.wt ((a - b) • fc + (b - c) • fa + (c - a) • fb) ≤ 3 * e) :
  (a - b) • fc + (b - c) • fa + (c - a) • fb = 0 := by
  classical
  -- The triple linear combination is a codeword in RS by closure under add and smul.
  have hfa' : fa ∈ (RS : Submodule F (ι → F)) := by simpa using hfa
  have hfb' : fb ∈ (RS : Submodule F (ι → F)) := by simpa using hfb
  have hfc' : fc ∈ (RS : Submodule F (ι → F)) := by simpa using hfc
  have hmem_RS :
      (a - b) • fc + (b - c) • fa + (c - a) • fb ∈ (RS : Set (ι → F)) := by
    -- Use Submodule closure operations
    have h1 : (a - b) • fc ∈ (RS : Submodule F (ι → F)) := by
      simpa using Submodule.smul_mem RS (a - b) hfc'
    have h2 : (b - c) • fa ∈ (RS : Submodule F (ι → F)) := by
      simpa using Submodule.smul_mem RS (b - c) hfa'
    have h3 : (c - a) • fb ∈ (RS : Submodule F (ι → F)) := by
      simpa using Submodule.smul_mem RS (c - a) hfb'
    have h12 : (a - b) • fc + (b - c) • fa ∈ (RS : Submodule F (ι → F)) := by
      simpa using Submodule.add_mem RS h1 h2
    have h123 : (a - b) • fc + (b - c) • fa + (c - a) • fb ∈ (RS : Submodule F (ι → F)) := by
      simpa using Submodule.add_mem RS h12 h3
    simpa using h123
  -- Turn the ≤ and < into a strict inequality via transitivity: wt < minDist
  have hlt : Code.wt ((a - b) • fc + (b - c) • fa + (c - a) • fb)
      < Code.minDist (RS : Set (ι → F)) := lt_of_le_of_lt hwt he
  -- Apply the general helper specialized to RS
  exact zero_of_wt_lt_minDist (L := RS) hmem_RS hlt

/-- Using `three_close_points_weight_bound`, the triple combination of
three `e`-close RS codewords along the line is the zero codeword when `3*e < minDist(RS)`. -/
lemma three_close_points_combo_is_zero
  (RS : LinearCode ι F) {e : ℕ} (u v : ι → F)
  (he : 3 * e < Code.minDist (RS : Set (ι → F)))
  {a b c : F} {fa fb fc : ι → F}
  (hfa : fa ∈ (RS : Set (ι → F))) (hfb : fb ∈ (RS : Set (ι → F))) (hfc : fc ∈ (RS : Set (ι → F)))
  (hwa : Δ₀(u + a • v, fa) ≤ e) (hwb : Δ₀(u + b • v, fb) ≤ e) (hwc : Δ₀(u + c • v, fc) ≤ e) :
  (a - b) • fc + (b - c) • fa + (c - a) • fb = 0 := by
  classical
  -- Use the shared weight bound and then apply the zero lemma.
  have hwt : Code.wt ((b - c) • fa + (c - a) • fb + (a - b) • fc) ≤ 3 * e := by
    -- Import from ThreeClosePoints; note the order of terms matches by commutativity.
    simpa [add_comm, add_left_comm, add_assoc]
      using (three_close_points_weight_bound (a := a) (b := b) (c := c)
        (u := u) (v := v) (wₐ := fa) (w_b := fb) (w_c := fc) hwa hwb hwc)
  -- The combination is a codeword in RS by closure (smul, add)
  have hfa' : fa ∈ (RS : Submodule F (ι → F)) := by simpa using hfa
  have hfb' : fb ∈ (RS : Submodule F (ι → F)) := by simpa using hfb
  have hfc' : fc ∈ (RS : Submodule F (ι → F)) := by simpa using hfc
  have hmem_RS : (a - b) • fc + (b - c) • fa + (c - a) • fb ∈ (RS : Set (ι → F)) := by
    have h1 : (a - b) • fc ∈ (RS : Submodule F (ι → F)) := by
      simpa using Submodule.smul_mem RS (a - b) hfc'
    have h2 : (b - c) • fa ∈ (RS : Submodule F (ι → F)) := by
      simpa using Submodule.smul_mem RS (b - c) hfa'
    have h3 : (c - a) • fb ∈ (RS : Submodule F (ι → F)) := by
      simpa using Submodule.smul_mem RS (c - a) hfb'
    have h12 := Submodule.add_mem RS h1 h2
    have h123 := Submodule.add_mem RS h12 h3
    simpa using h123
  -- Reorder hwt to the expected sum and conclude
  have hwt' : Code.wt ((a - b) • fc + (b - c) • fa + (c - a) • fb) ≤ 3 * e := by
    simpa [add_comm, add_left_comm, add_assoc] using hwt
  have hlt : Code.wt ((a - b) • fc + (b - c) • fa + (c - a) • fb)
        < Code.minDist (RS : Set (ι → F)) := lt_of_le_of_lt hwt' he
  exact zero_of_wt_lt_minDist (L := RS) hmem_RS hlt

end ProximityToRS
