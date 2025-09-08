/-
Lemma 4.4 (Ligero): RS proximity on an affine line (points form).

For every affine line ℓ = { u + α v : α ∈ F } in F^n, under 3e < d, either
all points are within distance ≤ e from the RS code, or only ≤ d points are.
-/

import ArkLib.Data.CodingTheory.Basic
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.InterleavedCode.ProximityToRS.ClosePoints
import ArkLib.Data.CodingTheory.InterleavedCode.ProximityToRS.Lemma44.DichotomyCardGood
import Mathlib.Tactic

set_option linter.style.longLine false
set_option linter.unnecessarySimpa false
set_option linter.unusedSectionVars false

noncomputable section

open Code

namespace ProximityToRS

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {deg : ℕ} {α : ι ↪ F} {e : ℕ}

/-- Lemma 4.4 in the “points on the line” form. -/
lemma line_dichotomy_points
  (he : 3 * e < Code.minDist (ReedSolomon.code α deg : Set (ι → F)))
  (u v : ι → F) :
  (∀ x ∈ Affine.line u v, distFromCode x (ReedSolomon.code α deg) ≤ e)
  ∨ (numberOfClosePts u v deg α e
       ≤ Code.minDist (ReedSolomon.code α deg : Set (ι → F))) := by
  classical
  -- Apply the scalar-count dichotomy and translate to point-count via ClosePoints.
  have h := ProximityToRS.line_dichotomy_card_good (deg := deg) (α := α) (e := e) he u v
  rcases h with hAll | hFew
  · -- Every scalar is good ⇒ every point on the line is within distance ≤ e.
    left
    intro x hx
    rcases hx with ⟨a, rfl⟩
    have := hAll a
    simpa [Pi.smul_apply, smul_eq_mul] using this
  · -- Otherwise, the number of close points is bounded by the number of good scalars.
    right
    have hbridge := numberOfClosePts_le_card_good (u := u) (v := v) (deg := deg) (α := α) (e := e)
    exact le_trans hbridge hFew

end ProximityToRS
