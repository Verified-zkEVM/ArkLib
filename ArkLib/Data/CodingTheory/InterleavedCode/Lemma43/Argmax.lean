/-
Argmax over the row span for the distance-to-code functional.
-/

import ArkLib.Data.CodingTheory.Basic
import ArkLib.Data.CodingTheory.InterleavedCode.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

noncomputable section

open Code

namespace InterleavedCode
namespace Lemma43

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {κ : Type*}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Existence of an argmax of `distFromCode · L` inside the finite `rowSpan U`. -/
lemma exists_argmax_dist_in_rowSpan
  (L : Set (ι → F)) (U : Matrix κ ι F) :
  ∃ v ∈ Matrix.rowSpan U,
    ∀ w ∈ Matrix.rowSpan U, distFromCode v L ≥ distFromCode w L := by
  classical
  let fFintype : Fintype F := Fintype.ofFinite F
  -- Work over the finite type of elements of the row span as a subtype.
  let S : Finset (Matrix.rowSpan U) := (Finset.univ : Finset (Matrix.rowSpan U))
  have hS_ne : S.Nonempty := by
    refine ⟨⟨0, by simp⟩, ?_⟩
    simp [S]
  -- Maximize the distance-to-code over S.
  obtain ⟨vS, hvS, hmaxS⟩ :=
    Finset.exists_max_image (s := S)
      (f := fun (x : Matrix.rowSpan U) => distFromCode (x : ι → F) L)
      hS_ne
  -- Project to an element v0 : ι → F in the row span.
  refine ⟨(vS : ι → F), (vS.property), ?_⟩
  intro w hw
  -- View w as a subtype element to apply maximality.
  have hwS : (⟨w, hw⟩ : Matrix.rowSpan U) ∈ S := by simp [S]
  have := hmaxS (⟨w, hw⟩) hwS
  -- Conclude the inequality in the requested orientation.
  simpa using this

end Lemma43
end InterleavedCode
