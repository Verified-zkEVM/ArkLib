/-
Fresh error coordinate from column mismatch set.
-/

import ArkLib.Data.CodingTheory.Basic
import ArkLib.Data.CodingTheory.InterleavedCode.Defs
import ArkLib.Data.CodingTheory.InterleavedCode.Lemma43.Aux
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

noncomputable section

open Code

namespace InterleavedCode
namespace Lemma43

variable {F : Type*} [DecidableEq F]
variable {κ : Type*} [Fintype κ]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/--
Fresh error with an explicit witness matrix: if `V` has each row in `L`, and
`distCodewords U V > e ≥ |E₀|`, then there is a row `i` and column `j` with
`j ∈ Err (U i) (V i)` but `j ∉ E₀`.
-/
lemma exists_row_and_fresh_coord
  {e : ℕ}
  (U V : Matrix κ ι F)
  (v0 c0 : ι → F)
  (hE0_le : (Err (ι := ι) v0 c0).card ≤ e)
  (hUV : e < distCodewords U V) :
  ∃ i : κ, ∃ j : ι, j ∈ Err (ι := ι) (U i) (V i) ∧ j ∉ Err (ι := ι) v0 c0 := by
  classical
  -- Let S := Matrix.neqCols U V, with S.card = distCodewords U V > e.
  set S := Matrix.neqCols U V
  have hScard : S.card = distCodewords U V := by rfl
  have hSgt : e < S.card := by simpa [hScard]
  -- If every j ∈ S belongs to E0, then S.card ≤ E0.card ≤ e
  have hnot_subset : ¬ S ⊆ Err (ι := ι) v0 c0 := by
    intro hsubset
    have hmono := Finset.card_mono hsubset
    have : S.card ≤ (Err (ι := ι) v0 c0).card := hmono
    exact (not_lt_of_ge (le_trans this hE0_le)) hSgt
  -- So pick j ∈ S with j ∉ E0
  have hsel : ∃ j, j ∈ S ∧ j ∉ Err (ι := ι) v0 c0 := by
    by_contra h
    have : S ⊆ Err (ι := ι) v0 c0 := by
      intro j hj
      by_contra hjmem
      exact h ⟨j, hj, hjmem⟩
    exact hnot_subset this
  rcases hsel with ⟨j, hjS, hjNotE0⟩
  -- By definition of S, we get a row i with a mismatch at column j
  have hx' : ∃ i : κ, V i j ≠ U i j := by simpa [S, Matrix.neqCols] using hjS
  rcases hx' with ⟨i, hVU⟩
  have hi : U i j ≠ V i j := by simpa [ne_comm] using hVU
  -- Conclude j ∈ Err(U i, V i)
  have hjErr : j ∈ Err (ι := ι) (U i) (V i) := by
    have hjuniv : j ∈ (Finset.univ : Finset ι) := by simp
    simp [Err, Finset.mem_filter, hjuniv, hi]
  exact ⟨i, j, hjErr, hjNotE0⟩

end Lemma43
end InterleavedCode
