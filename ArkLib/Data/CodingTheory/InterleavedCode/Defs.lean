/-
Basic definitions for interleaved codes and distance notions.
This file contains data structures, helper lemmas, and notations
used across the InterleavedCode lemmas.
-/

import ArkLib.Data.CodingTheory.Basic
import ArkLib.Data.CodingTheory.ReedSolomon
import Mathlib.Order.CompletePartialOrder
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Tactic

noncomputable section

variable {F : Type*} [Semiring F]
         {κ ι : Type*} [Fintype κ] [Fintype ι]
         {LC : LinearCode ι F}

abbrev MatrixSubmodule.{u, v, w} (κ : Type u) [Fintype κ] (ι : Type v) [Fintype ι]
                                 (F : Type w) [Semiring F] : Type (max u v w) :=
  Submodule F (Matrix κ ι F)

/--
The data needed to construct an interleaved code.
-/
structure InterleavedCode (κ ι : Type*) [Fintype κ] [Fintype ι] (F : Type*) [Semiring F] where
  MF : MatrixSubmodule κ ι F
  LC : LinearCode ι F

namespace InterleavedCode

/--
The condition making the `InterleavedCode` structure an interleaved code.
-/
def isInterleaved (IC : InterleavedCode κ ι F) :=
  ∀ V ∈ IC.MF, ∀ i, V i ∈ IC.LC

def LawfulInterleavedCode (κ : Type*) [Fintype κ] (ι : Type*) [Fintype ι]
                          (F : Type*) [Semiring F] :=
  { IC : InterleavedCode κ ι F // IC.isInterleaved }

/--
The submodule of the module of matrices whose rows belong to a linear code.
-/
def matrixSubmoduleOfLinearCode (κ : Type*) [Fintype κ]
                                (LC : LinearCode ι F) : MatrixSubmodule κ ι F :=
  Submodule.span F { V | ∀ i, V i ∈ LC }

def codeOfLinearCode (κ : Type*) [Fintype κ] (LC : LinearCode ι F) : InterleavedCode κ ι F :=
  { MF := matrixSubmoduleOfLinearCode κ LC, LC := LC }

/--
The module of matrices whose rows belong to a linear code is in fact an interleaved code.
-/
lemma isInterleaved_codeOfLinearCode : (codeOfLinearCode κ LC).isInterleaved := by
  classical
  intro V hV i
  -- Define the submodule of matrices whose rows lie in LC
  let T : Submodule F (Matrix κ ι F) :=
  { carrier := {W : Matrix κ ι F | ∀ j, W j ∈ LC}
    zero_mem' := by
      -- 0-row is the zero codeword in LC
      exact fun j => by rw [Pi.zero_apply]; exact Submodule.zero_mem LC
    add_mem' := by
      intro A B hA hB j; simpa using (Submodule.add_mem LC (hA j) (hB j))
    smul_mem' := by
      intro a A hA j; simpa using (Submodule.smul_mem LC a (hA j)) }
  have hle : (matrixSubmoduleOfLinearCode κ LC) ≤ T := by
    -- The span of the generator set is contained in T
    refine Submodule.span_le.mpr ?_
    intro M hM; exact hM
  have hVT : V ∈ T := hle hV
  -- Conclude row membership
  exact hVT i

def lawfulInterleavedCodeOfLinearCode (κ : Type*) [Fintype κ] (LC : LinearCode ι F) :
  LawfulInterleavedCode κ ι F := ⟨codeOfLinearCode κ LC, isInterleaved_codeOfLinearCode⟩

/--
Distance between codewords of an interleaved code.
-/
def distCodewords [DecidableEq F] (U V : Matrix κ ι F) : ℕ :=
  (Matrix.neqCols U V).card

/--
`Δ(U,V)` is the distance between codewords `U` and `V` of a `κ`-interleaved code `IC`.
-/
notation "Δ(" U "," V ")" => distCodewords U V

/--
Minimal distance of an interleaved code.
-/
def minDist [DecidableEq F] (IC : MatrixSubmodule κ ι F) : ℕ :=
  sInf { d : ℕ | ∃ U ∈ IC, ∃ V ∈ IC, U ≠ V ∧ distCodewords U V = d }

/--
`Δ IC` is the min distance of an interleaved code `IC`.
-/
notation "Δ" IC => minDist IC

/--
Distance from a matrix to the closest word in an interleaved code.
-/
def distToCode [DecidableEq F] (U : Matrix κ ι F) (IC : MatrixSubmodule κ ι F) : ℕ :=
 sInf { d : ℕ | ∃ V ∈ IC, distCodewords U V = d }

/--
`Δ(U,C')` denotes distance between a `κ x ι` matrix `U` and `κ`-interleaved code `IC`.
-/
notation "Δ(" U "," IC ")" => distToCode U IC

/--
Relative distance between codewords of an interleaved code.
-/
def relDistCodewords [DecidableEq F] (U V : Matrix κ ι F) : ℝ :=
  (Matrix.neqCols U V).card / Fintype.card ι

/-- List of codewords of IC r-close to U,
  with respect to relative distance of interleaved codes.
-/
def relHammingBallInterleavedCode [DecidableEq F] (U : Matrix κ ι F)
  (IC : MatrixSubmodule κ ι F) (r : ℝ) :=
    {V | V ∈ IC ∧ relDistCodewords U V < r}

/--`Λᵢ(U, IC, r)` denotes the list of codewords of IC r-close to U-/
notation "Λᵢ(" U "," IC "," r ")" => relHammingBallInterleavedCode U IC r

omit [Semiring F] in
/--
The minimal distance of an interleaved code is the same as
the minimal distance of its underlying linear code.
Helper: row support containment.
-/
lemma rowSupport_subset_neqCols [DecidableEq F]
  (U V : Matrix κ ι F) (i : κ) :
  (Finset.univ.filter fun j : ι => U i j ≠ V i j) ⊆ Matrix.neqCols U V := by
  intro j hj
  have hj' : U i j ≠ V i j := (Finset.mem_filter.mp hj).2
  have hj'' : V i j ≠ U i j := by simpa [ne_comm] using hj'
  have hexists : ∃ i0 : κ, V i0 j ≠ U i0 j := ⟨i, hj''⟩
  simpa [Matrix.neqCols] using hexists

lemma support_eq_for_single_row_diff [DecidableEq F] [DecidableEq κ]
  {u v : ι → F} (i₀ : κ)
  (U V : Matrix κ ι F)
  (hU : ∀ i, U i = (if i = i₀ then u else 0))
  (hV : ∀ i, V i = (if i = i₀ then v else 0)) :
  distCodewords U V = hammingDist u v := by
  classical
  -- Show both finset supports are equal by double inclusion
  -- Left-to-right: any differing column must be at row i₀
  apply le_antisymm
  · -- card(neqCols) ≤ card(support u≠v)
    have hsubset : Matrix.neqCols U V ⊆ (Finset.univ.filter fun j : ι => u j ≠ v j) := by
      intro j hj
      rcases (by simpa [Matrix.neqCols] using hj) with ⟨i, hi⟩
      by_cases hi0 : i = i₀
      · subst hi0
        have hvu : v j ≠ u j := by simpa [hU, hV] using hi
        have : u j ≠ v j := by simpa [ne_comm] using hvu
        simpa [Finset.mem_filter]
      · have : U i j = V i j := by simp [hU, hV, hi0]
        exact False.elim (hi (by simp [this]))
    have := Finset.card_mono hsubset
    simpa [distCodewords, hammingDist, Matrix.neqCols]
  · -- card(support u≠v) ≤ card(neqCols)
    have hsubset : (Finset.univ.filter fun j : ι => u j ≠ v j) ⊆ Matrix.neqCols U V := by
      intro j hj
      have : u j ≠ v j := (Finset.mem_filter.mp hj).2
      have : U i₀ j ≠ V i₀ j := by simpa [hU, hV] using this
      have : V i₀ j ≠ U i₀ j := by simpa [ne_comm] using this
      simpa [Matrix.neqCols] using ⟨i₀, this⟩
    have := Finset.card_mono hsubset
    simpa [distCodewords, hammingDist, Matrix.neqCols]

end InterleavedCode

-- Additional helpers used by the InterleavedCode lemmas
namespace InterleavedCode

variable {F : Type*} [Semiring F]
variable {κ ι : Type*} [Fintype κ]

/-- A finite linear combination of the rows of `U` lies in the row span of `U`. -/
lemma v_of_in_rowSpan (U : Matrix κ ι F) (r : κ → F) :
  (fun j => ∑ i, (r i) * (U i j)) ∈ Matrix.rowSpan U := by
  classical
  -- Identify the target as a finite linear combination of the generators U i
  have hfun : (fun j => ∑ i, (r i) * (U i j)) = (∑ i : κ, (r i) • (U i)) := by
    funext j; simp [Pi.smul_apply, smul_eq_mul]
  -- Finite linear combinations of generators lie in the span
  have hmem_univ : (Finset.univ.sum (fun i : κ => (r i) • (U i))) ∈ Matrix.rowSpan U := by
    -- Matrix.rowSpan U = span {U i | i}
    refine Finset.induction_on (Finset.univ : Finset κ) ?base ?step
    · simp
    · intro a s ha_notin hs_mem
      have h_head : (r a) • U a ∈ Matrix.rowSpan U := by
        refine Submodule.smul_mem (Matrix.rowSpan U) (r a) ?_
        exact Submodule.subset_span (by change U a ∈ {U i | i : κ}; simp)
      have h_tail : (Finset.sum s (fun i : κ => (r i) • U i)) ∈ Matrix.rowSpan U := hs_mem
      simpa [Finset.sum_insert, ha_notin] using Submodule.add_mem (Matrix.rowSpan U) h_head h_tail
  have hmem : (∑ i : κ, (r i) • (U i)) ∈ Matrix.rowSpan U := by simpa using hmem_univ
  simpa [hfun]

/-- A finite linear combination of rows `c i ∈ LC` is again in `LC`. -/
lemma linear_comb_rows_in_LC [Fintype ι] (LC : LinearCode ι F)
  (c : κ → ι → F)
  (hc : ∀ i, c i ∈ LC) (r : κ → F) :
  (fun j => ∑ i, (r i) * (c i j)) ∈ (LC : Set (ι → F)) := by
  classical
  -- Identify the target as a finite linear combination in the submodule LC
  have hfun : (fun j => ∑ i, (r i) * (c i j)) = (∑ i : κ, (r i) • (c i)) := by
    funext j; simp [Pi.smul_apply, smul_eq_mul]
  have hmem_univ : (Finset.univ.sum (fun i : κ => (r i) • (c i))) ∈ LC := by
    -- Finite sums of elements of LC with scalars lie in LC
    refine Finset.induction_on (Finset.univ : Finset κ) ?base ?step
    · simp
    · intro a s ha_notin hs_mem
      have h_head : (r a) • c a ∈ LC := by
        refine Submodule.smul_mem LC (r a) ?_
        simpa using hc a
      have h_tail : (Finset.sum s (fun i : κ => (r i) • c i)) ∈ LC := hs_mem
      simpa [Finset.sum_insert, ha_notin] using Submodule.add_mem LC h_head h_tail
  have : (∑ i : κ, (r i) • (c i)) ∈ LC := by simpa using hmem_univ
  simpa [hfun]

/-
Residuals and their linear combination along κ → F.
These are used pervasively in the interleaved-code lemmas.
-/

variable {F : Type*} [CommRing F]
variable {κ ι : Type*} [Fintype κ] [Fintype ι]

/-- Row-wise residual χ of U against a per-row codeword family c. -/
def residual (U : Matrix κ ι F) (c : κ → ι → F) : κ → ι → F :=
  fun i j => U i j - c i j

/-- Combined residual E of U, c along a coefficient map r : κ → F. -/
def E (U : Matrix κ ι F) (c : κ → ι → F) (r : κ → F) : ι → F :=
  fun j => ∑ i, (r i) * (residual U c i j)

end InterleavedCode
