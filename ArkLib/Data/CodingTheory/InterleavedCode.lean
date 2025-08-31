/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši
-/

import ArkLib.Data.CodingTheory.Basic
import ArkLib.Data.CodingTheory.ReedSolomon
import Mathlib.Order.CompletePartialOrder
import Mathlib.Probability.Distributions.Uniform

noncomputable section

/-!
  Definition of an interleaved code of a linear code over a semiring.
  Definition of distances for interleaved codes and statement for the relation between the minimal
  distance of an interleaved code and its underlying linear code.
  Statements of proximity results for Reed Solomon codes
  (`Lemma 4.3`, `Lemma 4.4` and `Lemma 4.5` from Ligero) with proximity parameter less than
  the minimal code distance divided by `3`.
-/

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

/--
The minimal distance of an interleaved code is the same as
the minimal distance of its underlying linear code.
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


lemma minDist_eq_minDist [DecidableEq F] [Nonempty κ] :
  Code.minDist (LC : Set (ι → F)) = minDist (matrixSubmoduleOfLinearCode κ LC) := by
  classical
  -- Abbreviations
  set C := (LC : Set (ι → F))
  set M := matrixSubmoduleOfLinearCode κ LC
  -- We prove both inequalities and conclude by antisymmetry on `≤` for naturals.
  apply le_antisymm
  · -- Lower bound: `Code.minDist C ≤ minDist M`.
    -- Split on whether there are any distinct base codewords.
    by_cases hC_nontriv : ∃ u ∈ C, ∃ v ∈ C, u ≠ v
    · -- Show that the witness set for `minDist M` is nonempty by constructing matrices
      -- from `u ≠ v`.
      rcases hC_nontriv with ⟨u, hu, v, hv, hne⟩
      classical
      obtain ⟨i₀⟩ := (inferInstance : Nonempty κ)
      let U0 : Matrix κ ι F := fun i j => if i = i₀ then u j else 0
      let V0 : Matrix κ ι F := fun i j => if i = i₀ then v j else 0
      -- U0,V0 are in the generator set, thus in the span M
      have h0mem : ∀ i, U0 i ∈ C := by
        intro i; by_cases h : i = i₀
        · subst h; simpa [U0]
        · have hz : (0 : ι → F) ∈ C := by simpa [C] using (Submodule.zero_mem LC : (0 : ι → F) ∈ LC)
          simpa [U0, h] using hz
      have h1mem : ∀ i, V0 i ∈ C := by
        intro i; by_cases h : i = i₀
        · subst h; simpa [V0]
        · have hz : (0 : ι → F) ∈ C := by simpa [C] using (Submodule.zero_mem LC : (0 : ι → F) ∈ LC)
          simpa [V0, h] using hz
      have hU0in : U0 ∈ M := by
        have : U0 ∈ {W : Matrix κ ι F | ∀ i, W i ∈ LC} := by simpa [C] using h0mem
        exact Submodule.subset_span this
      have hV0in : V0 ∈ M := by
        have : V0 ∈ {W : Matrix κ ι F | ∀ i, W i ∈ LC} := by simpa [C] using h1mem
        exact Submodule.subset_span this
      have hU0V0ne : U0 ≠ V0 := by
        intro hEq; apply hne; funext j
        simpa [U0, V0] using congrArg (fun f => f j) (congrArg (fun W => W i₀) hEq)
      -- Now apply lower-bound reasoning to all pairs in M and then `le_sInf_of_LB`
      have hLB : ∀ s ∈ {d : ℕ | ∃ U ∈ M, ∃ V ∈ M, U ≠ V ∧ distCodewords U V = d},
          Code.minDist C ≤ s := by
        intro s hs
        rcases hs with ⟨U, hU, V, hV, hNe', rfl⟩
        -- Pick a row where they differ
        have hex : ∃ i : κ, U i ≠ V i := by
          by_contra hAll; push_neg at hAll; exact hNe' (by funext i j; simp [hAll i])
        rcases hex with ⟨i, hi⟩
        -- Row-membership in the base code from `isInterleaved_codeOfLinearCode`
        have hUi : U i ∈ C := by
          -- `U ∈ M` implies every row in LC by construction
          have hrows := isInterleaved_codeOfLinearCode (κ := κ) (LC := LC)
          simpa [C] using hrows U hU i
        have hVi : V i ∈ C := by
          have hrows := isInterleaved_codeOfLinearCode (κ := κ) (LC := LC)
          simpa [C] using hrows V hV i
        -- minDist base ≤ row distance ≤ column distance
        have hbase_le : Code.minDist C ≤ hammingDist (U i) (V i) := by
          refine Nat.sInf_le ?_
          exact ⟨U i, hUi, V i, hVi, hi, rfl⟩
        have hrow_le_cols : hammingDist (U i) (V i) ≤ distCodewords U V := by
          simpa [hammingDist, distCodewords, Matrix.neqCols] using
            (Finset.card_mono (rowSupport_subset_neqCols (κ := κ) (ι := ι) U V i))
        exact le_trans hbase_le hrow_le_cols
      -- nonempty of S_M from constructed pair
      have hne : {d : ℕ | ∃ U ∈ M, ∃ V ∈ M, U ≠ V ∧ distCodewords U V = d}.Nonempty :=
        ⟨distCodewords U0 V0, ⟨U0, hU0in, V0, hV0in, hU0V0ne, rfl⟩⟩
      -- Conclude by lower-bound on sInf
      exact sInf.le_sInf_of_LB hne hLB
    · -- Base code has no distinct elements: `Code.minDist C = 0 ≤ minDist M`.
      have hC0 : Code.minDist C = 0 := by
        unfold Code.minDist
        have hemptyC : {d : ℕ | ∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ hammingDist u v = d} = (∅ : Set ℕ) := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro d hd; rcases hd with ⟨u, hu, v, hv, hne, _⟩
          exact hC_nontriv ⟨u, hu, v, hv, hne⟩
        simp [hemptyC]
      simp [hC0, Nat.zero_le (minDist M)]
  · -- Upper bound: realize a base pair inside the interleaved code by differing in one row.
    -- It suffices to show `minDist M ≤ d` for each `d` realized by distinct base codewords.
    by_cases hC_nontriv : ∃ u ∈ C, ∃ v ∈ C, u ≠ v
    · -- Use `le_sInf_of_LB` with `i = minDist M` and the base-code set nonempty.
      have hLB : ∀ d ∈ {d : ℕ | ∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ hammingDist u v = d},
          minDist M ≤ d := by
        intro d hd
        rcases hd with ⟨u, hu, v, hv, hne, rfl⟩
        classical
        obtain ⟨i₀⟩ := (inferInstance : Nonempty κ)
        let U : Matrix κ ι F := fun i j => if i = i₀ then u j else 0
        let V : Matrix κ ι F := fun i j => if i = i₀ then v j else 0
        -- Membership in M via generators
        have hUrows : ∀ i, U i ∈ C := by
          intro i; by_cases h : i = i₀
          · subst h; simpa [U]
          · have hz : (0 : ι → F) ∈ C := by
              simpa [C] using (Submodule.zero_mem LC : (0 : ι → F) ∈ LC)
            simpa [U, h] using hz
        have hVrows : ∀ i, V i ∈ C := by
          intro i; by_cases h : i = i₀
          · subst h; simpa [V]
          · have hz : (0 : ι → F) ∈ C := by
              simpa [C] using (Submodule.zero_mem LC : (0 : ι → F) ∈ LC)
            simpa [V, h] using hz
        have hUin : U ∈ M := by
          have : U ∈ {W : Matrix κ ι F | ∀ i, W i ∈ LC} := by simpa [C] using hUrows
          exact Submodule.subset_span this
        have hVin : V ∈ M := by
          have : V ∈ {W : Matrix κ ι F | ∀ i, W i ∈ LC} := by simpa [C] using hVrows
          exact Submodule.subset_span this
        have hUVne : U ≠ V := by
          intro hEq; apply hne; funext j;
          simpa [U, V] using congrArg (fun f => f j) (congrArg (fun W => W i₀) hEq)
        -- Distance equality
        have hUdef : ∀ i, U i = (if i = i₀ then u else 0) := by
          intro i; by_cases h : i = i₀
          · subst h; funext j; simp [U]
          · funext j; simp [U, h]
        have hVdef : ∀ i, V i = (if i = i₀ then v else 0) := by
          intro i; by_cases h : i = i₀
          · subst h; funext j; simp [V]
          · funext j; simp [V, h]
        have hdist_eq : distCodewords U V = hammingDist u v :=
          support_eq_for_single_row_diff (κ := κ) (ι := ι) i₀ U V hUdef hVdef
        -- Conclude `minDist M ≤ distCodewords U V = hammingDist u v`
        refine Nat.sInf_le ?_
        exact ⟨U, hUin, V, hVin, hUVne, hdist_eq⟩
      -- Nonemptiness of the base set
      have hne : {d : ℕ | ∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ hammingDist u v = d}.Nonempty := by
        rcases hC_nontriv with ⟨u, hu, v, hv, hne⟩
        exact ⟨hammingDist u v, ⟨u, hu, v, hv, hne, rfl⟩⟩
      -- Apply lower-bound-to-sInf on the base set with i = minDist M
      exact sInf.le_sInf_of_LB hne hLB
    · -- Base code has no distinct elements: both min distances are 0.
      have hC0 : Code.minDist C = 0 := by
        unfold Code.minDist
        have hemptyC : {d : ℕ | ∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ hammingDist u v = d} = (∅ : Set ℕ) := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro d hd; rcases hd with ⟨u, hu, v, hv, hne, _⟩
          exact hC_nontriv ⟨u, hu, v, hv, hne⟩
        simp [hemptyC]
      -- The witness set for M is empty as well
      have hemptyM : {d : ℕ | ∃ U ∈ M, ∃ V ∈ M, U ≠ V ∧ distCodewords U V = d} = (∅ : Set ℕ) := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro d hd
        rcases hd with ⟨U, hU, V, hV, hne, _⟩
        have hrows := isInterleaved_codeOfLinearCode (κ := κ) (LC := LC)
        -- Since LC has no distinct elements, every element of LC is 0
        have hOnlyZero : ∀ x ∈ LC, x = (0 : ι → F) := by
          intro x hx; by_contra hx0
          exact hC_nontriv ⟨x,
            by simpa [C] using hx, 0,
            by simpa [C] using (Submodule.zero_mem LC),
            hx0⟩
        have hU0 : U = 0 := by
          funext i j; have : U i ∈ LC := hrows U hU i; simp [hOnlyZero _ this]
        have hV0 : V = 0 := by
          funext i j; have : V i ∈ LC := hrows V hV i; simp [hOnlyZero _ this]
        exact hne (by simp [hU0, hV0])
      have hM0 : minDist M = 0 := by
        unfold minDist; simp [hemptyM]
      simp [hM0, hC0]

end InterleavedCode

noncomputable section

open InterleavedCode
open Code

variable {F : Type*} [Field F] [Finite F] [DecidableEq F]
         {κ : Type*} [Fintype κ] {ι : Type*} [Fintype ι]

local instance : Fintype F := Fintype.ofFinite F

/--
Lemma 4.3 Ligero
-/
lemma distInterleavedCodeToCodeLB
  {IC : LawfulInterleavedCode κ ι F} {U : Matrix κ ι F} {e : ℕ}
  (hF : Fintype.card F ≥ e)
  (he : (e : ℚ) ≤ (minDist (IC.1.LC : Set (ι → F)) / 3)) (hU : e < Δ(U,IC.1.MF)) :
  ∃ v ∈ Matrix.rowSpan U , e < distFromCode v IC.1.LC := sorry

namespace ProximityToRS

/--
The set of points on an affine line, which are within distance `e`
from a Reed-Solomon code.
-/
def closePtsOnAffineLine {ι : Type*} [Fintype ι]
                         (u v : ι → F) (deg : ℕ) (α : ι ↪ F) (e : ℕ) : Set (ι → F) :=
  {x : ι → F | x ∈ Affine.line u v ∧ distFromCode x (ReedSolomon.code α deg) ≤ e}

/--
The number of points on an affine line between, which are within distance `e`
from a Reed-Solomon code.
-/
def numberOfClosePts (u v : ι → F) (deg : ℕ) (α : ι ↪ F)
  (e : ℕ) : ℕ :=
  Fintype.card (closePtsOnAffineLine u v deg α e)

/--
Lemma 4.4 Ligero
Remark: Below, can use (ReedSolomonCode.minDist deg α) instead of ι - deg + 1 once proved.
-/
lemma e_leq_dist_over_3 {deg : ℕ} {α : ι ↪ F} {e : ℕ} {u v : ι → F}
  (he : (e : ℚ) < (Fintype.card ι - deg + 1 / 3)) :
  ∀ x ∈ Affine.line u v, distFromCode x (ReedSolomon.code α deg) ≤ e
  ∨ (numberOfClosePts u v deg α e) ≤ Fintype.card ι - deg + 1 := by sorry

/--
Lemma 4.5 Ligero
-/
lemma probOfBadPts {deg : ℕ} {α : ι ↪ F} {e : ℕ} {U : Matrix κ ι F}
  (he : (e : ℚ) < (Fintype.card ι - deg + 1 / 3))
  (hU : e < Δ(U,matrixSubmoduleOfLinearCode κ (ReedSolomon.code α deg))) :
  (PMF.uniformOfFintype (Matrix.rowSpan U)).toOuterMeasure
    { w | distFromCode (n := ι) (R := F) w (ReedSolomon.code α deg) ≤ e }
  ≤ (Fintype.card ι - deg + 1)/(Fintype.card F) := by
  sorry

end ProximityToRS
end

section GeneralInequalityAndCounterexample

open InterleavedCode

variable {F : Type*} [Semiring F] [DecidableEq F]
         {κ ι : Type*} [Fintype κ] [Fintype ι]

-- General inequality under nontriviality of the interleaved submodule
lemma baseMinDist_le_minDist_of_nontrivialMF
  {IC : LawfulInterleavedCode κ ι F}
  (hNE : ∃ U ∈ IC.1.MF, ∃ V ∈ IC.1.MF, U ≠ V) :
  Code.minDist (IC.1.LC : Set (ι → F)) ≤ InterleavedCode.minDist IC.1.MF := by
  classical
  let S := {d : ℕ | ∃ U ∈ IC.1.MF, ∃ V ∈ IC.1.MF, U ≠ V ∧ InterleavedCode.distCodewords U V = d}
  -- Lower bound for each element of the witness set: base minDist ≤ Δ(U,V)
  have hLB : ∀ s ∈ S, Code.minDist (IC.1.LC : Set (ι → F)) ≤ s := by
    intro s hs; rcases hs with ⟨U, hU, V, hV, hNe, rfl⟩
    -- pick a row where they differ
    have hex : ∃ i : κ, U i ≠ V i := by
      by_contra hAll; push_neg at hAll; exact hNe (by funext i j; simp [hAll i])
    rcases hex with ⟨i, hi⟩
    -- rows are in LC by lawfulness
    have hUi : U i ∈ IC.1.LC := IC.2 U hU i
    have hVi : V i ∈ IC.1.LC := IC.2 V hV i
    -- base ≤ row distance ≤ column distance
    have hbase_le : Code.minDist (IC.1.LC : Set (ι → F)) ≤ hammingDist (U i) (V i) := by
      refine Nat.sInf_le ?_; exact ⟨U i, hUi, V i, hVi, hi, rfl⟩
    have hrow_le_cols : hammingDist (U i) (V i) ≤ InterleavedCode.distCodewords U V := by
      -- as finsets
      simpa [hammingDist, InterleavedCode.distCodewords, Matrix.neqCols] using
        (Finset.card_mono (rowSupport_subset_neqCols U V i))
    exact le_trans hbase_le hrow_le_cols
  -- Nonempty witness set
  have hneS : S.Nonempty := by
    rcases hNE with ⟨U, hU, V, hV, hNe⟩
    exact ⟨InterleavedCode.distCodewords U V, ⟨U, hU, V, hV, hNe, rfl⟩⟩
  -- Conclude base ≤ sInf = minDist
  simpa [InterleavedCode.minDist, Set.mem_setOf_eq] using (sInf.le_sInf_of_LB hneS hLB)


def IC0 : InterleavedCode (Fin 1) (Fin 1) (ZMod 2) := { MF := ⊥, LC := ⊤ }

lemma IC0_isInterleaved : IC0.isInterleaved := by
  intro V _ i
  simp [IC0]

def LC0 : LawfulInterleavedCode (Fin 1) (Fin 1) (ZMod 2) := ⟨IC0, IC0_isInterleaved⟩

example :
  Code.minDist (LC0.1.LC : Set (Fin 1 → ZMod 2)) ≠ InterleavedCode.minDist LC0.1.MF := by
  -- Right-hand side: Δ(⊥) = 0 (no distinct matrices in ⊥)
  -- Compute minDist of ⊥ explicitly: witness set is empty
  have hMF : InterleavedCode.minDist LC0.1.MF = 0 := by
    unfold InterleavedCode.minDist
    -- Show emptiness of the witness set
    have hempty : {d : ℕ | ∃ U ∈ LC0.1.MF, ∃ V ∈ LC0.1.MF,
        U ≠ V ∧ InterleavedCode.distCodewords U V = d} = (∅ : Set ℕ) := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro d hd
      rcases hd with ⟨U, hU, V, hV, hne, _⟩
      have hU0 : U = 0 := by simpa [IC0] using hU
      have hV0 : V = 0 := by simpa [IC0] using hV
      exact hne (by simp [hU0, hV0])
    simp [hempty]
  -- Left-hand side: min distance of ⊤ on length-1 vectors over ZMod 2 is 1
  have hLC_le : Code.minDist (LC0.1.LC : Set (Fin 1 → ZMod 2)) ≤ 1 := by
    -- Witness: u = 0, v = 1
    let u : Fin 1 → ZMod 2 := fun _ => 0
    let v : Fin 1 → ZMod 2 := fun _ => 1
    have hu : u ∈ (LC0.1.LC : Set (Fin 1 → ZMod 2)) := by simp [LC0, IC0]
    have hv : v ∈ (LC0.1.LC : Set (Fin 1 → ZMod 2)) := by simp [LC0, IC0]
    have hne : u ≠ v := by
      intro h
      have h0 : u 0 ≠ v 0 := by decide
      exact h0 (congrArg (fun f => f 0) h)
    -- minDist ≤ Δ₀(u,v) ≤ 1 via general bound
    have h₁ : Code.minDist (LC0.1.LC : Set (Fin 1 → ZMod 2)) ≤ hammingDist u v := by
      refine Nat.sInf_le ?_;
      exact ⟨u, hu, v, hv, hne, rfl⟩
    have h₂' : hammingDist u v ≤ Fintype.card (Fin 1) := by
      simpa using (hammingDist_le_card_fintype (ι := Fin 1))
    have h₂ : hammingDist u v ≤ 1 := by
      simpa [Fintype.card_fin] using h₂'
    exact le_trans h₁ h₂
  -- Lower bound: every distinct pair in ⊤ differs in the only coordinate ⇒ distance ≥ 1
  have hLC_ge : 1 ≤ Code.minDist (LC0.1.LC : Set (Fin 1 → ZMod 2)) := by
    -- Use the general `le_sInf_of_LB` with the witness set for Code.minDist
    let S := {d : ℕ | ∃ u ∈ (LC0.1.LC : Set (Fin 1 → ZMod 2)),
                        ∃ v ∈ (LC0.1.LC : Set (Fin 1 → ZMod 2)),
                        u ≠ v ∧ hammingDist u v = d}
    -- S is nonempty: same witness as above
    have hS_ne : S.Nonempty := by
      let u : Fin 1 → ZMod 2 := fun _ => 0
      let v : Fin 1 → ZMod 2 := fun _ => 1
      have hu : u ∈ (LC0.1.LC : Set (Fin 1 → ZMod 2)) := by simp [LC0, IC0]
      have hv : v ∈ (LC0.1.LC : Set (Fin 1 → ZMod 2)) := by simp [LC0, IC0]
      have hne : u ≠ v := by
        intro h
        have h0 : u 0 ≠ v 0 := by decide
        exact h0 (congrArg (fun f => f 0) h)
      exact ⟨hammingDist u v, ⟨u, hu, v, hv, hne, rfl⟩⟩
    -- Every element of S is ≥ 1
    have hLB : ∀ s ∈ S, 1 ≤ s := by
      intro s hs; rcases hs with ⟨u, hu, v, hv, hne, rfl⟩
      -- On Fin 1, distinct functions differ at 0, so distance is 1
      have h0neq : u 0 ≠ v 0 := by
        by_contra hEq
        apply hne; funext j; have : j = 0 := Fin.fin_one_eq_zero j; simp [this, hEq]
      have hmem : (0 : Fin 1) ∈ (Finset.univ.filter fun j : Fin 1 => u j ≠ v j) := by
        simp [h0neq]
      have hpos : 0 < (Finset.univ.filter (fun j : Fin 1 => u j ≠ v j)).card :=
        Finset.card_pos.mpr ⟨0, hmem⟩
      have : 1 ≤ hammingDist u v := by
        simpa [hammingDist] using Nat.succ_le_of_lt hpos
      simpa using this
    -- Apply the helper lemma from Prelims
    have : 1 ≤ sInf S := sInf.le_sInf_of_LB hS_ne hLB
    simpa [Code.minDist, Set.mem_setOf_eq] using this
  -- Thus Code.minDist = 1, while Interleaved minDist = 0
  have hLC : Code.minDist (LC0.1.LC : Set (Fin 1 → ZMod 2)) = 1 := le_antisymm hLC_le hLC_ge
  -- Conclude inequality 1 ≠ 0
  simp [hLC, hMF]

end GeneralInequalityAndCounterexample
