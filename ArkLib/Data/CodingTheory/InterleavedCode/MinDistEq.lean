/-
Major lemma: equality of minimal distances between a linear code and
its associated interleaved-code row-span construction.
-/

import ArkLib.Data.CodingTheory.InterleavedCode.Defs
import ArkLib.Data.CodingTheory.Basic
import Mathlib.Tactic

noncomputable section

namespace InterleavedCode

variable {F : Type*} [Semiring F]
         {κ ι : Type*} [Fintype κ] [Fintype ι]
         (LC : LinearCode ι F)

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
      obtain ⟨i₀⟩ := (inferInstance : Nonempty κ)
      let U0 : Matrix κ ι F := fun i j => if i = i₀ then u j else 0
      let V0 : Matrix κ ι F := fun i j => if i = i₀ then v j else 0
      -- U0,V0 are in the generator set, thus in the span M
      have h0mem : ∀ i, U0 i ∈ C := by
        intro i; by_cases h : i = i₀
        · subst h; simpa [C, U0]
        · have hzC : (0 : ι → F) ∈ C := by simp [C]
          simpa [U0, h] using hzC
      have h1mem : ∀ i, V0 i ∈ C := by
        intro i; by_cases h : i = i₀
        · subst h; simpa [C, V0]
        · have hzC : (0 : ι → F) ∈ C := by simp [C]
          simpa [V0, h] using hzC
      have hU0in : U0 ∈ M := by
        have : U0 ∈ {W : Matrix κ ι F | ∀ i, W i ∈ LC} := by simpa [C] using h0mem
        exact Submodule.subset_span this
      have hV0in : V0 ∈ M := by
        have : V0 ∈ {W : Matrix κ ι F | ∀ i, W i ∈ LC} := by simpa [C] using h1mem
        exact Submodule.subset_span this
      -- Lower bound for each element of the witness set: base minDist ≤ Δ(U,V)
      have hLB : ∀ s ∈ {d : ℕ | ∃ U ∈ M, ∃ V ∈ M, U ≠ V ∧ InterleavedCode.distCodewords U V = d},
          Code.minDist C ≤ s := by
        intro s hs
        rcases hs with ⟨U, hU, V, hV, hNe', rfl⟩
        -- Pick a row where they differ
        have hex : ∃ i : κ, U i ≠ V i := by
          by_contra hAll
          push_neg at hAll
          exact hNe' (by funext i j; simp [hAll i])
        rcases hex with ⟨i, hi⟩
        -- rows are in LC by the construction of M
        have hrows := isInterleaved_codeOfLinearCode (κ := κ) (LC := LC)
        have hUi : U i ∈ LC := hrows U hU i
        have hVi : V i ∈ LC := hrows V hV i
        -- base ≤ row distance ≤ column distance
        have hbase_le : Code.minDist C ≤ hammingDist (U i) (V i) := by
          refine Nat.sInf_le ?_
          refine ⟨U i, ?_, V i, ?_, hi, rfl⟩
          · simpa [C] using hUi
          · simpa [C] using hVi
        have hrow_le_cols :
            hammingDist (U i) (V i) ≤ InterleavedCode.distCodewords U V := by
          -- as finsets
          simpa [hammingDist, InterleavedCode.distCodewords, Matrix.neqCols] using
            (Finset.card_mono (rowSupport_subset_neqCols U V i))
        exact le_trans hbase_le hrow_le_cols
      -- Nonempty witness set for M (given u ≠ v we can take U0,V0)
      have hneS :
          {d : ℕ | ∃ U ∈ M, ∃ V ∈ M, U ≠ V ∧ InterleavedCode.distCodewords U V = d}.Nonempty := by
        refine ⟨InterleavedCode.distCodewords U0 V0, ?_⟩
        exact ⟨U0, hU0in, V0, hV0in, by
          intro hEq; apply hne; funext j
          simpa [U0, V0] using congrArg (fun W => W i₀ j) hEq
        , rfl⟩
      -- Conclude base ≤ sInf = minDist
      simpa [InterleavedCode.minDist, Set.mem_setOf_eq, C, M]
        using (sInf.le_sInf_of_LB hneS hLB)
    · -- Base code has no distinct elements: both min distances are 0.
      have hC0 : Code.minDist C = 0 := by
        unfold Code.minDist
        have hemptyC : {d : ℕ | ∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ hammingDist u v = d} = (∅ : Set ℕ) := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro d hd; rcases hd with ⟨u, hu, v, hv, hne, _⟩
          exact hC_nontriv ⟨u, hu, v, hv, hne⟩
        simp [hemptyC]
      -- The witness set for M is empty as well (every row is 0)
      have hemptyM :
          {d : ℕ | ∃ U ∈ M, ∃ V ∈ M, U ≠ V ∧ InterleavedCode.distCodewords U V = d}
            = (∅ : Set ℕ) := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro d hd
        rcases hd with ⟨U, hU, V, hV, hne, _⟩
        have hrows := isInterleaved_codeOfLinearCode (κ := κ) (LC := LC)
        -- Since LC has no distinct elements, every element of LC is 0
        have hOnlyZero : ∀ x ∈ LC, x = (0 : ι → F) := by
          intro x hx; by_contra hx0
          exact hC_nontriv ⟨x, by simpa [C] using hx, 0, by simp [C], hx0⟩
        have hU0 : U = 0 := by
          funext i j; have : U i ∈ LC := hrows U hU i; simp [hOnlyZero _ this]
        have hV0 : V = 0 := by
          funext i j; have : V i ∈ LC := hrows V hV i; simp [hOnlyZero _ this]
        exact hne (by simp [hU0, hV0])
      have hM0 : minDist M = 0 := by
        unfold minDist; simp [hemptyM]
      simp [hM0, hC0, C, M]
  · -- Upper bound: `minDist M ≤ Code.minDist C`.
    -- It suffices to show `minDist M ≤ d` for each `d` realized by distinct base codewords.
    -- Use `le_sInf_of_LB` with witness set for `Code.minDist C`.
    have hLB : ∀ d ∈ {d : ℕ | ∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ hammingDist u v = d},
        minDist M ≤ d := by
      intro d hd
      rcases hd with ⟨u, hu, v, hv, hne, rfl⟩
      -- Build single-row matrices from u and v and relate their distance to hammingDist u v.
      obtain ⟨i₀⟩ := (inferInstance : Nonempty κ)
      let U : Matrix κ ι F := fun i j => if i = i₀ then u j else 0
      let V : Matrix κ ι F := fun i j => if i = i₀ then v j else 0
      -- Show each row lies in LC, then lift to membership in the span M
      have hrowsU : ∀ i, U i ∈ LC := by
        intro i; by_cases h : i = i₀
        · subst h; simpa [U, C] using hu
        · have hUi0 : U i = 0 := by
            ext j; simp [U, h]
          simp [hUi0] 
      have hrowsV : ∀ i, V i ∈ LC := by
        intro i; by_cases h : i = i₀
        · subst h; simpa [V, C] using hv
        · have hVi0 : V i = 0 := by
            ext j; simp [V, h]
          simp [hVi0]
      have hUin : U ∈ M := by
        have : U ∈ {W : Matrix κ ι F | ∀ i, W i ∈ LC} := by simpa using hrowsU
        exact Submodule.subset_span this
      have hVin : V ∈ M := by
        have : V ∈ {W : Matrix κ ι F | ∀ i, W i ∈ LC} := by simpa using hrowsV
        exact Submodule.subset_span this
      -- Distances coincide for these single-row matrices
      have hdist_eq : InterleavedCode.distCodewords U V = hammingDist u v :=
        support_eq_for_single_row_diff (i₀ := i₀) U V
          (by
            intro i; by_cases h : i = i₀
            · subst h; ext j; simp [U]
            · ext j; simp [U, h])
          (by
            intro i; by_cases h : i = i₀
            · subst h; ext j; simp [V]
            · ext j; simp [V, h])
      -- Conclude `minDist M ≤ distCodewords U V = hammingDist u v`
      have hle : minDist M ≤ InterleavedCode.distCodewords U V := by
        change sInf {d : ℕ | ∃ U' ∈ M, ∃ V' ∈ M, U' ≠ V' ∧ InterleavedCode.distCodewords U' V' = d}
              ≤ InterleavedCode.distCodewords U V
        refine Nat.sInf_le ?_
        exact ⟨U, hUin, V, hVin, by
          intro h; apply hne; funext j
          simpa [U, V] using congrArg (fun W => W i₀ j) h, rfl⟩
      -- rewrite the RHS using hdist_eq
      have : minDist M ≤ hammingDist u v := by simpa [hdist_eq] using hle
      exact this
    -- Conclude
    have : minDist M ≤ Code.minDist C := by
      -- If base witness set nonempty, use hLB.
      -- Else both sides are 0, so the inequality is trivial.
      by_cases hC_nontriv' : ∃ u ∈ C, ∃ v ∈ C, u ≠ v
      · have hneC :
            {d : ℕ | ∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ hammingDist u v = d}.Nonempty := by
          rcases hC_nontriv' with ⟨u, hu, v, hv, hne⟩
          exact ⟨hammingDist u v, ⟨u, hu, v, hv, hne, rfl⟩⟩
        have hineq := sInf.le_sInf_of_LB hneC (i := minDist M) hLB
        simpa [Code.minDist, C] using hineq
      · -- base set empty ⇒ Code.minDist C = 0, and also minDist M = 0 (as above), so ≤ holds
        have hC0 : Code.minDist C = 0 := by
          unfold Code.minDist
          have hemptyC : {d : ℕ | ∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ hammingDist u v = d} = (∅ : Set ℕ) := by
            apply Set.eq_empty_iff_forall_notMem.mpr
            intro d hd; rcases hd with ⟨u, hu, v, hv, hne, _⟩; exact hC_nontriv' ⟨u, hu, v, hv, hne⟩
          simp [hemptyC]
        have hemptyM :
            {d : ℕ | ∃ U ∈ M, ∃ V ∈ M, U ≠ V ∧ InterleavedCode.distCodewords U V = d}
              = (∅ : Set ℕ) := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro d hd; rcases hd with ⟨U, hU, V, hV, hneUV, _⟩
          have hrows := isInterleaved_codeOfLinearCode (κ := κ) (LC := LC)
          have hOnlyZero : ∀ x ∈ LC, x = (0 : ι → F) := by
            intro x hx; by_contra hx0
            exact hC_nontriv' ⟨x, by simpa [C] using hx, 0, by simp [C], hx0⟩
          have hU0 : U = 0 := by
            funext i j; have : U i ∈ LC := hrows U hU i; simp [hOnlyZero _ this]
          have hV0 : V = 0 := by
            funext i j; have : V i ∈ LC := hrows V hV i; simp [hOnlyZero _ this]
          exact hneUV (by simp [hU0, hV0])
        have hM0 : minDist M = 0 := by unfold minDist; simp [hemptyM]
        simp [hM0, hC0]
    exact this

end InterleavedCode
