/-
General inequality and a counterexample for min distances.
-/

import ArkLib.Data.CodingTheory.InterleavedCode.Defs
import Mathlib.Tactic

noncomputable section

open InterleavedCode

section GeneralInequalityAndCounterexample

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
