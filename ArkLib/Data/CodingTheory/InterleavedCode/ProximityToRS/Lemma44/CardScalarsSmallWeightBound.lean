/-
Bound on the number of scalars with small weight along an affine line.
-/

import ArkLib.Data.CodingTheory.Basic
import Mathlib.Tactic

noncomputable section

open Code

namespace ProximityToRS

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Case 2 (ii) (Appendix A): bound the number of scalars `a` for which
`wt(u + a•v) ≤ e`. We record a slightly looser but sufficient bound `≤ e`
(Appendix A gives `≤ |supp(u) ∩ supp(v)|`). -/
lemma card_scalars_with_small_weight_bound
  (u v : ι → F) {e : ℕ}
  (hv : Code.wt v ≤ e)
  (h_union_ge : ((Finset.univ.filter fun i : ι => u i ≠ 0) ∪
                 (Finset.univ.filter fun i : ι => v i ≠ 0)).card ≥ e + 1) :
  Nat.card {a : F // Code.wt (u + a • v) ≤ e} ≤ e := by
  classical
  -- Notation
  let Su : Finset ι := Finset.univ.filter fun i : ι => u i ≠ 0
  let Sv : Finset ι := Finset.univ.filter fun i : ι => v i ≠ 0
  let T : Finset ι := Su ∪ Sv
  have h_T_large : e < T.card := Nat.lt_of_succ_le h_union_ge

  -- Domain of scalars with small weight
  let G := {a : F // Code.wt (u + a • v) ≤ e}

  -- For each a ∈ G, find an index i ∈ T such that (u + a•v) i = 0 and v i ≠ 0
  have exists_zero_in_T : ∀ x : G, ∃ i : ι, i ∈ T ∧ (u + x.1 • v) i = 0 ∧ v i ≠ 0 := by
    intro x
    -- support of (u + a•v) is contained in T
    let Ssum : Finset ι := Finset.univ.filter (fun i : ι => (u i + x.1 * v i) ≠ 0)
    have hsubset : Ssum ⊆ T := by
      intro i hi
      have hne : u i + x.1 * v i ≠ 0 := (Finset.mem_filter.mp hi).2
      by_cases hu0 : u i = 0
      · have hv0 : v i ≠ 0 := by
          intro hv_eq
          have : u i + x.1 * v i = 0 := by simp [hu0, hv_eq]
          exact hne this
        have : i ∈ Sv := by simp [Sv, hv0]
        exact Finset.mem_union.mpr (Or.inr this)
      · have : i ∈ Su := by simp [Su, hu0]
        exact Finset.mem_union.mpr (Or.inl this)
    -- Weight bound implies |Ssum| ≤ e
    have hSsum_le_e : Ssum.card ≤ e := by
      have hwt_eq : Code.wt (u + x.1 • v) = Ssum.card := by
        simp [Code.wt, Ssum, Pi.smul_apply, smul_eq_mul]
      simpa [hwt_eq] using x.2
    -- Since T.card ≥ e+1, Ssum ⊂ T, hence T \ Ssum is nonempty
    have hlt : Ssum.card < T.card := lt_of_le_of_lt hSsum_le_e h_T_large
    have hneq : Ssum ≠ T := by
      intro hEq
      -- contradiction: card Ssum < card T but Ssum = T
      simpa [hEq] using hlt
    have hss : Ssum ⊂ T := Finset.ssubset_iff_subset_ne.mpr ⟨hsubset, hneq⟩
    rcases Finset.exists_of_ssubset hss with ⟨i, hiT, hin⟩
    have hwi0 : (u + x.1 • v) i = 0 := by
      -- i ∉ Ssum ⇒ (u + a•v) i = 0
      have : (u i + x.1 * v i) = 0 := by
        have : i ∉ Ssum := hin
        have : ¬ (u i + x.1 * v i ≠ 0) := by simpa [Ssum] using this
        simpa [not_ne_iff] using this
      simpa [Pi.smul_apply, smul_eq_mul, add_comm, add_left_comm, add_assoc] using this
    -- i ∈ T and w i = 0 force v i ≠ 0
    have hvi_ne0 : v i ≠ 0 := by
      by_cases hv0 : v i = 0
      · have : i ∈ Su ∨ i ∈ Sv := (Finset.mem_union.mp hiT)
        cases this with
        | inl hiSu =>
          have hui_ne0 : u i ≠ 0 := by simpa [Su] using hiSu
          have : (u + x.1 • v) i ≠ 0 := by simp [Pi.smul_apply, smul_eq_mul, hv0, hui_ne0]
          exact (this (by simpa using hwi0)).elim
        | inr hiSv =>
          have : v i ≠ 0 := by simpa [Sv] using hiSv
          exact (this hv0).elim
      · exact hv0
    exact ⟨i, hiT, hwi0, hvi_ne0⟩

  -- Define an injection φ : G → Idx by choosing an index i with v i ≠ 0 and (u + a•v) i = 0
  let Idx := {i : ι // v i ≠ 0}
  have exists_zero_at : ∀ x : G, ∃ i : ι, v i ≠ 0 ∧ (u + x.1 • v) i = 0 := by
    intro x
    obtain ⟨i, hiT, hw0, hvi0⟩ := exists_zero_in_T x
    exact ⟨i, hvi0, hw0⟩
  let pickIdx : G → ι := fun x => Classical.choose (exists_zero_at x)
  have pickIdx_ne0 : ∀ x : G, v (pickIdx x) ≠ 0 := by
    intro x; exact (Classical.choose_spec (exists_zero_at x)).1
  have pickIdx_eq0 : ∀ x : G, (u + x.1 • v) (pickIdx x) = 0 := by
    intro x; exact (Classical.choose_spec (exists_zero_at x)).2
  let φ : G → Idx := fun x => ⟨pickIdx x, pickIdx_ne0 x⟩
  -- Uniqueness of the scalar at a fixed index with v i ≠ 0
  have uniq_scalar_at_index : ∀ i : ι, v i ≠ 0 → ∀ {a b : F},
      u i + a * v i = 0 → u i + b * v i = 0 → a = b := by
    intro i hvi a b ha hb
    have ha' : a * v i = -u i := by
      have := congrArg (fun t => t - u i) ha
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    have hb' : b * v i = -u i := by
      have := congrArg (fun t => t - u i) hb
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    have : a = b := by
      have hmul : a = (-u i) * (v i)⁻¹ := by
        have := congrArg (fun t => t * (v i)⁻¹) ha'
        simpa [mul_assoc, hvi] using this
      have hmul' : b = (-u i) * (v i)⁻¹ := by
        have := congrArg (fun t => t * (v i)⁻¹) hb'
        simpa [mul_assoc, hvi] using this
      simpa [hmul, hmul']
    simpa using this
  -- φ is injective because for a fixed index i there is at most one scalar
  have inj_φ : Function.Injective φ := by
    intro x y hxy
    apply Subtype.ext
    have hi : pickIdx x = pickIdx y := by simpa using congrArg Subtype.val hxy
    -- Use uniqueness at index hi
    have hx :
        u (pickIdx x) + x.1 * v (pickIdx x) = 0 := by
      simpa [Pi.smul_apply, smul_eq_mul] using pickIdx_eq0 x
    have hy :
        u (pickIdx y) + y.1 * v (pickIdx y) = 0 := by
      simpa [Pi.smul_apply, smul_eq_mul] using pickIdx_eq0 y
    have := uniq_scalar_at_index (pickIdx x) (pickIdx_ne0 x) (a := x.1) (b := y.1)
      (by simpa using hx) (by simpa [hi] using hy)
    exact this
  -- Hence card G ≤ card Idx
  have hG_le_Idx : Nat.card G ≤ Nat.card Idx :=
    Finite.card_le_of_injective φ inj_φ
  -- Combine with bound card Idx by wt(v) ≤ e
  have hIdx_le_e : Nat.card Idx ≤ e := by
    -- Fintype.card Idx = card Sv = Code.wt v ≤ e
    have hcard_idx : Nat.card Idx = (Finset.univ.filter fun i : ι => v i ≠ 0).card := by
      classical
      simpa [Idx] using Fintype.card_subtype (fun i : ι => v i ≠ 0)
    have : (Finset.univ.filter fun i : ι => v i ≠ 0).card = Code.wt v := by
      simp [Code.wt]
    rwa [hcard_idx, this]
  exact le_trans hG_le_Idx hIdx_le_e

/-
  A slightly more general bound: if we only know a bound `R` on the weight of `v`,
  then the number of scalars producing small weight (≤ `e`) is at most `R`.
  This is the same proof as above, ending with `Fintype.card Idx = Code.wt v ≤ R`.
-/
lemma card_scalars_with_small_weight_bound_by_wt
  (u v : ι → F) {e R : ℕ}
  (hv : Code.wt v ≤ R)
  (h_union_ge :
      ((Finset.univ.filter fun i : ι => u i ≠ 0) ∪
       (Finset.univ.filter fun i : ι => v i ≠ 0)).card ≥ e + 1) :
  Nat.card {a : F // Code.wt (u + a • v) ≤ e} ≤ R := by
  classical
  -- We can reuse the entire construction from the previous lemma, but finish with `≤ R`.
  -- Domain of scalars with small weight
  let G := {a : F // Code.wt (u + a • v) ≤ e}
  -- As before, produce an index with `v i ≠ 0` and `(u + a•v) i = 0` for each `a ∈ G`.
  -- We reuse the proof blocks from `card_scalars_with_small_weight_bound` verbatim.
  let Su : Finset ι := Finset.univ.filter fun i : ι => u i ≠ 0
  let Sv : Finset ι := Finset.univ.filter fun i : ι => v i ≠ 0
  let T : Finset ι := Su ∪ Sv
  have h_T_large : e < T.card := Nat.lt_of_succ_le h_union_ge
  have exists_zero_in_T : ∀ x : G, ∃ i : ι, i ∈ T ∧ (u + x.1 • v) i = 0 ∧ v i ≠ 0 := by
    intro x
    let Ssum : Finset ι := Finset.univ.filter (fun i : ι => (u i + x.1 * v i) ≠ 0)
    have hsubset : Ssum ⊆ T := by
      intro i hi
      have hne : u i + x.1 * v i ≠ 0 := (Finset.mem_filter.mp hi).2
      by_cases hu0 : u i = 0
      · have hv0 : v i ≠ 0 := by
          intro hv_eq
          have : u i + x.1 * v i = 0 := by simp [hu0, hv_eq]
          exact hne this
        have : i ∈ Sv := by simp [Sv, hv0]
        exact Finset.mem_union.mpr (Or.inr this)
      · have : i ∈ Su := by simp [Su, hu0]
        exact Finset.mem_union.mpr (Or.inl this)
    have hSsum_le_e : Ssum.card ≤ e := by
      have hwt_eq : Code.wt (u + x.1 • v) = Ssum.card := by
        simp [Code.wt, Ssum, Pi.smul_apply, smul_eq_mul]
      simpa [hwt_eq] using x.2
    have hlt : Ssum.card < T.card := lt_of_le_of_lt hSsum_le_e h_T_large
    have hneq : Ssum ≠ T := by
      intro hEq; simpa [hEq] using hlt
    have hss : Ssum ⊂ T := Finset.ssubset_iff_subset_ne.mpr ⟨hsubset, hneq⟩
    rcases Finset.exists_of_ssubset hss with ⟨i, hiT, hin⟩
    have hwi0 : (u + x.1 • v) i = 0 := by
      have : (u i + x.1 * v i) = 0 := by
        have : i ∉ Ssum := hin
        have : ¬ (u i + x.1 * v i ≠ 0) := by simpa [Ssum] using this
        simpa [not_ne_iff] using this
      simpa [Pi.smul_apply, smul_eq_mul, add_comm, add_left_comm, add_assoc] using this
    have hvi_ne0 : v i ≠ 0 := by
      by_cases hv0 : v i = 0
      · have : i ∈ Su ∨ i ∈ Sv := (Finset.mem_union.mp hiT)
        cases this with
        | inl hiSu =>
          have hui_ne0 : u i ≠ 0 := by simpa [Su] using hiSu
          have : (u + x.1 • v) i ≠ 0 := by simp [Pi.smul_apply, smul_eq_mul, hv0, hui_ne0]
          exact (this (by simpa using hwi0)).elim
        | inr hiSv =>
          have : v i ≠ 0 := by simpa [Sv] using hiSv
          exact (this hv0).elim
      · exact hv0
    exact ⟨i, hiT, hwi0, hvi_ne0⟩
  let Idx := {i : ι // v i ≠ 0}
  have exists_zero_at : ∀ x : G, ∃ i : ι, v i ≠ 0 ∧ (u + x.1 • v) i = 0 := by
    intro x
    obtain ⟨i, hiT, hw0, hvi0⟩ := exists_zero_in_T x
    exact ⟨i, hvi0, hw0⟩
  let pickIdx : G → ι := fun x => Classical.choose (exists_zero_at x)
  have pickIdx_ne0 : ∀ x : G, v (pickIdx x) ≠ 0 := by
    intro x; exact (Classical.choose_spec (exists_zero_at x)).1
  have pickIdx_eq0 : ∀ x : G, (u + x.1 • v) (pickIdx x) = 0 := by
    intro x; exact (Classical.choose_spec (exists_zero_at x)).2
  let φ : G → Idx := fun x => ⟨pickIdx x, pickIdx_ne0 x⟩
  -- Injectivity as before
  have uniq_scalar_at_index : ∀ i : ι, v i ≠ 0 → ∀ {a b : F},
      u i + a * v i = 0 → u i + b * v i = 0 → a = b := by
    intro i hvi a b ha hb
    have ha' : a * v i = -u i := by
      have := congrArg (fun t => t - u i) ha
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    have hb' : b * v i = -u i := by
      have := congrArg (fun t => t - u i) hb
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    have : a = b := by
      have hmul : a = (-u i) * (v i)⁻¹ := by
        have := congrArg (fun t => t * (v i)⁻¹) ha'
        simpa [mul_assoc, hvi] using this
      have hmul' : b = (-u i) * (v i)⁻¹ := by
        have := congrArg (fun t => t * (v i)⁻¹) hb'
        simpa [mul_assoc, hvi] using this
      simpa [hmul, hmul']
    simpa using this
  have inj_φ : Function.Injective φ := by
    intro x y hxy
    apply Subtype.ext
    have hi : pickIdx x = pickIdx y := by
      simpa using congrArg Subtype.val hxy
    have hx : u (pickIdx x) + x.1 * v (pickIdx x) = 0 := by
      simpa [Pi.smul_apply, smul_eq_mul] using pickIdx_eq0 x
    have hy : u (pickIdx y) + y.1 * v (pickIdx y) = 0 := by
      simpa [Pi.smul_apply, smul_eq_mul] using pickIdx_eq0 y
    have := uniq_scalar_at_index (pickIdx x) (pickIdx_ne0 x) (a := x.1) (b := y.1)
      (by simpa using hx) (by simpa [hi] using hy)
    exact this
  have hG_le_Idx : Nat.card G ≤ Nat.card Idx :=
    Finite.card_le_of_injective φ inj_φ
  -- Finish with the bound `card Idx = wt v ≤ R`.
  have hIdx_le_R : Nat.card Idx ≤ R := by
    have hcard_idx : Nat.card Idx = (Finset.univ.filter fun i : ι => v i ≠ 0).card := by
      classical
      simpa [Idx] using Fintype.card_subtype (fun i : ι => v i ≠ 0)
    have : (Finset.univ.filter fun i : ι => v i ≠ 0).card = Code.wt v := by
      simp [Code.wt]
    rwa [hcard_idx, this]
  exact le_trans hG_le_Idx hIdx_le_R

end ProximityToRS
