/-
Bad-α control and weight growth lemmas for Lemma 4.3.
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

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {κ : Type*} [Fintype κ]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- For fixed `a, b ≠ 0`, there is at most one `α` with `a + α*b = 0`. -/
lemma one_cancellation_per_coordinate (a b : F) (hb : b ≠ 0) :
  {α : F | a + α*b = 0}.Finite ∧ Nat.card {α : F | a + α*b = 0} ≤ 1 := by
  classical
  -- Finiteness since F is finite
  have hfinite : ({α : F | a + α * b = 0} : Set F).Finite := by
    simpa using (Set.finite_univ.subset (by intro x hx; simp))
  -- At most one solution: if a + α b = 0 and a + α' b = 0 then α = α'
  have hsub : Subsingleton {α : F // a + α * b = 0} := by
    refine ⟨?_⟩
    intro x y
    apply Subtype.ext
    have hx : a + x.val * b = 0 := x.property
    have hy : a + y.val * b = 0 := y.property
    -- (x - y) * b = 0
    have hxy : (x.val - y.val) * b = 0 := by
      have hx' : x.val * b = -a := by simpa [add_comm, eq_neg_iff_add_eq_zero] using hx
      have hy' : y.val * b = -a := by simpa [add_comm, eq_neg_iff_add_eq_zero] using hy
      calc
        (x.val - y.val) * b = x.val * b - y.val * b := by ring
        _ = (-a) - (-a) := by simp [hx', hy']
        _ = 0 := by simp
    -- From (x - y) * b = 0 and hb, deduce x - y = 0
    have hsubzero : x.val - y.val = 0 := by
      have hdisj := mul_eq_zero.mp hxy
      cases hdisj with
      | inl h0 => exact h0
      | inr hb0 => exact (hb hb0).elim
    -- conclude x.val = y.val
    have : x.val = y.val := by
      have := sub_eq_zero.mp hsubzero
      exact this
    simpa using this
  have hcard_le : Nat.card {α : F // a + α * b = 0} ≤ 1 :=
    Finite.card_le_one_iff_subsingleton.mpr (by apply Subsingleton.intro; intro x y; exact hsub.elim x y)
  exact ⟨hfinite, hcard_le⟩

/-- The finite set of “bad” α values that cause cancellations on `E₀`, plus α = 0. -/
def Bad (E0 : Finset ι) (χ0 χi : ι → F) : Finset F :=
  insert 0 <|
    (E0.filter (fun t => χi t ≠ 0)).image (fun t => - χ0 t / χi t)

omit [Fintype F] [Fintype ι] [DecidableEq ι] in
lemma bad_alpha_card_le (E0 : Finset ι) (χ0 χi : ι → F) :
  (Bad (ι := ι) E0 χ0 χi).card ≤ E0.card.succ := by
  classical
  set S := (E0.filter (fun t => χi t ≠ 0)).image (fun t => - χ0 t / χi t) with hS
  have h1 : (insert (0:F) S).card ≤ S.card.succ := Finset.card_insert_le _ _
  have h2 : S.card ≤ (E0.filter (fun t => χi t ≠ 0)).card := by
    have := Finset.card_image_le (s := E0.filter (fun t => χi t ≠ 0)) (f := fun t => - χ0 t / χi t)
    simpa [hS] using this
  have h3 : (E0.filter (fun t => χi t ≠ 0)).card ≤ E0.card := Finset.card_filter_le _ _
  have : (Bad (ι := ι) E0 χ0 χi).card ≤ S.card.succ := by
    simpa [Bad, hS] using h1
  exact le_trans this (Nat.succ_le_succ (le_trans h2 h3))

omit [Fintype F] [DecidableEq ι] in
/-- Outside `Bad`, the Hamming weight of `χ0 + α • χi` is at least `weight χ0 + 1`. -/
lemma weight_increase_by_one
  (E0 : Finset ι) (χ0 χi : ι → F)
  (j : ι) (hj_new : χi j ≠ 0) (hj_old : χ0 j = 0)
  {α : F} (hα : α ∉ Bad (ι := ι) E0 χ0 χi)
  (hE0 : E0 = (Finset.univ.filter fun t : ι => χ0 t ≠ 0)) :
  hammingNorm (fun t => χ0 t + α * χi t) ≥ hammingNorm χ0 + 1 := by
  classical
  -- α ≠ 0 since 0 ∈ Bad
  have hα_ne0 : α ≠ 0 := by
    intro h; exact hα (by simpa [Bad, h] using Finset.mem_insert_self (0:F) _)
  -- Define supports
  let supp0 : Finset ι := Finset.univ.filter (fun t : ι => χ0 t ≠ 0)
  let suppα : Finset ι := Finset.univ.filter (fun t : ι => χ0 t + α * χi t ≠ 0)
  have hE0' : E0 = supp0 := hE0
  -- Claim 1: No cancellations on E0 = supp0
  have h_nocancel : supp0 ⊆ suppα := by
    intro t ht
    have ht_univ : t ∈ (Finset.univ : Finset ι) := by simp
    have hχ0_ne : χ0 t ≠ 0 := by
      have := (Finset.mem_filter.mp ht).2; simpa [supp0] using this
    by_cases hχi0 : χi t = 0
    · have : χ0 t + α * χi t ≠ 0 := by simpa [hχi0] using hχ0_ne
      exact (Finset.mem_filter.mpr ⟨ht_univ, by simpa [suppα]⟩)
    · have ht_in_E0 : t ∈ E0 := by simpa [hE0', supp0] using ht
      have h_in_image : (- χ0 t / χi t) ∈ (E0.filter (fun s => χi s ≠ 0)).image (fun s => - χ0 s / χi s) := by
        have ht_in_filter : t ∈ E0.filter (fun s => χi s ≠ 0) := by
          exact Finset.mem_filter.mpr ⟨ht_in_E0, hχi0⟩
        exact Finset.mem_image.mpr ⟨t, ht_in_filter, rfl⟩
      have hα_ne_forbid : α ≠ - χ0 t / χi t := by
        intro h_eq
        have hin : (- χ0 t / χi t)
                    ∈ insert (0:F) ((E0.filter (fun s => χi s ≠ 0)).image (fun s => - χ0 s / χi s)) :=
          Finset.mem_insert_of_mem h_in_image
        have hα_in : α ∈ insert (0:F) ((E0.filter (fun s => χi s ≠ 0)).image (fun s => - χ0 s / χi s)) := by
          simpa [h_eq] using hin
        have : α ∈ Bad (ι := ι) E0 χ0 χi := by simpa [Bad] using hα_in
        exact hα this
      have : χ0 t + α * χi t ≠ 0 := by
        intro hsum
        have hαeq : α = - χ0 t / χi t := by
          have hmul : α * χi t = - χ0 t := by
            have : α * χi t + χ0 t = 0 := by simpa [add_comm] using hsum
            exact (eq_neg_iff_add_eq_zero).mpr this
          have := congrArg (fun z => z * (χi t)⁻¹) hmul
          have hχ0 : χi t ≠ 0 := hχi0
          simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, hχ0] using this
        exact hα_ne_forbid hαeq
      exact (Finset.mem_filter.mpr ⟨ht_univ, by simpa [suppα]⟩)
  -- Claim 2: j is newly nonzero in suppα and not in supp0
  have hj_not_in_supp0 : j ∉ supp0 := by
    have : j ∈ (Finset.univ : Finset ι) := by simp
    have : j ∈ Finset.univ.filter (fun t : ι => χ0 t = 0) := by
      simp [Finset.mem_filter, this, hj_old]
    by_contra hjin
    have : χ0 j ≠ 0 := by
      have := (Finset.mem_filter.mp hjin).2; simpa [supp0] using this
    exact this hj_old
  have hj_in_suppα : j ∈ suppα := by
    have : χ0 j + α * χi j ≠ 0 := by
      have : α * χi j ≠ 0 := mul_ne_zero hα_ne0 hj_new
      simpa [hj_old, add_comm] using this
    have hjuniv : j ∈ (Finset.univ : Finset ι) := by simp
    exact (Finset.mem_filter.mpr ⟨hjuniv, by simpa [suppα]⟩)
  -- Cardinality: supp0 ⊆ suppα and j ∈ suppα \ supp0 ⇒ |suppα| ≥ |supp0| + 1
  have hsubset : supp0 ⊆ suppα := by simpa [hE0'] using h_nocancel
  have hstrict_lt : supp0.card < suppα.card := by
    have hss : supp0 ⊂ suppα := by
      refine Finset.ssubset_iff_subset_ne.mpr ?_
      refine And.intro hsubset ?_
      intro hEq; exact hj_not_in_supp0 (by simpa [hEq] using hj_in_suppα)
    exact Finset.card_lt_card hss
  have hstrict : (supp0.card + 1) ≤ suppα.card := Nat.succ_le_of_lt hstrict_lt
  simpa [hammingNorm, supp0, suppα, Nat.add_comm] using hstrict

omit [Fintype ι] [DecidableEq ι] in
lemma exists_good_alpha
  {e : ℕ}
  (hF : Nat.card F ≥ e.succ.succ)
  (E0 : Finset ι) (χ0 χi : ι → F)
  (t_le_e : E0.card ≤ e) :
  ∃ α : F, α ≠ 0 ∧ α ∉ Bad (ι := ι) E0 χ0 χi := by
  classical
  have hBad_le : (Bad (ι := ι) E0 χ0 χi).card ≤ e.succ :=
    (bad_alpha_card_le (E0 := E0) (χ0 := χ0) (χi := χi)).trans (Nat.succ_le_succ t_le_e)
  have : (Bad (ι := ι) E0 χ0 χi).card < Nat.card F := by
    have h1 : e.succ < e.succ.succ := Nat.lt_succ_self _
    have h2 : e.succ.succ ≤ Nat.card F := by simpa using hF
    exact lt_of_le_of_lt hBad_le (lt_of_lt_of_le h1 h2)
  obtain ⟨α, hα_notin⟩ :=
    exists_not_mem_of_card_lt_univ (s := (Bad (ι := ι) E0 χ0 χi)) this
  have hα_ne0 : α ≠ 0 := by
    intro h0
    exact hα_notin (by simp [Bad, h0])
  exact ⟨α, hα_ne0, hα_notin⟩

end Lemma43
end InterleavedCode
