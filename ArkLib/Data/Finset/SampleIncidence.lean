/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Set.Card
public import Mathlib.Algebra.Order.Chebyshev
public import ArkLib.ToMathlib.Set.Finite

/-!
# Sample-incidence bounds for finite-set families

Let `S x` be a finite subset of an ambient finite type. If every `S x` has at least `A`
elements and no `k`-element sample belongs to two distinct family members, then double counting
the pairs `(x, sample)` gives

`|T| * A.choose k ≤ (Fintype.card ι).choose k`.

When `k ≤ A`, the set-level theorem derives finiteness from the same bound rather than assuming
the family or ambient indexing type is finite. This is the generic incidence argument behind finite
agreement
lists; it has no coding-theory, field, or polynomial hypotheses.
-/

@[expose] public section

namespace Finset

open Classical in
/-- A finite family whose distinct members have intersection size below `k` satisfies the sharp
`k`-sample incidence bound. -/
theorem card_mul_choose_le_of_inter_card_lt
    {κ ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : Finset κ) (S : κ → Finset ι) (A k : ℕ)
    (hlarge : ∀ x ∈ T, A ≤ (S x).card)
    (hpair : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → ((S x) ∩ (S y)).card < k) :
    T.card * A.choose k ≤ (Fintype.card ι).choose k := by
  let samples := (Finset.univ : Finset ι).powersetCard k
  let incidence := T.sigma fun x ↦ (S x).powersetCard k
  have hincidenceLower : T.card * A.choose k ≤ incidence.card := by
    simp only [incidence, Finset.card_sigma]
    calc
      T.card * A.choose k = ∑ _x ∈ T, A.choose k := by simp
      _ ≤ ∑ x ∈ T, (S x).card.choose k := by
        apply Finset.sum_le_sum
        intro x hx
        exact Nat.choose_le_choose k (hlarge x hx)
      _ = ∑ x ∈ T, ((S x).powersetCard k).card := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.card_powersetCard]
  have hincidenceUpper : incidence.card ≤ samples.card := by
    apply Finset.card_le_card_of_injOn Sigma.snd
    · intro x hx
      obtain ⟨_, hxsample⟩ := Finset.mem_sigma.mp hx
      exact Finset.mem_powersetCard.mpr
        ⟨(Finset.mem_powersetCard.mp hxsample).1.trans (Finset.subset_univ _),
          (Finset.mem_powersetCard.mp hxsample).2⟩
    · intro x hx y hy hxy
      obtain ⟨hxT, hxsample⟩ := Finset.mem_sigma.mp hx
      obtain ⟨hyT, hysample⟩ := Finset.mem_sigma.mp hy
      have hxdata := Finset.mem_powersetCard.mp hxsample
      have hydata := Finset.mem_powersetCard.mp hysample
      have hindex : x.1 = y.1 := by
        by_contra hne
        have hsubset : x.2 ⊆ S x.1 ∩ S y.1 := by
          intro i hi
          exact Finset.mem_inter.mpr ⟨hxdata.1 hi, hydata.1 (hxy ▸ hi)⟩
        have hk_le : k ≤ ((S x.1) ∩ (S y.1)).card := by
          rw [← hxdata.2]
          exact Finset.card_le_card hsubset
        exact (Nat.not_lt_of_ge hk_le) (hpair x.1 hxT y.1 hyT hne)
      cases x with
      | mk xIndex xSample =>
          cases y with
          | mk yIndex ySample =>
              change xIndex = yIndex at hindex
              change xSample = ySample at hxy
              subst yIndex
              subst ySample
              rfl
  exact hincidenceLower.trans <| by
    calc
      incidence.card ≤ samples.card := hincidenceUpper
      _ = (Fintype.card ι).choose k := by simp [samples]

end Finset

namespace Set

open Classical in
/-- The set-level sample-incidence theorem. Finiteness follows from the uniform bound on every
finite subfamily, so the family type itself need not be finite. -/
theorem finite_and_ncard_mul_choose_le_of_inter_card_lt
    {κ ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Set κ) (S : κ → Finset ι) (A k : ℕ) (hkA : k ≤ A)
    (hlarge : ∀ x ∈ C, A ≤ (S x).card)
    (hpair : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → ((S x) ∩ (S y)).card < k) :
    C.Finite ∧ C.ncard * A.choose k ≤ (Fintype.card ι).choose k := by
  have hchoose : 0 < A.choose k := Nat.choose_pos hkA
  have hfinite : C.Finite := by
    apply Set.finite_of_forall_finset_card_le
      (R := ℕ) (ℓ := (Fintype.card ι).choose k / A.choose k)
    intro T hT
    apply (Nat.le_div_iff_mul_le hchoose).2
    exact Finset.card_mul_choose_le_of_inter_card_lt T S A k
      (fun x hx ↦ hlarge x (hT hx))
      (fun x hx y hy hne ↦ hpair x (hT hx) y (hT hy) hne)
  refine ⟨hfinite, ?_⟩
  rw [Set.ncard_eq_toFinset_card C hfinite]
  exact Finset.card_mul_choose_le_of_inter_card_lt hfinite.toFinset S A k
    (fun x hx ↦ hlarge x (hfinite.mem_toFinset.mp hx))
    (fun x hx y hy hne ↦
      hpair x (hfinite.mem_toFinset.mp hx) y (hfinite.mem_toFinset.mp hy) hne)

end Set
