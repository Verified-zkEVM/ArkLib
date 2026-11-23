/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Multiset.UnionInter

/-!
# Generic zero patterns and generic multiplicity patterns

A family `S : Fin m → Finset σ` is a *generic zero pattern* if every nonempty subfamily `I`
satisfies `#(⋂_{ℓ ∈ I} S ℓ) + #I ≤ m`. Over an infinite field, every generic zero pattern is
realised by `m` linearly independent polynomials of degree `< m` and distinct points: the `ℓ`-th
polynomial vanishes at the points of `S ℓ`
(`Polynomial.exists_embedding_linearIndependent_of_isGenericZeroPattern`); the finite-field bound
of [Lov18, Theorem 1.2] is not proved here.

The proof runs through a more general notion on multiplicity vectors, which we represent as
multisets `s i : Multiset ι`: the family is a *generic multiplicity pattern of dimension `k`* if
`card (s i) < k` for every `i` and every nonempty subfamily `I` satisfies
`∑_{i ∈ I} (k - card (s i)) + card (⨅_{i ∈ I} s i) ≤ k`.

This file contains the definitions and their basic closure properties; the induction proving that
the associated polynomial families are linearly independent is in
`ArkLib.ToMathlib.RingTheory.Polynomial.GenericZeroPattern`.

## Main definitions

* `Finset.IsGenericZeroPattern m S`: the generic zero pattern condition. It is decidable, so
  `decide` checks it on small explicit families.
* `Multiset.IsGenericMultiplicityPattern k s`: the generic multiplicity pattern condition.
* `Multiset.CountLeOneExcept d s`: every multiplicity is at most one except at the point `d`.

## Main statements

* `Multiset.IsGenericMultiplicityPattern.not_le`: no member of a generic multiplicity pattern is
  contained in another one.
* `Finset.IsGenericZeroPattern.exists_pad`: a generic zero pattern extends, by points private to
  each set, to one whose sets all have `m - 1` elements.

## References

* [Lovett, S., *MDS matrices over small fields: A proof of the GM-MDS conjecture*][Lov18]
-/

@[expose] public section

universe u

open Finset

variable {α β ι : Type*} {σ : Type u}

namespace Finset

/-- A family of `m` finite sets `S ℓ` is a *generic zero pattern* if every nonempty subfamily `I`
satisfies `#(⋂_{ℓ ∈ I} S ℓ) + #I ≤ m`. -/
def IsGenericZeroPattern [DecidableEq σ] (m : ℕ) (S : Fin m → Finset σ) : Prop :=
  ∀ (I : Finset (Fin m)) (hI : I.Nonempty), #(I.inf' hI S) + #I ≤ m

instance [DecidableEq σ] (m : ℕ) (S : Fin m → Finset σ) : Decidable (IsGenericZeroPattern m S) :=
  inferInstanceAs (Decidable (∀ (I : Finset (Fin m)) (hI : I.Nonempty), #(I.inf' hI S) + #I ≤ m))

end Finset

namespace Multiset

/-- A family of multisets `s i` (multiplicity vectors on `ι`) is a *generic multiplicity pattern
of dimension `k`* if each `s i` has fewer than `k` elements and every nonempty subfamily `I`
satisfies `∑_{i ∈ I} (k - card (s i)) + card (⨅_{i ∈ I} s i) ≤ k`. -/
structure IsGenericMultiplicityPattern [DecidableEq ι] (k : ℕ) (s : α → Multiset ι) : Prop where
  /-- Each multiset has fewer than `k` elements. -/
  card_lt : ∀ i, Multiset.card (s i) < k
  /-- The subfamily condition. -/
  sum_add_card_inf'_le : ∀ (I : Finset α) (hI : I.Nonempty),
    ∑ i ∈ I, (k - Multiset.card (s i)) + Multiset.card (I.inf' hI s) ≤ k

/-- Every multiset `s i` has multiplicity at most one at every point other than `d`. -/
def CountLeOneExcept [DecidableEq ι] (d : ι) (s : α → Multiset ι) : Prop :=
  ∀ i x, x ≠ d → (s i).count x ≤ 1

namespace IsGenericMultiplicityPattern

variable [DecidableEq ι] {k : ℕ} {s : α → Multiset ι}

/-- No member of a generic multiplicity pattern is contained in another one. -/
theorem not_le (hs : IsGenericMultiplicityPattern k s) {i j : α} (hij : i ≠ j) :
    ¬ s i ≤ s j := by
  classical
  intro hle
  have h := hs.sum_add_card_inf'_le {i, j} (Finset.insert_nonempty _ _)
  have hinf : ({i, j} : Finset α).inf' (Finset.insert_nonempty _ _) s = s i := by
    rw [Finset.inf'_insert, Finset.inf'_singleton]
    · exact inf_eq_left.2 hle
    · exact Finset.singleton_nonempty j
  rw [Finset.sum_pair hij, hinf] at h
  have := hs.card_lt i
  have := hs.card_lt j
  omega

/-- A subfamily of a generic multiplicity pattern is one. -/
theorem comp (hs : IsGenericMultiplicityPattern k s) (e : β → α) (he : Function.Injective e) :
    IsGenericMultiplicityPattern k (s ∘ e) := by
  classical
  refine ⟨fun i => hs.card_lt (e i), fun I hI => ?_⟩
  have h := hs.sum_add_card_inf'_le (I.map ⟨e, he⟩) hI.map
  rw [Finset.sum_map, Finset.inf'_map] at h
  exact h

/-- Removing a point common to all multisets lowers the dimension by one. -/
theorem erase (hs : IsGenericMultiplicityPattern k s) {d : ι} (hd : CountLeOneExcept d s)
    (j : ι) (hj : ∀ i, j ∈ s i) :
    IsGenericMultiplicityPattern (k - 1) (fun i => (s i).erase j) ∧
      CountLeOneExcept d (fun i => (s i).erase j) := by
  have hcard : ∀ i, Multiset.card ((s i).erase j) + 1 = Multiset.card (s i) := fun i => by
    rw [Multiset.card_erase_of_mem (hj i), Nat.pred_eq_sub_one]
    have := Multiset.card_pos_iff_exists_mem.2 ⟨j, hj i⟩
    omega
  refine ⟨⟨fun i => ?_, fun I hI => ?_⟩, fun i x hx => ?_⟩
  · have := hcard i
    have := hs.card_lt i
    omega
  · have h := hs.sum_add_card_inf'_le I hI
    have hsum : ∑ i ∈ I, (k - 1 - Multiset.card ((s i).erase j)) =
        ∑ i ∈ I, (k - Multiset.card (s i)) :=
      Finset.sum_congr rfl fun i _ => by have := hcard i; omega
    have hle : j ::ₘ I.inf' hI (fun i => (s i).erase j) ≤ I.inf' hI s :=
      Finset.le_inf' hI _ fun i hi => by
        have := Multiset.cons_le_cons j (Finset.inf'_le (fun i => (s i).erase j) hi)
        rwa [Multiset.cons_erase (hj i)] at this
    have hc := Multiset.card_le_card hle
    rw [Multiset.card_cons] at hc
    rw [hsum]
    omega
  · exact (Multiset.count_le_of_le x (Multiset.erase_le j (s i))).trans (hd i x hx)

end IsGenericMultiplicityPattern

/-- Subfamilies keep the bound on multiplicities. -/
theorem CountLeOneExcept.comp [DecidableEq ι] {d : ι} {s : α → Multiset ι}
    (hd : CountLeOneExcept d s) (e : β → α) : CountLeOneExcept d (s ∘ e) :=
  fun i => hd (e i)

end Multiset

namespace Finset

open Multiset (IsGenericMultiplicityPattern CountLeOneExcept)

namespace IsGenericZeroPattern

variable [DecidableEq σ] {m : ℕ} {S : Fin m → Finset σ}

/-- A generic zero pattern whose sets all have `m - 1` elements is a generic multiplicity pattern
of dimension `m`, with all multiplicities at most one. -/
theorem isGenericMultiplicityPattern (hS : IsGenericZeroPattern m S)
    (hcard : ∀ ℓ, #(S ℓ) + 1 = m) :
    IsGenericMultiplicityPattern m (fun ℓ => (S ℓ).val) := by
  refine ⟨fun ℓ => ?_, fun I hI => ?_⟩
  · rw [Finset.card_val]
    have := hcard ℓ
    omega
  · have hinf : I.inf' hI (fun ℓ => (S ℓ).val) = (I.inf' hI S).val :=
      (Finset.apply_inf'_eq_inf'_comp hI (f := S) Finset.val fun a b => Finset.inter_val a b).symm
    have hsum : ∑ ℓ ∈ I, (m - Multiset.card (S ℓ).val) = #I := by
      rw [Finset.card_eq_sum_ones]
      exact Finset.sum_congr rfl fun ℓ _ => by
        rw [Finset.card_val]
        have := hcard ℓ
        omega
    rw [hinf, hsum, Finset.card_val]
    have := hS I hI
    omega

/-- Padding: a generic zero pattern on `σ` extends, by points private to each set, to a generic
zero pattern on a larger finite type whose sets all have `m - 1` elements. -/
theorem exists_pad [Finite σ] (hS : IsGenericZeroPattern m S) :
    ∃ (τ : Type u) (_ : Fintype τ) (_ : DecidableEq τ) (e : σ ↪ τ) (S' : Fin m → Finset τ),
      IsGenericZeroPattern m S' ∧ (∀ ℓ, #(S' ℓ) + 1 = m) ∧ ∀ ℓ, (S ℓ).map e ⊆ S' ℓ := by
  classical
  have := Fintype.ofFinite σ
  have hle : ∀ ℓ, #(S ℓ) + 1 ≤ m := fun ℓ => by
    simpa using hS {ℓ} (Finset.singleton_nonempty ℓ)
  let τ := σ ⊕ (Σ ℓ : Fin m, Fin (m - 1 - #(S ℓ)))
  let pad : Fin m → Finset τ := fun ℓ =>
    (Finset.univ : Finset (Fin (m - 1 - #(S ℓ)))).map
      ⟨fun t => Sum.inr ⟨ℓ, t⟩, fun a b h => eq_of_heq (Sigma.mk.inj (Sum.inr_injective h)).2⟩
  let S' : Fin m → Finset τ := fun ℓ => (S ℓ).map Function.Embedding.inl ∪ pad ℓ
  have hinr : ∀ ℓ ℓ' t, (Sum.inr ⟨ℓ', t⟩ : τ) ∈ S' ℓ → ℓ' = ℓ := by
    intro ℓ ℓ' t h
    simp only [S', pad, Finset.mem_union, Finset.mem_map, Finset.mem_univ, true_and] at h
    rcases h with ⟨y, -, hy⟩ | ⟨w, hw⟩
    · simp at hy
    · exact (Sigma.mk.inj (Sum.inr_injective hw)).1.symm
  have hinl : ∀ ℓ y, (Sum.inl y : τ) ∈ S' ℓ → y ∈ S ℓ := by
    intro ℓ y h
    simp only [S', pad, Finset.mem_union, Finset.mem_map, Finset.mem_univ, true_and] at h
    rcases h with ⟨z, hz, hzy⟩ | ⟨w, hw⟩
    · have : z = y := Sum.inl_injective hzy
      exact this ▸ hz
    · simp at hw
  have hcardS' : ∀ ℓ, #(S' ℓ) + 1 = m := fun ℓ => by
    have hdisj : Disjoint ((S ℓ).map Function.Embedding.inl) (pad ℓ) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [Finset.mem_map, pad] at hx hx'
      obtain ⟨y, -, rfl⟩ := hx
      obtain ⟨t, -, ht⟩ := hx'
      simp at ht
    have := hle ℓ
    simp only [S']
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_map, Finset.card_map, Finset.card_univ,
      Fintype.card_fin]
    omega
  refine ⟨τ, inferInstance, inferInstance, Function.Embedding.inl, S', fun I hI => ?_, hcardS',
    fun ℓ => Finset.subset_union_left⟩
  by_cases h1 : #I = 1
  · obtain ⟨ℓ, rfl⟩ := Finset.card_eq_one.1 h1
    rw [Finset.inf'_singleton, Finset.card_singleton]
    exact (hcardS' ℓ).le
  have hsub : I.inf' hI S' ⊆ (I.inf' hI S).map Function.Embedding.inl := by
    intro x hx
    rw [Finset.mem_inf'] at hx
    obtain ⟨a, ha⟩ := id hI
    obtain ⟨b, hb, hba⟩ := Finset.exists_mem_ne (s := I) (by have := hI.card_pos; omega) a
    rcases x with y | ⟨ℓ, t⟩
    · rw [Finset.mem_map]
      refine ⟨y, ?_, rfl⟩
      rw [Finset.mem_inf']
      exact fun i hi => hinl i y (hx i hi)
    · exact absurd ((hinr b ℓ t (hx b hb)).symm.trans (hinr a ℓ t (hx a ha))) hba
  have := Finset.card_le_card hsub
  rw [Finset.card_map] at this
  have := hS I hI
  omega

end IsGenericZeroPattern

/-- The underlying multisets of a family of finite sets have all multiplicities at most one. -/
theorem countLeOneExcept_val [DecidableEq σ] {γ : Type*} (d : σ) (S : γ → Finset σ) :
    CountLeOneExcept d (fun ℓ => (S ℓ).val) :=
  fun ℓ x _ => Multiset.nodup_iff_count_le_one.mp (S ℓ).nodup x

end Finset
