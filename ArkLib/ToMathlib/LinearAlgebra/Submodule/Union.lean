/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Algebra.Module.Submodule.Union
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Avoiding a finite union of proper submodules

This file strengthens Mathlib's finite-union avoidance theorem at the sharp boundary for finite
division rings. If `K` is finite and a family contains at most `|K| = Nat.card K` proper
submodules of a `K`-module `M`, then some vector lies outside every member of the family. The
module `M` may be infinite-dimensional or trivial.

Mathlib's `Submodule.iUnion_ssubset_of_forall_ne_top_of_card_lt` proves the corresponding result
over a field for strictly fewer than `|K|` submodules. For finite `K`, the theorem below also
covers equality. The bound is sharp: a two-dimensional space over `K` is the union of its
`|K| + 1` lines through the origin.

## Main statement

* `Submodule.exists_forall_notMem_of_card_le` — at most `|K|` proper submodules do not cover a
  module over the finite division ring `K`.

## Proof outline

In a nontrivial finite-dimensional space of dimension `d`, each proper submodule has at most
`|K|^(d - 1) - 1` nonzero vectors. Counting nonzero vectors, which avoids overcounting the common
zero vector, shows that at most `|K|` proper submodules cover fewer than `|K|^d` vectors. A general
module reduces to this case: the span of one chosen vector outside each proper submodule is a
finite-dimensional submodule in which every restricted member of the family remains proper.

## References

The counting proof is extracted from
`ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.PowerAgreement` at immutable ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`, where `exists_vector_avoiding_submodules` selected a
common projection for an interleaved Reed--Solomon argument. The source theorem assumed a finite
nontrivial ambient module; this file removes both assumptions.
-/

@[expose] public section

namespace Submodule

/-- The counting argument behind `exists_forall_notMem_of_card_le`, in a nontrivial
finite-dimensional module. -/
private theorem exists_forall_notMem_of_card_le_of_finiteDimensional
    {ι K M : Type*} [DivisionRing K] [Finite K] [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] [Nontrivial M]
    (s : Finset ι) (p : ι → Submodule K M)
    (hp : ∀ i ∈ s, p i ≠ ⊤) (hs : s.card ≤ Nat.card K) :
    ∃ x : M, ∀ i ∈ s, x ∉ p i := by
  classical
  let _ := Fintype.ofFinite K
  let b := Module.finBasis K M
  let _ : Finite M :=
    Finite.of_equiv (Fin (Module.finrank K M) → K) b.equivFun.toEquiv.symm
  let _ := Fintype.ofFinite M
  let q := Fintype.card K
  let d := Module.finrank K M
  let nonzero (i : ι) := Finset.univ.filter fun x : M ↦ x ∈ p i ∧ x ≠ 0
  let covered := insert (0 : M) (s.biUnion nonzero)
  have hq : 1 < q := Fintype.one_lt_card
  have hd : 0 < d := Module.finrank_pos
  have hs' : s.card ≤ q := by
    simpa only [q, Nat.card_eq_fintype_card] using hs
  have hnonzero (i : ι) (hi : i ∈ s) :
      (nonzero i).card ≤ q ^ (d - 1) - 1 := by
    let all := Finset.univ.filter fun x : M ↦ x ∈ p i
    have hzero : (0 : M) ∈ all := by simp [all]
    have hnonzero_eq : nonzero i = all.erase 0 := by
      ext x
      simp [nonzero, all, and_comm]
    rw [hnonzero_eq, Finset.card_erase_of_mem hzero]
    have hcard : all.card = Fintype.card (p i) := by
      symm
      exact Fintype.card_ofFinset all (by simp [all])
    have hcardpow : Fintype.card (p i) = q ^ Module.finrank K (p i) := by
      simpa [q] using (Module.card_eq_pow_finrank (K := K) (V := p i))
    rw [hcard, hcardpow]
    exact Nat.sub_le_sub_right
      (Nat.pow_le_pow_right (Nat.zero_lt_of_lt hq)
        (Nat.le_sub_one_of_lt (Submodule.finrank_lt (hp i hi)))) 1
  have hcovered : covered.card < Fintype.card M := by
    have hbiUnion : (s.biUnion nonzero).card ≤ s.card * (q ^ (d - 1) - 1) := by
      calc
        (s.biUnion nonzero).card ≤ ∑ i ∈ s, (nonzero i).card :=
          Finset.card_biUnion_le
        _ ≤ ∑ _i ∈ s, (q ^ (d - 1) - 1) :=
          Finset.sum_le_sum fun i hi ↦ hnonzero i hi
        _ = s.card * (q ^ (d - 1) - 1) := by simp
    have hmul : s.card * (q ^ (d - 1) - 1) ≤ q * (q ^ (d - 1) - 1) :=
      Nat.mul_le_mul_right _ hs'
    have hpow : q ^ d = q * q ^ (d - 1) := by
      conv_lhs => rw [← Nat.succ_pred_eq_of_pos hd]
      simp [pow_succ, Nat.mul_comm]
    have hcardM : Fintype.card M = q ^ d := by
      simpa [q, d] using (Module.card_eq_pow_finrank (K := K) (V := M))
    rw [hcardM, hpow]
    calc
      covered.card ≤ (s.biUnion nonzero).card + 1 := Finset.card_insert_le _ _
      _ ≤ s.card * (q ^ (d - 1) - 1) + 1 := Nat.add_le_add_right hbiUnion 1
      _ ≤ q * (q ^ (d - 1) - 1) + 1 := Nat.add_le_add_right hmul 1
      _ < q * q ^ (d - 1) := by
        have hpos : 0 < q ^ (d - 1) := pow_pos (Nat.zero_lt_of_lt hq) _
        have hqmul : q ≤ q * q ^ (d - 1) := by
          simpa using Nat.mul_le_mul_left q hpos
        rw [Nat.mul_sub_left_distrib]
        simp only [mul_one]
        omega
  obtain ⟨x, -, hx⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := covered) (t := Finset.univ) (by simpa using hcovered)
  refine ⟨x, fun i hi hxi ↦ hx ?_⟩
  by_cases hx0 : x = 0
  · simp [covered, hx0]
  · simp only [covered, Finset.mem_insert]
    exact Or.inr (Finset.mem_biUnion.mpr ⟨i, hi, by simp [nonzero, hxi, hx0]⟩)

/-- A family of at most `|K|` proper submodules cannot cover a module over the finite division
ring `K`.

The module `M` need not be finite-dimensional or nontrivial; for trivial `M`, every submodule is
`⊤`, so the properness hypothesis forces `s` to be empty. The weak inequality on `s.card` is the
sharp finite-division-ring boundary and is stronger than the strict-cardinality hypothesis of
Mathlib's general union theorem. -/
theorem exists_forall_notMem_of_card_le
    {ι K M : Type*} [DivisionRing K] [Finite K] [AddCommGroup M] [Module K M]
    -- The family is indexed by `s`, and each of its members is a proper submodule.
    (s : Finset ι) (p : ι → Submodule K M) (hp : ∀ i ∈ s, p i ≠ ⊤)
    -- The family has at most as many members as the coefficient ring has elements.
    (hs : s.card ≤ Nat.card K) :
    ∃ x : M, ∀ i ∈ s, x ∉ p i := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
  · exact ⟨0, by simp⟩
  have hwitness : ∀ i ∈ s, ∃ v : M, v ∉ p i := by
    intro i hi
    by_contra! hall
    exact hp i hi (eq_top_iff.mpr fun v _ ↦ hall v)
  choose! v hv using hwitness
  let W : Submodule K M := span K ((s.image v : Finset M) : Set M)
  have hvW : ∀ i ∈ s, v i ∈ W := fun i hi ↦
    subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem v hi))
  have hv₀ : v i₀ ≠ 0 := fun h ↦ hv i₀ hi₀ (h ▸ (p i₀).zero_mem)
  have : Nontrivial W :=
    nontrivial_of_ne ⟨v i₀, hvW i₀ hi₀⟩ 0 fun h ↦ hv₀ (congrArg Subtype.val h)
  obtain ⟨x, hx⟩ := exists_forall_notMem_of_card_le_of_finiteDimensional s
    (fun i ↦ (p i).comap W.subtype)
    (fun i hi htop ↦ hv i hi <| by
      have hmem : (⟨v i, hvW i hi⟩ : W) ∈ (p i).comap W.subtype := htop ▸ mem_top
      simpa using hmem)
    hs
  exact ⟨x, fun i hi hxi ↦ hx i hi (by simpa using hxi)⟩

end Submodule
