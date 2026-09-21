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
division rings. If `K` is finite, `M` is a nontrivial finite-dimensional `K`-module, and a family
contains at most `|K| = Nat.card K` proper submodules, then some vector lies outside every member
of the family.

Mathlib's `Submodule.iUnion_ssubset_of_forall_ne_top_of_card_lt` proves the corresponding result
for strictly fewer than `|K|` submodules without requiring the ambient space to be finite. The
finite counting argument below covers equality as well: each proper submodule contains at most
`|K|^(finrank K M - 1)` vectors, and counting nonzero vectors avoids overcounting their common
zero vector.

## Main statement

* `Submodule.exists_forall_notMem_of_card_le` — at most `|K|` proper submodules do not cover a
  nontrivial finite `K`-vector space.

## References

The proof is extracted from
`ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.PowerAgreement` at immutable ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`, where it selected a common projection for an
interleaved Reed--Solomon argument.
-/

@[expose] public section

namespace Submodule

/-- A family of at most `|K|` proper submodules cannot cover a nontrivial finite vector space
over the finite division ring `K`.

The nontriviality assumption records the positive-dimension condition of the source theorem.
The weak inequality on `s.card` is the sharp finite-division-ring boundary and is stronger than
the strict-cardinality hypothesis of Mathlib's general union theorem. -/
theorem exists_forall_notMem_of_card_le
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

end Submodule
