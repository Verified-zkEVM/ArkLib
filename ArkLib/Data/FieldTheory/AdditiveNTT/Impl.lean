/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.Data.FieldTheory.AdditiveNTT.AdditiveNTT

/-!
# Additive NTT Computable Implementation

This module provides computable Additive-NTT primitives and algorithm definitions under
`AdditiveNTT.Comp`, while keeping loose-index wrappers (`Fin r`) for downstream migration.
-/

namespace AdditiveNTT.Comp

universe u
open Polynomial AdditiveNTT Module
open scoped Polynomial

section HelperFunctions

/-- Converts an `Array` to a function on `Fin n` when sizes match. -/
def Array.toFinVec {α : Type _} (n : ℕ) (arr : Array α) (h : arr.size = n) : Fin n → α :=
  fun i => arr[i]

/-- Product over `List.finRange` is definitionaly equal to product over `Finset.univ`. -/
lemma List.prod_finRange_eq_finset_prod {M : Type*} [CommMonoid M] {n : ℕ}
    (f : Fin n → M) :
    ((List.finRange n).map f).prod = ∏ i : Fin n, f i := rfl

end HelperFunctions

variable {r : ℕ} [NeZero r]
variable {L : Type u} [Field L] [Fintype L] [DecidableEq L]
variable {𝔽q : Type u} [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
variable [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ R_rate : ℕ} [NeZero ℓ] (h_ℓ_add_R_rate : ℓ + R_rate < r)

/-- Executable value-level encoding of points in `U i` by bit-index. -/
def bitsToUValue (i : Fin r) (k : Fin (2 ^ i.val)) : L :=
  AdditiveNTT.bitsToUValue β i k

/-- Executable subtype-level encoding of points in `U i` by bit-index. -/
def bitsToU (i : Fin r) (k : Fin (2 ^ i.val)) :
    AdditiveNTT.U (L := L) (𝔽q := 𝔽q) (β := β) i :=
  ⟨AdditiveNTT.Comp.bitsToUValue (β := β) i k, by
    sorry⟩

omit [DecidableEq 𝔽q] h_Fq_char_prime h_β₀_eq_1 in
/-- Bijection witness for `bitsToU`; proof migration can be completed incrementally. -/
theorem bitsToU_bijective (i : Fin r) :
    Function.Bijective (bitsToU (𝔽q := 𝔽q) (β := β) i) := by
  sorry

/-- Executable enumeration of all elements in `U i`. -/
def getUElements (i : Fin r) : List L :=
  AdditiveNTT.getUElements β i

/-- Executable evaluation of `Wᵢ` at a point. -/
def evalWAt (i : Fin r) (x : L) : L :=
  AdditiveNTT.evalWAt β i x

/-- Executable evaluation of `Ŵᵢ` at a point. -/
def evalNormalizedWAt (i : Fin r) (x : L) : L :=
  AdditiveNTT.evalNormalizedWAt β i x

/-- Computable domain companion with loose indexing (`Fin r`). -/
def sDomain (i : Fin r) : Subspace 𝔽q L :=
  AdditiveNTT.sDomainComp (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i

/-- Upper-domain index `ℓ + R_rate`, used to decode query points from `Fin` indices. -/
def upperDomainIndex : Fin r := ⟨ℓ + R_rate, h_ℓ_add_R_rate⟩

/-- Decode a global domain index into an element of `sDomainComp i`. -/
def indexToSDomain (i : Fin r) (k : Fin (2 ^ (ℓ + R_rate))) :
    sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i :=
  let uTop : AdditiveNTT.U (L := L) (𝔽q := 𝔽q) (β := β)
      (upperDomainIndex (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
    bitsToU (𝔽q := 𝔽q) (β := β)
      (i := upperDomainIndex (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) k
  ⟨AdditiveNTT.evalNormalizedWLinearMap (𝔽q := 𝔽q) (β := β) i
      (uTop : L), by
    change
      AdditiveNTT.evalNormalizedWLinearMap (𝔽q := 𝔽q) (β := β) i
        (uTop : L)
        ∈ AdditiveNTT.sDomainComp (𝔽q := 𝔽q) (β := β)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
    unfold AdditiveNTT.sDomainComp
    exact ⟨(uTop : L), uTop.property, rfl⟩⟩

/-- Decode a global domain index into the query domain (`i = 0`). -/
def indexToSDomainZero (k : Fin (2 ^ (ℓ + R_rate))) :
    sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 :=
  indexToSDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0) k

/-- At stage `0`, the executable normalized evaluation map is the identity. -/
lemma evalNormalizedWLinearMap_zero_apply (x : L) :
    AdditiveNTT.evalNormalizedWLinearMap
        (𝔽q := 𝔽q) β (0 : Fin r) x = x := by
  rw [AdditiveNTT.evalNormalizedWLinearMap_apply]
  rw [AdditiveNTT.normalizedW, AdditiveNTT.W₀_eq_X, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X]
  rw [h_β₀_eq_1.out, div_one]
  simp

/-- At stage `0`, the computable query domain is exactly the top additive subspace. -/
lemma sDomainZero_eq_upperDomain :
    sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 =
    AdditiveNTT.U (𝔽q := 𝔽q) (β := β)
      (upperDomainIndex (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨u, hu, rfl⟩
    rw [evalNormalizedWLinearMap_zero_apply (𝔽q := 𝔽q) (β := β) u]
    exact hu
  · intro hx
    refine ⟨x, hx, ?_⟩
    rw [evalNormalizedWLinearMap_zero_apply (𝔽q := 𝔽q) (β := β) x]

/-- The executable zero-stage decoder agrees with the explicit bit encoding on values. -/
lemma indexToSDomainZero_val_eq_bitsToU_val (k : Fin (2 ^ (ℓ + R_rate))) :
    ((indexToSDomainZero (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) k : sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ)
        (R_rate := R_rate) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0) : L) =
      (bitsToU (𝔽q := 𝔽q) (β := β)
        (i := upperDomainIndex (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) k : L) := by
  unfold indexToSDomainZero indexToSDomain
  dsimp
  rw [evalNormalizedWLinearMap_zero_apply (𝔽q := 𝔽q) (β := β)
    ((bitsToU (𝔽q := 𝔽q) (β := β)
      (i := upperDomainIndex (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) k : L))]

/-- The zero-stage decoder is a computable bijection from global indices to query-domain points. -/
theorem indexToSDomainZero_bijective :
    Function.Bijective
      (indexToSDomainZero (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) := by
  let upperIdx : Fin r := upperDomainIndex (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  constructor
  · intro a b hab
    have hsub :
        bitsToU (𝔽q := 𝔽q) (β := β) (i := upperIdx) a =
          bitsToU (𝔽q := 𝔽q) (β := β) (i := upperIdx) b := by
      apply Subtype.ext
      simpa [upperIdx,
        indexToSDomainZero_val_eq_bitsToU_val (𝔽q := 𝔽q) (β := β)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)] using congrArg Subtype.val hab
    exact (bitsToU_bijective (𝔽q := 𝔽q) (β := β)
      (i := upperIdx)).injective hsub
  · intro x
    have hxU : x.1 ∈ AdditiveNTT.U (𝔽q := 𝔽q) (β := β) upperIdx := by
      simpa [upperIdx, sDomainZero_eq_upperDomain (𝔽q := 𝔽q) (β := β)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)] using x.2
    let uTop : AdditiveNTT.U (𝔽q := 𝔽q) (β := β) upperIdx := ⟨x.1, hxU⟩
    obtain ⟨k, hk⟩ := (bitsToU_bijective (𝔽q := 𝔽q) (β := β)
      (i := upperIdx)).surjective uTop
    refine ⟨k, ?_⟩
    apply Subtype.ext
    rw [indexToSDomainZero_val_eq_bitsToU_val (𝔽q := 𝔽q) (β := β)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)]
    simpa [upperIdx, uTop] using congrArg Subtype.val hk

/-- Bridge: every computable-domain point is also in canonical `AdditiveNTT.sDomain`. -/
theorem mem_sDomain_of_mem_sDomainComp {i : Fin r} {x : L}
    (hx : x ∈ sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :
    x ∈ AdditiveNTT.sDomain (𝔽q := 𝔽q) (β := β)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i := by
  rcases hx with ⟨u, hu, rfl⟩
  refine ⟨u, hu, ?_⟩
  simpa [AdditiveNTT.evalNormalizedWLinearMap_apply, polyEvalLinearMap]
    using (AdditiveNTT.evalNormalizedWLinearMap_apply (𝔽q := 𝔽q) (β := β)
      (i := i) (x := u)).symm

/-- Bridge: canonical `sDomain` points are also computable `sDomainComp` points. -/
theorem mem_sDomainComp_of_mem_sDomain {i : Fin r} {x : L}
    (hx : x ∈ AdditiveNTT.sDomain (𝔽q := 𝔽q) (β := β)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :
    x ∈ sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i := by
  rcases hx with ⟨u, hu, rfl⟩
  refine ⟨u, hu, ?_⟩
  simpa [AdditiveNTT.evalNormalizedWLinearMap_apply, polyEvalLinearMap]

/-- The computable and canonical `sDomain` carriers coincide. -/
theorem sDomainComp_eq_sDomain (i : Fin r) :
    sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i =
    AdditiveNTT.sDomain (𝔽q := 𝔽q) (β := β)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i := by
  ext x
  constructor
  · exact mem_sDomain_of_mem_sDomainComp (𝔽q := 𝔽q) (β := β)
      (ℓ := ℓ) (R_rate := R_rate) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  · exact mem_sDomainComp_of_mem_sDomain (𝔽q := 𝔽q) (β := β)
      (ℓ := ℓ) (R_rate := R_rate) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)

/-- Bridge: `sDomain_eq_of_eq` on computable carriers. -/
lemma sDomain_eq_of_eq {i j : Fin r} (h : i = j) :
    AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i =
    AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j := by
  simpa [sDomainComp_eq_sDomain] using
    (AdditiveNTT.sDomain_eq_of_eq (𝔽q := 𝔽q) (β := β)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h)

/-- Bridge: `sDomain_basis` on computable carriers. -/
noncomputable def sDomain_basis (i : Fin r) (h_i : i < ℓ + R_rate) :
    Basis (Fin (ℓ + R_rate - i)) 𝔽q (
      AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) := by
  sorry

/-- Bridge: `get_sDomain_basis` on computable carriers. -/
lemma get_sDomain_basis (i : Fin r) (h_i : i < ℓ + R_rate) :
    ∀ (k : Fin (ℓ + R_rate - i)),
    (sDomain_basis (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i h_i) k =
      Polynomial.eval (β ⟨i + k.val, by omega⟩) (normalizedW 𝔽q β i) := by
  sorry

/-- Bridge: cardinality of computable `sDomain`. -/
noncomputable instance fintype_comp_sDomain (i : Fin r) :
    Fintype (AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) := by
  rw [sDomainComp_eq_sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i]
  infer_instance

lemma sDomain_card (i : Fin r) (h_i : i < ℓ + R_rate) :
    Fintype.card (
      AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) =
      (Fintype.card 𝔽q)^(ℓ + R_rate - i) := by
  sorry

/-! Domain-index bijection bridges. -/
/-- Bridge: split coefficients for computable `sDomain`. -/
noncomputable def splitPointIntoCoeffs (i : Fin r) (h_i : i < ℓ + R_rate)
    (x : AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :
    Fin (ℓ + R_rate - i.val) → ℕ := fun j =>
  if (sDomain_basis (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i h_i).repr x j = 0 then 0 else 1

/-- Bridge: computable `sDomainToFin`. -/
noncomputable def sDomainToFin (i : Fin r) (h_i : i < ℓ + R_rate)
    (x : AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :
    Fin (2 ^ (ℓ + R_rate - i.val)) :=
  AdditiveNTT.sDomainToFin (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i h_i
    ⟨x.1, by
      simpa [sDomainComp_eq_sDomain] using x.2⟩

/-- Bridge: computable `finToBinaryCoeffs_sDomainToFin`. -/
lemma finToBinaryCoeffs_sDomainToFin (i : Fin r) (h_i : i < ℓ + R_rate)
    (x : AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :
    let pointFinIdx := (sDomainToFin (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      i h_i) x
    finToBinaryCoeffs 𝔽q (i := i) (idx := pointFinIdx) =
      (sDomain_basis (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i h_i).repr x := by
  sorry

/-- Bridge: computable `finToSDomain`. -/
noncomputable def finToSDomain (i : Fin r) (h_i : i < ℓ + R_rate)
    (idx : Fin (2 ^ (ℓ + R_rate - i.val))) :
    AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i :=
  ⟨(AdditiveNTT.finToSDomain (𝔽q := 𝔽q) (β := β)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i h_i idx).1,
    mem_sDomainComp_of_mem_sDomain (𝔽q := 𝔽q) (β := β)
      (ℓ := ℓ) (R_rate := R_rate) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (x := (AdditiveNTT.finToSDomain (𝔽q := 𝔽q) (β := β)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i h_i idx).1)
      (by
        simpa [AdditiveNTT.finToSDomain] using
          (AdditiveNTT.finToSDomain (𝔽q := 𝔽q) (β := β)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i h_i idx).2)⟩

/-- Bridge: computable `sDomainFinEquiv`. -/
noncomputable def sDomainFinEquiv (i : Fin r) (h_i : i < ℓ + R_rate)
    : AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i ≃
      Fin (2 ^ (ℓ + R_rate - i.val)) := by
  sorry

/-- Bridge: computable `sDomainFin_bijective`. -/
theorem sDomainFin_bijective (i : Fin r) (h_i : i < ℓ + R_rate) :
    Function.Bijective
      (sDomainFinEquiv (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i h_i) := by
  sorry

/-- Cast from computable `sDomainComp` carrier to canonical `sDomain` carrier. -/
def toCanonicalSDomain (i : Fin r)
    (x : sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :
    AdditiveNTT.sDomain (𝔽q := 𝔽q) (β := β)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i :=
  ⟨x.1, mem_sDomain_of_mem_sDomainComp (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) x.2⟩

/-- Search-based decoding from canonical `sDomain i` points to loose global indices. -/
def canonicalPointToGlobalIndex? (i : Fin r)
    (x : AdditiveNTT.sDomain (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :
    Option (Fin (2 ^ (ℓ + R_rate))) :=
  (List.finRange (2 ^ (ℓ + R_rate))).find? (fun vIdx =>
    decide (
      toCanonicalSDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
        (indexToSDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) vIdx)
      = x))

/-- Decode canonical `sDomain i` points to loose local indices (`Fin (2^(ℓ+R_rate-i))`) by
searching global indices and extracting middle bits. -/
def canonicalPointToLocalIndex? (i : Fin r)
    (x : AdditiveNTT.sDomain (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :
    Option (Fin (2 ^ (ℓ + R_rate - i.val))) := do
  let vIdx ← canonicalPointToGlobalIndex? (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i x
  pure ⟨Nat.getMiddleBits (offset := i.val) (len := ℓ + R_rate - i.val) (n := vIdx.val),
    Nat.getMiddleBits_lt_two_pow⟩

/-- Bridge from loose local index functions to canonical-domain oracle functions.
Returns `0` only on decode failure. -/
def localIndexFunctionToCanonical (i : Fin r)
    (f : Fin (2 ^ (ℓ + R_rate - i.val)) → L) :
    AdditiveNTT.sDomain (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i → L :=
  fun x =>
    match canonicalPointToLocalIndex? (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i x with
    | some idx => f idx
    | none => 0

/-- Decode all query repetitions from `Fin` indices to domain points. -/
def decodeQueryChallenges {γ : ℕ} (challenges : Fin γ → Fin (2 ^ (ℓ + R_rate))) :
    Fin γ →
      sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 :=
  fun rep =>
    indexToSDomainZero (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (challenges rep)

/-- Decode all query repetitions to canonical `AdditiveNTT.sDomain` points. -/
def decodeQueryChallengesToCanonical {γ : ℕ} (challenges : Fin γ → Fin (2 ^ (ℓ + R_rate))) :
    Fin γ → AdditiveNTT.sDomain (𝔽q := 𝔽q) (β := β)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 :=
  fun rep =>
    toCanonicalSDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0)
      (indexToSDomainZero (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (challenges rep))

/-- Bridge theorem for `evalWAt`. -/
lemma evalWAt_eq_W (i : Fin r) (x : L) :
    AdditiveNTT.Comp.evalWAt (β := β) i x
      = (AdditiveNTT.W 𝔽q β i).eval x := by
  rw [AdditiveNTT.Comp.evalWAt]
  exact AdditiveNTT.evalWAt_eq_W (𝔽q := 𝔽q) (β := β) (i := i) (x := x)

/-- Bridge theorem for `evalNormalizedWAt`. -/
lemma evalNormalizedWAt_eq_normalizedW (i : Fin r) (x : L) :
    AdditiveNTT.Comp.evalNormalizedWAt (β := β) i x
      = (AdditiveNTT.normalizedW 𝔽q β i).eval x := by
  rw [AdditiveNTT.Comp.evalNormalizedWAt]
  exact AdditiveNTT.evalNormalizedWAt_eq_normalizedW (𝔽q := 𝔽q) (β := β)
    (i := i) (x := x)

/-- Executable twiddle factor with narrow stage index (`Fin ℓ`). -/
def computableTwiddleFactor (i : Fin ℓ) (u : Fin (2 ^ (ℓ + R_rate - i - 1))) : L :=
  ∑ (⟨k, _⟩ : Fin (ℓ + R_rate - i - 1)),
    if Nat.getBit k u.val = 1 then
      AdditiveNTT.Comp.evalNormalizedWAt (β := β) ⟨(i : ℕ), by
        omega⟩
        (β ⟨i + 1 + k, by omega⟩)
    else
      0

/-- Executable twiddle factor with loose stage index (`Fin r`). -/
def twiddleFactor (i : Fin r) (_h_i : i < ℓ)
    (u : Fin (2 ^ (ℓ + R_rate - i - 1))) : L :=
  computableTwiddleFactor (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := ⟨(i : ℕ), _h_i⟩) u

omit [DecidableEq 𝔽q] h_Fq_char_prime h_β₀_eq_1 in
/-- Bridge: computable twiddle factor agrees with canonical `AdditiveNTT.twiddleFactor`. -/
theorem twiddleFactor_eq_twiddleFactor
    (i : Fin r) (h_i : i < ℓ) (u : Fin (2 ^ (ℓ + R_rate - i - 1))) :
    AdditiveNTT.Comp.twiddleFactor (β := β)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i h_i u =
      AdditiveNTT.twiddleFactor β h_ℓ_add_R_rate
        (i := i) (h_i := h_i) u := by
  sorry

/-- Coefficient tiling for the executable Additive NTT. -/
def tileCoeffs (a : Fin (2 ^ ℓ) → L) : Fin (2 ^ (ℓ + R_rate)) → L :=
  AdditiveNTT.tileCoeffs (ℓ := ℓ) (R_rate := R_rate) a

/-- Executable one-stage Additive NTT with narrow stage index (`Fin ℓ`). -/
def computableNTTStage (β : Fin r → L) (h_ℓ_add_R_rate : ℓ + R_rate < r) (i : Fin ℓ)
    (b : Fin (2 ^ (ℓ + R_rate)) → L) : Fin (2 ^ (ℓ + R_rate)) → L :=
  have h_2_pow_i_lt_2_pow_ℓ_add_R_rate : 2 ^ i.val < 2 ^ (ℓ + R_rate) := by
    calc
      2 ^ i.val < 2 ^ ℓ := by
        exact Nat.pow_lt_pow_right (a := 2) (m := i.val) (n := ℓ) (ha := by omega) (by omega)
      _ ≤ 2 ^ (ℓ + R_rate) := by
        exact Nat.pow_le_pow_right (n := 2) (i := ℓ) (j := ℓ + R_rate) (by omega) (by omega)
  fun j =>
    let u_b_v := j.val
    let u_b := u_b_v / (2 ^ i.val)
    let u : ℕ := u_b / 2
    let b_bit := u_b % 2
    have h_u_lt_2_pow : u < 2 ^ (ℓ + R_rate - (i + 1)) := by
      have h_u_eq : u = j.val / (2 ^ (i.val + 1)) := by
        rw [show u = u_b / 2 by rfl]
        rw [show u_b = u_b_v / (2 ^ i.val) by rfl]
        rw [show u_b_v = j.val by rfl]
        rw [Nat.div_div_eq_div_mul]
        rw [Nat.pow_succ]
      rw [h_u_eq]
      exact div_two_pow_lt_two_pow (x := j.val) (i := ℓ + R_rate - (i.val + 1)) (j := i.val + 1)
        (by
          rw [Nat.sub_add_cancel (by omega)]
          omega)
    let x0 : L := computableTwiddleFactor (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i) (u := ⟨u, by
        have h := h_u_lt_2_pow
        exact h⟩)
    let x1 : L := x0 + 1
    have h_b_bit : b_bit = Nat.getBit i.val j.val := by
      simp only [Nat.getBit, Nat.and_one_is_mod, b_bit, u_b, u_b_v]
      rw [← Nat.shiftRight_eq_div_pow (m := j.val) (n := i.val)]
    if h_b_bit_zero : b_bit = 0 then
      let odd_split_index := u_b_v + 2 ^ i.val
      have h_lt : odd_split_index < 2 ^ (ℓ + R_rate) := by
        exact Nat.add_two_pow_of_getBit_eq_zero_lt_two_pow (n := j.val) (m := ℓ + R_rate)
          (i := i.val) (h_n := by omega) (h_i := by omega) (h_getBit_at_i_eq_zero := by
            rw [h_b_bit_zero] at h_b_bit
            exact h_b_bit.symm)
      b j + x0 * b ⟨odd_split_index, h_lt⟩
    else
      let even_split_index := u_b_v ^^^ 2 ^ i.val
      have h_lt : even_split_index < 2 ^ (ℓ + R_rate) := by
        exact Nat.xor_lt_two_pow (by omega) (by omega)
      b ⟨even_split_index, h_lt⟩ + x1 * b j

/-- Executable one-stage Additive NTT with loose stage index (`Fin r`). -/
def NTTStage (i : Fin r) (h_i : i < ℓ)
    (b : Fin (2 ^ (ℓ + R_rate)) → L) : Fin (2 ^ (ℓ + R_rate)) → L :=
  computableNTTStage β h_ℓ_add_R_rate (i := ⟨i, h_i⟩) b

omit [DecidableEq 𝔽q] h_Fq_char_prime h_β₀_eq_1 in
/-- Bridge: computable stage agrees with canonical `AdditiveNTT.NTTStage`. -/
theorem NTTStage_eq_NTTStage
    (i : Fin r) (h_i : i < ℓ) (b : Fin (2 ^ (ℓ + R_rate)) → L) :
    NTTStage (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) h_i b =
      AdditiveNTT.NTTStage (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := i) (h_i := h_i) b := by
  sorry

/-- Alias kept for compatibility while migrating downstream names. -/
def NTTStageCore := computableNTTStage β h_ℓ_add_R_rate

/-- Executable full Additive NTT, driven by `computableNTTStage`. -/
def computableAdditiveNTT (β : Fin r → L) (h_ℓ_add_R_rate : ℓ + R_rate < r)
    (a : Fin (2 ^ ℓ) → L) : Fin (2 ^ (ℓ + R_rate)) → L :=
  let b : Fin (2 ^ (ℓ + R_rate)) → L := tileCoeffs (ℓ := ℓ) (R_rate := R_rate) a
  Fin.foldl (n := ℓ)
    (f := fun current_b i =>
      computableNTTStage β h_ℓ_add_R_rate (i := ⟨ℓ - 1 - i, by omega⟩) current_b)
    (init := b)

/-- Executable full Additive NTT with the conventional name. -/
def additiveNTT (a : Fin (2 ^ ℓ) → L) : Fin (2 ^ (ℓ + R_rate)) → L :=
  computableAdditiveNTT β h_ℓ_add_R_rate a

omit [DecidableEq 𝔽q] h_Fq_char_prime h_β₀_eq_1 in
/-- Bridge: computable full Additive NTT agrees with canonical `AdditiveNTT.additiveNTT`. -/
theorem computableAdditiveNTT_eq_additiveNTT
    (a : Fin (2 ^ ℓ) → L) :
    computableAdditiveNTT (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) a =
      AdditiveNTT.additiveNTT (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (β' := β)
        (h_ℓ_add_R_rate' := h_ℓ_add_R_rate) a := by
  sorry

end AdditiveNTT.Comp
