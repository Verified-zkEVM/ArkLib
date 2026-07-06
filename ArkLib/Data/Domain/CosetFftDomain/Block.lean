/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilia Vlasov
-/

import Mathlib.Algebra.Polynomial.Roots

import ArkLib.Data.Domain.CosetFftDomain.Ops
import ArkLib.Data.Domain.FftDomain.Ops

/-! This module provides a definition of a block of a
  coset FFT domain (definition 4.16 from [ACFY24]).

## Main definitions

- `block`: A block of a coset FFT domain at a point `x`.
- `blockIdx`: The indices of the elements of a block of
  a coset FFT domain at a point `x`.

## Main results

- `card_block_le`: The cardinality bound of a block.
- `card_blockIdx`: The cardinality of `block` and `blockIdx` coincide.

## References

  * [Arnon, G., Chiesa, A., Fenzi, G., and Yogev, E., *WHIR: Reed–Solomon Proximity Testing
      with Super-Fast Verification*][ACFY24]
-/

namespace Domain

variable {ι : Type} [Fintype ι] [AddCommGroup ι]
variable {F : Type} [Field F] [DecidableEq F]

namespace CosetFftDomainClass

variable {n : ℕ}
variable {D : Type} [FunLike D ι F] [CosetFftDomainClass D ι F]
variable {ω : D} {k : ℕ} {x y : F}

open Finset Polynomial

/-- The `k`th roots of `x` from the domain `ω`.

  This is the definition 4.16 from [ACFY24].
  Note, we do not require `x` to be from a subdomain. -/
def block (ω : D) (k : ℕ) (x : F) : Finset F :=
  {y ∈ toFinset ω | y ^ 2 ^ k = x}

/-- An equivalent definition of the membership to a block. -/
@[simp]
lemma mem_block :
  y ∈ block ω k x ↔ y ∈ ω ∧ y ^ 2 ^ k = x := by simp [block]

/-- There are no roots of `0` in any domain. -/
@[simp]
lemma block_x_0 :
  block ω k 0 = ∅ := by aesop

@[simp]
lemma block_k_1 :
  block ω 0 x = if x ∈ ω then {x} else ∅ := by aesop

/-- An alternative definition of `block` in terms of
  `Polynomial.nthRootsFinset`. -/
lemma block_eq_nthRootsFinset :
  block ω k x = nthRootsFinset (2 ^ k) x ∩ toFinset ω := by aesop (add unsafe cases Nat)

/-- The cardinality of a block does not exceed its degree. -/
@[simp]
lemma card_block_le :
  (block ω k x).card ≤ 2 ^ k := by
  rw [block_eq_nthRootsFinset]
  exact le_trans (card_le_card inter_subset_left) <| by
    simp only [nthRootsFinset, Multiset.toFinset, card_mk]
    exact le_trans
      (@Multiset.toFinset_card_le F (Classical.decEq F) _)
      (card_nthRoots _ _)

/-- The set of indices of a block of `ω` at `x` of the degree `k`. -/
def blockIdx (ω : D) (k : ℕ) (x : F) : Finset ι :=
  {i | ω i ^ 2 ^ k = x}

omit [AddCommGroup ι] [CosetFftDomainClass D ι F] in
/-- The definition of membership to a `blockIdx`. -/
lemma mem_blockIdx {i : ι} :
  i ∈ blockIdx ω k x ↔ ω i ^ 2 ^ k = x := by simp [blockIdx]

omit [AddCommGroup ι] [CosetFftDomainClass D ι F] in
@[simp]
lemma mem_blockIdx_self {i : ι} :
  i ∈ blockIdx ω k (ω i ^ 2 ^ k) := by simp [blockIdx]

lemma mem_blockIdx_iff_mem_block {i : ι} :
  i ∈ blockIdx ω k x ↔ ω i ∈ block ω k x := by simp [blockIdx]

/-- There are no roots of `0` in any domain. -/
@[simp]
lemma blockIdx_x_0 :
  blockIdx ω k 0 = ∅ := by aesop (add simp [mem_blockIdx_iff_mem_block])

lemma blockIdx_k_1_of_eq {i : ι} (hi : ω i = x) :
  blockIdx ω 0 x = {i} := by
  ext j
  have := CosetFftDomainClass.injective ω (a₁ := i) (a₂ := j)
  aesop
    (add simp [mem_blockIdx_iff_mem_block])

lemma blockIdx_k_1_of_ne_mem (hx : x ∉ ω) :
  blockIdx ω 0 x = ∅ := by
  aesop
    (add simp [mem_blockIdx_iff_mem_block])

/-- `blockIdx` is the preimage of `block`. -/
lemma blockIdx_eq_preimage_block :
  blockIdx ω k x =
    preimage
      (block ω k x) ω
      (fun _ _ _ _ h ↦ CosetFftDomainClass.injective _ h) := by
  aesop (add simp [mem_blockIdx_iff_mem_block])

/-- The cardinality of `blockIdx` is that of `block`. -/
@[simp]
lemma card_blockIdx :
  (blockIdx ω k x).card = (block ω k x).card := by
  aesop
    (add simp [blockIdx_eq_preimage_block, card_preimage])
    (add unsafe congrArg)

end CosetFftDomainClass

end Domain
