/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilia Vlasov
-/

import Mathlib.Algebra.Polynomial.Roots

import ArkLib.Data.Domain.CosetFftDomain.Ops
import ArkLib.Data.Domain.CosetFftDomain.Log
import ArkLib.Data.Domain.FftDomain.Ops

namespace Domain

variable {ι : Type} [Fintype ι] [AddCommGroup ι]
variable {F : Type} [Field F] [DecidableEq F]

namespace CosetFftDomainClass

variable {n : ℕ}
variable {D : Type} [FunLike D ι F] [CosetFftDomainClass D ι F]
variable {ω : D} {k : ℕ} {x y : F}

open Finset Polynomial

def block (ω : D) (k : ℕ) (x : F) : Finset F :=
  {y ∈ toFinset ω | y ^ k = x}

@[simp]
lemma mem_block :
  y ∈ block ω k x ↔ y ∈ ω ∧ y ^ k = x := by simp [block]

@[simp]
lemma block_x_0 :
  block ω k 0 = ∅ := by aesop

@[simp]
lemma block_k_0 :
  block ω 0 x = if x = 1 then toFinset ω else ∅ := by aesop

lemma block_eq_nthRootsFinset [NeZero k] :
  block ω k x = nthRootsFinset k x ∩ toFinset ω := by aesop (add unsafe cases Nat)

@[simp]
lemma block_card_le [NeZero k] :
  (block ω k x).card ≤ k := by
  rw [block_eq_nthRootsFinset]
  exact le_trans (card_le_card inter_subset_left) <| by
    simp only [nthRootsFinset, Multiset.toFinset, card_mk]
    exact le_trans
      (@Multiset.toFinset_card_le F (Classical.decEq F) _)
      (card_nthRoots _ _)

def blockIdx (ω : D) (k : ℕ) (x : F) : Finset ι :=
  {i | ω i ^ k = x}

omit [AddCommGroup ι] [CosetFftDomainClass D ι F] in
lemma mem_blockIdx {i : ι} :
  i ∈ blockIdx ω k x ↔ ω i ^ k = x := by simp [blockIdx]

omit [AddCommGroup ι] [CosetFftDomainClass D ι F] in
@[simp]
lemma mem_blockIdx_self {i : ι} :
  i ∈ blockIdx ω k (ω i ^ k) := by simp [blockIdx]

lemma mem_blockIdx_iff_mem_block {i : ι} :
  i ∈ blockIdx ω k x ↔ ω i ∈ block ω k x := by simp [blockIdx]

lemma blockIdx_eq_preimage_block :
  blockIdx ω k x =
    preimage
      (block ω k x) ω
      (fun _ _ _ _ h ↦ CosetFftDomainClass.injective _ h) := by
  aesop (add simp [mem_blockIdx_iff_mem_block])

@[simp]
lemma card_blockIdx :
  (blockIdx ω k x).card = (block ω k x).card := by
  aesop
    (add simp [blockIdx_eq_preimage_block, card_preimage])
    (add unsafe congrArg)

end CosetFftDomainClass

end Domain
