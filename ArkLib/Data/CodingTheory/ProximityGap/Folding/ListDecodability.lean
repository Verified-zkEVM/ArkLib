/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: František Silváši, Ilia Vlasov
-/

import ArkLib.Data.CodingTheory.Basic.BlockRelDistance
import ArkLib.Data.CodingTheory.ProximityGap.Folding

namespace ProximityGap

open NNReal Finset Function
open scoped ProbabilityTheory
open scoped BigOperators LinearCode
open Code Affine ReedSolomon
open Polynomial Domain
open CosetFftDomain CosetFftDomainClass
open BlockRelDistance

variable {F : Type} [Field F] [DecidableEq F]
variable {n k : ℕ}
variable {ω : SmoothCosetFftDomain n F}
variable {f : Word F (Fin (2 ^ n))}

/-!
  This file contains a proof of Theorem 4.20 from [ACFY24] (WIP for now).

## References

* [Arnon, G., Chiesa, A., Fenzi, G., and Yogev, E., *WHIR: Reed–Solomon Proximity Testing
    with Super-Fast Verification*][ACFY24]
-/

/-- The block distance of foldings of two words does not exceed
  the block distance of the original words.

  This is a part of the proof of the claim 4.22 of [ACFY24]. -/
lemma folding_contracts_block_distance
  {α : F} (hk : 1 ≤ k) (hkn : k ≤ n)
  {u : Word F (Fin (2 ^ n))} :
  Δ𞁒(k - 1, ω.subdomain 1, foldWord ω u 1 α, foldWord ω f 1 α) ≤
    Δ𞁒(k , ω, u, f) := by
  have : NeZero n := ⟨by omega⟩
  simp only [blockDistance, card_disagreementSet', card_toFinset, Fintype.card_fin]
  rw [show n - 1 - (k - 1) = n - k by omega,
      Nat.sub_le_sub_iff_left (by simp)]
  exact Finset.card_le_card <| fun x hx ↦ by
    simp_all only [complDisagreementSet_def', mem_filter]
    exact And.intro
      (by aesop (add unsafe (by rw [Nat.add_sub_cancel']))) <| fun i hi ↦ by
      rw [foldWord_k_1, foldWord_k_1]
      extract_lets y j j'
      have : 2 ^ k = 2 * 2 ^ (k - 1) := by rw [←pow_succ', Nat.sub_add_cancel hk]
      have hj : j ∈ blockIdx ω k x := by
        aesop
          (add simp [mem_blockIdx_iff_mem_block, pow_mul])
          (add unsafe (by rw [←CosetFftDomainClass.mem_toFinset_iff_mem]))
      have hj' : j' ∈ blockIdx ω k x := by
        aesop
          (add simp [mem_blockIdx_iff_mem_block, pow_mul])
          (add unsafe (by rw [←CosetFftDomainClass.mem_toFinset_iff_mem]))
      rw [hx.2 _ hj, hx.2 _ hj']

/-- The block relative distance of foldings of two words does not exceed
  the block relative distance of the original words.

  This is a part of the proof of the claim 4.22 of [ACFY24]. -/
lemma folding_contracts_block_rel_distance
  {α : F} (hk : 1 ≤ k) (hkn : k ≤ n)
  {u : Word F (Fin (2 ^ n))} :
  δ𞁒(k - 1, ω.subdomain 1, foldWord ω u 1 α, foldWord ω f 1 α) ≤
    δ𞁒(k , ω, u, f) := by
  have : n - 1 - (k - 1) = n - k := by omega
  aesop
    (add simp blockRelDistance)
    (add unsafe folding_contracts_block_distance)
    (add safe (by field_simp))

/-- If a word `u` belongs to a block relative distance ball
  then its folding belongs to a "folded" block relative distance ball too.

  This is the claim 4.22 from [ACFY24] with unfolded definition `⊆`.
-/
lemma folding_block_rel_ball {d : ℕ}
  {α : F} {δ : ℝ≥0} (hk : 1 ≤ k) (hd : k ≤ d)
  (hkn : k ≤ n) {u : Word F (Fin (2 ^ n))}
  (hu : u ∈ Λ𞁒(code (ω : Fin (2 ^ n) ↪ F) (2 ^ d), k, ω, f, δ)) :
  foldWord ω u 1 α ∈
    Λ𞁒(code (ω.subdomain 1 : Fin (2 ^ (n - 1)) ↪ F) (2 ^ (d - 1)),
       k - 1, ω.subdomain 1,
       foldWord ω f 1 α, δ) := by
  have hn : 1 ≤ n := by omega
  simp_all only [Word, blockRelDistanceBall, SetLike.mem_coe, Set.mem_ofPred_eq]
  constructor
  · have : 2 ^ (d - 1) = 2 ^ d / 2 := by rw [Nat.pow_sub_one] <;> omega
    rw [this]
    exact foldWord_mem_code_of_mem_code hn (by grind) hu.1
  · exact le_trans
      (NNRat.cast_le.2 <| folding_contracts_block_rel_distance hk hkn)
      (by aesop)

/-- The image of a block relative distance ball under the folding map
  is contained in the "folded" block relative distance ball.

  This is the claim 4.22 from [ACFY24].
-/
theorem folding_preserves_block_balls {d : ℕ}
  {α : F} {δ : ℝ≥0} (hk : 1 ≤ k) (hd : k ≤ d) (hkn : k ≤ n) :
  Set.image
    (fun u ↦ foldWord ω u 1 α)
    (Λ𞁒(code (ω : Fin (2 ^ n) ↪ F) (2 ^ d), k, ω, f, δ)) ⊆
      Λ𞁒(code (ω.subdomain 1 : Fin (2 ^ (n - 1)) ↪ F) (2 ^ (d - 1)),
         k - 1, ω.subdomain 1, foldWord ω f 1 α, δ) := fun x hx ↦ by
  aesop (add unsafe folding_block_rel_ball)

end ProximityGap
