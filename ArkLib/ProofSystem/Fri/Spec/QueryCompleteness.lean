/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import ArkLib.Data.Domain.CosetFftDomain.Subdomain
public import ArkLib.Data.CodingTheory.Basic.RelativeDistance
public import ArkLib.Data.Probability.Instances

/-!
# Clean first blocks and FRI completeness bounds

The clean first blocks give a challenge-independent lower bound on the probability
that independently sampled FRI queries accept an honest folded history. Only the initial
word can contain errors; a block is clean when it avoids all disagreements with the witness.
-/

@[expose] public section

namespace Fri.Spec

open Domain Finset Domain.CosetFftDomainClass
open scoped NNReal ENNReal

variable {F : Type} [Field F] [DecidableEq F] {n : ℕ}

/-- The first-fold images of positions where the initial words disagree. -/
def firstErrorBlocks (ω : SmoothCosetFftDomain n F) (r : ℕ)
    (f g : Fin (2 ^ n) → F) : Finset F :=
  (Code.disagreementCols f g).image fun z ↦ ω z ^ 2 ^ r

/-- Initial positions whose entire first folding block avoids every disagreement. -/
def cleanFirstQueries (ω : SmoothCosetFftDomain n F) (r : ℕ)
    (f g : Fin (2 ^ n) → F) : Finset (Fin (2 ^ n)) :=
  ((firstErrorBlocks ω r f g).biUnion (blockIdx ω r))ᶜ

@[simp]
theorem firstErrorBlocks_self (ω : SmoothCosetFftDomain n F) (r : ℕ)
    (f : Fin (2 ^ n) → F) : firstErrorBlocks ω r f f = ∅ := by
  simp [firstErrorBlocks, Code.disagreementCols]

@[simp]
theorem cleanFirstQueries_self (ω : SmoothCosetFftDomain n F) (r : ℕ)
    (f : Fin (2 ^ n) → F) : cleanFirstQueries ω r f f = univ := by
  simp [cleanFirstQueries]

/-- A query is clean exactly when the words agree throughout its folding fiber. -/
theorem mem_cleanFirstQueries (ω : SmoothCosetFftDomain n F) (r : ℕ)
    (f g : Fin (2 ^ n) → F) (z : Fin (2 ^ n)) :
    z ∈ cleanFirstQueries ω r f g ↔
      ∀ y : Fin (2 ^ n), ω y ^ 2 ^ r = ω z ^ 2 ^ r → f y = g y := by
  classical
  simp only [cleanFirstQueries, mem_compl, mem_biUnion, firstErrorBlocks,
    mem_image, Code.mem_disagreementCols, mem_blockIdx]
  constructor
  · intro h y hy
    by_contra hne
    exact h ⟨ω y ^ 2 ^ r, ⟨y, hne, rfl⟩, hy.symm⟩
  · intro h ⟨x, ⟨y, hy, hxy⟩, hx⟩
    exact hy (h y (hxy.trans hx.symm))

/-- The number of corrupted folding blocks is at most the number of erroneous positions. -/
theorem card_firstErrorBlocks_le (ω : SmoothCosetFftDomain n F) (r : ℕ)
    (f g : Fin (2 ^ n) → F) :
    (firstErrorBlocks ω r f g).card ≤ hammingDist f g := by
  exact card_image_le.trans_eq (Code.hammingDist_eq_disagreementCols_card f g).symm

/-- Corrupted first blocks contain exactly `2 ^ r` positions each. -/
theorem card_biUnion_firstErrorBlocks (ω : SmoothCosetFftDomain n F) (r : ℕ) (hr : r ≤ n)
    (f g : Fin (2 ^ n) → F) :
    ((firstErrorBlocks ω r f g).biUnion (blockIdx ω r)).card =
      (firstErrorBlocks ω r f g).card * 2 ^ r := by
  rw [card_biUnion pairwise_disjoint_blockIdx]
  apply sum_const_nat
  intro x hx
  rw [card_blockIdx]
  apply card_block_of_mem_subdomain' hr
  obtain ⟨z, hz, rfl⟩ := mem_image.mp hx
  rw [← pow_eq_subdomain_sqFoldMapGen]
  exact mem_self

/-- Clean positions and positions in corrupted first blocks partition the initial domain. -/
theorem card_cleanFirstQueries_add (ω : SmoothCosetFftDomain n F) (r : ℕ) (hr : r ≤ n)
    (f g : Fin (2 ^ n) → F) :
    (cleanFirstQueries ω r f g).card +
      (firstErrorBlocks ω r f g).card * 2 ^ r = 2 ^ n := by
  rw [← card_biUnion_firstErrorBlocks ω r hr f g]
  simpa only [cleanFirstQueries, Fintype.card_fin] using
    card_compl_add_card ((firstErrorBlocks ω r f g).biUnion (blockIdx ω r))

/-- The clean-query density counts complete uncorrupted first blocks exactly. -/
theorem cleanFirstQueries_density (ω : SmoothCosetFftDomain n F) (r : ℕ) (hr : r ≤ n)
    (f g : Fin (2 ^ n) → F) :
    ((cleanFirstQueries ω r f g).card : ℝ≥0) / 2 ^ n =
      1 - ((firstErrorBlocks ω r f g).card : ℝ≥0) * 2 ^ r / 2 ^ n := by
  apply eq_tsub_of_add_eq
  rw [← add_div]
  have hc : ((cleanFirstQueries ω r f g).card : ℝ≥0) +
      ((firstErrorBlocks ω r f g).card : ℝ≥0) * 2 ^ r = 2 ^ n := by
    exact_mod_cast card_cleanFirstQueries_add ω r hr f g
  rw [hc, div_self (by positivity)]

/-- The clipped completeness error for `l` queries with first-fold exponent `s 0`. -/
def completenessError {k : ℕ} (s : Fin (k + 1) → ℕ+) (δ : ℝ≥0) (l : ℕ) : ℝ≥0 :=
  1 - (1 - min 1 ((2 ^ (s 0).val : ℝ≥0) * δ)) ^ l

/-- The completeness error is at most one. -/
theorem completenessError_le_one {k : ℕ} (s : Fin (k + 1) → ℕ+) (δ : ℝ≥0) (l : ℕ) :
    completenessError s δ l ≤ 1 :=
  tsub_le_self

@[simp]
theorem completenessError_zero {k : ℕ} (s : Fin (k + 1) → ℕ+) (l : ℕ) :
    completenessError s 0 l = 0 := by
  simp [completenessError]

@[simp]
theorem completenessError_zero_queries {k : ℕ} (s : Fin (k + 1) → ℕ+) (δ : ℝ≥0) :
    completenessError s δ 0 = 0 := by
  simp [completenessError]

/-- The success bound complementary to the clipped completeness error. -/
theorem one_sub_completenessError {k : ℕ} (s : Fin (k + 1) → ℕ+) (δ : ℝ≥0) (l : ℕ) :
    1 - completenessError s δ l = (1 - min 1 ((2 ^ (s 0).val : ℝ≥0) * δ)) ^ l := by
  exact tsub_tsub_cancel_of_le (pow_le_one₀ (by positivity) tsub_le_self)

/-- Increasing the input radius increases the completeness error. -/
theorem completenessError_mono {k : ℕ} (s : Fin (k + 1) → ℕ+) (l : ℕ) :
    Monotone (fun δ ↦ completenessError s δ l) := by
  intro δ ε h
  exact tsub_le_tsub_left (pow_le_pow_left' (tsub_le_tsub_left
    (min_le_min_left 1 (mul_le_mul_of_nonneg_left h zero_le)) 1) l) 1

/-- The clean-query density lies in the unit interval. -/
theorem cleanFirstQueries_density_le_one (ω : SmoothCosetFftDomain n F) (r : ℕ)
    (f g : Fin (2 ^ n) → F) :
    ((cleanFirstQueries ω r f g).card : ℝ≥0) / 2 ^ n ≤ 1 := by
  rw [div_le_one (by positivity)]
  exact_mod_cast (show (cleanFirstQueries ω r f g).card ≤ 2 ^ n by
    simpa only [Fintype.card_fin] using card_le_univ (cleanFirstQueries ω r f g))

/-- Proximity of the initial words gives the clipped first-block density bound. -/
theorem one_sub_min_le_cleanFirstQueries_density (ω : SmoothCosetFftDomain n F)
    (r : ℕ) (hr : r ≤ n) (f g : Fin (2 ^ n) → F) (δ : ℝ≥0)
    (hδ : (Code.relHammingDist f g : ℝ≥0) ≤ δ) :
    1 - min 1 ((2 ^ r : ℝ≥0) * δ) ≤
      ((cleanFirstQueries ω r f g).card : ℝ≥0) / 2 ^ n := by
  rw [cleanFirstQueries_density ω r hr f g]
  apply tsub_le_tsub_left
  apply le_min
  · rw [div_le_one (by positivity)]
    have hcard := card_cleanFirstQueries_add ω r hr f g
    exact_mod_cast (show (firstErrorBlocks ω r f g).card * 2 ^ r ≤ 2 ^ n by omega)
  · calc
      ((firstErrorBlocks ω r f g).card : ℝ≥0) * 2 ^ r / 2 ^ n ≤
          (hammingDist f g : ℝ≥0) * 2 ^ r / 2 ^ n := by
            gcongr
            exact_mod_cast card_firstErrorBlocks_le ω r f g
      _ = (2 ^ r : ℝ≥0) * (Code.relHammingDist f g : ℝ≥0) := by
        simp only [Code.relHammingDist, NNRat.cast_div, NNRat.cast_natCast, Fintype.card_fin,
          Nat.cast_pow, Nat.cast_ofNat]
        push_cast
        ring
      _ ≤ (2 ^ r : ℝ≥0) * δ := mul_le_mul_of_nonneg_left hδ zero_le

/-- A set containing every clean query has at least the clean-block success probability. -/
theorem cleanFirstQueries_pow_le_prob_uniform_queries (ω : SmoothCosetFftDomain n F)
    (r : ℕ) (f g : Fin (2 ^ n) → F) (A : Finset (Fin (2 ^ n)))
    (hA : cleanFirstQueries ω r f g ⊆ A) (l : ℕ) :
    (((cleanFirstQueries ω r f g).card : ℝ≥0∞) / 2 ^ n) ^ l ≤
      Pr{let zs ← $ᵗ (Fin l → Fin (2 ^ n))}[∀ j, zs j ∈ A] := by
  rw [Probability.prob_uniform_pi_mem_finset_eq]
  apply pow_le_pow_left'
  simp only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
  gcongr

/-- The clipped radius bound holds for independent queries in any set containing clean queries. -/
theorem one_sub_completenessError_le_prob_uniform_queries {k : ℕ}
    (ω : SmoothCosetFftDomain n F) (s : Fin (k + 1) → ℕ+) (hs : (s 0).val ≤ n)
    (f g : Fin (2 ^ n) → F) (δ : ℝ≥0)
    (hδ : (Code.relHammingDist f g : ℝ≥0) ≤ δ) (A : Finset (Fin (2 ^ n)))
    (hA : cleanFirstQueries ω (s 0).val f g ⊆ A) (l : ℕ) :
    1 - (completenessError s δ l : ℝ≥0∞) ≤
      Pr{let zs ← $ᵗ (Fin l → Fin (2 ^ n))}[∀ j, zs j ∈ A] := by
  calc
    1 - (completenessError s δ l : ℝ≥0∞) =
        (((1 - min 1 ((2 ^ (s 0).val : ℝ≥0) * δ)) ^ l : ℝ≥0) : ℝ≥0∞) := by
          rw [← ENNReal.coe_one, ← ENNReal.coe_sub, one_sub_completenessError]
    _ ≤ (((cleanFirstQueries ω (s 0).val f g).card : ℝ≥0∞) / 2 ^ n) ^ l := by
      rw [ENNReal.coe_pow]
      apply pow_le_pow_left'
      have h := one_sub_min_le_cleanFirstQueries_density ω (s 0).val hs f g δ hδ
      simpa using (ENNReal.coe_le_coe.mpr h)
    _ ≤ _ := cleanFirstQueries_pow_le_prob_uniform_queries ω (s 0).val f g A hA l

end Fri.Spec
