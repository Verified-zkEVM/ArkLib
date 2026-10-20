/-
Copyright (c) 2025-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poulami Das (Least Authority), Alexander Hicks, Ilia Vlasov,
         Aristotle (Harmonic)
-/
module

public import Mathlib.Data.Finset.Union

public import ArkLib.Data.CodingTheory.Basic.RelativeDistance
public import ArkLib.Data.CodingTheory.ReedSolomon
public import ArkLib.Data.CodingTheory.ListDecodability
public import ArkLib.Data.Domain.CosetFftDomain.Block
public import ArkLib.Data.Domain.CosetFftDomain.Subdomain

/-!
# Block Relative Distance for smooth Reed-Solomon Codes

## Implementation notes

Block relative distance is defined for smooth rather than constrained Reed Solomon codes,
as is done in the reference paper, as they are more general.

## References

* [Arnon, G., Chiesa, A., Fenzi, G., and Yogev, E., *WHIR: Reed–Solomon Proximity Testing
    with Super-Fast Verification*][ACFY24]

-/

@[expose] public section

namespace BlockRelDistance

open Domain Code NNReal ReedSolomon CosetFftDomainClass

variable {F : Type} [Field F] [DecidableEq F]
         {n k : ℕ}
         {φ : SmoothCosetFftDomain n F}
         {f g : Fin (2 ^ n) → F}

/-- Let C be a smooth ReedSolomon code `C = RS[F, ι^(2ⁱ), φ', m]` and `f,g : ι^(2ⁱ) → F`, then
  the (i,k)-wise block relative distance is defined as
    Δᵣ(i, k, f, S', φ', g) = |{z ∈ ι ^ 2^k : ∃ y ∈ Block(i,k,S',φ',z) f(y) ≠ g(y)}| / |ι^(2^k)|. -/
def disagreementSet
    (k : ℕ) (φ : SmoothCosetFftDomain n F) (f g : Fin (2 ^ n) → F) : Finset F :=
  { z ∈ (φ.subdomain k).toFinset | ∃ i ∈ blockIdx φ k z, f i ≠ g i }

@[simp]
lemma disagreementSet_sub_subdomain :
    disagreementSet k φ f g ⊆ (φ.subdomain k).toFinset := by simp [disagreementSet]

@[simp]
lemma disagreementSet_intersect_subdomain_eq :
    disagreementSet k φ f g ∩ (φ.subdomain k).toFinset =
    disagreementSet k φ f g := by simp [disagreementSet]

@[simp]
lemma card_disagreementSet_le :
    (disagreementSet k φ f g).card ≤ 2 ^ (n - k) := by
  rw [show 2 ^ (n - k) = Finset.card (φ.subdomain k).toFinset by simp]
  exact Finset.card_le_card (by simp)

lemma disagreementSet_k_0 :
    disagreementSet 0 φ f g = { z ∈ φ.toFinset | ∃ i, φ i = z ∧ f i ≠ g i } := by
  ext z
  simp only [disagreementSet, Finset.mem_filter, mem_toFinset_iff_mem, mem_subdomain_0_iff_mem,
    mem_blockIdx, pow_zero, pow_one]

lemma disagreementSet_k_0_eq_image :
    disagreementSet 0 φ f g = Finset.image φ { i | f i ≠ g i } := by
  rw [disagreementSet_k_0]
  ext z
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨-, i, rfl, hfg⟩
    exact ⟨i, hfg, rfl⟩
  · rintro ⟨i, hfg, rfl⟩
    exact ⟨mem_toFinset_self, i, rfl, hfg⟩

@[simp]
lemma card_disagreementSet_k_0 :
    (disagreementSet 0 φ f g).card = Finset.card { i | f i ≠ g i } := by
  rw [disagreementSet_k_0_eq_image, Finset.card_image_of_injective _ (by simp)]

/-- Given the disagreementSet from above, we obtain the block distance as |disagreementSet|.
  Definition 4.17 from [ACFY24].
-/
def blockDistance
    (k : ℕ) (φ : SmoothCosetFftDomain n F) (f g : Fin (2 ^ n) → F) : ℕ :=
  Finset.card <| disagreementSet k φ f g

/-- Given the disagreementSet from above, we obtain the block relative distance as
  |disagreementSet|/ |ι ^ (2^k)|.
  Definition 4.17 from [ACFY24].
-/
def blockRelDistance
    (k : ℕ) (φ : SmoothCosetFftDomain n F) (f g : Fin (2 ^ n) → F) : ℚ≥0 :=
  (blockDistance k φ f g : ℚ≥0) / (φ.subdomain k).toFinset.card

/-- Notation `Δ𞁒(k, φ', f, g)` is the k-wise block distance. -/
scoped notation "Δ𞁒("k", "φ'", "f", "g")"  => blockDistance k φ' f g

/-- Notation `δ𞁒(k, φ', f, g)` is the k-wise block relative distance. -/
scoped notation "δ𞁒("k", "φ'", "f", "g")"  => blockRelDistance k φ' f g

/-- blockDistance from a set of words. -/
noncomputable def blockDistanceFromCode
  (k : ℕ) (φ : SmoothCosetFftDomain n F) (f : Fin (2 ^ n) → F)
  (C : Set (Fin (2 ^ n) → F)) : ℕ∞ :=
  sInf {d | ∃ v ∈ C, blockDistance k φ f v ≤ d}

private lemma natCast_div_le_one {a b : ℕ} (h : a ≤ b) : (a : ℚ≥0) / b ≤ 1 :=
  div_le_one_of_le₀ (Nat.cast_le.2 h) zero_le

@[simp]
lemma blockDistance_le :
    Δ𞁒(k, φ, f, g) ≤ 2 ^ (n - k) := by simp [blockDistance]

lemma blockDistance_symm :
    Δ𞁒(k, φ, f, g) = Δ𞁒(k, φ, g, f) := by
  simp only [blockDistance, disagreementSet, ne_comm]

lemma blockRelDistance_symm :
    δ𞁒(k, φ, f, g) = δ𞁒(k, φ, g, f) := by
  unfold blockRelDistance
  rw [blockDistance_symm]

/-- blockRelDistance from a set of words. -/
noncomputable def blockRelDistanceFromCode
  (k : ℕ) (φ : SmoothCosetFftDomain n F) (f : Fin (2 ^ n) → F)
  (C : Set (Fin (2 ^ n) → F)) : ENNReal :=
  sInf {d | ∃ v ∈ C, blockRelDistance k φ f v ≤ d}

scoped notation "Δ𞁒("k", "φ'", "f", "C")"  => blockDistanceFromCode k φ' f C
scoped notation "δ𞁒("k", "φ'", "f", "C")"  => blockRelDistanceFromCode k φ' f C

/-- The block distance simplifies to the standard Hamming distance when `k=0`. -/
@[simp]
lemma blockDistance_eq_hammingDist_k_0 :
    Δ𞁒(0, φ, f, g) = Δ₀(f, g) := by simp [blockDistance, hammingDist]

/-- The block relative distance simplifies to the standard relative Hamming distance when `k=0`. -/
@[simp]
lemma blockRelDistance_eq_relHammingDist_k_0 :
    δ𞁒(0, φ, f, g) = δᵣ(f, g) := by simp [blockRelDistance, Code.relHammingDist]

@[simp]
lemma blockRelDistance_le_one :
    δ𞁒(k, φ, f, g) ≤ 1 :=
  natCast_div_le_one (Finset.card_le_card disagreementSet_sub_subdomain)

/-- Definition 4.18
  For a smooth ReedSolomon code C = RS[F, ι^(2ⁱ), φ', m], proximity parameter δ ∈ [0,1]
  function f : ι^(2ⁱ) → F, we define the following as the list of codewords of C δ-close to f,
  i.e., u ∈ C such that Δᵣ(k, φ', f, u) ≤ δ. -/
noncomputable def blockRelDistanceBall
  (k : ℕ) (φ : SmoothCosetFftDomain n F)
  (f : Fin (2 ^ n) → F)
  (δ : ℝ≥0) (C : Set (Fin (2 ^ n) → F)) : Set (Fin (2 ^ n) → F) :=
  { u ∈ C | δ𞁒(k, φ, f, u) ≤ δ }

/-- `Λ𞁒(C, k, φ', f, δ)` denotes the list of codewords of C δ-close to f,
  wrt to the block relative distance. -/
scoped notation "Λ𞁒("C", "k", "φ'", "f", "δ")" =>
  blockRelDistanceBall k φ' f δ C

@[simp]
lemma mem_blockRelDistanceBall {g : Fin (2 ^ n) → F}
    (C : Set (Fin (2 ^ n) → F)) (δ : ℝ≥0) :
  f ∈ Λ𞁒(C, k, φ, g, δ) ↔ f ∈ C ∧ δ𞁒(k, φ, f, g) ≤ δ := by
  simp [blockRelDistanceBall, blockRelDistance_symm]

@[simp]
lemma not_mem_blockRelDistanceBall {g : Fin (2 ^ n) → F}
    (C : Set (Fin (2 ^ n) → F)) (δ : ℝ≥0) :
  f ∉ Λ𞁒(C, k, φ, g, δ) ↔ f ∉ C ∨ δ < δ𞁒(k, φ, f, g) := by
  aesop (add safe (by grind))

/-- The `0`-wise block relative distance list is the ordinary list of codewords within relative
  Hamming distance `δ`. -/
lemma blockRelDistanceBall_zero {n : ℕ} {ω : SmoothCosetFftDomain n F}
    (C : Set (Fin (2 ^ n) → F)) (g : Fin (2 ^ n) → F) (δ : ℝ≥0) :
    Λ𞁒(C, 0, ω, g, δ) = {u | u ∈ C ∧ ((δᵣ(g, u) : ℚ≥0) : ℝ≥0) ≤ δ} := by
  aesop (add simp blockRelDistanceBall)

def complDisagreementSet
    (k : ℕ) (φ : SmoothCosetFftDomain n F) (f g : Fin (2 ^ n) → F) : Finset F :=
  (φ.subdomain k).toFinset \ disagreementSet k φ f g

lemma complDisagreementSet_def' :
    complDisagreementSet k φ f g =
    { z ∈ (φ.subdomain k).toFinset | ∀ i ∈ blockIdx φ k z, f i = g i  } := by
  rw [complDisagreementSet, disagreementSet, ← Finset.filter_not]
  simp only [not_exists, not_and, ne_eq, not_not]

@[simp]
lemma card_complDisagreementSet_le :
    (complDisagreementSet k φ f g).card ≤ 2 ^ (n - k) := by
  simp [complDisagreementSet, Finset.card_sdiff]

@[simp]
lemma complDisagreementSet_sub_subdomain :
    complDisagreementSet k φ f g ⊆ (φ.subdomain k).toFinset := by simp [complDisagreementSet]

lemma blockRelDistance_eq_one_sub' :
    δ𞁒(k, φ, f, g) =
    1 - ((complDisagreementSet k φ f g).card : ℚ) / (φ.subdomain k).toFinset.card := by
  have hS : ((φ.subdomain k).toFinset.card : ℚ) ≠ 0 := by simp
  rw [complDisagreementSet, Finset.card_sdiff_of_subset disagreementSet_sub_subdomain,
    Nat.cast_sub (Finset.card_le_card disagreementSet_sub_subdomain), _root_.sub_div, div_self hS,
    sub_sub_cancel]
  simp only [blockRelDistance, blockDistance, NNRat.cast_div, NNRat.cast_natCast]

lemma blockRelDistance_eq_one_sub :
    δ𞁒(k, φ, f, g) =
    1 - ((complDisagreementSet k φ f g).card : ℚ≥0) / (φ.subdomain k).toFinset.card := by
  rw [←NNRat.coe_inj, blockRelDistance_eq_one_sub',
      NNRat.coe_sub (natCast_div_le_one (Finset.card_le_card complDisagreementSet_sub_subdomain))]
  rfl

lemma card_complDisagreementSet :
    (complDisagreementSet k φ f g).card =
    (φ.subdomain k).toFinset.card - (disagreementSet k φ f g).card := by
  simp [complDisagreementSet, Finset.card_sdiff]

lemma card_disagreementSet' :
    (disagreementSet k φ f g).card =
    (φ.subdomain k).toFinset.card - (complDisagreementSet k φ f g).card := by
  rw [card_complDisagreementSet,
    Nat.sub_sub_self (Finset.card_le_card disagreementSet_sub_subdomain)]

def agreementBlockUnion
    (k : ℕ) (φ : SmoothCosetFftDomain n F)
  (f g : Fin (2 ^ n) → F) : Finset (Fin (2 ^ n)) :=
  Finset.biUnion (complDisagreementSet k φ f g) (blockIdx φ k)

@[simp]
lemma card_agreementBlockUnion_le :
    (agreementBlockUnion k φ f g).card ≤ 2 ^ n := by
  conv_rhs =>
    rw [show 2 ^ n = (Finset.univ (α := Fin (2 ^ n))).card by simp]
  exact Finset.card_le_card (by simp)

lemma card_agreementBlockUnion
    (hkn : k ≤ n) :
  (agreementBlockUnion k φ f g).card =
    2 ^ k * (complDisagreementSet k φ f g).card := by
  unfold agreementBlockUnion
  rw [Finset.card_biUnion pairwise_disjoint_blockIdx, Finset.sum_const_nat fun i hi ↦ ?_, mul_comm]
  rw [card_blockIdx, card_block_of_mem_subdomain' hkn
    (mem_toFinset_iff_mem.1 (complDisagreementSet_sub_subdomain hi))]

lemma agreement_sub_agreementBlockUnion :
    agreementBlockUnion k φ f g ⊆ ({ i | f i = g i } : Finset _) := fun x hx ↦ by
  obtain ⟨z, hz, hxz⟩ := Finset.mem_biUnion.1 hx
  rw [complDisagreementSet_def', Finset.mem_filter] at hz
  exact Finset.mem_filter.2 ⟨Finset.mem_univ x, hz.2 x hxz⟩

lemma card_disagreement_le :
    Finset.card { i | f i ≠ g i } ≤ 2 ^ n - (agreementBlockUnion k φ f g).card := by
  conv_rhs =>
    lhs
    rw [show 2 ^ n = (Fintype.card (α := Fin (2 ^ n))) by simp]
  rw [←Finset.card_compl]
  exact Finset.card_le_card <| fun x hx ↦ by
    simp only [Finset.mem_compl]
    intro contra
    have := agreement_sub_agreementBlockUnion contra
    simp_all

lemma relHammingDist_le_sub_agreementBlockUnion' :
    δᵣ(f, g) ≤ 1 - ((agreementBlockUnion k φ f g).card : ℚ) / (2 ^ n) := by
  have hD : hammingDist f g + (agreementBlockUnion k φ f g).card ≤ 2 ^ n :=
    (Nat.le_sub_iff_add_le card_agreementBlockUnion_le).1 card_disagreement_le
  rw [Code.relHammingDist, NNRat.cast_div, NNRat.cast_natCast, NNRat.cast_natCast,
    Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat, le_sub_iff_add_le, ← add_div,
    div_le_one (by positivity)]
  exact_mod_cast hD

lemma relHammingDist_le_sub_agreementBlockUnion :
    δᵣ(f, g) ≤ 1 - ((agreementBlockUnion k φ f g).card : ℚ≥0) / (2 ^ n) := by
  have := relHammingDist_le_sub_agreementBlockUnion' (f := f) (g := g) (φ := φ)
            (k := k)
  rw [←NNRat.cast_le (K := ℚ)]
  exact le_trans this <| le_of_eq <| by
    rw [NNRat.coe_sub (div_le_one_of_le₀ (by exact_mod_cast card_agreementBlockUnion_le) zero_le)]
    rfl

/-- Claim 4.19 from [ACFY24], Part 1
  For a smooth Reed-Solomon code, the standard relative Hamming distance `δᵣ(f,g)`
  is a lower bound for the k-wise block relative distance `δᵣ(k, φ, f, g)`.
-/
lemma relHammingDist_le_blockRelDistance (hkn : k ≤ n) :
    δᵣ(f, g) ≤ δ𞁒(k, φ, f, g) := by
  have h2 : (2 : ℚ) ^ n = 2 ^ k * 2 ^ (n - k) := by rw [← pow_add, Nat.add_sub_of_le hkn]
  rw [← NNRat.coe_le_coe]
  refine (relHammingDist_le_sub_agreementBlockUnion' (k := k) (φ := φ)).trans (le_of_eq ?_)
  rw [blockRelDistance_eq_one_sub', card_agreementBlockUnion hkn]
  simp only [card_toFinset, Fintype.card_fin, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [h2, mul_div_mul_left _ _ (pow_ne_zero _ two_ne_zero)]

/-- Claim 4.19 from [ACFY24], Part 2
  As a consequence of `relHammingDist_le_blockRelDistance`, the list of codewords
  within a certain block relative distance `δ` is a subset of the list of codewords
  within the same relative Hamming distance `δ`.
-/
lemma listBlock_subset_listHamming (hkn : k ≤ n) (δ : ℝ≥0) (C : Set (Fin (2 ^ n) → F)) :
    Λ𞁒(C, k, φ, f, δ) ⊆ closeCodewordsRel C f δ := by
  intro u hu
  simp only [blockRelDistanceBall, Set.mem_sep_iff] at hu
  refine ⟨hu.1, ?_⟩
  have h1 := relHammingDist_le_blockRelDistance
              (φ := φ) (k := k) (f := f) (g := u) hkn
  simp only [Code.relHammingBall, Set.mem_ofPred_eq, ge_iff_le]
  apply le_trans (b := NNRat.cast δ𞁒(k, φ, f, u))
  · rewrite [NNRat.cast_le]
    convert h1
  · aesop

end BlockRelDistance
