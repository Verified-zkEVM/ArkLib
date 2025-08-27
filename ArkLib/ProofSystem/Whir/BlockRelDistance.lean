/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poulami Das (Least Authority), Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.ListDecodability

/-!
# Block Relative Distance for smooth Reed-Solomon Codes

This file formalizes the notion of mutual correlated agreement for proximity generators,
introduced in the [Section 4 of the WHIR paper][todo: ArkLib bibliography].

## Implementation notes

Block relative distance is defined for smooth rather than constrained Reed Solomon codes,
as is done in the reference paper, as they are more general.
The definition of `block' is also stated in a more general form than the reference paper.

We define distances for smooth ReedSolomon codes with respect to power and fiber domains,
as per Section 4.3.1, [ACFY24].
We have generalized the definitions for a generic i to present (i,k)-wise distance measures.
This modification is necessary to support following lemmas from Section  4.3.2.
The definitions from Section 4.3.1 correspond to i = 0.
## References

* G Arnon, A Chiesa, G Fenzi, and E Yogev,
[*WHIR: Reed–Solomon Proximity Testing with Super-Fast Verification*][todo: ArkLib bibliography]
Freely available at https://eprint.iacr.org/2024/1586

-/

namespace BlockRelDistance

open ListDecodable NNReal ReedSolomon

variable {F : Type*} [Field F]
         {ι : Type*} [Fintype ι] [Pow ι ℕ]

/-- The `2^k`-th power images over an embedding `φ : ι ↪ F` and a finite set
  of elements `S : Finset ι`.

  In particular, it returns the set of field elements `y ∈ F` for which there exists `x ∈ S`
  such that `y = (φ x)^(2ᵏ)`. It models the image of the map `x ↦ (φ x)^(2ᵏ)` restricted to `S`.
  Semantically: `indexPowT S φ k = { (φ x)^(2ᵏ) | x ∈ S } ⊆ F`.
-/
def indexPowT (S : Finset ι) (φ : ι ↪ F) (k : ℕ) := { y : F // ∃ x ∈ S, y = (φ x) ^ (2^k) }

/-- For i ≤ k, the generic `2^(k-i)`-th power fiber over `y ∈ indexPowT S φ k`.
  For `φ' : ι^(2ⁱ) → F`, this defines the preimage of `y` under the map
  `x^(2ⁱ) ↦ x^(2ᵏ)` restricted to `x^(2ⁱ) ∈ S'`.

  It returns the subset `S'` of elements of type `ι^(2ⁱ)`
    such that `(x^(2ⁱ))^(2^(k-i)) = x^(2^k) = y`.
  Example i = 0 : powFiberT 0 k S' φ' y = { x ∈ S' | (x)^(2^k) = y }.
  Example i = 1 : powFiberT 1 k S' φ' y = { x^2 ∈ S' | (x^2)^(2^(k-1)) = y }.
-/
def powFiberT (i : ℕ) {k : ℕ} {S : Finset ι} {φ : ι ↪ F} (S' : Finset (indexPowT S φ i))
  (φ' : (indexPowT S φ i) ↪ F) (y : indexPowT S φ k) :=
  { x : (indexPowT S φ i) // x ∈ S' ∧ (φ' x) ^ (2^(k-i)) = y.val }

/-- Definition 4.16
  For `ι` be a smooth evaluation domain, `k` be a folding parameter, `z ∈ (ι^(2ᵏ))`,
  Block is the set of elements `{ y ∈ S', y ^ 2^(k-i) = z }`, for `S' : Finset ι^(2ⁱ)`. -/
def block (i : ℕ) {k : ℕ} {S : Finset ι} {φ : ι ↪ F}
  (S' : Finset (indexPowT S φ i))
  (φ' : (indexPowT S φ i) ↪ F) (z : indexPowT S φ k)
  [DecidableEq F] [DecidableEq ι] [Smooth φ] :=
    powFiberT i S' φ' z

/-- The class DecidableBlockDisagreement provides a decidability instance for testing
  pointwise inequality of two functions `f, g : ι^(2ⁱ) → F` on elements of `block i k S' φ' z`,
  for all `z ∈ LpowT S' φ' k`.

  This class abstracts the decidability condition required to determine whether two
  functions disagree on any point in the preimage of `z` under the map `x^(2ⁱ) ↦ x^(2ᵏ)` over the
  evaluation domain `φ' : ι^(2ⁱ) ↪ F`. This is useful in defining sets of such `z`.
-/
class DecidableBlockDisagreement
  (i k : ℕ) {S : Finset ι} {φ : ι ↪ F}
  [DecidableEq F] [DecidableEq ι] [Smooth φ]
  (f : (indexPowT S φ i) → F) (S' : Finset (indexPowT S φ i))
  (φ' : (indexPowT S φ i) ↪ F) where
  dec_inst :
    ∀ z : indexPowT S φ k, ∀ g : (indexPowT S φ i) → F,
      Decidable (∃ y : block i S' φ' z, f y.val ≠ g y.val)

/-- Let C be a smooth ReedSolomon code `C = RS[F, ι^(2ⁱ), φ', m]` and `f,g : ι^(2ⁱ) → F`, then
  the (i,k)-wise block relative distance is defined as
    Δᵣ(i, k, f, S', φ', g) = |{z ∈ ι ^ 2^k : ∃ y ∈ Block(i,k,S',φ',z) f(y) ≠ g(y)}| / |ι^(2^k)|.

  Below, we define a disagreementSet(i,k,f,S',φ') as a map (g → Finset (indexPow S φ k))
  using the class DecidableBlockDisagreement, to filter a finite subset of the Finset
  (indexPow S φ k), as per {z ∈ ι ^ 2^k : ∃ y ∈ Block(i,k,S',φ',z) f(y) ≠ g(y)} for a given g. -/
noncomputable def disagreementSet
  (i k : ℕ) {S : Finset ι} {φ : ι ↪ F}
  [DecidableEq F] [DecidableEq ι] [Smooth φ]
  (f : (indexPowT S φ i) → F) (S' : Finset (indexPowT S φ i))
  (φ' : (indexPowT S φ i) ↪ F) [∀ i : ℕ, Fintype (indexPowT S φ i)]
  [h : DecidableBlockDisagreement i k f S' φ'] :
  (g : (indexPowT S φ i) → F) → Finset (indexPowT S φ k) :=
  fun g =>
    Finset.univ.filter (fun z => @decide _ (h.dec_inst z g))

/-- Definition 4.17
  Given the disagreementSet from above, we obtain the block relative distance as
  |disagreementSet|/ |ι ^ (2^k)|
-/
noncomputable def blockRelDistance
  (i k : ℕ) {S : Finset ι} {φ : ι ↪ F}
  [DecidableEq F] [DecidableEq ι] [Smooth φ]
  (f : (indexPowT S φ i) → F) (S' : Finset (indexPowT S φ i))
  (φ' : (indexPowT S φ i) ↪ F) [∀ i : ℕ, Fintype (indexPowT S φ i)]
  [h : DecidableBlockDisagreement i k f S' φ'] :
  (g : (indexPowT S φ i) → F) → ℝ≥0 :=
  fun g =>
    (disagreementSet i k f S' φ' g).card / (Fintype.card (indexPowT S φ k) : ℝ≥0)

/-- notation `Δᵣ(i, k, f, S', φ', g)` is the (i,k)-wise block relative distance. -/
scoped notation "Δᵣ( "i", "k", "f", "S'", "φ'", "g" )"  => blockRelDistance i k f S' φ' g

/-- The block relative distance simplifies to the standard relative Hamming distance when `k=0`. -/
lemma blockRelDistance_eq_relHammingDist_of_k_eq_i -- Renamed for clarity
  (i : ℕ) {S : Finset ι} {φ : ι ↪ F}
  [DecidableEq F] [DecidableEq ι] [Smooth φ]
  -- The Fintype instance is now declared before it is needed by `hS'`.
  [h_fintype : ∀ i : ℕ, Fintype (indexPowT S φ i)]
  (f g : (indexPowT S φ i) → F) (S' : Finset (indexPowT S φ i))
  (hS' : S' = Finset.univ) -- This now works.
  (φ' : (indexPowT S φ i) ↪ F)
  [h_dec : DecidableBlockDisagreement i i f S' φ'] [DecidableEq (indexPowT S φ i)] :
  Δᵣ(i, i, f, S', φ', g) = δᵣ(f, g) := by sorry

/-- For the set S ⊆ F^ι, we define the minimum block relative distance wrt set S. -/
noncomputable def minBlockRelDistance
  (i k : ℕ) {S : Finset ι} {φ : ι ↪ F}
  [DecidableEq F] [DecidableEq ι] [Smooth φ]
  (f : (indexPowT S φ i) → F) (S' : Finset (indexPowT S φ i))
  (φ' : (indexPowT S φ i) ↪ F) (Set : Set ((indexPowT S φ i) → F))
  [∀ i : ℕ, Fintype (indexPowT S φ i)]
  [h : DecidableBlockDisagreement i k f S' φ'] : ℝ≥0 :=
    sInf { d : ℝ≥0 | ∃ g ∈ Set, Δᵣ(i, k, f, S', φ', g) = d}

/-- notation `Δₛ(i, k, f, S', φ', Set)` denotes the minimum block relative distance wrt `Set`. -/
scoped notation "Δₛ( "i", "k", "f", "S'", "φ'", "Set" )"  => minBlockRelDistance i k f S' φ' Set

/-- Definition 4.18
  For a smooth ReedSolomon code C = RS[F, ι^(2ⁱ), φ', m], proximity parameter δ ∈ [0,1]
  function f : ι^(2ⁱ) → F, we define the following as the list of codewords of C δ-close to f,
  i.e., u ∈ C such that Δᵣ(i, k, f, S', φ', u) ≤ δ. -/
noncomputable def listBlockRelDistance
  (i k : ℕ) {S : Finset ι} {φ : ι ↪ F} {φ' : (indexPowT S φ i) ↪ F}
  {m : ℕ} [DecidableEq F] [DecidableEq ι] [Smooth φ]
  (f : (indexPowT S φ i) → F) (S' : Finset (indexPowT S φ i))
  [∀ i : ℕ, Fintype (indexPowT S φ i)] [DecidableEq (indexPowT S φ i)] [Smooth φ']
  (C : Set ((indexPowT S φ i) → F)) (_hcode : C = smoothCode φ' m) (δ : ℝ≥0)
  [h : DecidableBlockDisagreement i k f S' φ'] : (Set ((indexPowT S φ i) → F)) :=
    { u ∈ C | Δᵣ(i, k, f, S', φ', u) ≤ δ }

/-- `Λᵣ(i, k, f, S', C, hcode, δ)` denotes the list of codewords of C δ-close to f,
  wrt to the block relative distance. -/
scoped notation "Λᵣ( "i", "k", "f", "S'", "C", "hcode", "δ")" =>
  listBlockRelDistance i k f S' C hcode δ

/-- Claim 4.19, Part 1
  For a smooth Reed-Solomon code, the standard relative Hamming distance `δᵣ(f,g)`
  is a lower bound for the (i, k)-wise block relative distance `Δᵣ(i, k, f, S', φ', g)`.
-/
lemma relHammingDist_le_blockRelDistance
  (i k : ℕ) {S : Finset ι} {φ : ι ↪ F} {φ' : (indexPowT S φ i) ↪ F}
  [DecidableEq F] [DecidableEq ι] [Smooth φ]
  (f g : (indexPowT S φ i) → F) (S' : Finset (indexPowT S φ i))
  [h_fintype : ∀ i : ℕ, Fintype (indexPowT S φ i)]
  [DecidableEq (indexPowT S φ i)] [Smooth φ']
  [h_dec : DecidableBlockDisagreement i k f S' φ'] :
  δᵣ(f, g) ≤ Δᵣ(i, k, f, S', φ', g) := by sorry

/-- Claim 4.19, Part 2
  As a consequence of `relHammingDist_le_blockRelDistance`, the list of codewords
  within a certain block relative distance `δ` is a subset of the list of codewords
  within the same relative Hamming distance `δ`.
-/
lemma listBlock_subset_listHamming
  (i k : ℕ) {S : Finset ι} {φ : ι ↪ F} {φ' : (indexPowT S φ i) ↪ F}
  {m : ℕ} [DecidableEq F] [DecidableEq ι] [Smooth φ]
  (f : (indexPowT S φ i) → F) (S' : Finset (indexPowT S φ i))
  [h_fintype : ∀ i : ℕ, Fintype (indexPowT S φ i)] [DecidableEq (indexPowT S φ i)] [Smooth φ']
  (C : Set ((indexPowT S φ i) → F)) (hcode : C = smoothCode φ' m)
  [h_dec : DecidableBlockDisagreement i k f S' φ']
  (δ : ℝ≥0) (hδLe : δ ≤ 1) :
  Λᵣ(i, k, f, S', C, hcode, δ) ⊆ relHammingBall C f δ := by sorry


end BlockRelDistance
