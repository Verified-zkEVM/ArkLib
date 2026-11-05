/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aryaethn
-/
module

public import ArkLib.Data.Matrix.DotProduct
public import ArkLib.Data.Nat.BitSum
public import CompPoly.Data.Nat.Bitwise

/-!
# BitZ: bitifying a witness over a finitely generated ring

BitZ proves a linear claim `⟨ψ(f), v⟩ = μ` in a ring `R` about a witness `f ∈ Sˡ⁰` over a finitely
generated ring `S`, with `ψ : S →+* R`, by committing to a vector of *bits* `g` with `f = L · g`
for a public *bitification matrix* `L`, and by proving the claim `⟨g, ψ(L)ᵀ v⟩ = μ` instead
([BGKLSW26, Definition 4.9 and Lemma 4.12]). This file formalizes that algebra for the standard
matrix `L = I ⊗ (1, 2, …, 2^{B-1}) ⊗ γ`, independently of any commitment or protocol.

## Main statements

* `BitZ.boundedCombos γ B` is the set of sums `∑ⱼ hⱼ · γⱼ` with integer coefficients `0 ≤ hⱼ < 2^B`
  ([BGKLSW26, §3.1]).
* `BitZ.bitMatrix γ B` is the standard bitification matrix, `BitZ.bitWeights ψ γ B v` is the weight
  vector `v ⊗ (1, …, 2^{B-1}) ⊗ ψ(γ)` of [BGKLSW26, (47)], and
  `BitZ.bitMatrix_map_transpose_mulVec` shows that it is `ψ(L)ᵀ v`.
* `BitZ.bitMatrix_mulVec_mem` is the closure property [BGKLSW26, (14)]: `L · g` has entries in
  `boundedCombos γ B` for every vector of bits `g`.
* `BitZ.exists_bitification` shows that every vector with entries in `boundedCombos γ B` is
  `L · g` for a vector of bits `g`. The bits are computed by `BitZ.coeffBits` from the
  coefficients (`BitZ.bitMatrix_mulVec_coeffBits`).
* `Matrix.dotProduct_map_mulVec` gives `⟨ψ(L x), v⟩ = ⟨ψ(x), ψ(L)ᵀ v⟩` (Lemma 4.12), and
  `BitZ.exists_witness_iff_exists_bits` states that bitification preserves satisfiability.

`bitMatrix`, `bitWeights` and `coeffBits` are executable. `boundedCombos` is a `Set` in an arbitrary
ring, so it is a mathematical specification: membership has no decision procedure, and a member
carries its coefficient vector as data (the argument `h` of `coeffBits`).

Paper-specific correspondence and remaining formalization work are recorded in the
[BitZ KB](https://github.com/Verified-zkEVM/ArkLib/blob/main/docs/kb/papers/BGKLSW26.md).

## References

* [Bloemen, R., Garreta, A., Kostrzewa, M., Londhe, S., Soukhanov, L., and Wu, J.,
    *BitZ: proofs and commitments in arbitrary rings through binary fields*][BGKLSW26]
-/

@[expose] public section

open Finset Matrix

namespace BitZ

section Digits

variable {ι M : Type*}

/-- The binary digits of the coefficients `h i j`: entry `(i, k, j)` is the `k`-th digit of
`h i j`. -/
def coeffBits (B : ℕ) (h : ι → M → ℕ) : ι × Fin B × M → ℕ :=
  fun x => Nat.getBit x.2.1 (h x.1 x.2.2)

/-- The entries of `coeffBits` are bits. -/
theorem coeffBits_le_one (B : ℕ) (h : ι → M → ℕ) (x : ι × Fin B × M) : coeffBits B h x ≤ 1 :=
  Nat.lt_succ_iff.1 Nat.getBit_lt_2

end Digits

section Combos

variable {S : Type*} [CommSemiring S] {M : Type*} [Fintype M]

/-- The sums `∑ⱼ hⱼ · γⱼ` over the family `γ` with natural coefficients `hⱼ < 2 ^ B`. The family
`γ` need not be injective, so it may list the same ring element several times. -/
def boundedCombos (γ : M → S) (B : ℕ) : Set S :=
  {s | ∃ h : M → ℕ, (∀ j, h j < 2 ^ B) ∧ s = ∑ j, (h j : S) * γ j}

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The standard **bitification matrix** `I_ι ⊗ (1, 2, …, 2^{B-1}) ⊗ γ`, whose columns are indexed
by `(i, k, j)`: the entry in row `i` and column `(i, k, j)` is `2 ^ k * γⱼ`, and all other entries
are zero. -/
def bitMatrix (γ : M → S) (B : ℕ) : Matrix ι (ι × Fin B × M) S :=
  Matrix.of fun i x => if i = x.1 then (2 : S) ^ (x.2.1 : ℕ) * γ x.2.2 else 0

/-- `(L x)ᵢ = ∑ₖ ∑ⱼ 2 ^ k * γⱼ * x(i, k, j)`. -/
theorem bitMatrix_mulVec_apply (γ : M → S) (B : ℕ) (x : ι × Fin B × M → S) (i : ι) :
    (bitMatrix γ B *ᵥ x) i = ∑ k : Fin B, ∑ j : M, (2 : S) ^ (k : ℕ) * γ j * x (i, k, j) := by
  simp only [mulVec, dotProduct, bitMatrix, of_apply, Fintype.sum_prod_type, ite_mul, zero_mul]
  simp [Finset.sum_ite_eq]

/-- **Closure.** For every vector of bits `g`, the entries of `L · g` lie in `boundedCombos γ B`. -/
theorem bitMatrix_mulVec_mem (γ : M → S) (B : ℕ) (g : ι × Fin B × M → ℕ) (hg : ∀ x, g x ≤ 1)
    (i : ι) : (bitMatrix γ B *ᵥ fun x => (g x : S)) i ∈ boundedCombos γ B := by
  refine ⟨fun j => ∑ k : Fin B, 2 ^ (k : ℕ) * g (i, k, j), fun j => ?_, ?_⟩
  · exact Nat.sum_pow_two_mul_lt (fun k => g (i, k, j)) fun k => hg _
  · rw [bitMatrix_mulVec_apply, sum_comm]
    refine sum_congr rfl fun j _ => ?_
    push_cast
    rw [sum_mul]
    exact sum_congr rfl fun k _ => by ring

/-- **The bits of the coefficients are a bitification.** If every coefficient `h i j` is below
`2 ^ B`, then `L` applied to `coeffBits B h` is the vector with entries `∑ⱼ h i j * γⱼ`. -/
theorem bitMatrix_mulVec_coeffBits (γ : M → S) {B : ℕ} (h : ι → M → ℕ)
    (hlt : ∀ i j, h i j < 2 ^ B) :
    bitMatrix γ B *ᵥ (fun x => (coeffBits B h x : S)) = fun i => ∑ j, (h i j : S) * γ j := by
  funext i
  rw [bitMatrix_mulVec_apply, sum_comm]
  refine sum_congr rfl fun j _ => ?_
  conv_rhs => rw [Nat.getBit_repr_univ (h i j) (hlt i j)]
  push_cast
  rw [sum_mul]
  exact sum_congr rfl fun k _ => by simp only [coeffBits]; ring

/-- **Every element of `boundedCombos` has a bitification.** If every entry of `f` lies in
`boundedCombos γ B`, there is a vector of bits `g` with `f = L · g`. -/
theorem exists_bitification (γ : M → S) (B : ℕ) (f : ι → S) (hf : ∀ i, f i ∈ boundedCombos γ B) :
    ∃ g : ι × Fin B × M → ℕ, (∀ x, g x ≤ 1) ∧ f = bitMatrix γ B *ᵥ fun x => (g x : S) := by
  choose h hlt hfi using hf
  exact ⟨coeffBits B h, coeffBits_le_one B h, by
    rw [bitMatrix_mulVec_coeffBits γ h hlt]
    exact funext hfi⟩

end Combos

section Weights

variable {S R : Type*} [CommSemiring S] [CommSemiring R] (ψ : S →+* R) {M : Type*} {ι : Type*}

/-- The **bitified weight vector** `v ⊗ (1, 2, …, 2^{B-1}) ⊗ (ψ(γⱼ))ⱼ`, with entries indexed by
`(i, k, j)`. -/
def bitWeights (γ : M → S) (B : ℕ) (v : ι → R) : ι × Fin B × M → R :=
  fun x => v x.1 * (2 : R) ^ (x.2.1 : ℕ) * ψ (γ x.2.2)

variable [Fintype ι] [DecidableEq ι]

/-- For the standard bitification matrix, `ψ(L)ᵀ v` is the bitified weight vector. -/
theorem bitMatrix_map_transpose_mulVec (γ : M → S) (B : ℕ) (v : ι → R) :
    ((bitMatrix γ B).map ψ)ᵀ *ᵥ v = bitWeights ψ γ B v := by
  funext x
  obtain ⟨i, k, j⟩ := x
  simp only [mulVec, dotProduct, transpose_apply, map_apply, bitMatrix, of_apply, bitWeights]
  rw [Finset.sum_eq_single i]
  · simp only [↓reduceIte, map_mul, map_pow, map_ofNat]
    ring
  · intro b _ hb
    simp [hb]
  · simp

variable [Fintype M]

omit [DecidableEq ι] in
/-- **Bitification preserves satisfiability.** The original claim has a witness `f` with entries
in `boundedCombos γ B` and `⟨v, ψ(f)⟩ = μ` if and only if the bitified claim `⟨g, u⟩ = μ`, with
`u` the bitified weight vector, has a witness `g` of bits. In the proof, the `←` direction takes
`f := L · g`. -/
theorem exists_witness_iff_exists_bits (γ : M → S) (B : ℕ) (v : ι → R) (μ : R) :
    (∃ f : ι → S, (∀ i, f i ∈ boundedCombos γ B) ∧ v ⬝ᵥ (fun i => ψ (f i)) = μ) ↔
      ∃ g : ι × Fin B × M → ℕ, (∀ x, g x ≤ 1) ∧
        (fun p => (g p : R)) ⬝ᵥ bitWeights ψ γ B v = μ := by
  classical
  have key : ∀ g : ι × Fin B × M → ℕ,
      v ⬝ᵥ (fun i => ψ ((bitMatrix γ B *ᵥ fun x => (g x : S)) i)) =
        (fun p => (g p : R)) ⬝ᵥ bitWeights ψ γ B v := fun g => by
    simpa [bitMatrix_map_transpose_mulVec] using
      dotProduct_map_mulVec ψ (bitMatrix γ B) (fun x => (g x : S)) v
  constructor
  · rintro ⟨f, hf, hfv⟩
    obtain ⟨g, hg, rfl⟩ := exists_bitification γ B f hf
    exact ⟨g, hg, (key g).symm.trans hfv⟩
  · rintro ⟨g, hg, hgv⟩
    exact ⟨_, bitMatrix_mulVec_mem γ B g hg, (key g).trans hgv⟩

end Weights

end BitZ
