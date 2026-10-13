/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aryaethn
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.Ring

/-!
# BitZ: bitification of a witness over a finitely generated ring

BitZ ([BGKLSW26], Definition 4.9, Lemma 4.12 and §2.5.2) proves a linear claim `⟨ψ(f), v⟩ = μ` in a
ring `R` about a witness `f ∈ Sˡ⁰`, `ψ : S →+* R`, by committing to a vector of *bits* `g` with
`f = L · g` for a public *bitification matrix* `L`, and proving the claim `⟨ψ(g), Lᵀ v⟩ = μ`
instead. This file formalizes that algebra, independently of any commitment or protocol.

* `BitZ.boundedSpan γ B` is the set `S^{<D}_{≤B}` of [BGKLSW26, §3.1]: the sums `∑ⱼ hⱼ · γⱼ` over a
  family `γ` of "monomials" with integer coefficients `0 ≤ hⱼ < 2^B`. The family is left abstract;
  in the paper it is the monomials of total degree `< D` in the generators of `S`.
* `BitZ.bitMatrix γ B` is the standard bitification matrix `L = I ⊗ (1, 2, …, 2^{B-1}) ⊗ γ`.
* `BitZ.bitMatrix_mulVec_mem`: `L · g ∈ S^{<D}_{≤B}` for every bit vector `g`, the closure property
  (14) that guarantees extractors output witnesses in the allowed subset
  (so the range check comes "for free").
* `BitZ.exists_bitification`: every `f ∈ S^{<D}_{≤B}` has a bitification (completeness).
* `BitZ.dotProduct_map_mulVec`: Lemma 4.12, `⟨ψ(L x), v⟩ = ⟨ψ(x), ψ(L)ᵀ v⟩`, with the explicit
  weight vector `u = v ⊗ (1, …, 2^{B-1}) ⊗ ψ(γ)` of (47) in `BitZ.bitMatrix_transpose_mulVec`.
* `BitZ.exists_witness_iff_exists_bits`: a witness for the original claim exists iff a bit vector
  for the bitified claim does, "no knowledge-soundness loss" for Step 2 of [BGKLSW26, §2.5].
* `BitZ.sum_mul_eq_sum_dotProduct`: the tensor split of an inner product used in Round 2.

## References

* [BGKLSW26] R. Bloemen, A. Garreta, M. Kostrzewa, S. Londhe, L. Soukhanov, J. Wu.
  *BitZ: proofs and commitments in arbitrary rings through binary fields*. ePrint 2026/2141.
-/

@[expose] public section

open Finset Matrix

namespace BitZ

section Bits

/-- A vector of bits `b₀, …, b_{B-1} ∈ {0, 1}` encodes a number below `2^B`. -/
theorem sum_pow_two_mul_lt {B : ℕ} (b : Fin B → ℕ) (hb : ∀ k, b k ≤ 1) :
    ∑ k : Fin B, 2 ^ (k : ℕ) * b k < 2 ^ B := by
  induction B with
  | zero => simp
  | succ B ih =>
    rw [Fin.sum_univ_succ]
    have h := ih (fun k => b k.succ) (fun k => hb _)
    have h0 := hb 0
    have hs : ∑ k : Fin B, 2 ^ ((k.succ : Fin (B + 1)) : ℕ) * b k.succ =
        2 * ∑ k : Fin B, 2 ^ (k : ℕ) * b k.succ := by
      rw [mul_sum]
      exact sum_congr rfl fun k _ => by simp [pow_succ]; ring
    rw [hs, pow_succ]
    simp only [Fin.val_zero, pow_zero, one_mul]
    omega

/-- Every number below `2^B` is the value of a vector of `B` bits. -/
theorem exists_bits (B n : ℕ) (hn : n < 2 ^ B) :
    ∃ b : Fin B → ℕ, (∀ k, b k ≤ 1) ∧ n = ∑ k : Fin B, 2 ^ (k : ℕ) * b k := by
  induction B generalizing n with
  | zero => exact ⟨Fin.elim0, fun k => k.elim0, by simpa using hn⟩
  | succ B ih =>
    obtain ⟨b, hb, hsum⟩ := ih (n / 2) (by rw [pow_succ] at hn; omega)
    refine ⟨Fin.cons (n % 2) b, fun k => ?_, ?_⟩
    · refine Fin.cases ?_ (fun k => ?_) k
      · simp; omega
      · simpa using hb k
    · rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero, one_mul, Fin.cons_zero, Fin.val_succ, Fin.cons_succ]
      have : ∑ k : Fin B, 2 ^ ((k : ℕ) + 1) * b k = 2 * ∑ k : Fin B, 2 ^ (k : ℕ) * b k := by
        rw [mul_sum]
        exact sum_congr rfl fun k _ => by rw [pow_succ]; ring
      rw [this, ← hsum]
      omega

end Bits

section Span

variable {S : Type*} [CommRing S] {M : Type*} [Fintype M]

/-- The set `S^{<D}_{≤B}` of [BGKLSW26, §3.1]: the ring elements `∑ⱼ hⱼ · γⱼ` over the family `γ`
of monomials with coefficients `hⱼ` integers in `[0, 2^B)`. -/
def boundedSpan (γ : M → S) (B : ℕ) : Set S :=
  {s | ∃ h : M → ℕ, (∀ j, h j < 2 ^ B) ∧ s = ∑ j, (h j : S) * γ j}

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The standard **bitification matrix** `L = I_ι ⊗ (1, 2, …, 2^{B-1}) ⊗ (γⱼ)ⱼ` of
[BGKLSW26, Definition 4.9], with columns indexed by `(i, k, j)`. -/
def bitMatrix (γ : M → S) (B : ℕ) : Matrix ι (ι × Fin B × M) S :=
  fun i x => if i = x.1 then (2 : S) ^ (x.2.1 : ℕ) * γ x.2.2 else 0

/-- `(L x)ᵢ = ∑ₖ ∑ⱼ 2^k · γⱼ · x(i, k, j)`. -/
theorem bitMatrix_mulVec (γ : M → S) (B : ℕ) (x : ι × Fin B × M → S) (i : ι) :
    (bitMatrix γ B).mulVec x i = ∑ k : Fin B, ∑ j : M, (2 : S) ^ (k : ℕ) * γ j * x (i, k, j) := by
  simp only [mulVec, dotProduct, bitMatrix, Fintype.sum_prod_type, ite_mul, zero_mul]
  simp [Finset.sum_ite_eq]

/-- **Closure** (eq. (14) of [BGKLSW26]): `L · g ∈ S^{<D}_{≤B}` for every vector of bits `g`. -/
theorem bitMatrix_mulVec_mem (γ : M → S) (B : ℕ) (g : ι × Fin B × M → ℕ) (hg : ∀ x, g x ≤ 1)
    (i : ι) : (bitMatrix γ B).mulVec (fun x => (g x : S)) i ∈ boundedSpan γ B := by
  refine ⟨fun j => ∑ k : Fin B, 2 ^ (k : ℕ) * g (i, k, j), fun j => ?_, ?_⟩
  · exact sum_pow_two_mul_lt (fun k => g (i, k, j)) fun k => hg _
  · rw [bitMatrix_mulVec, sum_comm]
    refine sum_congr rfl fun j _ => ?_
    push_cast
    rw [sum_mul]
    exact sum_congr rfl fun k _ => by ring

/-- **Completeness of bitification:** every `f ∈ S^{<D}_{≤B}` has a bitification `g`,
i.e. a vector of bits with `f = L · g`. -/
theorem exists_bitification (γ : M → S) (B : ℕ) (f : ι → S) (hf : ∀ i, f i ∈ boundedSpan γ B) :
    ∃ g : ι × Fin B × M → ℕ, (∀ x, g x ≤ 1) ∧
      f = (bitMatrix γ B).mulVec (fun x => (g x : S)) := by
  choose h hlt hfi using hf
  have hbits : ∀ i j, ∃ b : Fin B → ℕ, (∀ k, b k ≤ 1) ∧
      h i j = ∑ k : Fin B, 2 ^ (k : ℕ) * b k :=
    fun i j => exists_bits B (h i j) (hlt i j)
  choose b hb hsum using hbits
  refine ⟨fun x => b x.1 x.2.2 x.2.1, fun x => hb _ _ _, funext fun i => ?_⟩
  rw [hfi i, bitMatrix_mulVec, sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [hsum i j]
  push_cast
  rw [sum_mul]
  exact sum_congr rfl fun k _ => by ring

end Span

section Lemma412

variable {S R : Type*} [CommRing S] [CommRing R] (ψ : S →+* R) {ι ℓ : Type*} [Fintype ι]
  [Fintype ℓ]

/-- **[BGKLSW26, Lemma 4.12].** For a matrix `L` over `S` and `ψ : S →+* R`,
`⟨ψ(L x), v⟩ = ⟨ψ(x), ψ(L)ᵀ v⟩`. -/
theorem dotProduct_map_mulVec (L : Matrix ι ℓ S) (x : ℓ → S) (v : ι → R) :
    v ⬝ᵥ (fun i => ψ ((L.mulVec x) i)) = (fun p => ψ (x p)) ⬝ᵥ ((L.map ψ)ᵀ.mulVec v) := by
  have h1 : (fun i => ψ ((L.mulVec x) i)) = (L.map ψ).mulVec (fun p => ψ (x p)) := by
    funext i
    simp [mulVec, dotProduct, map_sum]
  rw [h1, dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]

/-- Specialization to bit vectors: `ψ` sends the bits `0, 1 ∈ S` to the bits `0, 1 ∈ R`, so
`⟨ψ(L g), v⟩ = ⟨g, ψ(L)ᵀ v⟩` with `g` read in `R`. -/
theorem dotProduct_map_mulVec_bits (L : Matrix ι ℓ S) (g : ℓ → ℕ) (v : ι → R) :
    v ⬝ᵥ (fun i => ψ ((L.mulVec fun p => (g p : S)) i)) =
      (fun p => (g p : R)) ⬝ᵥ ((L.map ψ)ᵀ.mulVec v) := by
  simpa using dotProduct_map_mulVec ψ L (fun p => (g p : S)) v

end Lemma412

section Weights

variable {S R : Type*} [CommRing S] [CommRing R] (ψ : S →+* R) {M : Type*} [Fintype M]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype M] in
/-- **The bitified weight vector** (eq. (47) of [BGKLSW26]): for the standard matrix,
`ψ(L)ᵀ v = v ⊗ (1, 2, …, 2^{B-1}) ⊗ (ψ(γⱼ))ⱼ`. -/
theorem bitMatrix_transpose_mulVec (γ : M → S) (B : ℕ) (v : ι → R) (x : ι × Fin B × M) :
    ((bitMatrix γ B).map ψ)ᵀ.mulVec v x = v x.1 * (2 : R) ^ (x.2.1 : ℕ) * ψ (γ x.2.2) := by
  obtain ⟨i, k, j⟩ := x
  simp only [mulVec, dotProduct, transpose_apply, map_apply, bitMatrix]
  rw [Finset.sum_eq_single i]
  · simp only [↓reduceIte, map_mul, map_pow, map_ofNat]
    ring
  · intro b _ hb
    simp [hb]
  · simp

/-- **No knowledge-soundness loss in bitification** ([BGKLSW26, §2.5], Step 2). The original claim
has a witness `f ∈ (S^{<D}_{≤B})^ι` with `⟨ψ(f), v⟩ = μ` if and only if the bitified claim
`⟨g, ψ(L)ᵀ v⟩ = μ` has a witness `g` of bits. Moreover the two witnesses correspond via
`f = L · g` (`bitMatrix_mulVec_mem`, `exists_bitification`). -/
theorem exists_witness_iff_exists_bits (γ : M → S) (B : ℕ) (v : ι → R) (μ : R) :
    (∃ f : ι → S, (∀ i, f i ∈ boundedSpan γ B) ∧ v ⬝ᵥ (fun i => ψ (f i)) = μ) ↔
      ∃ g : ι × Fin B × M → ℕ, (∀ x, g x ≤ 1) ∧
        (fun p => (g p : R)) ⬝ᵥ (((bitMatrix γ B).map ψ)ᵀ.mulVec v) = μ := by
  constructor
  · rintro ⟨f, hf, hfv⟩
    obtain ⟨g, hg, rfl⟩ := exists_bitification γ B f hf
    exact ⟨g, hg, by rw [← dotProduct_map_mulVec_bits]; exact hfv⟩
  · rintro ⟨g, hg, hgv⟩
    exact ⟨(bitMatrix γ B).mulVec fun x => (g x : S), bitMatrix_mulVec_mem γ B g hg,
      by rw [dotProduct_map_mulVec_bits]; exact hgv⟩

end Weights

section Tensor

variable {α : Type*} [CommSemiring α] {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]

/-- **Tensor split of an inner product** (Round 2 of [BGKLSW26, Construction 4.4]): for a weight
vector `v₁ ⊗ v₂` and a witness `x` indexed by `ι₁ × ι₂`,
`⟨v₁ ⊗ v₂, x⟩ = ∑ⱼ ⟨v₁, x(·, j)⟩ · v₂ⱼ`. -/
theorem sum_mul_eq_sum_dotProduct (v₁ : ι₁ → α) (v₂ : ι₂ → α) (x : ι₁ × ι₂ → α) :
    ∑ p : ι₁ × ι₂, v₁ p.1 * v₂ p.2 * x p = ∑ j, (v₁ ⬝ᵥ fun i => x (i, j)) * v₂ j := by
  rw [Fintype.sum_prod_type_right]
  refine sum_congr rfl fun j _ => ?_
  rw [dotProduct, sum_mul]
  exact sum_congr rfl fun i _ => by ring

end Tensor

end BitZ
