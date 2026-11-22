/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import ArkLib.Data.CodingTheory.ListDecodability.Bounds.ReedSolomon.Certificate
public import ArkLib.Data.MvPolynomial.Degrees
public import ArkLib.ToMathlib.MvPolynomial.SchwartzZippel
public import ArkLib.ToMathlib.MvPolynomial.SchwartzZippelPrefix
public import Mathlib.Data.Fintype.CardEmbedding

/-!
# Rank loss of the intersection matrix at random evaluation points

Let `F` be a finite field with `q` elements and `H : Fin n → Finset (Fin (s + 1))` a hypergraph.
This file counts the tuples `α : Fin n ↪ F` of pairwise distinct evaluation points at which `H`
is not rigid for degree `k`, that is, at which the intersection matrix evaluated at `α` does not
have full column rank. There are `E = Fintype.card (Fin n ↪ F)` such tuples in all, and
coordinate `i` of a tuple takes one of the `q - i ≥ q - n + 1` values not taken before it.

If `H` is `k`-weakly partition-connected, its intersection matrix has a nonzero maximal minor. The
minor has degree at most `s * (k - 1)` in each of the `n` variables, hence total degree at most
`n * (s * (k - 1))`, and it vanishes at every tuple at which `H` is not rigid. Schwartz–Zippel
over pairwise-distinct points gives

  `#{α | ¬IsRigid H k α} * (q - n + 1) ≤ n * (s * (k - 1)) * E`

If `H` is `(k + 2 * r)`-weakly partition-connected, every tuple at which `H` is not rigid has a
certificate `c : Fin r ↪ Fin n` with fewer than `2 ^ (s + 1)` descents. For a fixed `c`, given
the coordinates before `c j`, the coordinate `c j` of a tuple with certificate `c` is one of at
most `s * (k - 1)` roots of a nonzero polynomial, so

  `#{α | IsCertificate F hH α c} * (q - n + 1) ^ r ≤ (s * (k - 1)) ^ r * E`

At most `n.choose r * (2 ^ (s + 1)) ^ r` embeddings `Fin r ↪ Fin n` have fewer than `2 ^ (s + 1)`
descents, and summing over them gives

  `#{α | ¬IsRigid H k α} * (q - n + 1) ^ r ≤ n.choose r * (2 ^ (s + 1)) ^ r * (s * (k - 1)) ^ r * E`

Dividing by `E` turns each count into a bound on the probability that a uniformly random tuple of
pairwise distinct points lies in the counted set.

## Main statements

* `card_filter_not_isRigid_mul_le`: the count of tuples at which a `k`-weakly
  partition-connected hypergraph is not rigid, from one nonzero minor.
* `card_filter_isCertificate_mul_pow_le`: the count of tuples with a given certificate.
* `card_filter_not_isRigid_mul_pow_le`: the count of tuples at which a `(k + 2 * r)`-weakly
  partition-connected hypergraph is not rigid, from the certificates.

`card_filter_isCertificate_mul_pow_le` is the bound of [AGL24] on the probability of one
certificate, and `card_filter_not_isRigid_mul_pow_le` is the counting form, with the certificate
length `r` free, of the main lemma of [AGL24].

## References

* [Alrabiah, O., Guruswami, V., and Li, R., *Randomly punctured Reed-Solomon codes achieve
    list-decoding capacity over linear-sized fields*][AGL24]
-/

@[expose] public section

namespace ReedSolomon

open Finset MvPolynomial

variable {F : Type*} [Field F] [Fintype F] {n s k r : ℕ} {H : Fin n → Finset (Fin (s + 1))}

open Classical in
/-- **Rank loss from one minor.** If `H` is `k`-weakly partition-connected, the number `N` of
tuples `α : Fin n ↪ F` at which `H` is not rigid for degree `k` satisfies
`N * (Fintype.card F - n + 1) ≤ n * (s * (k - 1)) * Fintype.card (Fin n ↪ F)`. -/
theorem card_filter_not_isRigid_mul_le (hH : IsWeaklyPartitionConnected H k) :
    #{α : Fin n ↪ F | ¬IsRigid H k α} * (Fintype.card F - n + 1) ≤
      n * (s * (k - 1)) * Fintype.card (Fin n ↪ F) := by
  obtain ⟨ρ, hρ⟩ := exists_det_submatrix_ne_zero_of_isWeaklyPartitionConnected F hH
  have hdeg : ((intersectionMatrix F H k).submatrix ρ id).det.totalDegree ≤ n * (s * (k - 1)) := by
    simpa using totalDegree_le_card_mul_of_mem_restrictDegree _ (s * (k - 1))
      ((mem_restrictDegree_iff_degreeOf_le _ _).2 (degreeOf_det_submatrix_le ρ))
  rw [Fintype.card_embedding_eq, Fintype.card_fin]
  refine (Nat.mul_le_mul_right _ (card_le_card_of_injOn (fun α : Fin n ↪ F ↦ ⇑α) (fun α hα ↦ ?_)
    fun α _ β _ h ↦ DFunLike.coe_injective h)).trans
    (((card_filter_injective_eval_eq_zero_le hρ univ).trans
      (Nat.mul_le_mul_right _ hdeg)).trans_eq (by rw [card_univ]))
  refine mem_coe.2 (mem_filter.2 ⟨Fintype.mem_piFinset.2 fun _ ↦ mem_univ _, α.injective, ?_⟩)
  rw [← coe_aeval_eq_eval]
  exact not_not.1 fun h ↦ (mem_filter.1 (mem_coe.1 hα)).2
    ((isRigid_iff_exists_aeval_det_ne_zero (R := F)).2 ⟨ρ, h⟩)

open Classical in
/-- **One certificate.** If `H` is `(k + 2 * r)`-weakly partition-connected, then for every
`c : Fin r ↪ Fin n` the number `N` of tuples `α : Fin n ↪ F` such that `c` is a certificate for
`α` satisfies `N * (Fintype.card F - n + 1) ^ r ≤ (s * (k - 1)) ^ r * Fintype.card (Fin n ↪ F)`. -/
theorem card_filter_isCertificate_mul_pow_le (hH : IsWeaklyPartitionConnected H (k + 2 * r))
    (c : Fin r ↪ Fin n) :
    #{α : Fin n ↪ F | IsCertificate F hH α c} * (Fintype.card F - n + 1) ^ r ≤
      (s * (k - 1)) ^ r * Fintype.card (Fin n ↪ F) := by
  rcases lt_or_ge (Fintype.card F) n with hq | hq
  · have := Function.Embedding.isEmpty_of_card_lt (α := Fin n) (β := F) (by simpa using hq)
    simp
  have hpow : (Fintype.card F - n + 1) ^ r ≤ ∏ i ∈ univ.map c, (#(univ : Finset F) - i) :=
    (pow_card_le_prod (univ.map c) _ (Fintype.card F - n + 1) fun i _ ↦ by
      have := i.isLt
      rw [card_univ]
      omega).trans_eq' (by simp)
  have hdeg : ∏ i ∈ univ.map c, (certificatePolynomial F hH c i).degreeOf i ≤
      (s * (k - 1)) ^ r :=
    (prod_le_pow_card _ _ _ fun i _ ↦ degreeOf_certificatePolynomial_le c i).trans_eq (by simp)
  refine (Nat.mul_le_mul (card_le_card_of_injOn (fun α : Fin n ↪ F ↦ ⇑α) (fun α hα ↦ ?_)
    fun α _ β _ h ↦ DFunLike.coe_injective h) hpow).trans
    ((card_filter_injective_sequential_le univ (univ.map c) (certificatePolynomial F hH c)).trans
      (Nat.mul_le_mul hdeg ?_))
  · refine mem_coe.2 (mem_filter.2 ⟨Fintype.mem_piFinset.2 fun _ ↦ mem_univ _, α.injective,
      fun i hi ↦ ?_⟩)
    obtain ⟨j, -, rfl⟩ := mem_map.1 hi
    rw [certificatePolynomial_apply]
    exact (mem_filter.1 (mem_coe.1 hα)).2 j
  · rw [card_univ, Fintype.card_embedding_eq, Fintype.card_fin]

open Classical in
/-- **Rank loss from certificates.** If `H` is `(k + 2 * r)`-weakly partition-connected, the
number `N` of tuples `α : Fin n ↪ F` at which `H` is not rigid for degree `k` satisfies
`N * (Fintype.card F - n + 1) ^ r ≤
n.choose r * (2 ^ (s + 1)) ^ r * (s * (k - 1)) ^ r * Fintype.card (Fin n ↪ F)`. -/
theorem card_filter_not_isRigid_mul_pow_le (hH : IsWeaklyPartitionConnected H (k + 2 * r)) :
    #{α : Fin n ↪ F | ¬IsRigid H k α} * (Fintype.card F - n + 1) ^ r ≤
      n.choose r * (2 ^ (s + 1)) ^ r * (s * (k - 1)) ^ r * Fintype.card (Fin n ↪ F) := by
  set C : Finset (Fin r ↪ Fin n) := {c | #(Tuple.descents c) < 2 ^ (s + 1)}
  have hsub : ({α : Fin n ↪ F | ¬IsRigid H k α} : Finset _) ⊆
      C.biUnion fun c ↦ {α : Fin n ↪ F | IsCertificate F hH α c} := fun α hα ↦ by
    obtain ⟨c, hc, hcert⟩ :=
      exists_embedding_isCertificate_of_not_isRigid (hH := hH) (mem_filter.1 hα).2
    exact mem_biUnion.2 ⟨c, mem_filter.2 ⟨mem_univ _, hc⟩, mem_filter.2 ⟨mem_univ _, hcert⟩⟩
  have hC : #C ≤ n.choose r * (2 ^ (s + 1)) ^ r := by
    simpa using Tuple.card_filter_card_descents_lt_le (α := Fin n) r (2 ^ (s + 1))
  calc #{α : Fin n ↪ F | ¬IsRigid H k α} * (Fintype.card F - n + 1) ^ r
      ≤ (∑ c ∈ C, #{α : Fin n ↪ F | IsCertificate F hH α c}) * (Fintype.card F - n + 1) ^ r :=
        Nat.mul_le_mul_right _ ((card_le_card hsub).trans card_biUnion_le)
    _ ≤ ∑ _c ∈ C, (s * (k - 1)) ^ r * Fintype.card (Fin n ↪ F) := by
        rw [sum_mul]
        exact sum_le_sum fun c _ ↦ card_filter_isCertificate_mul_pow_le hH c
    _ ≤ n.choose r * (2 ^ (s + 1)) ^ r * ((s * (k - 1)) ^ r * Fintype.card (Fin n ↪ F)) := by
        rw [sum_const, smul_eq_mul]
        exact Nat.mul_le_mul_right _ hC
    _ = _ := by ring

end ReedSolomon
