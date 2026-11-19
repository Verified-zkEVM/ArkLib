/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import ArkLib.Data.CodingTheory.ListDecodability.Bounds.ReedSolomon.IntersectionMatrix
public import ArkLib.Data.CodingTheory.ListDecodability.PartitionConnected
public import ArkLib.Data.CodingTheory.ReedSolomon.Dual
public import ArkLib.ToMathlib.Combinatorics.Hypergraph.GenericZeroPattern
public import ArkLib.ToMathlib.RingTheory.Polynomial.GenericZeroPattern
public import Mathlib.FieldTheory.RatFunc.Basic

/-!
# Full column rank of intersection matrices and generic Reed–Solomon codes

Let `H : ι → Finset (Fin (s + 1))` be a `k`-weakly partition-connected hypergraph. Then the
intersection matrix `intersectionMatrix F H k` over `MvPolynomial ι F` has a maximal minor that is
a nonzero polynomial: it has full column rank over the field of rational functions.

The proof finds a point of rigidity over an infinite field `K`. The nonempty edges give a generic
zero pattern (`IsWeaklyPartitionConnected.exists_isGenericZeroPattern`), and the generic zero
pattern gives pairwise distinct points `a i` and a basis `g ℓ` of the polynomials of degree less
than `N - k`, `N` the number of nonempty edges, with `g ℓ` vanishing at `a i` whenever the vertex
of `ℓ` is not on the edge `i`. For a tuple `f` of polynomials of degree less than `k` that agree on
every edge, the common values `y i` on the edges are orthogonal to the dual code
(`ReedSolomon.mem_code_iff_forall_dotProduct_eq_zero`), so `y` is a Reed–Solomon codeword of some
`Y`; every vertex lies on at least `k` edges, so `f j = Y` for every `j`, and `f = 0` since the
last polynomial is `0`. Over `K = RatFunc F` this gives a maximal minor of the intersection matrix
not vanishing at a point, hence nonzero.

For finitely many hypergraphs at once, the product of these minors does not vanish at some point
with pairwise distinct coordinates. Together with
`Code.exists_isWeaklyPartitionConnected_agreement_of_lt_Lambda` and `not_isRigid_of_mem_code` this
gives, for each `0 < ℓ`, evaluation points over any infinite field at which the Reed–Solomon code
of dimension `k` has lists of size at most `ℓ` at relative radius `ℓ / (ℓ + 1) * (1 - k / n)`,
the generalized Singleton bound.

## Main statements

* `exists_isRigid_of_isWeaklyPartitionConnected`: over an infinite field, a `k`-weakly
  partition-connected hypergraph is rigid for degree `k` at some point.
* `exists_det_submatrix_ne_zero_of_isWeaklyPartitionConnected`: its intersection matrix has a
  nonzero maximal minor.
* `exists_det_submatrix_ne_zero_of_card_le`: a `(k + b)`-weakly partition-connected hypergraph
  has a nonzero maximal minor whose rows avoid any given `b` edges.
* `exists_embedding_Lambda_le`: over an infinite field, for `0 < ℓ` there are evaluation points at
  which the Reed–Solomon code of dimension `k` satisfies `Lambda ≤ ℓ` at relative radius
  `ℓ / (ℓ + 1) * (1 - k / n)`.

`exists_det_submatrix_ne_zero_of_isWeaklyPartitionConnected` is the theorem of [AGL24] that the
reduced intersection matrix of a `k`-weakly partition-connected hypergraph has full column rank,
with the proof of [AGL24] through generic zero patterns. `exists_embedding_Lambda_le` is the
list-size form of the theorem of [BGM23] that generic Reed–Solomon codes are list-decodable up to
the generalized Singleton bound, for evaluation points in an infinite field. It is not the
average-radius form that [BGM23] proves, and it gives no bound on the size of a finite field with
such points.

## References

* [Alrabiah, O., Guruswami, V., and Li, R., *Randomly punctured Reed-Solomon codes achieve
    list-decoding capacity over linear-sized fields*][AGL24]
* [Brakensiek, J., Gopi, S., and Makam, V., *Generic Reed-Solomon codes achieve list-decoding
    capacity*][BGM23]
-/

@[expose] public section

namespace ReedSolomon

open Polynomial Finset Code

variable {ι : Type*} [Fintype ι] {s k : ℕ}

/-- `m` linearly independent polynomials of degree less than `m` span the polynomials of degree
less than `m`. -/
private theorem span_range_eq_degreeLT {K : Type*} [Field K] {m : ℕ} {g : Fin m → K[X]}
    (hg : ∀ ℓ, g ℓ ∈ degreeLT K m) (hli : LinearIndependent K g) :
    Submodule.span K (Set.range g) = degreeLT K m := by
  have : FiniteDimensional K (degreeLT K m) := (degreeLTEquiv K m).symm.finiteDimensional
  refine Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.2 (Set.range_subset_iff.2 hg)) ?_
  rw [finrank_span_eq_card hli, Fintype.card_fin, (degreeLTEquiv K m).finrank_eq,
    Module.finrank_fin_fun]

/-- **Rigidity at a point.** Over an infinite field `K`, a `k`-weakly partition-connected
hypergraph `H` is rigid for degree `k` at some point `α : ι → K`. -/
theorem exists_isRigid_of_isWeaklyPartitionConnected (K : Type*) [Field K] [Infinite K]
    {H : ι → Finset (Fin (s + 1))} (h : IsWeaklyPartitionConnected H k) :
    ∃ α : ι → K, IsRigid H k α := by
  classical
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · refine ⟨0, fun f _ hlast _ ↦ funext fun j ↦ ?_⟩
    obtain rfl : j = Fin.last 0 := Fin.ext (by simp)
    rw [hlast, Pi.zero_apply]
  have : Nontrivial (Fin (s + 1)) := Fin.nontrivial_iff_two_le.2 (by omega)
  have h' : IsWeaklyPartitionConnected (fun i : {i // (H i).Nonempty} ↦ H i) k :=
    (isWeaklyPartitionConnected_restrict_edges_iff fun i hi ↦ by
      simp [Finset.not_nonempty_iff_eq_empty.1 hi]).2 h
  obtain ⟨v, hv⟩ := h'.exists_isGenericZeroPattern fun i ↦ i.2
  obtain ⟨a, g, hgdeg, hgv, hgli⟩ :=
    Polynomial.exists_embedding_linearIndependent_of_isGenericZeroPattern (K := K) hv
  refine ⟨fun i ↦ if hi : (H i).Nonempty then a ⟨i, hi⟩ else 0, fun f hdeg hlast hagree ↦ ?_⟩
  set y : {i // (H i).Nonempty} → K := fun i ↦ (f ((H i).min' i.2)).eval (a i)
  have hy (i : {i // (H i).Nonempty}) (j : Fin (s + 1)) (hj : j ∈ H i) :
      (f j).eval (a i) = y i := by
    have := hagree i j hj _ ((H i).min'_mem i.2)
    simpa only [i.2, ↓reduceDIte, Subtype.coe_eta] using this
  have hycode : y ∈ code a k := by
    rw [mem_code_iff_forall_dotProduct_eq_zero]
    intro p hp
    rw [← span_range_eq_degreeLT hgdeg hgli] at hp
    induction hp using Submodule.span_induction with
    | mem p hp =>
      obtain ⟨ℓ, rfl⟩ := hp
      have hc : (fun i ↦ (f (v ℓ)).eval (a i)) ∈ code a k :=
        mem_code_iff_eval.2 ⟨_, mem_degreeLT.1 (hdeg _), fun _ ↦ rfl⟩
      rw [← dotProduct_eq_zero_of_mem_code a hc (hgdeg ℓ)]
      simp only [dotProduct]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      by_cases hj : v ℓ ∈ H i
      · rw [hy i _ hj]
      · rw [hgv ℓ i (by simp [hj]), mul_zero, zero_mul, zero_mul]
    | zero => simp [dotProduct]
    | add p q _ _ hp hq =>
      simp only [dotProduct, eval_add, mul_add, add_mul, Finset.sum_add_distrib] at hp hq ⊢
      rw [hp, hq, add_zero]
    | smul c p _ hp =>
      simp only [dotProduct, eval_smul, smul_eq_mul] at hp ⊢
      rw [← mul_zero c, ← hp, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
  obtain ⟨Y, hY, hYy⟩ := mem_code_iff_eval.1 hycode
  have hfY (j : Fin (s + 1)) : f j = Y := by
    have hk : k ≤ #{i : {i // (H i).Nonempty} | j ∈ H i} := by
      exact_mod_cast h'.le_card_filter_mem j
    refine eq_of_degree_sub_lt_of_eval_finset_eq
      (s := ({i : {i // (H i).Nonempty} | j ∈ H i} : Finset _).map a) ?_ fun x hx ↦ ?_
    · rw [card_map]
      exact (degree_sub_le _ _).trans_lt
        ((max_lt (mem_degreeLT.1 (hdeg j)) hY).trans_le (by exact_mod_cast hk))
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_map.1 hx
      rw [hy i j (Finset.mem_filter.1 hi).2, hYy]
  have hY0 := hfY (Fin.last s)
  rw [hlast] at hY0
  funext j
  rw [hfY j, ← hY0, Pi.zero_apply]

/-- **Full column rank** ([AGL24]). The intersection matrix over `MvPolynomial ι F` of a
`k`-weakly partition-connected hypergraph `H` has a square submatrix with all columns whose
determinant is a nonzero polynomial. -/
theorem exists_det_submatrix_ne_zero_of_isWeaklyPartitionConnected (F : Type*) [Field F]
    {H : ι → Finset (Fin (s + 1))} (h : IsWeaklyPartitionConnected H k) :
    ∃ ρ : Fin s × Fin k → IntersectionRow H,
      ((intersectionMatrix F H k).submatrix ρ id).det ≠ 0 := by
  have : Infinite (RatFunc F) := Infinite.of_injective _ (RatFunc.algebraMap_injective F)
  obtain ⟨α, hα⟩ := exists_isRigid_of_isWeaklyPartitionConnected (RatFunc F) h
  obtain ⟨ρ, hρ⟩ := (isRigid_iff_exists_aeval_det_ne_zero (R := F)).1 hα
  exact ⟨ρ, fun h0 ↦ hρ (by rw [h0, map_zero])⟩

/-- **Robustness to deletions.** A `(k + b)`-weakly partition-connected hypergraph `H` has a
square submatrix of its intersection matrix over `MvPolynomial ι F` with all columns, whose rows
avoid a given set `D` of at most `b` edges, and whose determinant is a nonzero polynomial. -/
theorem exists_det_submatrix_ne_zero_of_card_le (F : Type*) [Field F]
    {H : ι → Finset (Fin (s + 1))} {b : ℝ} (h : IsWeaklyPartitionConnected H (k + b))
    {D : Finset ι} (hD : (#D : ℝ) ≤ b) :
    ∃ ρ : Fin s × Fin k → IntersectionRow H, (∀ c, (ρ c).1.1 ∉ D) ∧
      ((intersectionMatrix F H k).submatrix ρ id).det ≠ 0 := by
  classical
  obtain ⟨ρ, hρ⟩ := exists_det_submatrix_ne_zero_of_isWeaklyPartitionConnected F (h.delete hD)
  have hD' (r : IntersectionRow fun i ↦ if i ∈ D then ∅ else H i) : r.1.1 ∉ D := fun hr ↦ by
    simpa [hr] using r.2.1
  have hH (r : IntersectionRow fun i ↦ if i ∈ D then ∅ else H i) :
      (if r.1.1 ∈ D then ∅ else H r.1.1) = H r.1.1 := by simp [hD' r]
  refine ⟨fun c ↦ ⟨(ρ c).1, hH (ρ c) ▸ (ρ c).2⟩, fun c ↦ hD' (ρ c), ?_⟩
  convert hρ using 2
  exact Matrix.ext fun c c' ↦ (intersectionMatrix_apply_of_eq (ρ c) (hH (ρ c)) c').symm

/-- **Generic points are rigid.** Over an infinite field `K` there are pairwise distinct points
`α : ι ↪ K` at which every `k`-weakly partition-connected hypergraph on `s + 1 ≤ ℓ + 1` vertices
is rigid for degree `k`. -/
private theorem exists_embedding_forall_isRigid (K : Type*) [Field K] [Infinite K] (k ℓ : ℕ) :
    ∃ α : ι ↪ K, ∀ s ≤ ℓ, ∀ H : ι → Finset (Fin (s + 1)),
      IsWeaklyPartitionConnected H k → IsRigid H k α := by
  classical
  let T := Σ s : Fin (ℓ + 1), {H : ι → Finset (Fin (s + 1)) // IsWeaklyPartitionConnected H k}
  choose ρ hρ using fun t : T ↦
    exists_det_submatrix_ne_zero_of_isWeaklyPartitionConnected K t.2.2
  obtain ⟨x, hx, hpx⟩ := MvPolynomial.exists_injective_eval_ne_zero
    (Finset.prod_ne_zero_iff.2 fun t (_ : t ∈ univ) ↦ hρ t)
  refine ⟨⟨x, hx⟩, fun s hs H hH ↦ ?_⟩
  rw [isRigid_iff_exists_aeval_det_ne_zero (R := K)]
  refine ⟨ρ ⟨⟨s, by omega⟩, H, hH⟩, ?_⟩
  rw [map_prod] at hpx
  exact Finset.prod_ne_zero_iff.1 hpx ⟨⟨s, by omega⟩, H, hH⟩ (mem_univ _)

/-- **Generic Reed–Solomon codes reach the generalized Singleton bound** ([BGM23]). Over an
infinite field `K`, for `0 < ℓ` there are evaluation points `α : ι ↪ K` at which the Reed–Solomon
code of dimension `k` has lists of size at most `ℓ` at relative radius
`ℓ / (ℓ + 1) * (1 - k / n)`, where `n = Fintype.card ι`. -/
theorem exists_embedding_Lambda_le (K : Type*) [Field K] [Infinite K] (k : ℕ) {ℓ : ℕ}
    (hℓ : 0 < ℓ) :
    ∃ α : ι ↪ K, Lambda (code α k : Set (ι → K))
      ((ℓ : ℝ) / (ℓ + 1) * (1 - (k : ℝ) / Fintype.card ι)) ≤ ℓ := by
  classical
  obtain ⟨α, hα⟩ := exists_embedding_forall_isRigid (ι := ι) K k ℓ
  refine ⟨α, not_lt.1 fun hlt ↦ ?_⟩
  obtain ⟨y, s, hs1, hsℓ, c, hc, hwpc⟩ :=
    exists_isWeaklyPartitionConnected_agreement_of_lt_Lambda hℓ hlt
  refine not_isRigid_of_mem_code (c := ⇑c) (fun j ↦ (mem_closeCodewordsRel_iff.1 (hc j)).1)
    ⟨0, Fin.last s, c.injective.ne
      (Fin.ext_iff.not.2 (by simp only [Fin.val_zero, Fin.val_last]; omega))⟩
    (fun i j hj j' hj' ↦ ?_) (hα s hsℓ _ hwpc)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj hj'
  exact hj.trans hj'.symm

end ReedSolomon
