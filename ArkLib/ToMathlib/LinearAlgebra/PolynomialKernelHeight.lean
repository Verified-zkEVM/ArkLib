/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.Polynomial.DegreeLT

/-!
# Polynomial kernel vectors of bounded degree

This file proves a sharp degree bound for a nonzero vector in the kernel of a rectangular
polynomial matrix. The proof regards the bounded coefficients of the vector as unknown scalars
and applies finite-dimensional rank-nullity to the resulting coefficient map.

For a matrix with `n` rows and `N` columns whose entries have degree at most `b`, the vector
coordinates can be chosen with degree at most `n * b / (N - n)` whenever `n < N`.
The intrinsic rank version proves the polynomial-kernel height lemma of [DKTZ26].

## References

* [Dao, Q., Kominers, S. D., Thaler, J., Zheng, K. Z., *Reed--Solomon List Decoding and Mutual
  Correlated Agreement up to Capacity*][DKTZ26], Section 5.1, Lemma 5.1.
-/

@[expose] public section

open Polynomial

namespace Matrix

variable {F : Type*} [Field F]

/-- Select actual rows forming a basis of the row space, indexed by the matrix rank. -/
theorem exists_rows_fin_rank {K : Type*} [Field K] {m N : ℕ}
    (A : Matrix (Fin m) (Fin N) K) :
    ∃ rows : Fin A.rank → Fin m,
      LinearIndependent K (fun i ↦ A.row (rows i)) ∧
        Submodule.span K (Set.range fun i ↦ A.row (rows i)) =
          Submodule.span K (Set.range A.row) := by
  classical
  let W := Submodule.span K (Set.range A.row)
  let rowW : Fin m → W := fun i ↦ ⟨A.row i, Submodule.subset_span ⟨i, rfl⟩⟩
  have hspanW : Submodule.span K (Set.range rowW) = ⊤ := by
    apply (Submodule.span_range_subtype_eq_top_iff W _).2
    rfl
  let basisW0 := Module.Basis.ofSpan hspanW.ge
  let basisW := basisW0.reindexRange
  let indexFintype : Fintype (Set.range basisW0) :=
    FiniteDimensional.fintypeBasisIndex basisW
  let _ := indexFintype
  have hb_mem (x : Set.range basisW0) : basisW x ∈ Set.range rowW := by
    rw [show basisW x = (x : W) by exact basisW0.reindexRange_apply x]
    exact Module.Basis.ofSpan_subset hspanW.ge x.property
  let pickRow (x) : Fin m := Classical.choose (hb_mem x)
  have hpick (x) : rowW (pickRow x) = basisW x := Classical.choose_spec (hb_mem x)
  have hfinrankW : Module.finrank K W = A.rank := by
    rw [A.rank_eq_finrank_span_row]
  have hcard : Fintype.card (Set.range basisW0) = A.rank := by
    rw [← Module.finrank_eq_card_basis basisW, hfinrankW]
  let e : Fin A.rank ≃ Set.range basisW0 := (Fintype.equivFinOfCardEq hcard).symm
  let rows : Fin A.rank → Fin m := fun i ↦ pickRow (e i)
  have hrows (i) : A.row (rows i) = basisW (e i) := by
    exact congrArg Subtype.val (hpick (e i))
  refine ⟨rows, ?_, ?_⟩
  · rw [show (fun i ↦ A.row (rows i)) = fun i ↦ (basisW (e i) : Fin N → K) by
      funext i
      exact hrows i]
    exact (basisW.linearIndependent.map' W.subtype W.ker_subtype).comp _ e.injective
  · rw [show (fun i ↦ A.row (rows i)) = fun i ↦ (basisW (e i) : Fin N → K) by
      funext i
      exact hrows i]
    have hrange :
        Set.range (fun i ↦ (basisW (e i) : Fin N → K)) =
          Set.range (fun i ↦ (basisW i : Fin N → K)) := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨e i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨e.symm i, by simp⟩
    rw [hrange]
    change Submodule.span K (Set.range (W.subtype ∘ basisW)) = W
    rw [Set.range_comp, ← Submodule.map_span, basisW.span_eq, Submodule.map_top,
      Submodule.range_subtype]

/-- A polynomial matrix with fewer rows than columns has a nonzero kernel vector whose
coordinate degrees are bounded by the coefficient-counting ratio.

This is the row-count form of the polynomial kernel-height lemma. Replacing `n` by the rank over
the fraction field gives the intrinsic rank form. -/
theorem exists_ne_zero_mulVec_eq_zero_natDegree_le {n N b : ℕ}
    (M : Matrix (Fin n) (Fin N) F[X]) (hdeg : ∀ i j, (M i j).natDegree ≤ b)
    (hN : n < N) :
    ∃ v : Fin N → F[X],
      v ≠ 0 ∧ M *ᵥ v = 0 ∧ ∀ j, (v j).natDegree ≤ n * b / (N - n) := by
  let h := n * b / (N - n)
  let decode : (Fin (h + 1) → F) →ₗ[F] F[X] :=
    (Polynomial.degreeLT F (h + 1)).subtype ∘ₗ
      (Polynomial.degreeLTEquiv F (h + 1)).symm.toLinearMap
  let decodeVec : (Fin N → Fin (h + 1) → F) →ₗ[F] (Fin N → F[X]) :=
    LinearMap.pi fun j ↦ decode ∘ₗ LinearMap.proj j
  let takeCoeffs : (Fin n → F[X]) →ₗ[F] (Fin n → Fin (h + b + 1) → F) :=
    LinearMap.pi fun i ↦ LinearMap.pi fun k ↦
      Polynomial.lcoeff F k ∘ₗ LinearMap.proj i
  let coefficientMap :
      (Fin N → Fin (h + 1) → F) →ₗ[F] (Fin n → Fin (h + b + 1) → F) :=
    takeCoeffs ∘ₗ (M.mulVecLin.restrictScalars F) ∘ₗ decodeVec
  have hden : 0 < N - n := Nat.sub_pos_of_lt hN
  have hcoeff : n * b < (h + 1) * (N - n) := by
    apply (Nat.div_lt_iff_lt_mul hden).mp
    exact Nat.lt_succ_self _
  have hdim :
      Module.finrank F (Fin n → Fin (h + b + 1) → F) <
        Module.finrank F (Fin N → Fin (h + 1) → F) := by
    simp only [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_fin, nsmul_eq_mul,
      Module.finrank_self, mul_one]
    have hsplit : n + (N - n) = N := Nat.add_sub_of_le hN.le
    nlinarith
  have hker : LinearMap.ker coefficientMap ≠ ⊥ :=
    coefficientMap.ker_ne_bot_of_finrank_lt hdim
  obtain ⟨c, hc, hcne⟩ := (LinearMap.ker coefficientMap).ne_bot_iff.mp hker
  let v : Fin N → F[X] := fun j ↦ decode (c j)
  have hvdeg (j : Fin N) : (v j).natDegree ≤ h := by
    apply Polynomial.natDegree_le_of_degree_le
    have hj : decode (c j) ∈ Polynomial.degreeLT F (h + 1) :=
      ((Polynomial.degreeLTEquiv F (h + 1)).symm (c j)).property
    rw [Polynomial.degreeLT_succ_eq_degreeLE] at hj
    exact Polynomial.mem_degreeLE.mp hj
  have hproduct (i : Fin n) (j : Fin N) :
      (M i j * v j).natDegree ≤ h + b := by
    exact (Polynomial.natDegree_mul_le_of_le (hdeg i j) (hvdeg j)).trans_eq (Nat.add_comm b h)
  have hmulVec_degree (i : Fin n) : ((M *ᵥ v) i).natDegree ≤ h + b := by
    change (∑ j, M i j * v j).natDegree ≤ h + b
    exact Polynomial.natDegree_sum_le_of_forall_le Finset.univ _ fun j _ ↦ hproduct i j
  have hmulVec : M *ᵥ v = 0 := by
    funext i
    apply Polynomial.ext
    intro k
    by_cases hk : k < h + b + 1
    · let k' : Fin (h + b + 1) := ⟨k, hk⟩
      have hzero := congrFun (congrFun (LinearMap.mem_ker.mp hc) i) k'
      have hdecodeVec : decodeVec c = v := by
        ext j
        rfl
      simp only [coefficientMap, LinearMap.comp_apply] at hzero
      rw [hdecodeVec] at hzero
      simpa [takeCoeffs, k'] using hzero
    · simp only [Pi.zero_apply, coeff_zero]
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      have hk' : h + b < k := by omega
      exact lt_of_le_of_lt (hmulVec_degree i) hk'
  have hvne : v ≠ 0 := by
    intro hv
    apply hcne
    have hdecode : Function.Injective decode := by
      intro x y hxy
      apply (Polynomial.degreeLTEquiv F (h + 1)).symm.injective
      apply Subtype.ext
      exact hxy
    funext j
    apply hdecode
    simpa [v] using congrFun hv j
  exact ⟨v, hvne, hmulVec, hvdeg⟩

/-- Intrinsic rank form of the polynomial kernel-height lemma. The rank is measured after mapping
the polynomial matrix into the rational function field. -/
theorem exists_ne_zero_mulVec_eq_zero_natDegree_le_of_rank_eq {m N b s : ℕ}
    (M : Matrix (Fin m) (Fin N) F[X]) (hdeg : ∀ i j, (M i j).natDegree ≤ b)
    (hrank : (M.map (algebraMap F[X] (RatFunc F))).rank = s) (hs : s < N) :
    ∃ v : Fin N → F[X],
      v ≠ 0 ∧ M *ᵥ v = 0 ∧ ∀ j, (v j).natDegree ≤ s * b / (N - s) := by
  classical
  let A := M.map (algebraMap F[X] (RatFunc F))
  change A.rank = s at hrank
  subst s
  obtain ⟨rows, _, hspan⟩ := exists_rows_fin_rank A
  let B : Matrix (Fin A.rank) (Fin N) F[X] := M.submatrix rows id
  obtain ⟨v, hvne, hB, hvdeg⟩ :=
    exists_ne_zero_mulVec_eq_zero_natDegree_le B
      (fun i j ↦ by simpa [B] using hdeg (rows i) j) hs
  let w : Fin N → RatFunc F := fun j ↦ algebraMap F[X] (RatFunc F) (v j)
  have hselected (i : Fin A.rank) : dotProduct (A.row (rows i)) w = 0 := by
    have hi := congrFun hB i
    have hi_map := congrArg (algebraMap F[X] (RatFunc F)) hi
    simpa [B, A, w, Matrix.mulVec, dotProduct] using hi_map
  have hA : A *ᵥ w = 0 := by
    funext i
    change dotProduct (A.row i) w = 0
    have hi : A.row i ∈ Submodule.span (RatFunc F)
        (Set.range fun j ↦ A.row (rows j)) := by
      rw [hspan]
      exact Submodule.subset_span ⟨i, rfl⟩
    have hzero_of_mem {x : Fin N → RatFunc F}
        (hx : x ∈ Submodule.span (RatFunc F) (Set.range fun j ↦ A.row (rows j))) :
        dotProduct x w = 0 := by
      induction hx using Submodule.span_induction with
      | mem x hx =>
          obtain ⟨j, rfl⟩ := hx
          exact hselected j
      | zero => simp
      | add x y _ _ hx hy => simp [add_dotProduct, hx, hy]
      | smul a x _ hx => simp [smul_dotProduct, hx]
    exact hzero_of_mem hi
  have hM : M *ᵥ v = 0 := by
    funext i
    apply RatFunc.algebraMap_injective
    have hi := congrFun hA i
    simpa [A, w, Matrix.mulVec, dotProduct] using hi
  exact ⟨v, hvne, hM, hvdeg⟩

end Matrix
