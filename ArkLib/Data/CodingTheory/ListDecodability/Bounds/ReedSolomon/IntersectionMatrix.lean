/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon
public import ArkLib.ToMathlib.LinearAlgebra.Matrix.RowBasis
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# The intersection matrix of a hypergraph

A hypergraph on the vertices `Fin (s + 1)` with edges indexed by `ι` is a family
`H : ι → Finset (Fin (s + 1))`. Its intersection matrix for degree `k` has entries in
`MvPolynomial ι R`, one variable `X i` per edge, and columns `Fin s × Fin k`: column `(j, m)` is
coefficient `m` of vertex `j.castSucc`, and the last vertex has no columns. For each edge `i` and
each vertex `u ∈ H i` other than the least vertex `j₁` of `H i` there is one row, with entry
`X i ^ m` in column `(j, m)` if `j.castSucc = j₁`, entry `-X i ^ m` if `j.castSucc = u`, and `0`
otherwise. This is the reduced intersection matrix of [AGL24].

Evaluated at a point `α : ι → K` of a field, a vector in the kernel is a tuple of polynomials
`f : Fin (s + 1) → K[X]` of degree less than `k` with `f (Fin.last s) = 0` whose values at `α i`
agree on every edge `i`. `IsRigid H k α` says that the only such tuple is zero; by
`isRigid_iff_mulVec_injective` this is full column rank of the evaluated matrix, and by
`isRigid_iff_exists_aeval_det_ne_zero` it is the existence of a maximal minor that does not vanish
at `α`.

## Main definitions

* `IntersectionRow H`: the row indices, pairs `(i, u)` with `u ∈ H i` not the least vertex of
  `H i`.
* `intersectionMatrix R H k`: the matrix described above.
* `IntersectionRow.relabel e he x`: the row `x` with its edge moved along a permutation `e` of the
  edges that preserves edge sets.
* `IsRigid H k α`: the kernel of the matrix evaluated at `α` is trivial, in polynomial form.

## Main statements

* `isRigid_iff_mulVec_injective`: `IsRigid H k α` is injectivity of `mulVec` for the matrix
  evaluated at `α`.
* `isRigid_iff_exists_aeval_det_ne_zero`: `IsRigid H k α` holds exactly when some square
  submatrix with all columns has determinant not vanishing at `α`.
* `not_isRigid_of_mem_code`: Reed–Solomon codewords for the evaluation points `α`, not all equal,
  that agree at every coordinate `i` on the edge `H i` show that `H` is not rigid at `α`.
* `degreeOf_det_submatrix_le`: every square submatrix with all columns has a determinant of degree
  at most `s * (k - 1)` in each variable.
* `intersectionMatrix_apply_of_eq`, `rename_intersectionMatrix_apply`: a row depends only on its
  edge, so emptying edges deletes their rows, and relabelling the variables relabels the rows.
* `det_submatrix_relabel`: permuting edges with equal edge sets maps maximal minors to maximal
  minors, renaming their determinants.

`not_isRigid_of_mem_code` with `isRigid_iff_mulVec_injective` is the lemma of [AGL24] that the
reduced intersection matrix of an agreement hypergraph of codewords that are not all equal does not
have full column rank at the evaluation points. `intersectionMatrix_apply_of_eq` is their
description of row deletion, and `rename_intersectionMatrix_apply` gives their exchangeability of
variables of equal edges.

## References

* [Alrabiah, O., Guruswami, V., and Li, R., *Randomly punctured Reed-Solomon codes achieve
    list-decoding capacity over linear-sized fields*][AGL24]
-/

@[expose] public section

namespace ReedSolomon

open Polynomial Finset
open scoped Matrix

variable {ι : Type*} {s k : ℕ}

/-- The rows of the intersection matrix of `H`: pairs `(i, u)` of an edge `i` and a vertex
`u ∈ H i` other than the least vertex of `H i`. -/
abbrev IntersectionRow (H : ι → Finset (Fin (s + 1))) : Type _ :=
  {p : ι × Fin (s + 1) // p.2 ∈ H p.1 ∧ (H p.1).min ≠ p.2}

/-- The intersection matrix of `H` for degree `k`. The row `(i, u)` has entry `X i ^ m` in column
`(j, m)` if `j.castSucc` is the least vertex of `H i`, entry `-X i ^ m` if `j.castSucc = u`, and
`0` otherwise. -/
noncomputable def intersectionMatrix (R : Type*) [CommRing R] (H : ι → Finset (Fin (s + 1)))
    (k : ℕ) : Matrix (IntersectionRow H) (Fin s × Fin k) (MvPolynomial ι R) :=
  Matrix.of fun r c ↦
    (if (H r.1.1).min = c.1.castSucc then MvPolynomial.X r.1.1 ^ (c.2 : ℕ) else 0) -
      if r.1.2 = c.1.castSucc then MvPolynomial.X r.1.1 ^ (c.2 : ℕ) else 0

/-- `H` is rigid for degree `k` at `α` if every tuple of polynomials of degree less than `k`,
vanishing at the last vertex, whose values at `α i` agree on every edge `H i`, is zero. -/
def IsRigid {K : Type*} [Field K] (H : ι → Finset (Fin (s + 1))) (k : ℕ) (α : ι → K) : Prop :=
  ∀ f : Fin (s + 1) → K[X], (∀ j, f j ∈ degreeLT K k) → f (Fin.last s) = 0 →
    (∀ i, ∀ j ∈ H i, ∀ j' ∈ H i, (f j).eval (α i) = (f j').eval (α i)) → f = 0

variable {R K : Type*} [CommRing R] {H : ι → Finset (Fin (s + 1))}

theorem intersectionMatrix_apply (r : IntersectionRow H) (c : Fin s × Fin k) :
    intersectionMatrix R H k r c =
      (if (H r.1.1).min = c.1.castSucc then MvPolynomial.X r.1.1 ^ (c.2 : ℕ) else 0) -
        if r.1.2 = c.1.castSucc then MvPolynomial.X r.1.1 ^ (c.2 : ℕ) else 0 :=
  rfl

/-- A row of the intersection matrix depends only on its edge: a row of `H'` whose edge is also an
edge of `H` is a row of `H` with the same entries. With `H'` equal to `H` off a set of emptied
edges, the intersection matrix of `H'` is that of `H` with the rows of those edges deleted. -/
theorem intersectionMatrix_apply_of_eq {H' : ι → Finset (Fin (s + 1))} (r : IntersectionRow H')
    (h : H' r.1.1 = H r.1.1) (c : Fin s × Fin k) :
    intersectionMatrix R H' k r c = intersectionMatrix R H k ⟨r.1, h ▸ r.2⟩ c := by
  simp only [intersectionMatrix_apply, h]

/-- Relabelling the variables along `e` maps the row `(i, u)` of the intersection matrix of
`H ∘ e` to the row `(e i, u)` of the intersection matrix of `H`. -/
theorem rename_intersectionMatrix_apply {ι' : Type*} (e : ι → ι') (H : ι' → Finset (Fin (s + 1)))
    (r : IntersectionRow (H ∘ e)) (c : Fin s × Fin k) :
    MvPolynomial.rename e (intersectionMatrix R (H ∘ e) k r c) =
      intersectionMatrix R H k ⟨(e r.1.1, r.1.2), r.2⟩ c := by
  simp only [intersectionMatrix_apply, Function.comp_apply]
  split_ifs <;> simp

/-- The row `(e i, u)` of the intersection matrix, for a row `(i, u)` and a permutation `e` of the
edges with `H (e i) = H i` for all `i`. -/
def IntersectionRow.relabel (e : Equiv.Perm ι) (he : ∀ i, H (e i) = H i)
    (x : IntersectionRow H) : IntersectionRow H :=
  ⟨(e x.1.1, x.1.2), by simpa only [he] using x.2⟩

/-- Relabelling the rows of a square submatrix of the intersection matrix along a permutation `e`
of the edges with `H (e i) = H i` renames its determinant along `e`. -/
theorem det_submatrix_relabel (e : Equiv.Perm ι) (he : ∀ i, H (e i) = H i)
    (ρ : Fin s × Fin k → IntersectionRow H) :
    ((intersectionMatrix R H k).submatrix (fun c ↦ (ρ c).relabel e he) id).det =
      MvPolynomial.rename e ((intersectionMatrix R H k).submatrix ρ id).det := by
  rw [AlgHom.map_det]
  congr 1
  ext c c'
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.submatrix_apply, id,
    intersectionMatrix_apply, IntersectionRow.relabel, he]
  split_ifs <;> simp

section Field

variable [Field K]

/-- The polynomial tuple of a column vector `v`: vertex `j.castSucc` gets
`∑ m, v (j, m) * X ^ m`, and the last vertex gets `0`. -/
private noncomputable def tupleOfVec (v : Fin s × Fin k → K) : Fin (s + 1) → K[X] :=
  Fin.lastCases 0 fun j ↦ ((degreeLTEquiv K k).symm fun m ↦ v (j, m) : K[X])

private theorem tupleOfVec_mem (v : Fin s × Fin k → K) (j : Fin (s + 1)) :
    tupleOfVec v j ∈ degreeLT K k := by
  cases j using Fin.lastCases with
  | last => simp [tupleOfVec]
  | cast j => simp [tupleOfVec]

/-- Summing `v c * a ^ c.2` over the columns `c` of vertex `w` evaluates the polynomial of `v` at
`w`. -/
private theorem sum_ite_eq_eval_tupleOfVec (v : Fin s × Fin k → K) (a : K) (w : Fin (s + 1)) :
    (∑ c : Fin s × Fin k, if w = c.1.castSucc then v c * a ^ (c.2 : ℕ) else 0) =
      (tupleOfVec v w).eval a := by
  rw [Fintype.sum_prod_type]
  cases w using Fin.lastCases with
  | last => simp [tupleOfVec, fun j : Fin s ↦ (Fin.castSucc_lt_last j).ne']
  | cast j =>
    rw [Finset.sum_eq_single j (fun j' _ hj' ↦ by simp [Fin.castSucc_inj, Ne.symm hj'])
      (by simp)]
    simp only [tupleOfVec, Fin.lastCases_castSucc]
    rw [eval_eq_sum_degreeLTEquiv (Submodule.coe_mem _)]
    simp

/-- Row `(i, u)` of the intersection matrix evaluated at `α`, applied to `v`, is the difference of
the values at `α i` of the polynomials of `v` at the least vertex of `H i` and at `u`. -/
private theorem mulVec_map_aeval_apply [Algebra R K] (α : ι → K) (v : Fin s × Fin k → K)
    (r : IntersectionRow H) :
    ((intersectionMatrix R H k).map (MvPolynomial.aeval α) *ᵥ v) r =
      (tupleOfVec v ((H r.1.1).min' ⟨_, r.2.1⟩)).eval (α r.1.1) -
        (tupleOfVec v r.1.2).eval (α r.1.1) := by
  obtain ⟨⟨i, u⟩, hu, -⟩ := r
  rw [← sum_ite_eq_eval_tupleOfVec, ← sum_ite_eq_eval_tupleOfVec, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  have hw : (H i).min = ((H i).min' ⟨u, hu⟩ : WithTop (Fin (s + 1))) := (Finset.coe_min' _).symm
  change MvPolynomial.aeval α (intersectionMatrix R H k _ c) * v c = _
  simp only [intersectionMatrix_apply, hw, WithTop.coe_inj]
  split_ifs <;> simp [mul_comm]

/-- `IsRigid H k α` says that the intersection matrix of `H`, evaluated at `α`, has injective
`mulVec`: it has full column rank. -/
theorem isRigid_iff_mulVec_injective [Algebra R K] {α : ι → K} :
    IsRigid H k α ↔
      Function.Injective ((intersectionMatrix R H k).map (MvPolynomial.aeval α)).mulVec := by
  rw [← Matrix.coe_mulVecLin, injective_iff_map_eq_zero]
  simp only [Matrix.mulVecLin_apply]
  constructor
  · intro h v hv
    have hagree (i : ι) (j : Fin (s + 1)) (hj : j ∈ H i) :
        (tupleOfVec v j).eval (α i) = (tupleOfVec v ((H i).min' ⟨j, hj⟩)).eval (α i) := by
      by_cases hjm : j = (H i).min' ⟨j, hj⟩
      · rw [← hjm]
      have hr : (H i).min ≠ j := by
        rw [← Finset.coe_min' ⟨j, hj⟩]
        exact WithTop.coe_injective.ne (Ne.symm hjm)
      have := congrFun hv ⟨(i, j), hj, hr⟩
      rw [mulVec_map_aeval_apply, Pi.zero_apply, sub_eq_zero] at this
      exact this.symm
    have hf := h (tupleOfVec v) (tupleOfVec_mem v) (by simp [tupleOfVec])
      fun i j hj j' hj' ↦ by rw [hagree i j hj, hagree i j' hj']
    funext c
    have := congrFun hf c.1.castSucc
    simp only [tupleOfVec, Fin.lastCases_castSucc, Pi.zero_apply, Submodule.coe_eq_zero,
      LinearEquiv.map_eq_zero_iff] at this
    exact congrFun this c.2
  · intro h f hdeg hlast hagree
    let v : Fin s × Fin k → K := fun c ↦ degreeLTEquiv K k ⟨f c.1.castSucc, hdeg _⟩ c.2
    have hfv : tupleOfVec v = f := funext fun j ↦ by
      cases j using Fin.lastCases with
      | last => simp [tupleOfVec, hlast]
      | cast j =>
        simp only [tupleOfVec, Fin.lastCases_castSucc]
        change ((degreeLTEquiv K k).symm (degreeLTEquiv K k ⟨f j.castSucc, hdeg _⟩) : K[X]) = _
        rw [LinearEquiv.symm_apply_apply]
    have hv := h v (funext fun r ↦ by
      rw [Pi.zero_apply, mulVec_map_aeval_apply, hfv]
      exact sub_eq_zero.2 (hagree _ _ (Finset.min'_mem _ _) _ r.2.1))
    funext j
    rw [← hfv, hv]
    cases j using Fin.lastCases with
    | last => simp [tupleOfVec]
    | cast j => simp [tupleOfVec, ← Pi.zero_def]

/-- `IsRigid H k α` holds exactly when some square submatrix of the intersection matrix with all
columns has a determinant that does not vanish at `α`. -/
theorem isRigid_iff_exists_aeval_det_ne_zero [Finite ι] [Algebra R K] {α : ι → K} :
    IsRigid H k α ↔ ∃ ρ : Fin s × Fin k → IntersectionRow H,
      MvPolynomial.aeval α ((intersectionMatrix R H k).submatrix ρ id).det ≠ 0 := by
  rw [isRigid_iff_mulVec_injective (R := R),
    Matrix.mulVec_injective_iff_exists_det_submatrix_ne_zero]
  simp only [AlgHom.map_det, AlgHom.mapMatrix_apply, Matrix.submatrix_map]

/-- **Codewords that agree on the edges are not rigid.** If `c j` are Reed–Solomon codewords of
degree `k` for the evaluation points `α`, not all equal, and `c j i = c j' i` whenever `j` and
`j'` lie on the edge `H i`, then `H` is not rigid for degree `k` at `α`. This applies to the
agreement hypergraph `fun i ↦ {j | c j i = y i}` of any word `y`. -/
theorem not_isRigid_of_mem_code {α : ι ↪ K} {c : Fin (s + 1) → ι → K} (hc : ∀ j, c j ∈ code α k)
    (hne : ∃ j j', c j ≠ c j') (hH : ∀ i, ∀ j ∈ H i, ∀ j' ∈ H i, c j i = c j' i) :
    ¬IsRigid H k α := by
  intro hrig
  choose p hp hpe using fun j ↦ mem_code_iff_eval.1 (hc j)
  have h0 := hrig (fun j ↦ p j - p (Fin.last s))
    (fun j ↦ Submodule.sub_mem _ (mem_degreeLT.2 (hp j)) (mem_degreeLT.2 (hp _))) (sub_self _)
    fun i j hj j' hj' ↦ by simp only [eval_sub, hpe, hH i j hj j' hj']
  have hall (j : Fin (s + 1)) : c j = c (Fin.last s) := funext fun x ↦ by
    rw [← hpe, ← hpe, sub_eq_zero.1 (congrFun h0 j)]
  obtain ⟨j, j', hjj'⟩ := hne
  exact hjj' ((hall j).trans (hall j').symm)

end Field

/-- Every square submatrix of the intersection matrix with all columns has a determinant of
degree at most `s * (k - 1)` in each variable: at most `s` of its rows involve `X i`, each in
degree at most `k - 1`. -/
theorem degreeOf_det_submatrix_le (ρ : Fin s × Fin k → IntersectionRow H) (i : ι) :
    ((intersectionMatrix R H k).submatrix ρ id).det.degreeOf i ≤ s * (k - 1) := by
  classical
  by_cases hρ : Function.Injective ρ
  swap
  · obtain ⟨a, b, hab, hne⟩ : ∃ a b, ρ a = ρ b ∧ a ≠ b := by
      simpa [Function.Injective] using hρ
    rw [Matrix.det_zero_of_row_eq hne (funext fun c ↦ by simp [hab])]
    simp
  have hentry (r : IntersectionRow H) (c : Fin s × Fin k) :
      (intersectionMatrix R H k r c).degreeOf i ≤ if r.1.1 = i then k - 1 else 0 := by
    have hX : ((MvPolynomial.X r.1.1 : MvPolynomial ι R) ^ (c.2 : ℕ)).degreeOf i ≤
        if r.1.1 = i then k - 1 else 0 := by
      split_ifs with hri
      · rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.degreeOf_le_iff]
        intro d hd
        rw [Finset.mem_singleton.1 (MvPolynomial.support_monomial_subset hd),
          Finsupp.single_apply]
        split_ifs
        omega
      · rw [MvPolynomial.degreeOf_X_pow_of_ne _ (Ne.symm hri)]
    rw [intersectionMatrix_apply]
    refine (MvPolynomial.degreeOf_sub_le _ _ _).trans (max_le ?_ ?_) <;>
      split_ifs <;> simp_all
  have hcard (σ : Equiv.Perm (Fin s × Fin k)) : #{c | (ρ (σ c)).1.1 = i} ≤ s := by
    rcases Finset.eq_empty_or_nonempty {c | (ρ (σ c)).1.1 = i} with h0 | ⟨c₀, hc₀⟩
    · simp [h0]
    have hne : (H i).Nonempty := ⟨_, (Finset.mem_filter.1 hc₀).2 ▸ (ρ (σ c₀)).2.1⟩
    calc #{c | (ρ (σ c)).1.1 = i}
        ≤ #(univ.erase ((H i).min' hne)) := by
          refine Finset.card_le_card_of_injOn (fun c ↦ (ρ (σ c)).1.2) (fun c hc ↦ ?_)
            fun c hc c' hc' hcc' ↦ ?_
          · have hci := (Finset.mem_filter.1 hc).2
            have hr := (ρ (σ c)).2.2
            rw [hci, ← Finset.coe_min' hne] at hr
            exact Finset.mem_erase.2 ⟨fun h ↦ hr (congrArg _ h.symm), mem_univ _⟩
          · have hci := (Finset.mem_filter.1 (Finset.mem_coe.1 hc)).2
            have hci' := (Finset.mem_filter.1 (Finset.mem_coe.1 hc')).2
            exact σ.injective (hρ (Subtype.ext (Prod.ext (hci.trans hci'.symm) hcc')))
      _ = s := by simp
  rw [Matrix.det_apply]
  refine (MvPolynomial.degreeOf_sum_le _ _ _).trans (Finset.sup_le fun σ _ ↦ ?_)
  have hprod : (∏ c, (intersectionMatrix R H k).submatrix ρ id (σ c) c).degreeOf i ≤
      s * (k - 1) := by
    refine (MvPolynomial.degreeOf_prod_le _ _ _).trans ?_
    refine (Finset.sum_le_sum fun c _ ↦ hentry (ρ (σ c)) c).trans ?_
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
    exact Nat.mul_le_mul_right _ (hcard σ)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
    simpa [h, Units.smul_def, MvPolynomial.degreeOf_neg] using hprod

end ReedSolomon
