/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.Polynomial.Basic

/-!
# The folded Wronskian [GK16, Definition 11]

For polynomials `P 0, …, P (σ−1)` over a field `F` and a folding element `ω : F`, the
`ω`-folded Wronskian is the determinant of the `σ × σ` matrix whose `(i, j)` entry is
`(P j).comp (ω^i • X)`, i.e. `P j (ω^i X)`.

This is the linear-independence certificate driving the folded Reed-Solomon subspace-design
theorem (ABF26 T2.18 / GK16 Theorem 14): for `ω` a generator of `Fˣ` and `deg < k ≤ |F| − 1`,
the folded Wronskian of linearly independent polynomials is a *nonzero* polynomial of degree
`≤ σ(k−1)` (GK16 Lemma 12), while each block of an FRS codeword subspace that vanishes forces
high-multiplicity roots — counting roots against the degree yields the design property.

## Main definitions

- `Polynomial.foldedWronskian` — GK16 Definition 11.

## Main statements

- `Polynomial.natDegree_foldedWronskian_le` — degree bound `σ · k` for entries of degree `≤ k`.
- `Polynomial.pow_dvd_det_of_forall_mem_col_dvd` — the multiplicity engine: if every entry of
  each of `t` distinct columns of a square matrix is divisible by `d`, then `d^t ∣ det`.
  (Replaces GK16's Hasse-derivative expansion of `det` — see the module docstring of
  `SubspaceDesign.lean` once T2.18 is proved.)
- `Polynomial.foldedWronskian_ne_zero_of_linearIndependent` — GK16 Lemma 12 (the criterion;
  currently in progress).

## References

- [GK16] Guruswami-Kopparty. *Explicit Subspace Designs.* Definition 11, Lemma 12,
  Theorem 14 and Appendix A.
-/

namespace Polynomial

open Matrix

variable {F : Type*} [Field F]

/-- **[GK16, Definition 11].** The `ω`-folded Wronskian of `σ` polynomials: the determinant
of the `σ × σ` matrix with `(i, j)` entry `P j (ω^i X)`. -/
noncomputable def foldedWronskian (σ : ℕ) (ω : F) (P : Fin σ → F[X]) : F[X] :=
  (Matrix.of fun i j : Fin σ => (P j).comp (C (ω ^ (i : ℕ)) * X)).det

/-- Entries of the folded Wronskian matrix have the degree of the folded polynomial:
composition with the degree-one polynomial `ω^i X` preserves `natDegree` (for `ω ≠ 0`), and
in general never increases it. -/
lemma natDegree_comp_C_mul_X_le (p : F[X]) (a : F) :
    (p.comp (C a * X)).natDegree ≤ p.natDegree := by
  rw [natDegree_comp]
  calc p.natDegree * (C a * X).natDegree
      ≤ p.natDegree * 1 := by
        refine Nat.mul_le_mul_left _ ?_
        rcases eq_or_ne a 0 with rfl | ha
        · simp
        · rw [natDegree_C_mul ha, natDegree_X]
    _ = p.natDegree := mul_one _

/-- **Degree bound**: if every `P j` has `natDegree ≤ k`, then the folded Wronskian has
`natDegree ≤ σ * k` (Leibniz expansion: each summand is a product of `σ` entries). -/
lemma natDegree_foldedWronskian_le (σ : ℕ) (ω : F) (P : Fin σ → F[X]) (k : ℕ)
    (hP : ∀ j, (P j).natDegree ≤ k) :
    (foldedWronskian σ ω P).natDegree ≤ σ * k := by
  classical
  unfold foldedWronskian
  rw [Matrix.det_apply]
  refine (natDegree_sum_le _ _).trans ?_
  simp only [Finset.fold_max_le]
  refine ⟨Nat.zero_le _, fun g _ => ?_⟩
  refine (natDegree_smul_le _ _).trans ?_
  refine (natDegree_prod_le _ _).trans ?_
  calc ∑ i : Fin σ, ((Matrix.of fun i j : Fin σ =>
          (P j).comp (C (ω ^ (i : ℕ)) * X)) (g i) i).natDegree
      ≤ ∑ _i : Fin σ, k := by
        refine Finset.sum_le_sum fun i _ => ?_
        exact (natDegree_comp_C_mul_X_le _ _).trans (hP i)
    _ = σ * k := by simp [Finset.sum_const]

/-- **The multiplicity engine.** If every entry of each of the columns indexed by `t` is
divisible by `d`, then `d ^ t.card` divides the determinant. This gives root multiplicities
of the folded Wronskian without Hasse-derivative calculus: a block-adapted basis makes `t`
whole columns vanish at an evaluation point `p`, i.e. every entry is divisible by `X − C p`.

Generic in the ring (used at `R := F[X]`). -/
lemma pow_dvd_det_of_forall_mem_col_dvd {R : Type*} [CommRing R] {n : Type*}
    [DecidableEq n] [Fintype n] (M : Matrix n n R) (d : R) (t : Finset n)
    (h : ∀ j ∈ t, ∀ i, d ∣ M i j) :
    d ^ t.card ∣ M.det := by
  classical
  induction t using Finset.induction generalizing M with
  | empty => simp
  | insert j₀ t hj₀ ih =>
    -- Factor `d` out of column `j₀`, then recurse on the remaining columns.
    choose v hv using fun i => h j₀ (Finset.mem_insert_self j₀ t) i
    have hM : M = Matrix.updateCol M j₀ (fun i => d * v i) := by
      ext i j
      by_cases hj : j = j₀
      · subst hj; rw [Matrix.updateCol_apply, if_pos rfl, hv i]
      · rw [Matrix.updateCol_apply, if_neg hj]
    rw [Finset.card_insert_of_notMem hj₀, hM]
    have hsmul : (Matrix.updateCol M j₀ fun i => d * v i)
        = Matrix.updateCol M j₀ (d • v) := by
      congr 1
    rw [hsmul, Matrix.det_updateCol_smul]
    have hrec : d ^ t.card ∣ (Matrix.updateCol M j₀ v).det := by
      refine ih (Matrix.updateCol M j₀ v) fun j hj i => ?_
      have hne : j ≠ j₀ := fun hcontra => hj₀ (hcontra ▸ hj)
      rw [Matrix.updateCol_apply, if_neg hne]
      exact h j (Finset.mem_insert_of_mem hj) i
    rw [pow_succ']
    exact mul_dvd_mul_left d hrec

/-- **[GK16, Lemma 12] — folded Wronskian criterion for linear independence** (the direction
needed by T2.18). Over a finite field `F` with `ω` a generator of `Fˣ` and `k ≤ |F| − 1`:
linearly independent polynomials of degree `< k` have a nonzero folded Wronskian.

Proof route (GK16 Appendix A): if the Wronskian vanishes, its rows admit a polynomial
dependency `∑ᵢ Aᵢ(X) · P(ωⁱX) = 0` with the `Aᵢ` not all divisible by the irreducible
`E := X^{q−1} − ω`. Modulo `E` one has `X^q ≡ ωX`, so `P(ωⁱX) ≡ P(X)^{qⁱ}` (Frobenius),
and the dependency becomes a nonzero linearized polynomial `Q(Y) = ∑ αᵢ Y^{qⁱ}` of degree
`≤ q^{σ−1}` vanishing on the (injective) image of the whole span in the field `F[X]/(E)` —
forcing `|span| ≤ q^{σ−1} < q^σ`, contradicting independence. -/
theorem foldedWronskian_ne_zero_of_linearIndependent [Fintype F] [DecidableEq F]
    {σ k : ℕ} {ω : F} (hω : orderOf ω = Fintype.card F - 1)
    (hk : k ≤ Fintype.card F - 1)
    (P : Fin σ → F[X]) (hdeg : ∀ j, P j ∈ degreeLT F k)
    (hind : LinearIndependent F P) :
    foldedWronskian σ ω P ≠ 0 := by
  sorry -- W2 of the GK16 T2.18 plan (docs/kb/queries/gk16-t218-folded-wronskian-bootstrap.md)

end Polynomial
