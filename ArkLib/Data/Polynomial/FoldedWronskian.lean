/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ToMathlib.LinearAlgebra.Matrix.Determinant
import ArkLib.ToMathlib.FieldTheory.Kummer
import ArkLib.ToMathlib.Polynomial.CompositionDegree
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finiteness

/-!
# The folded Wronskian

For polynomials `P 0, …, P (σ-1)` over a field `F` and an element `ω : F`, the *`ω`-folded
Wronskian* is the determinant of the `σ × σ` matrix whose `(i, j)` entry is `P j (ω ^ i * X)`.
It plays the role of the classical Wronskian as a linear-independence certificate, with the
substitutions `X ↦ ω ^ i * X` in place of successive derivatives.

## Main definitions

* `Polynomial.foldedWronskian`

## Main statements

* `Polynomial.natDegree_foldedWronskian_le` — the degree bound `σ * k` for entries of degree
  at most `k`.
* `Polynomial.foldedWronskian_ne_zero_iff_linearIndependent` — over a finite field, for `ω` a
  generator of `Fˣ` and `k ≤ |F| - 1`, polynomials of degree `< k` are linearly independent
  iff their folded Wronskian is nonzero. The two directions are also available separately as
  `Polynomial.foldedWronskian_ne_zero_of_linearIndependent` and
  `Polynomial.foldedWronskian_eq_zero_of_not_linearIndependent`, the latter needing neither
  finiteness of `F` nor any hypothesis on `ω` and `k`.

## References

* [Guruswami, V., and Kopparty, S., *Explicit subspace designs*][GK16]
-/
namespace Polynomial

open Matrix

variable {F : Type*} [Field F]

/-- The `ω`-folded Wronskian of `σ` polynomials: the determinant of the `σ × σ` matrix with
`(i, j)` entry `P j (ω ^ i * X)`. -/
noncomputable def foldedWronskian (σ : ℕ) (ω : F) (P : Fin σ → F[X]) : F[X] :=
  (Matrix.of fun i j : Fin σ => (P j).comp (C (ω ^ (i : ℕ)) * X)).det

/-- If every `P j` has degree at most `k`, the folded Wronskian has degree at most `σ * k`:
each summand of the Leibniz expansion is a product of `σ` entries. -/
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

section Frobenius

variable [Fintype F]

/-- Let `K` be a field extension of `F = 𝔽_q` containing an element `x` with
`x ^ (q - 1) = ω`, at which evaluation is injective on polynomials of degree `< k`. Then the
folded Wronskian matrix of linearly independent `P j ∈ degreeLT F k` has nonzero determinant.

Pushing the matrix through `p ↦ p x` turns the `(i, j)` entry `P j (ω ^ i * X)` into
`(P j x) ^ (q ^ i)`, by Frobenius and `x ^ (q ^ i) = ω ^ i * x`, so the image is a Moore
matrix. A vanishing determinant would give a nonzero row dependency `α`, whose linearized
polynomial `Q Y = ∑ αᵢ * Y ^ (q ^ i)` has degree at most `q ^ (σ - 1)` yet vanishes on the
image of the whole `F`-span of the `P j`, a set of `q ^ σ` elements. -/
private lemma foldedWronskian_matrix_det_ne_zero {K : Type*} [Field K] [Algebra F K]
    {σ k : ℕ} {ω : F} {x : K} (hσ : 0 < σ)
    (hx : x ^ (Fintype.card F - 1) = algebraMap F K ω)
    (hxinj : ∀ p ∈ degreeLT F k, aeval x p = 0 → p = 0)
    (P : Fin σ → F[X]) (hdeg : ∀ j, P j ∈ degreeLT F k)
    (hind : LinearIndependent F P) :
    (Matrix.of fun i j : Fin σ => (P j).comp (C (ω ^ (i : ℕ)) * X)).det ≠ 0 := by
  classical
  have hq2 : 1 < Fintype.card F := Fintype.one_lt_card
  intro hdet
  -- Frobenius: evaluation at `x` sends the `(i, j)` entry to `(P j)(x) ^ (q ^ i)`.
  have hentry : ∀ (i : ℕ) (p : F[X]),
      aeval x (p.comp (C (ω ^ i) * X)) = (aeval x p) ^ (Fintype.card F ^ i) := by
    intro i p
    rw [aeval_comp]
    simp only [map_mul, aeval_C, aeval_X]
    rw [← FiniteField.pow_card_pow_eq_mul hx i, aeval_pow_card_pow]
  -- the folded Wronskian matrix becomes the Moore matrix of `β j := (P j)(x)`
  have hdet' : (Matrix.of fun i j : Fin σ =>
      (aeval x (P j)) ^ (Fintype.card F ^ (i : ℕ))).det = 0 := by
    have hmap : (Matrix.of fun i j : Fin σ => (aeval x (P j)) ^ (Fintype.card F ^ (i : ℕ)))
        = ((aeval x : F[X] →ₐ[F] K).toRingHom).mapMatrix
            (Matrix.of fun i j : Fin σ => (P j).comp (C (ω ^ (i : ℕ)) * X)) := by
      ext i j
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [hentry]
    rw [hmap, ← RingHom.map_det, hdet, map_zero]
  obtain ⟨α, hα0, hαv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet'
  have hdep : ∀ j : Fin σ,
      ∑ i : Fin σ, α i * (aeval x (P j)) ^ (Fintype.card F ^ (i : ℕ)) = 0 := by
    intro j
    have h := congrFun hαv j
    simpa [Matrix.vecMul, dotProduct] using h
  -- the dependency extends from the basis to the whole `F`-span
  have hspan : ∀ c : Fin σ → F,
      ∑ i : Fin σ, α i * (aeval x (∑ j, c j • P j)) ^ (Fintype.card F ^ (i : ℕ)) = 0 := by
    intro c
    have step : ∀ i : Fin σ, (aeval x (∑ j, c j • P j)) ^ (Fintype.card F ^ (i : ℕ))
        = ∑ j, c j • ((aeval x (P j)) ^ (Fintype.card F ^ (i : ℕ))) := by
      intro i
      rw [← aeval_pow_card_pow, map_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [map_smul, aeval_pow_card_pow]
    calc ∑ i : Fin σ, α i * (aeval x (∑ j, c j • P j)) ^ (Fintype.card F ^ (i : ℕ))
        = ∑ i : Fin σ, ∑ j : Fin σ,
            c j • (α i * (aeval x (P j)) ^ (Fintype.card F ^ (i : ℕ))) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [step i, Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => mul_smul_comm _ _ _
      _ = ∑ j : Fin σ, ∑ i : Fin σ,
            c j • (α i * (aeval x (P j)) ^ (Fintype.card F ^ (i : ℕ))) := Finset.sum_comm
      _ = 0 := by
          refine Finset.sum_eq_zero fun j _ => ?_
          rw [← Finset.smul_sum, hdep j, smul_zero]
  -- the linearized polynomial `Q`
  obtain ⟨i₀, hi₀⟩ : ∃ i, α i ≠ 0 := Function.ne_iff.mp hα0
  set Q : K[X] := ∑ i : Fin σ, C (α i) * X ^ (Fintype.card F ^ (i : ℕ)) with hQ
  have hQ0 : Q ≠ 0 := by
    intro hzero
    have hcoeff : Q.coeff (Fintype.card F ^ (i₀ : ℕ)) = α i₀ := by
      simp only [hQ, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
      rw [Finset.sum_eq_single i₀]
      · simp
      · intro b _ hb
        have hne : ¬ (Fintype.card F ^ (i₀ : ℕ) = Fintype.card F ^ (b : ℕ)) := fun hc =>
          hb (Fin.val_injective (Nat.pow_right_injective (by omega) hc)).symm
        simp [hne]
      · simp
    rw [hzero, coeff_zero] at hcoeff
    exact hi₀ hcoeff.symm
  have hQdeg : Q.natDegree ≤ Fintype.card F ^ (σ - 1) := by
    rw [hQ]
    refine natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
    refine (natDegree_C_mul_le _ _).trans ?_
    rw [natDegree_X_pow]
    have := i.isLt
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have hQeval : ∀ c : Fin σ → F, Q.eval (aeval x (∑ j, c j • P j)) = 0 := by
    intro c
    rw [hQ]
    simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    exact hspan c
  -- the `q ^ σ` elements of the span inject into the roots of `Q`
  have hinj : ∀ c d : Fin σ → F,
      aeval x (∑ j, c j • P j) = aeval x (∑ j, d j • P j) → c = d := by
    intro c d hcd
    have hsub : (∑ j, (c j - d j) • P j) = (∑ j, c j • P j) - (∑ j, d j • P j) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => sub_smul _ _ _
    have h0 : aeval x (∑ j, (c j - d j) • P j) = 0 := by
      rw [hsub, map_sub, sub_eq_zero]; exact hcd
    have hmem : (∑ j, (c j - d j) • P j) ∈ degreeLT F k :=
      Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hdeg j)
    have hzero := Fintype.linearIndependent_iff.mp hind (fun j => c j - d j) (hxinj _ hmem h0)
    funext j
    exact sub_eq_zero.mp (hzero j)
  have hcount : (Finset.univ : Finset (Fin σ → F)).card ≤ Q.roots.toFinset.card := by
    refine Finset.card_le_card_of_injOn (fun c => aeval x (∑ j, c j • P j))
      (fun c _ => ?_) (fun c _ d _ h => hinj c d h)
    simp only [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hQ0, IsRoot.def]
    exact hQeval c
  have hfinal : Fintype.card F ^ σ ≤ Fintype.card F ^ (σ - 1) :=
    calc Fintype.card F ^ σ = (Finset.univ : Finset (Fin σ → F)).card := by simp
      _ ≤ Q.roots.toFinset.card := hcount
      _ ≤ Multiset.card Q.roots := Multiset.toFinset_card_le _
      _ ≤ Q.natDegree := card_roots' Q
      _ ≤ Fintype.card F ^ (σ - 1) := hQdeg
  have hlt : Fintype.card F ^ (σ - 1) < Fintype.card F ^ σ :=
    Nat.pow_lt_pow_right hq2 (by omega)
  omega

end Frobenius

/-- Over a finite field `F` with `ω` a generator of `Fˣ` and `k ≤ |F| - 1`, linearly
independent polynomials of degree `< k` have a nonzero folded Wronskian.

The proof works in the field `K = F[X]/(E)` for the irreducible `E = X ^ (q-1) - C ω`
(`X_pow_card_sub_one_sub_C_irreducible`), where `X ^ q ≡ ω * X` and hence
`P (ω ^ i * X) ≡ P X ^ (q ^ i)`. Evaluation at the root is injective on `degreeLT F k` since
`k ≤ deg E`, so `foldedWronskian_matrix_det_ne_zero` applies. -/
theorem foldedWronskian_ne_zero_of_linearIndependent [Fintype F]
    {σ k : ℕ} {ω : F} (hω : orderOf ω = Fintype.card F - 1)
    (hk : k ≤ Fintype.card F - 1)
    (P : Fin σ → F[X]) (hdeg : ∀ j, P j ∈ degreeLT F k)
    (hind : LinearIndependent F P) :
    foldedWronskian σ ω P ≠ 0 := by
  classical
  rcases Nat.eq_zero_or_pos σ with rfl | hσ
  · simp [foldedWronskian]
  have hq2 : 1 < Fintype.card F := Fintype.one_lt_card
  -- the arena: the field `K = F[X]/(E)` for the irreducible `E = X ^ (q − 1) − ω`
  set E : F[X] := X ^ (Fintype.card F - 1) - C ω with hE
  have hEirr : Irreducible E := by rw [hE]; exact X_pow_card_sub_one_sub_C_irreducible hω
  have : Fact (Irreducible E) := ⟨hEirr⟩
  -- the root of `E` satisfies `x ^ (q − 1) = ω`
  have h0 : aeval (AdjoinRoot.root E) ((X : F[X]) ^ (Fintype.card F - 1) - C ω) = 0 := by
    rw [← hE, AdjoinRoot.aeval_eq]; exact AdjoinRoot.mk_self
  have hx : (AdjoinRoot.root E) ^ (Fintype.card F - 1) = algebraMap F (AdjoinRoot E) ω := by
    simpa [sub_eq_zero] using h0
  -- evaluation at the root is injective on `degreeLT F k`, as `k ≤ q − 1 = deg E`
  have hxinj : ∀ p ∈ degreeLT F k, aeval (AdjoinRoot.root E) p = 0 → p = 0 := by
    intro p hp hp0
    by_contra hpne
    have hdvd : E ∣ p := AdjoinRoot.mk_eq_zero.mp (by rwa [← AdjoinRoot.aeval_eq])
    have hEd : E.degree = ((Fintype.card F - 1 : ℕ) : WithBot ℕ) := by
      rw [hE]; exact degree_X_pow_sub_C (by omega) ω
    exact hpne (eq_zero_of_dvd_of_degree_lt hdvd
      (hEd ▸ lt_of_lt_of_le (mem_degreeLT.mp hp) (Nat.cast_le.mpr hk)))
  change (Matrix.of fun i j : Fin σ => (P j).comp (C (ω ^ (i : ℕ)) * X)).det ≠ 0
  exact foldedWronskian_matrix_det_ne_zero hσ hx hxinj P hdeg hind

/-- Linearly dependent polynomials have a vanishing folded Wronskian: if `∑ j, a j • P j = 0`
with `a ≠ 0`, then `∑ j, a j • P j (ω ^ i * X) = 0` for every `i`, so the constant vector
`fun j ↦ C (a j)` is a nonzero kernel element of the folded Wronskian matrix over `F[X]`.

This direction needs no finiteness of `F`, no condition on `ω`, and no degree bound. -/
theorem foldedWronskian_eq_zero_of_not_linearIndependent (σ : ℕ) (ω : F) (P : Fin σ → F[X])
    (hind : ¬ LinearIndependent F P) :
    foldedWronskian σ ω P = 0 := by
  classical
  obtain ⟨a, ha, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.mp hind
  refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨fun j => C (a j), ?_, ?_⟩
  · intro h
    exact hi₀ (by simpa using congrFun h i₀)
  · funext i
    have : ∑ j : Fin σ, (P j).comp (C (ω ^ (i : ℕ)) * X) * C (a j)
        = (∑ j : Fin σ, a j • P j).comp (C (ω ^ (i : ℕ)) * X) := by
      rw [sum_comp]
      exact Finset.sum_congr rfl fun j _ => by
        rw [smul_eq_C_mul, mul_comp, C_comp, mul_comm]
    simpa [Matrix.mulVec, dotProduct, ha] using this

/-- Over a finite field `F` with `ω` a generator of `Fˣ` and `k ≤ |F| - 1`, polynomials of
degree `< k` are linearly independent iff their `ω`-folded Wronskian is nonzero. -/
theorem foldedWronskian_ne_zero_iff_linearIndependent [Fintype F]
    {σ k : ℕ} {ω : F} (hω : orderOf ω = Fintype.card F - 1)
    (hk : k ≤ Fintype.card F - 1)
    (P : Fin σ → F[X]) (hdeg : ∀ j, P j ∈ degreeLT F k) :
    foldedWronskian σ ω P ≠ 0 ↔ LinearIndependent F P := by
  refine ⟨fun h => ?_, foldedWronskian_ne_zero_of_linearIndependent hω hk P hdeg⟩
  by_contra hind
  exact h (foldedWronskian_eq_zero_of_not_linearIndependent σ ω P hind)

end Polynomial
