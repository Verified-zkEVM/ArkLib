/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finiteness

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
- `Polynomial.foldedWronskian_ne_zero_iff_linearIndependent` — GK16 Lemma 12 in full. The two
  directions are also available separately:
  `Polynomial.foldedWronskian_ne_zero_of_linearIndependent` (the direction consumed by T2.18,
  and the only hard one) and `Polynomial.foldedWronskian_eq_zero_of_not_linearIndependent`
  (which needs neither finiteness of `F` nor any hypothesis on `ω` and `k`).

## Contents beyond the folded Wronskian

The file is not homogeneous: besides the folded Wronskian proper it contains two auxiliary
results with no Wronskian content, kept here only because this is currently their sole
consumer. Both are `ArkLib/ToMathlib/` candidates (a move across directories is deliberately
left as a separate change):

- `Matrix.pow_dvd_det_of_forall_mem_col_dvd` — the multiplicity engine, a lemma about
  determinants over an arbitrary `CommRing`: if every entry of each of `t` distinct columns of
  a square matrix is divisible by `d`, then `d ^ t.card ∣ det`. (Replaces GK16's
  Hasse-derivative expansion of `det`; consumed by `CodingTheory.frs_is_subspaceDesign_gk16`
  in `SubspaceDesign.lean`.) Intended home: `ArkLib/ToMathlib/LinearAlgebra/Matrix/`.
- `Polynomial.X_pow_card_sub_one_sub_C_irreducible` — a Kummer-type irreducibility result over
  a finite field: `X^{q−1} − ω` is irreducible for `ω` a generator of `Fˣ`. This is the
  polynomial cutting out the field `F[X]/(E)` in which the criterion is proved, which is the
  only reason it appears here. (Mathlib's Kummer criterion does not cover the even exponent
  `q − 1`, so this is proved from the order of `ω`.) Intended home:
  `ArkLib/ToMathlib/FieldTheory/`.

## References

- [GK16] Guruswami-Kopparty. *Explicit Subspace Designs.* Definition 11, Lemma 12,
  Theorem 14 and Appendix A.
-/

namespace Matrix

/-- **The multiplicity engine.** If every entry of each of the columns indexed by `t` is
divisible by `d`, then `d ^ t.card` divides the determinant.

Nothing here is specific to polynomials; the lemma is stated over an arbitrary `CommRing`
(and used at `R := F[X]`, where it gives root multiplicities of the folded Wronskian without
Hasse-derivative calculus: a block-adapted basis makes `t` whole columns vanish at an
evaluation point `p`, i.e. every entry is divisible by `X − C p`).

TODO: this belongs in `ArkLib/ToMathlib/LinearAlgebra/Matrix/`, and is a clean Mathlib
upstreaming candidate — Mathlib has no divisibility lemma for `Matrix.det` of this shape. It
lives here only because `ArkLib.Data.CodingTheory.SubspaceDesign` is its sole consumer. -/
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

end Matrix

namespace Polynomial

open Matrix

variable {F : Type*} [Field F]

/-- **[GK16, Definition 11].** The `ω`-folded Wronskian of `σ` polynomials: the determinant
of the `σ × σ` matrix with `(i, j)` entry `P j (ω^i X)`. -/
noncomputable def foldedWronskian (σ : ℕ) (ω : F) (P : Fin σ → F[X]) : F[X] :=
  (Matrix.of fun i j : Fin σ => (P j).comp (C (ω ^ (i : ℕ)) * X)).det

/-- Composing with the scaling `X ↦ a • X` never increases `natDegree`: immediate from
Mathlib's `Polynomial.comp_C_mul_X_coeff`, since the `n`-th coefficient is only rescaled.
(For `a ≠ 0` this is in fact an equality, but only the bound is needed here.) -/
lemma natDegree_comp_C_mul_X_le (p : F[X]) (a : F) :
    (p.comp (C a * X)).natDegree ≤ p.natDegree :=
  natDegree_le_iff_coeff_eq_zero.mpr fun _ hm => by
    simp [comp_C_mul_X_coeff, coeff_eq_zero_of_natDegree_lt hm]

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

section Frobenius

variable [Fintype F]

/-- Iterating `FiniteField.expand_card`: over `F = 𝔽_q`, the operator `expand F (q ^ i)` is the
`q ^ i`-th power map on `F[X]`. -/
private lemma expand_card_pow (i : ℕ) (f : F[X]) :
    expand F (Fintype.card F ^ i) f = f ^ (Fintype.card F ^ i) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ, expand_mul, FiniteField.expand_card, map_pow, ih, ← pow_mul]

/-- **Frobenius transport.** Over `F = 𝔽_q`, evaluating an `F`-polynomial at a `q ^ i`-th power
is the `q ^ i`-th power of the evaluation: the coefficient-wise Frobenius is the identity on
`𝔽_q`. -/
private lemma aeval_pow_card_pow {K : Type*} [CommSemiring K] [Algebra F K] (y : K) (f : F[X])
    (i : ℕ) :
    aeval (y ^ (Fintype.card F ^ i)) f = (aeval y f) ^ (Fintype.card F ^ i) := by
  rw [← expand_aeval, expand_card_pow, map_pow]

/-- If `x ^ (q − 1) = ω` in an `F`-algebra, then `x ^ (q ^ i) = ω ^ i · x`: the relation
`x ^ q = ω x` iterated, using `ω ^ q = ω` in `𝔽_q`. -/
private lemma pow_card_pow_eq {K : Type*} [CommRing K] [Algebra F K] {ω : F} {x : K}
    (hx : x ^ (Fintype.card F - 1) = algebraMap F K ω) (i : ℕ) :
    x ^ (Fintype.card F ^ i) = algebraMap F K (ω ^ i) * x := by
  have hcard : Fintype.card F = (Fintype.card F - 1) + 1 :=
    (Nat.succ_pred_eq_of_pos Fintype.card_pos).symm
  have hxq : x ^ Fintype.card F = algebraMap F K ω * x := by
    conv_lhs => rw [hcard]
    rw [pow_succ, hx]
  induction i with
  | zero => simp
  | succ i ih =>
    calc x ^ (Fintype.card F ^ (i + 1))
        = (x ^ (Fintype.card F ^ i)) ^ Fintype.card F := by rw [← pow_mul, ← pow_succ]
      _ = algebraMap F K ((ω ^ i) ^ Fintype.card F) * x ^ Fintype.card F := by
          rw [ih, mul_pow, ← map_pow]
      _ = algebraMap F K (ω ^ i) * (algebraMap F K ω * x) := by rw [FiniteField.pow_card, hxq]
      _ = algebraMap F K (ω ^ (i + 1)) * x := by rw [← mul_assoc, ← map_mul, ← pow_succ]

/-- **The Kummer polynomial of a generator is irreducible.** For `ω` a generator of `Fˣ` over a
finite field `F` with `q` elements, `X ^ (q − 1) − ω` is irreducible; the field `F[X]/(E)` is the
arena of GK16 Lemma 12.

Mathlib's Kummer criterion (`X_pow_sub_C_irreducible_of_odd`) does not apply here, since `q − 1`
is even whenever `q` is odd. We argue directly instead: let `g` be an irreducible factor of `E`
of degree `d`, and `x` the root of `g` in the field `K := F[X]/(g)`, which has `q ^ d` elements.
Then `x ^ (q − 1) = ω`, hence `x ^ (q ^ i) = ω ^ i · x`; at `i = d` the identity `x ^ (q ^ d) = x`
gives `ω ^ d = 1`, so `q − 1 = orderOf ω` divides `d ≤ q − 1`, forcing `d = q − 1`. -/
theorem X_pow_card_sub_one_sub_C_irreducible {ω : F} (hω : orderOf ω = Fintype.card F - 1) :
    Irreducible ((X : F[X]) ^ (Fintype.card F - 1) - C ω) := by
  classical
  have hq2 : 1 < Fintype.card F := Fintype.one_lt_card
  have hq1 : Fintype.card F - 1 ≠ 0 := by omega
  have hEmonic : ((X : F[X]) ^ (Fintype.card F - 1) - C ω).Monic := monic_X_pow_sub_C ω hq1
  have hE0 : ((X : F[X]) ^ (Fintype.card F - 1) - C ω) ≠ 0 := hEmonic.ne_zero
  have hEdeg : ((X : F[X]) ^ (Fintype.card F - 1) - C ω).natDegree = Fintype.card F - 1 :=
    natDegree_X_pow_sub_C
  have hEnu : ¬ IsUnit ((X : F[X]) ^ (Fintype.card F - 1) - C ω) :=
    not_isUnit_of_natDegree_pos _ (by omega)
  obtain ⟨g, hg, hgd⟩ := WfDvdMonoid.exists_irreducible_factor hEnu hE0
  haveI : Fact (Irreducible g) := ⟨hg⟩
  have hd0 : 0 < g.natDegree := hg.natDegree_pos
  have hdle : g.natDegree ≤ Fintype.card F - 1 := hEdeg ▸ natDegree_le_of_dvd hgd hE0
  -- `K := F[X]/(g)` is a finite field with `q ^ d` elements.
  haveI : Module.Finite F (AdjoinRoot g) := PowerBasis.finite (AdjoinRoot.powerBasis hg.ne_zero)
  haveI : Finite (AdjoinRoot g) := Module.finite_of_finite F
  haveI : Fintype (AdjoinRoot g) := Fintype.ofFinite _
  have hcardK : Fintype.card (AdjoinRoot g) = Fintype.card F ^ g.natDegree := by
    rw [Module.card_eq_pow_finrank (K := F)]
    congr 1
    exact ((AdjoinRoot.powerBasis hg.ne_zero).finrank).trans (AdjoinRoot.powerBasis_dim _)
  -- the root of `g` is a root of `E`, i.e. `x ^ (q − 1) = ω`
  have hx : (AdjoinRoot.root g) ^ (Fintype.card F - 1) = algebraMap F (AdjoinRoot g) ω := by
    have h0 : aeval (AdjoinRoot.root g) ((X : F[X]) ^ (Fintype.card F - 1) - C ω) = 0 := by
      rw [AdjoinRoot.aeval_eq]; exact AdjoinRoot.mk_eq_zero.mpr hgd
    simpa [sub_eq_zero] using h0
  have hω0 : ω ≠ 0 := by
    intro h
    have h1 := pow_orderOf_eq_one ω
    rw [hω, h, zero_pow hq1] at h1
    exact zero_ne_one h1
  have hx0 : (AdjoinRoot.root g) ≠ 0 := by
    intro h
    rw [h, zero_pow hq1] at hx
    exact hω0 ((map_eq_zero (algebraMap F (AdjoinRoot g))).mp hx.symm)
  -- `x ^ (q ^ d) = x` (as `|K| = q ^ d`) forces `ω ^ d = 1`
  have hfix : (AdjoinRoot.root g) ^ (Fintype.card F ^ g.natDegree) = AdjoinRoot.root g := by
    rw [← hcardK]; exact FiniteField.pow_card _
  have hωd : ω ^ g.natDegree = 1 := by
    have h1 : algebraMap F (AdjoinRoot g) (ω ^ g.natDegree) * AdjoinRoot.root g
        = algebraMap F (AdjoinRoot g) 1 * AdjoinRoot.root g := by
      rw [map_one, one_mul, ← pow_card_pow_eq hx g.natDegree]
      exact hfix
    exact (algebraMap F (AdjoinRoot g)).injective (mul_right_cancel₀ hx0 h1)
  have hdvd : Fintype.card F - 1 ∣ g.natDegree := hω ▸ orderOf_dvd_of_pow_eq_one hωd
  have hdeq : g.natDegree = Fintype.card F - 1 := le_antisymm hdle (Nat.le_of_dvd hd0 hdvd)
  -- `g` has the full degree of `E`, so the cofactor is a unit and `E` is irreducible
  obtain ⟨h, hh⟩ := hgd
  have hh0 : h ≠ 0 := by rintro rfl; rw [mul_zero] at hh; exact hE0 hh
  have hhdeg : h.natDegree = 0 := by
    have := natDegree_mul hg.ne_zero hh0
    rw [← hh, hEdeg, hdeq] at this
    omega
  have hhu : IsUnit h :=
    isUnit_iff_degree_eq_zero.mpr (by rw [degree_eq_natDegree hh0, hhdeg]; rfl)
  exact (Associated.irreducible ⟨hhu.unit, by rw [IsUnit.unit_spec]; exact hh.symm⟩ hg)

/-- **The engine of GK16 Lemma 12.** Let `K` be a field extension of `F = 𝔽_q` containing an
element `x` with `x ^ (q − 1) = ω`, such that evaluation at `x` is injective on polynomials of
degree `< k`. Then the folded Wronskian matrix of linearly independent `P j ∈ degreeLT F k` has
nonzero determinant.

Proof: pushing the matrix through `p ↦ p(x)` turns the `(i, j)` entry `P j (ω^i X)` into
`(P j (x)) ^ (q ^ i)` (Frobenius, since `x ^ (q ^ i) = ω ^ i · x`), i.e. into a Moore matrix. If
its determinant vanished, a nonzero row-dependency `α` would make the linearized polynomial
`Q(Y) = ∑ αᵢ Y ^ (q ^ i)`, of degree `≤ q ^ (σ − 1)`, vanish on the whole image of the `F`-span
of the `P j` — which has `q ^ σ` elements by independence and injectivity. -/
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
    rw [← pow_card_pow_eq hx i, aeval_pow_card_pow]
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

/-- **[GK16, Lemma 12] — folded Wronskian criterion for linear independence** (the substantial
direction, and the one needed by T2.18). Over a finite field `F` with `ω` a generator of `Fˣ`
and `k ≤ |F| − 1`: linearly independent polynomials of degree `< k` have a nonzero folded
Wronskian. See `foldedWronskian_ne_zero_iff_linearIndependent` for the full biconditional.

Proof route (a streamlining of GK16 Appendix A): work modulo the irreducible
`E := X^{q−1} − ω` (`X_pow_card_sub_one_sub_C_irreducible`) in the field `K := F[X]/(E)`,
where `X^q ≡ ωX` and hence `P(ωⁱX) ≡ P(X)^{qⁱ}` (Frobenius). The folded Wronskian matrix
therefore maps to the Moore matrix of the `βⱼ := Pⱼ(x)`, so a vanishing Wronskian yields a
*nonzero* row dependency `α` over `K` directly — GK16's clearing of denominators over
`F(X)` and stripping of common `E`-factors are not needed. The dependency is the linearized
polynomial `Q(Y) = ∑ αᵢ Y^{qⁱ}` of degree `≤ q^{σ−1}`, which vanishes on the (injective,
as `k ≤ deg E`) image of the whole span — forcing `q^σ = |span| ≤ q^{σ−1}`, absurd. -/
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
  haveI : Fact (Irreducible E) := ⟨hEirr⟩
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

/-- **[GK16, Lemma 12] — the easy direction.** Linearly *dependent* polynomials have a vanishing
folded Wronskian.

This is GK16 Appendix A's opening remark: if `∑ⱼ aⱼ Pⱼ(X) = 0` with `a ≠ 0`, then
`∑ⱼ aⱼ Pⱼ(ωⁱX) = 0` for every `i`, i.e. the constant vector `(C a₀, …, C a_{σ−1})` is a nonzero
element of the kernel of the folded Wronskian matrix over the domain `F[X]`, so its determinant
vanishes.

Unlike the forward direction this needs no finiteness of `F`, no primitivity of `ω`, and no
degree bound on the `P j`. -/
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

/-- **[GK16, Lemma 12] in full.** Over a finite field `F` with `ω` a generator of `Fˣ` and
`k ≤ |F| − 1`, polynomials of degree `< k` are linearly independent over `F` **iff** their
`ω`-folded Wronskian is nonzero.

The forward direction is `foldedWronskian_ne_zero_of_linearIndependent` (the substantial one,
GK16 Appendix A); the converse is `foldedWronskian_eq_zero_of_not_linearIndependent`, which
needs none of `hω`, `hk`, `hdeg` or finiteness of `F`. -/
theorem foldedWronskian_ne_zero_iff_linearIndependent [Fintype F]
    {σ k : ℕ} {ω : F} (hω : orderOf ω = Fintype.card F - 1)
    (hk : k ≤ Fintype.card F - 1)
    (P : Fin σ → F[X]) (hdeg : ∀ j, P j ∈ degreeLT F k) :
    foldedWronskian σ ω P ≠ 0 ↔ LinearIndependent F P := by
  refine ⟨fun h => ?_, foldedWronskian_ne_zero_of_linearIndependent hω hk P hdeg⟩
  by_contra hind
  exact h (foldedWronskian_eq_zero_of_not_linearIndependent σ ω P hind)

end Polynomial
