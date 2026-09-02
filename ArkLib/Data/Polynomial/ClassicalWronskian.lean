/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ToMathlib.LinearAlgebra.Matrix.Determinant
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.Nat.Factorial.NatCast
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Vandermonde

/-!
# The classical Wronskian

The classical Wronskian of `P 0, …, P (σ - 1)` is the determinant of the matrix whose
`(i, j)` entry is the `i`-th ordinary formal derivative of `P j`. Over a field of
characteristic zero, or of positive characteristic at least the common strict degree bound,
it is nonzero exactly when the polynomials are linearly independent.

The characteristic guard is essential: in characteristic `p`, the nonconstant polynomial
`X ^ p` has zero derivative.

## Main definitions

* `Polynomial.classicalWronskian`

## Main statements

* `Polynomial.natDegree_classicalWronskian_le` — the degree bound `σ * k` for entries of
  degree at most `k`.
* `Polynomial.classicalWronskian_ne_zero_of_natDegree_injective` — nonzero polynomials with
  distinct degrees, all `< k`, have nonzero Wronskian under the guard
  `ringChar F = 0 ∨ k ≤ ringChar F`.
* `Polynomial.classicalWronskian_of_linearComb` — changing the family by a constant
  coefficient matrix `U` multiplies the Wronskian by `C U.det`.
* `Polynomial.classicalWronskian_ne_zero_of_basis` — the same nonvanishing for an arbitrary
  basis of a polynomial subspace in degrees `< k`.

## References

* [Guruswami, V., and Kopparty, S., *Explicit subspace designs*][GK16]
-/

namespace Polynomial

open Module
open Matrix
open scoped Function BigOperators

/-- The classical Wronskian of a finite family of polynomials: the determinant of the matrix
whose `(i, j)` entry is the `i`-th derivative of `P j`. -/
noncomputable def classicalWronskian {F : Type*} [CommRing F]
    (sigma : ℕ) (P : Fin sigma → F[X]) : F[X] :=
  (Matrix.of fun i j : Fin sigma => derivative^[i.val] (P j)).det

/-- A coarse degree bound for the classical Wronskian. -/
lemma natDegree_classicalWronskian_le {F : Type*} [CommRing F]
    (sigma : ℕ) (P : Fin sigma → F[X]) (k : ℕ)
    (hP : ∀ j, (P j).natDegree ≤ k) :
    (classicalWronskian sigma P).natDegree ≤ sigma * k := by
  classical
  unfold classicalWronskian
  rw [Matrix.det_apply]
  refine (natDegree_sum_le _ _).trans ?_
  simp only [Finset.fold_max_le]
  refine ⟨Nat.zero_le _, fun g _ => ?_⟩
  refine (natDegree_smul_le _ _).trans ?_
  refine (natDegree_prod_le _ _).trans ?_
  calc ∑ i : Fin sigma, ((Matrix.of fun i j : Fin sigma =>
          derivative^[i.val] (P j)) (g i) i).natDegree
      ≤ ∑ _i : Fin sigma, k := by
        refine Finset.sum_le_sum fun i _ => ?_
        exact (natDegree_iterate_derivative _ _).trans
          ((Nat.sub_le _ _).trans (hP i))
    _ = sigma * k := by simp [Finset.sum_const]

private lemma isUnit_natCast_descFactorial {F : Type*} [Field F]
    {d i k : ℕ} (hi : i ≤ d) (hd : d < k)
    (hk : ringChar F = 0 ∨ k ≤ ringChar F) :
    IsUnit (d.descFactorial i : F) := by
  have hfac : IsUnit (d.factorial : F) := by
    rcases hk with hk0 | hkpos
    · let : CharZero F := (CharP.ringChar_zero_iff_CharZero F).mp hk0
      exact IsUnit.natCast_factorial_of_algebra F d
    · let : NeZero (ringChar F) :=
        ⟨Nat.ne_zero_of_lt ((Nat.zero_le d).trans_lt (hd.trans_le hkpos))⟩
      let : Fact (ringChar F).Prime := CharP.char_is_prime_of_pos F _
      exact (IsUnit.natCast_factorial_iff_of_charP (ringChar F)).2 (hd.trans_le hkpos)
  have hmul : IsUnit (((d - i).factorial : F) * (d.descFactorial i : F)) := by
    rw [← Nat.cast_mul, Nat.factorial_mul_descFactorial hi]
    exact hfac
  exact (IsUnit.mul_iff.mp hmul).2

private lemma natDegree_iterate_derivative_eq {F : Type*} [Field F]
    {p : F[X]} (hp : p ≠ 0) {i k : ℕ} (hi : i ≤ p.natDegree)
    (hdeg : p.natDegree < k) (hk : ringChar F = 0 ∨ k ≤ ringChar F) :
    (derivative^[i] p).natDegree = p.natDegree - i := by
  apply le_antisymm (natDegree_iterate_derivative p i)
  apply le_of_not_gt
  intro hlt
  have hcoeff := coeff_eq_zero_of_natDegree_lt hlt
  rw [coeff_iterate_derivative] at hcoeff
  have hadd : p.natDegree - i + i = p.natDegree := Nat.sub_add_cancel hi
  rw [hadd, coeff_natDegree, nsmul_eq_mul] at hcoeff
  exact (mul_ne_zero
    (isUnit_natCast_descFactorial hi hdeg hk).ne_zero
    (leadingCoeff_ne_zero.mpr hp)) hcoeff

private lemma leadingCoeff_iterate_derivative {F : Type*} [Field F]
    {p : F[X]} (hp : p ≠ 0) {i k : ℕ} (hi : i ≤ p.natDegree)
    (hdeg : p.natDegree < k) (hk : ringChar F = 0 ∨ k ≤ ringChar F) :
    (derivative^[i] p).leadingCoeff =
      (p.natDegree.descFactorial i : F) * p.leadingCoeff := by
  rw [leadingCoeff, natDegree_iterate_derivative_eq hp hi hdeg hk,
    coeff_iterate_derivative, Nat.sub_add_cancel hi, nsmul_eq_mul, coeff_natDegree]

/-- The classical Wronskian of nonzero polynomials with pairwise distinct degrees is nonzero
in characteristic zero, and remains so in positive characteristic when their common strict
degree bound is no greater than the characteristic. -/
theorem classicalWronskian_ne_zero_of_natDegree_injective
    {F : Type*} [Field F] {sigma k : ℕ}
    (P : Fin sigma → F[X]) (hP0 : ∀ j, P j ≠ 0)
    (hPdeg : ∀ j, (P j).natDegree < k)
    (hPinj : Function.Injective (fun j => (P j).natDegree))
    (hk : ringChar F = 0 ∨ k ≤ ringChar F) : classicalWronskian sigma P ≠ 0 := by
  classical
  let d : Fin sigma → ℕ := fun j => (P j).natDegree
  let D : ℕ := (∑ j, d j) - ∑ i : Fin sigma, i.val
  let A : Matrix (Fin sigma) (Fin sigma) F :=
    Matrix.of fun i j => (d j).descFactorial i.val
  have hcastinj : Function.Injective (fun j => (d j : F)) := by
    intro i j hij
    apply hPinj
    rcases hk with hk0 | hkpos
    · let : CharZero F := (CharP.ringChar_zero_iff_CharZero F).mp hk0
      exact Nat.cast_injective hij
    · exact CharP.natCast_injOn_Iio F (ringChar F)
        ((hPdeg i).trans_le hkpos) ((hPdeg j).trans_le hkpos) hij
  have hAdet : A.det ≠ 0 := by
    have hv := (Matrix.det_vandermonde_ne_zero_iff (R := F)
      (v := fun j => (d j : F))).2 hcastinj
    have heval := Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde
      (v := fun j => (d j : F)) (p := fun i : Fin sigma => descPochhammer F i.val)
      (fun i => descPochhammer_natDegree F i.val)
      (fun i => monic_descPochhammer F i.val)
    have heq : (Matrix.vandermonde (fun j => (d j : F))).det = A.det := by
      rw [heval]
      rw [← Matrix.det_transpose]
      congr 1
      ext i j
      simp [A, d, descPochhammer_eval_eq_descFactorial]
    rwa [heq] at hv
  let L : Fin sigma → F := fun j => (P j).leadingCoeff
  have hL : ∀ j, L j ≠ 0 := fun j => leadingCoeff_ne_zero.mpr (hP0 j)
  let B : Matrix (Fin sigma) (Fin sigma) F :=
    Matrix.of fun i j => (d j).descFactorial i.val * L j
  have hBdet : B.det ≠ 0 := by
    have hBA : B = A * Matrix.diagonal L := by
      ext i j
      simp [B, A]
    rw [hBA, Matrix.det_mul, Matrix.det_diagonal]
    exact mul_ne_zero hAdet (Finset.prod_ne_zero_iff.mpr fun j _ => hL j)
  apply fun hW => hBdet ?_
  have hcoeff : (classicalWronskian sigma P).coeff D = B.det := by
    unfold classicalWronskian
    rw [Matrix.det_apply', Polynomial.finsetSum_coeff, Matrix.det_apply']
    apply Finset.sum_congr rfl
    intro g hg
    simp only [Matrix.of_apply]
    simp only [coeff_intCast_mul, mul_eq_mul_left_iff]
    apply Or.inl
    by_cases hall : ∀ j : Fin sigma, (g j).val ≤ d j
    · have hder0 : ∀ j : Fin sigma, derivative^[((g j).val)] (P j) ≠ 0 := by
        intro j hzero
        have hlc := leadingCoeff_iterate_derivative (hP0 j) (hall j) (hPdeg j) hk
        rw [hzero, leadingCoeff_zero] at hlc
        exact (mul_ne_zero
          (isUnit_natCast_descFactorial (hall j) (hPdeg j) hk).ne_zero
          (leadingCoeff_ne_zero.mpr (hP0 j))) (by simpa [d] using hlc.symm)
      have hD : (∑ j, (d j - (g j).val)) = D := by
        simp only [D]
        rw [Finset.sum_tsub_distrib Finset.univ (fun j _ => hall j)]
        congr 1
        exact Equiv.sum_comp g (fun i : Fin sigma => i.val)
      have hproddeg : (∏ j : Fin sigma, derivative^[((g j).val)] (P j)).natDegree = D := by
        rw [natDegree_prod Finset.univ _ (fun j _ => hder0 j)]
        simp_rw [natDegree_iterate_derivative_eq (hP0 _) (hall _) (hPdeg _) hk]
        exact hD
      rw [← hproddeg, coeff_natDegree, leadingCoeff_prod]
      simp only [B, Matrix.of_apply]
      apply Finset.prod_congr rfl
      intro j hj
      rw [leadingCoeff_iterate_derivative (hP0 j) (hall j) (hPdeg j) hk]
    · simp only [not_forall, not_le] at hall
      obtain ⟨j, hj⟩ := hall
      have hzero : derivative^[((g j).val)] (P j) = 0 :=
        iterate_derivative_eq_zero hj
      rw [Finset.prod_eq_zero (Finset.mem_univ j) hzero, coeff_zero]
      simp only [B, Matrix.of_apply]
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      change ((d j).descFactorial (g j).val : F) * L j = 0
      rw [Nat.descFactorial_eq_zero_iff_lt.mpr hj, Nat.cast_zero, zero_mul]
  rw [hW, coeff_zero] at hcoeff
  exact hcoeff.symm

private theorem exists_basis_natDegree_injective_aux
    {F M : Type*} [Field F] [AddCommGroup M] [Module F M]
    [FiniteDimensional F M] (e : M →ₗ[F] F[X]) (he : Function.Injective e)
    (k : ℕ) (hdeg : ∀ x, x ≠ 0 → (e x).natDegree < k) :
    ∃ b : Basis (Fin (finrank F M)) F M,
      Function.Injective (fun i => (e (b i)).natDegree) := by
  induction k generalizing M with
  | zero =>
      have hM : ∀ x : M, x = 0 := by
        intro x
        by_contra hx
        exact (Nat.not_lt_zero _ (hdeg x hx))
      have hrank : finrank F M = 0 :=
        Module.finrank_zero_iff.mpr ⟨fun x y => (hM x).trans (hM y).symm⟩
      let b := Module.finBasis F M
      refine ⟨b, ?_⟩
      intro i j hij
      exact Fin.elim0 (Fin.cast hrank i)
  | succ k ih =>
      let f : M →ₗ[F] F := (lcoeff F k).comp e
      by_cases hf : f = 0
      · have hdeg' : ∀ x, x ≠ 0 → (e x).natDegree < k := by
          intro x hx
          have hle : (e x).natDegree ≤ k := Nat.lt_succ_iff.mp (hdeg x hx)
          apply lt_of_le_of_ne hle
          intro heq
          have hcoeff : (e x).coeff k = 0 := by
            have := LinearMap.congr_fun hf x
            simpa [f, lcoeff_apply] using this
          have hex : e x ≠ 0 := fun h => hx (he (h.trans (map_zero e).symm))
          rw [← heq, coeff_natDegree, leadingCoeff_eq_zero] at hcoeff
          exact hex hcoeff
        exact ih e he hdeg'
      · have hdegKer : ∀ x : LinearMap.ker f, x ≠ 0 →
            (e.comp (LinearMap.ker f).subtype x).natDegree < k := by
          intro x hx
          have hxM : (x : M) ≠ 0 := fun h => hx (Subtype.ext h)
          have hle : (e x).natDegree ≤ k := Nat.lt_succ_iff.mp (hdeg x hxM)
          apply lt_of_le_of_ne hle
          intro heq
          have hcoeff : (e x).coeff k = 0 := by
            have hxker : f (x : M) = 0 := LinearMap.mem_ker.mp x.2
            change (lcoeff F k) (e x) = 0 at hxker
            change (e x).coeff k = 0
            simpa only [lcoeff_apply] using hxker
          have hex : e x ≠ 0 := fun h => hxM (he (h.trans (map_zero e).symm))
          rw [← heq, coeff_natDegree, leadingCoeff_eq_zero] at hcoeff
          exact hex hcoeff
        have heKer : Function.Injective (e.comp (LinearMap.ker f).subtype) :=
          he.comp (LinearMap.ker f).subtype_injective
        obtain ⟨b, hb⟩ := ih (e.comp (LinearMap.ker f).subtype) heKer hdegKer
        obtain ⟨y, hy⟩ : ∃ y : M, f y ≠ 0 := by
          simpa [LinearMap.ext_iff] using hf
        have hli : ∀ (c : F), ∀ x ∈ LinearMap.ker f, c • y + x = 0 → c = 0 := by
          intro c x hxN hzero
          have hfx : f x = 0 := LinearMap.mem_ker.mp hxN
          have hmap : f (c • y + x) = f 0 := congr_arg f hzero
          rw [map_add, map_smul, map_zero, hfx, add_zero] at hmap
          have hmul : c * f y = 0 := by simpa [smul_eq_mul] using hmap
          exact (mul_eq_zero.mp hmul).resolve_right hy
        have hsp : ∀ z : M, ∃ c : F, z + c • y ∈ LinearMap.ker f := by
          intro z
          refine ⟨-(f z / f y), ?_⟩
          simp only [LinearMap.mem_ker, map_add, map_smul]
          simp [smul_eq_mul, hy]
        let b' : Basis (Fin (finrank F (LinearMap.ker f) + 1)) F M :=
          Basis.mkFinSnoc b y hli hsp
        have hrank : finrank F (LinearMap.ker f) + 1 = finrank F M :=
          Module.Dual.finrank_ker_add_one_of_ne_zero hf
        let b'' : Basis (Fin (finrank F M)) F M := b'.reindex (finCongr hrank)
        refine ⟨b'', ?_⟩
        have hydeg : (e y).natDegree = k := by
          have hy0 : y ≠ 0 := by
            intro h
            apply hy
            rw [h, map_zero]
          apply le_antisymm (Nat.lt_succ_iff.mp (hdeg y hy0))
          apply le_of_not_gt
          intro hlt
          have : (e y).coeff k = 0 := coeff_eq_zero_of_natDegree_lt hlt
          exact hy (by simpa [f, lcoeff_apply] using this)
        have hsmall : ∀ i, (e ((b i : LinearMap.ker f) : M)).natDegree < k := by
          intro i
          exact hdegKer (b i) (b.ne_zero i)
        have hsnoc : Function.Injective
            (fun i : Fin (finrank F (LinearMap.ker f) + 1) => (e (b' i)).natDegree) := by
          have hb' : (b' : Fin (_ + 1) → M) = Fin.snoc ((↑) ∘ b) y := by
            simp [b']
          rw [show (fun i => (e (b' i)).natDegree) =
              Fin.snoc (fun i => (e ((b i : LinearMap.ker f) : M)).natDegree) k from by
            funext i
            rw [hb']
            refine Fin.lastCases ?_ (fun j => ?_) i
            · simp [hydeg]
            · simp]
          rw [Fin.snoc_injective_iff]
          refine ⟨hb, ?_⟩
          rintro ⟨i, hi⟩
          exact (Nat.ne_of_lt (hsmall i)) hi
        simp only [b'', Basis.reindex_apply]
        exact hsnoc.comp (finCongr hrank).symm.injective

/-- Replacing the polynomials by constant linear combinations right-multiplies the
Wronskian matrix by the coefficient matrix. -/
lemma classicalWronskian_of_linearComb {F : Type*} [Field F] {sigma : ℕ}
    (P c : Fin sigma → F[X]) (U : Matrix (Fin sigma) (Fin sigma) F)
    (hc : ∀ j, c j = ∑ i, U i j • P i) :
    classicalWronskian sigma c =
      classicalWronskian sigma P * C U.det := by
  classical
  have hM : (Matrix.of fun i j : Fin sigma => derivative^[i.val] (c j))
      = (Matrix.of fun i j : Fin sigma => derivative^[i.val] (P j)) *
        ((C : F →+* F[X]).mapMatrix U) := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.of_apply, Matrix.mul_apply, RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [hc j, iterate_derivative_sum]
    exact Finset.sum_congr rfl fun i' _ => by
      rw [iterate_derivative_smul]
      simp [smul_eq_C_mul, mul_comm]
  unfold classicalWronskian
  rw [hM, Matrix.det_mul, ← RingHom.map_det]

/-- If a finite-dimensional polynomial subspace has a basis of polynomials of degree `< k`,
its classical Wronskian is nonzero in characteristic zero, and in positive characteristic at
least `k`.

The proof changes to a basis in degree-echelon form, where the top-degree coefficient of the
Wronskian is a nonzero Vandermonde determinant; changing back multiplies the Wronskian by a
nonzero constant. -/
theorem classicalWronskian_ne_zero_of_basis {F : Type*} [Field F] {sigma k : ℕ}
    {B : Submodule F F[X]} (bas : Basis (Fin sigma) F B)
    (hdeg : ∀ j, ((bas j : B) : F[X]).natDegree < k)
    (hk : ringChar F = 0 ∨ k ≤ ringChar F) :
    classicalWronskian sigma (fun j => ((bas j : B) : F[X])) ≠ 0 := by
  classical
  let : Module.Finite F B := Module.Finite.of_basis bas
  have hrank : finrank F B = sigma := by
    rw [Module.finrank_eq_card_basis bas, Fintype.card_fin]
  have hbound : ∀ x : B, x ≠ 0 → (B.subtype x).natDegree < k := by
    intro x hx
    have hmem : B.subtype x ∈ degreeLT F k := by
      rw [← bas.sum_repr x]
      rw [map_sum]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (by
        rw [mem_degreeLT, degree_eq_natDegree, Nat.cast_lt]
        · exact hdeg j
        · exact fun h => bas.ne_zero j (Subtype.ext h))
    rw [mem_degreeLT, degree_eq_natDegree, Nat.cast_lt] at hmem
    · exact hmem
    · exact fun h => hx (B.subtype_injective (h.trans (map_zero B.subtype).symm))
  obtain ⟨cb₀, hcb₀⟩ :=
    exists_basis_natDegree_injective_aux B.subtype B.subtype_injective k hbound
  let cb : Basis (Fin sigma) F B := cb₀.reindex (finCongr hrank)
  have hcbinj : Function.Injective
      (fun j => (((cb j : B) : F[X])).natDegree) := by
    simp only [cb, Basis.reindex_apply]
    exact hcb₀.comp (finCongr hrank).symm.injective
  have hcbdeg : ∀ j, (((cb j : B) : F[X])).natDegree < k := fun j =>
    hbound (cb j) (cb.ne_zero j)
  have hcbW : classicalWronskian sigma (fun j => ((cb j : B) : F[X])) ≠ 0 :=
    classicalWronskian_ne_zero_of_natDegree_injective _
      (fun j => fun h => cb.ne_zero j (Subtype.ext h)) hcbdeg hcbinj hk
  let U : Matrix (Fin sigma) (Fin sigma) F := bas.toMatrix (⇑cb)
  have hcomb : ∀ j, ((cb j : B) : F[X]) =
      ∑ i, U i j • ((bas i : B) : F[X]) := by
    intro j
    have h1 : ∑ i, U i j • bas i = cb j :=
      Module.Basis.sum_toMatrix_smul_self bas (⇑cb) j
    have h2 : B.subtype (∑ i, U i j • bas i) = B.subtype (cb j) := by rw [h1]
    rw [map_sum] at h2
    simp only [map_smul, Submodule.coe_subtype] at h2
    exact h2.symm
  have hdetU : U.det ≠ 0 := by
    have h := congrArg Matrix.det (Module.Basis.toMatrix_mul_toMatrix_flip bas cb)
    rw [Matrix.det_mul, Matrix.det_one] at h
    intro h0
    rw [h0, zero_mul] at h
    exact zero_ne_one h
  have hW := classicalWronskian_of_linearComb
    (fun j => ((bas j : B) : F[X])) (fun j => ((cb j : B) : F[X])) U hcomb
  intro hzero
  rw [hzero, zero_mul] at hW
  exact hcbW hW

end Polynomial
