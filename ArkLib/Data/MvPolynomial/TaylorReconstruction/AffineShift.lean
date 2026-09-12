/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.MvPolynomial.BoxTruncation
public import CompPoly.Multivariate.Operations
public import CompPoly.Multivariate.Rename
public import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# Division-free parameter shifts

Sparse substitution computes translation over an arbitrary commutative ring. No
factorials or inverses occur, so polynomial degrees may reach the characteristic.
-/

@[expose] public section

namespace CPoly.TaylorReconstruction

variable {r : ℕ} {R : Type*} [CommRing R] [BEq R] [LawfulBEq R]

/-- Translate every parameter by its supplied center using stored sparse substitution. -/
def shift (a : Fin r → R) (p : CMvPolynomial r R) : CMvPolynomial r R :=
  CMvPolynomial.bind₁ (fun i => CMvPolynomial.X i + CMvPolynomial.C (a i)) p

/-- Shift and keep the canonical coordinatewise box representative. -/
def shiftToBox (N : ℕ) (a : Fin r → R) (p : CMvPolynomial r R) :
    CMvPolynomial r R := BoxTruncation.truncate N (shift a p)

/-- Translation leaves scalar polynomials fixed. -/
@[simp] theorem shift_C (a : Fin r → R) (c : R) :
    shift a (CMvPolynomial.C c) = CMvPolynomial.C c := by
  simp [shift]

/-- Translation distributes over addition. -/
@[simp] theorem shift_add (a : Fin r → R) (p q : CMvPolynomial r R) :
    shift a (p + q) = shift a p + shift a q := by
  simp [shift]

/-- Translation distributes over multiplication. -/
@[simp] theorem shift_mul (a : Fin r → R) (p q : CMvPolynomial r R) :
    shift a (p * q) = shift a p * shift a q := by
  simp [shift]

/-- Translation sends each coordinate to its affine expression. -/
@[simp] theorem shift_X (a : Fin r → R) (i : Fin r) :
    shift a (CMvPolynomial.X i) = CMvPolynomial.X i + CMvPolynomial.C (a i) := by
  simp [shift]

/-- Sparse polynomials inherit the constant/addition/variable induction principle. -/
private theorem polynomial_induction (P : CMvPolynomial r R → Prop)
    (hC : ∀ c, P (CMvPolynomial.C c))
    (hadd : ∀ p q, P p → P q → P (p + q))
    (hX : ∀ p i, P p → P (p * CMvPolynomial.X i)) (p : CMvPolynomial r R) : P p := by
  have hc (c : R) : polyRingEquiv.symm (MvPolynomial.C c) = CMvPolynomial.C (n := r) c := by
    apply polyRingEquiv.injective
    rw [RingEquiv.apply_symm_apply]
    exact (CMvPolynomial.fromCMvPolynomial_C (n := r) c).symm
  have hx (i : Fin r) : polyRingEquiv.symm (MvPolynomial.X i) = CMvPolynomial.X (R := R) i := by
    apply polyRingEquiv.injective
    rw [RingEquiv.apply_symm_apply]
    exact (CPoly.fromCMvPolynomial_X (R := R) i).symm
  have h : ∀ q : MvPolynomial (Fin r) R, P (polyRingEquiv.symm q) := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C c => simpa [hc] using hC c
    | add q t hq ht => simpa using hadd _ _ hq ht
    | mul_X q i hq => simpa [hx] using hX _ i hq
  simpa using h (polyRingEquiv p)

/-- Opposite translations cancel over any commutative ring, in every characteristic. -/
@[simp] theorem shift_neg_shift (a : Fin r → R) (p : CMvPolynomial r R) :
    shift (fun i => -a i) (shift a p) = p := by
  apply polynomial_induction (fun p => shift (fun i => -a i) (shift a p) = p)
  · intro c
    simp
  · intro p q hp hq
    simp [hp, hq]
  · intro p i hp
    simp only [shift_mul, shift_X, shift_add, shift_C, hp]
    congr 1
    apply eq_iff_fromCMvPolynomial.mpr
    simp [CPoly.map_add, CMvPolynomial.fromCMvPolynomial_C,
      CPoly.fromCMvPolynomial_X, add_assoc]

/-- The computed affine translation is injective without a degree restriction. -/
theorem shift_injective (a : Fin r → R) : Function.Injective (shift a) := by
  intro p q h
  have := congrArg (shift (fun i => -a i)) h
  simpa using this

/-- The sparse shift refines ordinary substitution of affine parameter expressions. -/
theorem shift_semantics (a : Fin r → R) (p : CMvPolynomial r R) :
    fromCMvPolynomial (shift a p) =
      MvPolynomial.eval₂ MvPolynomial.C
        (fun i => MvPolynomial.X i + MvPolynomial.C (a i)) (fromCMvPolynomial p) := by
  apply polynomial_induction (fun p => fromCMvPolynomial (shift a p) =
    MvPolynomial.eval₂ MvPolynomial.C
      (fun i => MvPolynomial.X i + MvPolynomial.C (a i)) (fromCMvPolynomial p))
  · intro c
    simp [CMvPolynomial.fromCMvPolynomial_C]
  · intro p q hp hq
    simp [CPoly.map_add, MvPolynomial.eval₂_add, hp, hq]
  · intro p i hp
    simp [CPoly.map_mul, CPoly.map_add, CPoly.fromCMvPolynomial_X,
      CMvPolynomial.fromCMvPolynomial_C, MvPolynomial.eval₂_mul, hp]

/-- Affine parameter substitution cannot increase total degree. -/
theorem totalDegree_shift_le [Nontrivial R] (a : Fin r → R) (p : CMvPolynomial r R) :
    (fromCMvPolynomial (shift a p)).totalDegree ≤ (fromCMvPolynomial p).totalDegree := by
  rw [shift_semantics, MvPolynomial.eval₂_eq]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro d hd
  apply le_trans (MvPolynomial.totalDegree_mul _ _)
  simp only [MvPolynomial.totalDegree_C, zero_add]
  apply le_trans (MvPolynomial.totalDegree_finsetProd _ _)
  apply le_trans _ (MvPolynomial.le_totalDegree hd)
  apply Finset.sum_le_sum
  intro i _
  apply le_trans (MvPolynomial.totalDegree_pow _ _)
  have hi : (MvPolynomial.X i + MvPolynomial.C (a i) :
      MvPolynomial (Fin r) R).totalDegree ≤ 1 := by
    simpa using MvPolynomial.totalDegree_add (MvPolynomial.X i)
      (MvPolynomial.C (a i))
  simpa using Nat.mul_le_mul_left (d i) hi

/-- A polynomial already below the total-degree precision loses no box coefficients. -/
theorem truncate_eq_self_of_totalDegree_lt (N : ℕ) (p : CMvPolynomial r R)
    (hp : (fromCMvPolynomial p).totalDegree < N) : BoxTruncation.truncate N p = p := by
  apply eq_iff_fromCMvPolynomial.mpr
  apply MvPolynomial.ext
  intro m
  rw [BoxTruncation.coeff_semantics]
  split_ifs with hm
  · rfl
  · symm
    apply MvPolynomial.notMem_support_iff.mp
    intro hs
    apply hm
    intro i
    exact lt_of_le_of_lt
      ((MvPolynomial.le_degreeOf_of_mem_support i hs).trans
        (MvPolynomial.degreeOf_le_totalDegree _ i)) hp

/-- Box truncation is injective on polynomials with the stated total-degree bound. -/
theorem truncate_injective_of_totalDegree_le (N L : ℕ) (hNL : L < N)
    (p q : CMvPolynomial r R)
    (hp : (fromCMvPolynomial p).totalDegree ≤ L)
    (hq : (fromCMvPolynomial q).totalDegree ≤ L)
    (h : BoxTruncation.truncate N p = BoxTruncation.truncate N q) : p = q := by
  rwa [truncate_eq_self_of_totalDegree_lt N p (hp.trans_lt hNL),
    truncate_eq_self_of_totalDegree_lt N q (hq.trans_lt hNL)] at h

/-- Opposite shifting recovers a degree-bounded polynomial from its local box. -/
theorem recover_shiftToBox [Nontrivial R] (N L : ℕ) (hNL : L < N)
    (a : Fin r → R) (p : CMvPolynomial r R)
    (hp : (fromCMvPolynomial p).totalDegree ≤ L) :
    shift (fun i => -a i) (shiftToBox N a p) = p := by
  rw [shiftToBox, truncate_eq_self_of_totalDegree_lt N (shift a p)
    ((totalDegree_shift_le a p).trans_lt (hp.trans_lt hNL)), shift_neg_shift]

/-- Truncated affine shifts distinguish every polynomial of total degree at most `L<N`. -/
theorem shiftToBox_injective_of_totalDegree_le [Nontrivial R]
    (N L : ℕ) (hNL : L < N) (a : Fin r → R) (p q : CMvPolynomial r R)
    (hp : (fromCMvPolynomial p).totalDegree ≤ L)
    (hq : (fromCMvPolynomial q).totalDegree ≤ L)
    (h : shiftToBox N a p = shiftToBox N a q) : p = q := by
  have he := congrArg (shift (fun i => -a i)) h
  simpa [recover_shiftToBox N L hNL a p hp, recover_shiftToBox N L hNL a q hq] using he

end CPoly.TaylorReconstruction
