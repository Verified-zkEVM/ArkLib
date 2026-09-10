/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Isolating a nonsingular zero by a polynomial neighborhood

At a common zero u, write Q_j(X)=Σ_i A_ji(X)(X_i-u_i). Differentiation gives A(u)=Jac_Q(u),
so g=det(A) is nonzero at u when the Jacobian is invertible. Every common zero v in the basic
open g(v)≠0 satisfies A(v)(v-u)=0 and hence v=u. The same argument works after any field extension.

This elementary certificate is the isolation conclusion needed by the sparse root solver. Other
roots and positive-dimensional components may remain outside this neighborhood.
-/

@[expose] public section

namespace MvPolynomial
open scoped BigOperators
variable {F : Type*} [Field F] {s : ℕ}

private theorem sub_eval_mem_coordinateIdeal (u : Fin s → F) (p : MvPolynomial (Fin s) F) :
    p - C (eval u p) ∈ Ideal.span (Set.range fun i => X i - C (u i)) := by
  let I : Ideal (MvPolynomial (Fin s) F) := Ideal.span (Set.range fun i => X i - C (u i))
  change p - C (eval u p) ∈ I
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
      simpa only [map_add, add_sub_add_comm] using I.add_mem hp hq
  | mul_X p i hp =>
      have hx : X i - C (u i) ∈ I := Ideal.subset_span (Set.mem_range_self i)
      have hm := I.add_mem (I.mul_mem_right (X i) hp) (I.mul_mem_left (C (eval u p)) hx)
      convert hm using 1
      simp only [map_mul, eval_X]
      ring

/-- Vanishing at u expresses a polynomial in the coordinate differences X_i-u_i. -/
theorem exists_coordinateFactorization (u : Fin s → F) (p : MvPolynomial (Fin s) F)
    (hp : eval u p = 0) :
    ∃ a : Fin s → MvPolynomial (Fin s) F, ∑ i, a i * (X i - C (u i)) = p := by
  apply Ideal.mem_span_range_iff_exists_fun.mp
  simpa [hp] using sub_eval_mem_coordinateIdeal u p

/-- At u the difference-factor matrix is the Jacobian: all remaining difference terms vanish. -/
theorem coordinateFactorization_derivative (u : Fin s → F) (p : MvPolynomial (Fin s) F)
    (a : Fin s → MvPolynomial (Fin s) F)
    (ha : ∑ j, a j * (X j - C (u j)) = p) (i : Fin s) :
    eval u (pderiv i p) = eval u (a i) := by
  rw [← ha, map_sum]
  simp only [pderiv_mul, map_sub, pderiv_C, sub_zero, map_sum, map_add, map_mul,
    eval_X, eval_C, sub_self, mul_zero]
  simp [pderiv_X, Pi.single_apply, mul_comm]


universe v

/-- An affine basic-open neighborhood contains no other common zero, even after extending the
field. Root membership is a separate premise: this certificate describes the neighborhood. -/
def HasIsolatingPolynomial (equations : Fin s → MvPolynomial (Fin s) F) (u : Fin s → F) : Prop :=
  ∃ g : MvPolynomial (Fin s) F, eval u g ≠ 0 ∧
    ∀ (L : Type v) [Field L] (ι : F →+* L) (point : Fin s → L),
      (∀ j, eval₂ ι point (equations j) = 0) → eval₂ ι point g ≠ 0 →
        point = fun i => ι (u i)

/-- A common zero with invertible Jacobian has a polynomial neighborhood isolating it.
This proves geometric point isolation directly and does not assume that the full zero locus is
finite or that other components are zero-dimensional. -/
theorem hasIsolatingPolynomial_of_jacobian_det_ne_zero
    (equations : Fin s → MvPolynomial (Fin s) F) (u : Fin s → F)
    (hroot : ∀ j, eval u (equations j) = 0)
    (hjac : Matrix.det (fun j i => eval u (pderiv i (equations j))) ≠ 0) :
    HasIsolatingPolynomial.{v, _} equations u := by
  classical
  -- Factor Q_j as Σ_i A_ji(X)(X_i-u_i); differentiating at u identifies A(u) with Jac(u).
  choose A hA using fun j => exists_coordinateFactorization u (equations j) (hroot j)
  have hat : (fun j i => eval u (A j i)) =
      (fun j i => eval u (pderiv i (equations j))) := by
    funext j i
    exact (coordinateFactorization_derivative u (equations j) (A j) (hA j) i).symm
  let M : Matrix (Fin s) (Fin s) (MvPolynomial (Fin s) F) := Matrix.of A
  -- On the basic open det(A)≠0, the root equations force every coordinate difference to zero.
  refine ⟨M.det, ?_, ?_⟩
  · have hmap : eval u M.det = Matrix.det (fun j i => eval u (A j i)) :=
      (eval u).map_det M
    rw [hmap, hat]
    exact hjac
  · intro L _ ι point hpoint hg
    let B : Matrix (Fin s) (Fin s) L := fun j i => eval₂ ι point (A j i)
    have hB : B.det ≠ 0 := by
      have hmap : eval₂ ι point M.det = B.det := (eval₂Hom ι point).map_det M
      rwa [← hmap]
    have hzero : B.mulVec (fun i => point i - ι (u i)) = 0 := by
      funext j
      have heq := congrArg (eval₂Hom ι point) (hA j)
      change (∑ i, eval₂ ι point (A j i) * (point i - ι (u i))) = 0
      calc
        _ = eval₂ ι point (equations j) := by simpa using heq
        _ = 0 := hpoint j
    have hdiff := Matrix.eq_zero_of_mulVec_eq_zero hB hzero
    funext i
    exact sub_eq_zero.mp (congrFun hdiff i)

end MvPolynomial
