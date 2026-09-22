/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.RingTheory.Nullstellensatz.PrincipalOpenParametrization
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Acceptance tests for principal open subsets covered by parametrizations

These examples use the public API through an ordinary import. Over `ℚ`, with points in the
algebraic closure `K` of `ℚ`, the parabola `y = x²` is covered by `t ↦ (t, t²)`, so its ideal has
dimension at most `1`; any ideal containing `x` and `y` is covered by the empty parametrization,
so it has dimension `0`. The boundary examples show that regularity of `s` is needed in the
principal-open Nullstellensatz and that positive dimension is needed for the vanishing statement.
The last examples derive the source's graph statements on `Option σ`, including the second
conjunct `aeval w s ≠ 0`.
-/

open MvPolynomial

namespace PrincipalOpenParametrizationTest

local notation "𝕂" => AlgebraicClosure ℚ

/-- The coordinate ring `ℚ[x, y]` of the plane. -/
local notation "R₂" => MvPolynomial (Fin 2) ℚ

/-- The class of `1` is regular modulo every ideal. -/
theorem isLeftRegular_mk_one {R : Type*} [CommRing R] (I : Ideal R) :
    IsLeftRegular (Ideal.Quotient.mk I 1) := by
  rw [map_one]
  exact isRegular_one.left

/-- Modulo a prime `P`, the class of every `s ∉ P` is regular, since the quotient is a domain.
This is how the source's hypotheses `P.IsPrime` and `s ∉ P` give the regularity hypothesis. -/
theorem isLeftRegular_mk_of_isPrime {R : Type*} [CommRing R] {P : Ideal R} (hP : P.IsPrime)
    {s : R} (hs : s ∉ P) : IsLeftRegular (Ideal.Quotient.mk P s) :=
  IsLeftCancelMulZero.mul_left_cancel_of_ne_zero fun h ↦ hs (Ideal.Quotient.eq_zero_iff_mem.mp h)

/-- The parabola `y = x²` over `ℚ` has dimension at most `1`: every point over `K` is
`(t, t²)` for `t = x`. -/
example : (affineHilbertPolynomial (Ideal.span {(X 1 - X 0 ^ 2 : R₂)})).natDegree ≤ 1 := by
  refine natDegree_affineHilbertPolynomial_le_one_of_principalOpen_subset_range (K := 𝕂)
    (isLeftRegular_mk_one _) ![Polynomial.X, Polynomial.X ^ 2] fun x hx _ ↦ ⟨x 0, ?_⟩
  have h := (mem_zeroLocus_iff.mp hx) _ (Ideal.mem_span_singleton_self _)
  simp only [map_sub, map_pow, aeval_X, sub_eq_zero] at h
  funext i
  fin_cases i <;> simp [h]

/-- An ideal of `ℚ[x, y]` containing `x` and `y` has dimension `0`. Its zero locus over `K` is
at most the origin, which is the image of the empty parametrization `τ = Empty`. -/
theorem natDegree_affineHilbertPolynomial_eq_zero_of_X_mem {J : Ideal R₂} (h0 : X 0 ∈ J)
    (h1 : X 1 ∈ J) : (affineHilbertPolynomial J).natDegree = 0 := by
  have h := natDegree_affineHilbertPolynomial_le_of_principalOpen_subset_range (K := 𝕂)
    (τ := Empty) (isLeftRegular_mk_one J) (fun _ ↦ 0) fun x hx _ ↦ ⟨isEmptyElim, ?_⟩
  · simpa using h
  funext i
  have hi : aeval x (X i : R₂) = 0 := (mem_zeroLocus_iff.mp hx) _ (by fin_cases i <;> assumption)
  simpa using hi

/-- Regularity of `s` is needed in `mem_radical_of_forall_principalOpen`. For `I = (xy)` and
`s = x`, the class of `x` is a zero divisor, the polynomial `y` vanishes wherever `xy = 0` and
`x ≠ 0`, but `y` is not in the radical of `(xy)`, since `(xy)` vanishes at `(0, 1)` and `y` does
not. -/
example :
    (∀ x : Fin 2 → 𝕂, x ∈ zeroLocus 𝕂 (Ideal.span {(X 0 * X 1 : R₂)}) →
      aeval x (X 0 : R₂) ≠ 0 → aeval x (X 1 : R₂) = 0) ∧
    (X 1 : R₂) ∉ (Ideal.span {(X 0 * X 1 : R₂)}).radical := by
  refine ⟨fun x hx hs ↦ ?_, fun hmem ↦ ?_⟩
  · have h := (mem_zeroLocus_iff.mp hx) _ (Ideal.mem_span_singleton_self _)
    simp only [map_mul, aeval_X] at h hs ⊢
    exact (mul_eq_zero.mp h).resolve_left hs
  · let e : R₂ →+* ℚ := eval ![0, 1]
    have hle : (Ideal.span {(X 0 * X 1 : R₂)}).radical ≤ RingHom.ker e :=
      (Ideal.IsPrime.radical_le_iff (RingHom.ker_isPrime e)).mpr
        ((Ideal.span_singleton_le_iff_mem _).mpr (by simp [e]))
    have := RingHom.mem_ker.mp (hle hmem)
    simp [e] at this

/-- Positive dimension is needed in `aeval_eq_zero_of_principalOpen_subset_range`. For the
point `I = (x)` on the line over `K`, `s = 1` and `w = X`, the set `U(I) = {0}` is covered and
`p = x` vanishes on it, but `aeval w p = X ≠ 0`. -/
example :
    (∀ x : Unit → 𝕂, x ∈ zeroLocus 𝕂 (Ideal.span {(X () : MvPolynomial Unit 𝕂)}) →
      aeval x (1 : MvPolynomial Unit 𝕂) ≠ 0 → ∃ z : 𝕂, x = fun _ ↦ (Polynomial.X.eval z : 𝕂)) ∧
    (∀ x : Unit → 𝕂, x ∈ zeroLocus 𝕂 (Ideal.span {(X () : MvPolynomial Unit 𝕂)}) →
      aeval x (1 : MvPolynomial Unit 𝕂) ≠ 0 → aeval x (X () : MvPolynomial Unit 𝕂) = 0) ∧
    aeval (fun _ : Unit ↦ (Polynomial.X : Polynomial 𝕂)) (X () : MvPolynomial Unit 𝕂) ≠ 0 := by
  have hzero : ∀ x : Unit → 𝕂, x ∈ zeroLocus 𝕂 (Ideal.span {(X () : MvPolynomial Unit 𝕂)}) →
      aeval x (X () : MvPolynomial Unit 𝕂) = 0 := fun x hx ↦
    (mem_zeroLocus_iff.mp hx) _ (Ideal.mem_span_singleton_self _)
  refine ⟨fun x hx _ ↦ ⟨x (), ?_⟩, fun x hx _ ↦ hzero x hx, by simp⟩
  funext i
  simp

/-! ### Source-shaped statements -/

section Source

variable {F σ : Type*} [Field F]

/-- The source's `eval_polynomialGraphPullback`, with the graph pullback written as `aeval` of
`Option.elim · X w` and the graph point written out. -/
theorem source_eval_polynomialGraphPullback (w : σ → Polynomial F) (z : F)
    (p : MvPolynomial (Option σ) F) :
    (aeval (fun i : Option σ ↦ i.elim Polynomial.X w) p).eval z =
      aeval (fun i : Option σ ↦ i.elim z fun j ↦ (w j).eval z) p := by
  rw [polynomial_eval_aeval]
  change eval _ p = eval _ p
  congr 2
  funext i
  cases i <;> simp

/-- The source's `eval_affineGraphPullback`. -/
theorem source_eval_affineGraphPullback (a b : σ → F) (z : F) (p : MvPolynomial (Option σ) F) :
    (aeval (fun i : Option σ ↦ i.elim Polynomial.X
        fun j ↦ Polynomial.C (a j) + Polynomial.X * Polynomial.C (b j)) p).eval z =
      aeval (fun i : Option σ ↦ i.elim z fun j ↦ a j + z * b j) p := by
  rw [source_eval_polynomialGraphPullback]
  congr 2
  funext i
  cases i
  · simp
  · simp only [Option.elim_some, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X]

/-- The source's `polynomialGraphPullback_eq_zero_of_infinite`. -/
theorem source_polynomialGraphPullback_eq_zero_of_infinite (w : σ → Polynomial F)
    {S : Set (Option σ → F)} (hS : S.Infinite)
    (hgraph : ∀ x ∈ S, x = fun i : Option σ ↦ i.elim (x none) fun j ↦ (w j).eval (x none))
    (p : MvPolynomial (Option σ) F) (hzero : ∀ x ∈ S, aeval x p = 0) :
    aeval (fun i : Option σ ↦ i.elim Polynomial.X w) p = 0 :=
  aeval_eq_zero_of_infinite _ hS
    (fun x hx ↦ ⟨x none, (hgraph x hx).trans (funext fun i ↦ by cases i <;> simp)⟩)
    fun x hx ↦ hzero x hx

/-- The source's `polynomialGraphPullback_vanishes_of_principalOpen`. The first conjunct is
`aeval_eq_zero_of_principalOpen_subset_range`; the second evaluates `aeval w s` at the parameter of
one point of the principal open subset, which is nonempty since it is infinite. -/
theorem source_polynomialGraphPullback_vanishes_of_principalOpen [IsAlgClosed F] [Finite σ]
    {P : Ideal (MvPolynomial (Option σ) F)} (hP : P.IsPrime) {s : MvPolynomial (Option σ) F}
    (hs : s ∉ P) (hd : 0 < (affineHilbertPolynomial P).natDegree) (w : σ → Polynomial F)
    (hgraph : ∀ x ∈ {x : Option σ → F | x ∈ zeroLocus F P ∧ aeval x s ≠ 0},
      x = fun i : Option σ ↦ i.elim (x none) fun j ↦ (w j).eval (x none)) :
    (∀ p ∈ P, aeval (fun i : Option σ ↦ i.elim Polynomial.X w) p = 0) ∧
      aeval (fun i : Option σ ↦ i.elim Polynomial.X w) s ≠ 0 := by
  have hreg := isLeftRegular_mk_of_isPrime hP hs
  have hrange : ∀ x : Option σ → F, x ∈ zeroLocus F P → aeval x s ≠ 0 →
      ∃ z : F, x = fun i ↦ ((fun i : Option σ ↦ i.elim Polynomial.X w) i).eval z :=
    fun x hx hxs ↦ ⟨x none, (hgraph x ⟨hx, hxs⟩).trans (funext fun i ↦ by cases i <;> simp)⟩
  refine ⟨fun p hp ↦ aeval_eq_zero_of_principalOpen_subset_range hreg hd _ hrange
    fun x hx _ ↦ (mem_zeroLocus_iff.mp hx) p hp, fun hzero ↦ ?_⟩
  have hinf : ¬ {x : Option σ → F | x ∈ zeroLocus F P ∧ aeval x s ≠ 0}.Finite := fun hfin ↦
    hd.ne' ((finite_principalOpen_iff_natDegree_affineHilbertPolynomial_eq_zero hreg).mp hfin)
  obtain ⟨x, hx, hxs⟩ := Set.Infinite.nonempty hinf
  obtain ⟨z, rfl⟩ := hrange x hx hxs
  have h := polynomial_eval_aeval (fun i : Option σ ↦ i.elim Polynomial.X w) z s
  rw [hzero, Polynomial.eval_zero] at h
  exact hxs h.symm

/-- The source's `hilbertPolynomial_natDegree_le_one_of_principalOpen_subset_polynomialGraph`.
The hypothesis `0 < natDegree H(P)` of the source is not needed. -/
theorem source_natDegree_le_one_of_principalOpen_subset_polynomialGraph [IsAlgClosed F]
    [Finite σ] {P : Ideal (MvPolynomial (Option σ) F)} (hP : P.IsPrime)
    {s : MvPolynomial (Option σ) F} (hs : s ∉ P) (w : σ → Polynomial F)
    (hgraph : ∀ x ∈ {x : Option σ → F | x ∈ zeroLocus F P ∧ aeval x s ≠ 0},
      x = fun i : Option σ ↦ i.elim (x none) fun j ↦ (w j).eval (x none)) :
    (affineHilbertPolynomial P).natDegree ≤ 1 :=
  natDegree_affineHilbertPolynomial_le_one_of_principalOpen_subset_range (K := F)
    (isLeftRegular_mk_of_isPrime hP hs) (fun i : Option σ ↦ i.elim Polynomial.X w)
    fun x hx hxs ↦ ⟨x none, (hgraph x ⟨hx, hxs⟩).trans (funext fun i ↦ by cases i <;> simp)⟩

/-- The source's `hilbertPolynomial_natDegree_le_one_of_principalOpen_subset_affineGraph`,
with the base field not required to be algebraically closed: the points lie in `K`. -/
theorem source_natDegree_le_one_of_principalOpen_subset_affineGraph {k : Type*} [Field k]
    [Algebra k 𝕂] [Finite σ] {P : Ideal (MvPolynomial (Option σ) k)} (hP : P.IsPrime)
    {s : MvPolynomial (Option σ) k} (hs : s ∉ P) (a b : σ → k)
    (hgraph : ∀ x ∈ {x : Option σ → 𝕂 | x ∈ zeroLocus 𝕂 P ∧ aeval x s ≠ 0},
      x = fun i : Option σ ↦ i.elim (x none) fun j ↦ algebraMap k 𝕂 (a j) +
        x none * algebraMap k 𝕂 (b j)) :
    (affineHilbertPolynomial P).natDegree ≤ 1 :=
  natDegree_affineHilbertPolynomial_le_one_of_principalOpen_subset_range (K := 𝕂)
    (isLeftRegular_mk_of_isPrime hP hs) (fun i : Option σ ↦ i.elim Polynomial.X
      fun j ↦ Polynomial.C (a j) + Polynomial.X * Polynomial.C (b j))
    fun x hx hxs ↦ ⟨x none, (hgraph x ⟨hx, hxs⟩).trans (funext fun i ↦ by
      cases i
      · simp
      · simp only [Option.elim_some, Polynomial.aeval_add, Polynomial.aeval_mul,
          Polynomial.aeval_C, Polynomial.aeval_X])⟩

end Source

end PrincipalOpenParametrizationTest
