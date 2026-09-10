/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.ToMathlib.AlgebraicGeometry.PrincipalOpen.Finite
public import ArkLib.ToMathlib.AlgebraicGeometry.Hilbert.FiniteAlgebraGrowth
public import ArkLib.ToMathlib.AlgebraicGeometry.PrincipalCut.Polynomial

/-! # Polynomial identities along polynomial graphs

A positive-dimensional principal open whose points lie on a polynomial graph supplies
infinitely many parameter values. Consequently every polynomial vanishing on the open
vanishes identically after restriction to that graph. This avoids constructing image
closures when recognizing one-parameter families of polynomial solutions.
-/

@[expose] public section

noncomputable section

open MvPolynomial

namespace AffineHilbert

variable {F σ : Type*} [Field F]

/-- A polynomial graph retaining its parameter as the `none` coordinate. -/
def polynomialGraphPoint (w : σ → Polynomial F) (z : F) : Option σ → F :=
  fun i ↦ i.elim z (fun j ↦ (w j).eval z)

/-- Restriction to a polynomial graph, with no bound on the coordinate degrees. -/
def polynomialGraphPullback (w : σ → Polynomial F) :
    MvPolynomial (Option σ) F →ₐ[F] Polynomial F :=
  aeval (fun i ↦ i.elim Polynomial.X w)

/-- Polynomial-graph restriction commutes with evaluation of the retained parameter. -/
theorem eval_polynomialGraphPullback (w : σ → Polynomial F) (z : F)
    (p : MvPolynomial (Option σ) F) :
    (polynomialGraphPullback w p).eval z = aeval (polynomialGraphPoint w z) p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [polynomialGraphPullback]
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p i hp =>
      simp only [map_mul, Polynomial.eval_mul, hp]
      congr 1
      cases i <;> simp [polynomialGraphPullback, polynomialGraphPoint]

/-- An infinite subset of a polynomial graph detects all polynomial identities on the graph.
Retaining the parameter makes its projection injective, even when the other coordinates
are constant or inseparable polynomials. -/
theorem polynomialGraphPullback_eq_zero_of_infinite
    (w : σ → Polynomial F) {S : Set (Option σ → F)} (hS : S.Infinite)
    (hgraph : ∀ x ∈ S, x = polynomialGraphPoint w (x none))
    (p : MvPolynomial (Option σ) F) (hzero : ∀ x ∈ S, aeval x p = 0) :
    polynomialGraphPullback w p = 0 := by
  have hinj : Set.InjOn (fun x : Option σ → F ↦ x none) S := by
    intro x hx y hy hxy
    change x none = y none at hxy
    rw [hgraph x hx, hgraph y hy, hxy]
  apply Polynomial.eq_zero_of_infinite_isRoot
  apply (hS.image hinj).mono
  rintro z ⟨x, hx, rfl⟩
  change (polynomialGraphPullback w p).eval (x none) = 0
  rw [eval_polynomialGraphPullback, ← hgraph x hx]
  exact hzero x hx

/-- A positive-dimensional prime principal open supported on a polynomial graph extends to
identities on the whole graph. Its denominator remains a nonzero univariate polynomial. -/
theorem polynomialGraphPullback_vanishes_of_principalOpen [IsAlgClosed F] [Finite σ]
    {P : Ideal (MvPolynomial (Option σ) F)} (hP : P.IsPrime)
    {s : MvPolynomial (Option σ) F} (hs : s ∉ P)
    (hd : 0 < (hilbertPolynomial P).natDegree) (w : σ → Polynomial F)
    (hgraph : ∀ x ∈ principalOpenZeroLocus P s,
      x = polynomialGraphPoint w (x none)) :
    (∀ p ∈ P, polynomialGraphPullback w p = 0) ∧ polynomialGraphPullback w s ≠ 0 := by
  have hinfinite : (principalOpenZeroLocus P s).Infinite := by
    intro hfinite
    have hz := hilbertPolynomial_natDegree_zero_of_finite_principalOpen hP hs hfinite
    omega
  constructor
  · intro p hp
    exact polynomialGraphPullback_eq_zero_of_infinite w hinfinite hgraph p
      (fun x hx ↦ hx.1 p hp)
  · obtain ⟨x, hx⟩ := hinfinite.nonempty
    intro hz
    have heval := eval_polynomialGraphPullback w (x none) s
    rw [hz, Polynomial.eval_zero, ← hgraph x hx] at heval
    exact hx.2 heval.symm

/-- A prime principal open contained in a one-parameter polynomial graph has Hilbert dimension
at most one.

The proof constructs the coordinate-algebra map in the dimension-preserving direction.  Its
kernel is exactly the source prime: a polynomial in the kernel vanishes on the principal open,
so its product with the open denominator vanishes on the whole prime zero locus.  The
Nullstellensatz and primality then put the polynomial itself in the source prime. -/
theorem hilbertPolynomial_natDegree_le_one_of_principalOpen_subset_polynomialGraph
    [IsAlgClosed F] [Finite σ]
    {P : Ideal (MvPolynomial (Option σ) F)} (hP : P.IsPrime)
    {s : MvPolynomial (Option σ) F} (hs : s ∉ P)
    (hd : 0 < (hilbertPolynomial P).natDegree) (w : σ → Polynomial F)
    (hgraph : ∀ x ∈ principalOpenZeroLocus P s,
      x = polynomialGraphPoint w (x none)) :
    (hilbertPolynomial P).natDegree ≤ 1 := by
  have hvanish := (polynomialGraphPullback_vanishes_of_principalOpen hP hs hd w hgraph).1
  have hker : RingHom.ker (polynomialGraphPullback w).toRingHom = P := by
    apply le_antisymm
    · intro p hp
      change polynomialGraphPullback w p = 0 at hp
      have hsp : s * p ∈ P.radical := by
        rw [← vanishingIdeal_zeroLocus_eq_radical (K := F)]
        intro x hx
        by_cases hxs : aeval x s = 0
        · simp [map_mul, hxs]
        · have hxopen : x ∈ principalOpenZeroLocus P s := ⟨hx, hxs⟩
          have heval := eval_polynomialGraphPullback w (x none) p
          rw [hp, Polynomial.eval_zero, ← hgraph x hxopen] at heval
          rw [map_mul, ← heval, mul_zero]
      have hspP : s * p ∈ P := by simpa only [hP.radical] using hsp
      exact (hP.mem_or_mem hspP).resolve_left hs
    · exact hvanish
  let graphMv : MvPolynomial (Option σ) F →ₐ[F] MvPolynomial Unit F :=
    (MvPolynomial.uniqueAlgEquiv F Unit).symm.toAlgHom.comp (polynomialGraphPullback w)
  have hkerMv : RingHom.ker graphMv.toRingHom = P := by
    rw [show graphMv.toRingHom =
      (MvPolynomial.uniqueAlgEquiv F Unit).symm.toRingHom.comp
        (polynomialGraphPullback w).toRingHom by rfl]
    rw [RingHom.ker_comp_of_injective _ (MvPolynomial.uniqueAlgEquiv F Unit).symm.injective]
    exact hker
  have hle : P ≤ (⊥ : Ideal (MvPolynomial Unit F)).comap graphMv := by
    change P ≤ RingHom.ker graphMv.toRingHom
    rw [hkerMv]
  let qmap : (MvPolynomial (Option σ) F ⧸ P) →ₐ[F]
      (MvPolynomial Unit F ⧸ (⊥ : Ideal (MvPolynomial Unit F))) :=
    Ideal.quotientMapₐ ⊥ graphMv hle
  have hqinj : Function.Injective qmap := by
    change Function.Injective (Ideal.quotientMap ⊥ graphMv.toRingHom hle)
    exact Ideal.quotientMap_injective' (H := hle) (by
      change RingHom.ker graphMv.toRingHom ≤ P
      rw [hkerMv])
  have hdegree := hilbertPolynomial_natDegree_le_of_injective_algHom qmap hqinj hP.ne_top
  simpa only [hilbertPolynomial_bot_natDegree, Nat.card_unique] using hdegree

/-- The point on an affine graph with parameter `z` and coordinate slopes `b`. -/
def affineGraphPoint (a b : σ → F) (z : F) : Option σ → F :=
  fun i ↦ i.elim z (fun j ↦ a j + z * b j)

/-- Restriction of a multivariate polynomial to an affine graph. -/
def affineGraphPullback (a b : σ → F) :
    MvPolynomial (Option σ) F →ₐ[F] Polynomial F :=
  aeval (fun i ↦ i.elim Polynomial.X
    (fun j ↦ Polynomial.C (a j) + Polynomial.X * Polynomial.C (b j)))

/-- Restriction followed by evaluation equals evaluation at the graph point. -/
theorem eval_affineGraphPullback (a b : σ → F) (z : F)
    (p : MvPolynomial (Option σ) F) :
    (affineGraphPullback a b p).eval z = aeval (affineGraphPoint a b z) p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [affineGraphPullback]
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p i hp =>
      simp only [map_mul, Polynomial.eval_mul, hp]
      congr 1
      cases i <;> simp only [affineGraphPullback, affineGraphPoint,
        MvPolynomial.aeval_X, Option.elim, Polynomial.eval_add,
        Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]

/-- Vanishing on infinitely many points of an affine graph implies a polynomial
identity after restriction to the graph. -/
theorem affineGraphPullback_eq_zero_of_infinite
    (a b : σ → F) {S : Set (Option σ → F)} (hS : S.Infinite)
    (hgraph : ∀ x ∈ S, x = affineGraphPoint a b (x none))
    (p : MvPolynomial (Option σ) F) (hzero : ∀ x ∈ S, aeval x p = 0) :
    affineGraphPullback a b p = 0 := by
  have hinj : Set.InjOn (fun x : Option σ → F ↦ x none) S := by
    intro x hx y hy hxy
    change x none = y none at hxy
    rw [hgraph x hx, hgraph y hy, hxy]
  apply Polynomial.eq_zero_of_infinite_isRoot
  apply (hS.image hinj).mono
  rintro z ⟨x, hx, rfl⟩
  change (affineGraphPullback a b p).eval (x none) = 0
  rw [eval_affineGraphPullback, ← hgraph x hx]
  exact hzero x hx

variable [IsAlgClosed F] [Finite σ]

/-- A positive-dimensional regular principal open lying on an affine graph forces
every polynomial in its prime ideal to vanish identically on the graph. The defining
denominator remains nonzero as a polynomial on that graph. -/
theorem graphPullback_vanishes_of_principalOpen
    {P : Ideal (MvPolynomial (Option σ) F)} (hP : P.IsPrime)
    {s : MvPolynomial (Option σ) F} (hs : s ∉ P)
    (hd : 0 < (hilbertPolynomial P).natDegree) (a b : σ → F)
    (hgraph : ∀ x ∈ principalOpenZeroLocus P s,
      x = affineGraphPoint a b (x none)) :
    (∀ p ∈ P, affineGraphPullback a b p = 0) ∧ affineGraphPullback a b s ≠ 0 := by
  have hinfinite : (principalOpenZeroLocus P s).Infinite := by
    intro hfinite
    have hz := hilbertPolynomial_natDegree_zero_of_finite_principalOpen hP hs hfinite
    omega
  constructor
  · intro p hp
    exact affineGraphPullback_eq_zero_of_infinite a b hinfinite hgraph p
      (fun x hx ↦ hx.1 p hp)
  · obtain ⟨x, hx⟩ := hinfinite.nonempty
    intro hz
    have heval := eval_affineGraphPullback a b (x none) s
    rw [hz, Polynomial.eval_zero, ← hgraph x hx] at heval
    exact hx.2 heval.symm

/-- An affine graph is a one-parameter polynomial graph, so a positive-dimensional prime
principal open contained in it has Hilbert dimension at most one. -/
theorem hilbertPolynomial_natDegree_le_one_of_principalOpen_subset_affineGraph
    {P : Ideal (MvPolynomial (Option σ) F)} (hP : P.IsPrime)
    {s : MvPolynomial (Option σ) F} (hs : s ∉ P)
    (hd : 0 < (hilbertPolynomial P).natDegree) (a b : σ → F)
    (hgraph : ∀ x ∈ principalOpenZeroLocus P s,
      x = affineGraphPoint a b (x none)) :
    (hilbertPolynomial P).natDegree ≤ 1 := by
  let w : σ → Polynomial F := fun i ↦
    Polynomial.C (a i) + Polynomial.X * Polynomial.C (b i)
  apply hilbertPolynomial_natDegree_le_one_of_principalOpen_subset_polynomialGraph
    hP hs hd w
  intro x hx
  rw [hgraph x hx]
  funext i
  cases i with
  | none => rfl
  | some i =>
      change a i + x none * b i =
        (Polynomial.C (a i) + Polynomial.X * Polynomial.C (b i)).eval (x none)
      simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
        Polynomial.eval_X]

end AffineHilbert
