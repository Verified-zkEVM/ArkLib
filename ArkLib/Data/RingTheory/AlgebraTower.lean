/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import Mathlib

/-!
  # Tower of Algebras and Tower of Algebra Equivalences

  This file contains definitions, theorems, instances that are used in defining tower of algebras
  and their equivalences.

  ## Main definitions

  * `AlgebraTower` : a tower of algebras
  * `CoherentAlgebraTower` : a tower of algebras with coherence condition
  * `AlgebraTowerEquiv` : an equivalence of towers of algebras
  * `CoherentAlgebraTowerEquiv` : an equivalence of towers of coherent algebras

Some considerations:

1. Can we reuse existing `Algebra` and `AlgEquiv` definitions? For instance, `AlgebraTower` can just
   contain an algebra instance `Algebra (TA i) (TA j)` for every `i, j : ι` with `i ≤ j`. This
   allows for using the root namespace definition `algebraMap`, instead of the custom notation
   `towerAlgebraMap`. Since `algebraMap` is natively supported in mathlib with lots of theorems,
   this may lead to better simplification behavior. Same for `AlgEquiv`.

2. Name change: the condition in `Associative` is exactly in associativity format (i.e. `(a * b) * c
   = a * (b * c)`). One may consider renaming this to `Coherent`.

3. Can we merge the coherence / associativity condition into `AlgebraTower`? If we never encounter
   algebra towers that are not coherent, then there is no need for a separate type class.

4. After everything, run `#min_imports` to minimize imports instead of importing the whole of
   mathlib.
-/

/-- A tower of algebras is a sequence of algebras `TA i` indexed over a preorder `ι` with the
    following data:
    - `towerAlgebraMap : TA i →+* TA j` is a ring homomorphism from `TA i` to `TA j` for all `i ≤ j`
    - `commutes'` is a proof that the ring homomorphism commutes with the multiplication
    - `smul_def'` is a proof that the scalar multiplication is defined by the ring homomorphism.
-/
class AlgebraTower {ι : Type*} [Preorder ι] (TA : ι → Type*)
  [∀ i, CommSemiring (TA i)] where
  /-- Ring homomorphisms from `TA i` to `TA j` for all `i ≤ j`. -/
  protected towerAlgebraMap : ∀ i j, (h : i ≤ j) → (TA i →+* TA j)
  /-- Scalar multiplication from `TA i` to `TA j` for all `i ≤ j`. -/
  protected smul: ∀ i j, (h: i ≤ j) → (SMul (TA i) (TA j))
  /-- Commutativity of multiplication with respect to the ring homomorphism. -/
  commutes' : ∀ (i j : ι) (h : i ≤ j) (r : TA i) (x : TA j),
    (towerAlgebraMap i j h r) * x = x * (towerAlgebraMap i j h r)
  /-- Scalar multiplication is determined by the ring homomorphism. -/
  smul_def' : ∀ (i j : ι) (h : i ≤ j) (r : TA i) (x : TA j),
    (towerAlgebraMap i j h r) * x = (towerAlgebraMap i j h r) * x

/-- A tower of algebras is coherent if the algebra maps satisfy the coherence condition:
    the direct map from i to k equals the composition of maps i → j → k. -/
class CoherentAlgebraTower {ι : Type*} [Preorder ι] (TA : ι → Type*)
  [∀ i, CommSemiring (TA i)] extends AlgebraTower TA where
  coherence': ∀ (i j k : ι) (h1 : i ≤ j) (h2 : j ≤ k),
    towerAlgebraMap i k (h1.trans h2) =
      (towerAlgebraMap j k h2).comp (towerAlgebraMap i j h1)

variable {ι : Type*} [Preorder ι]
  {A : ι → Type*} [∀ i, CommSemiring (A i)] [AlgebraTower A]
  {B : ι → Type*} [∀ i, CommSemiring (B i)] [AlgebraTower B]
  {C : ι → Type*} [∀ i, CommSemiring (C i)] [CoherentAlgebraTower C]

@[simp]
def AlgebraTower.toAlgebra {i j : ι} (h : i ≤ j) : Algebra (A i) (A j) :=
  (AlgebraTower.towerAlgebraMap (i:=i) (j:=j) (h:=h)).toAlgebra

@[simp]
instance CoherentAlgebraTower.toIsScalarTower (a : CoherentAlgebraTower C) {i j k : ι}
    (h1 : i ≤ j) (h2 : j ≤ k) :
    letI : Algebra (C i) (C j) := by exact a.toAlgebra h1
    letI : Algebra (C j) (C k) := by exact a.toAlgebra h2
    letI : Algebra (C i) (C k) := by exact a.toAlgebra (h1.trans h2)
    IsScalarTower (C i) (C j) (C k) := by
  letI instIJ: Algebra (C i) (C j) := by exact a.toAlgebra h1
  letI instJK: Algebra (C j) (C k) := by exact a.toAlgebra h2
  letI instIK: Algebra (C i) (C k) := by exact a.toAlgebra (h1.trans h2)
  exact {
    smul_assoc := fun (x : C i) (y : C j) (z : C k) => by
      simp_rw [Algebra.smul_def]
      simp only [map_mul]
      rw [←RingHom.comp_apply]
      unfold instIJ instJK instIK AlgebraTower.toAlgebra
      simp_rw [algebraMap, Algebra.algebraMap]
      have h_assoc := a.coherence' (i:=i) (j:=j) (k:=k) (h1:=h1) (h2:=h2)
      rw [h_assoc]
      rw [mul_assoc]
  }

structure AlgebraTowerEquiv (A : ι → Type*) [∀ i, CommSemiring (A i)] [a : AlgebraTower A]
  (B : ι → Type*) [∀ i, CommSemiring (B i)] [AlgebraTower B]
  where
    toRingEquiv: ∀ i, (A i ≃+* B i)
    commutesLeft' : ∀ (i j : ι) (h : i ≤ j) (r : A i),
      AlgebraTower.towerAlgebraMap (TA:=B) (i:=i) (j:=j) (h:=h) ((toRingEquiv i) r) =
      (toRingEquiv j) (AlgebraTower.towerAlgebraMap (TA:=A) (i:=i) (j:=j) (h:=h) r)

lemma AlgebraTowerEquiv.commutesRight' (e : AlgebraTowerEquiv A B)
    {i j : ι} (h : i ≤ j) (r : B i) :
  AlgebraTower.towerAlgebraMap (TA:=A) (i:=i) (j:=j) (h:=h) ((e.toRingEquiv i).symm r) =
  (e.toRingEquiv j).symm (AlgebraTower.towerAlgebraMap (TA:=B) (i:=i) (j:=j) (h:=h) r):= by
  apply (e.toRingEquiv j).injective
  set r2: A i := (e.toRingEquiv i).symm r
  rw [←e.commutesLeft' (i:=i) (j:=j) (h:=h) (r:=r2)]
  simp only [RingEquiv.apply_symm_apply]
  have h_e_r2_rfl: e.toRingEquiv i r2 = r := by exact RingEquiv.apply_symm_apply (e.toRingEquiv i) r
  rw [h_e_r2_rfl]

def AlgebraTowerEquiv.symm (e : AlgebraTowerEquiv A B) : AlgebraTowerEquiv B A where
  toRingEquiv := fun i => (e.toRingEquiv i).symm
  commutesLeft' := fun i j h r => by exact commutesRight' e h r

def AlgebraTowerEquiv.algebraMapRightUp (e : AlgebraTowerEquiv A B) (i j : ι)
    (h : i ≤ j): (A i) →+* (B j) := by
  have hBij: B i →+* B j := AlgebraTower.towerAlgebraMap (TA:=B) (i:=i) (j:=j) (h:=h)
  have hiRingEquiv: RingEquiv (A i) (B i) := e.toRingEquiv i
  exact hBij.comp hiRingEquiv.toRingHom

def AlgebraTowerEquiv.algebraMapLeftUp (e : AlgebraTowerEquiv A B) (i j : ι)
    (h : i ≤ j): (B i) →+* (A j) := by
  have hAij: A i →+* A j := AlgebraTower.towerAlgebraMap (TA:=A) (i:=i) (j:=j) (h:=h)
  have hjRingEquiv: RingEquiv (B i) (A i) := (e.toRingEquiv i).symm
  exact hAij.comp hjRingEquiv.toRingHom

def AlgebraTowerEquiv.toAlgebraOverLeft (e : AlgebraTowerEquiv A B) (i j : ι)
    (h : i ≤ j): Algebra (A i) (B j) := by
  exact (e.algebraMapRightUp i j h).toAlgebra

def AlgebraTowerEquiv.toAlgebraOverRight (e : AlgebraTowerEquiv A B) (i j : ι)
    (h : i ≤ j): Algebra (B i) (A j) := by
  exact (e.algebraMapLeftUp i j h).toAlgebra

def AlgebraTowerEquiv.toAlgEquivOverLeft (e : AlgebraTowerEquiv A B) (i j : ι) (h : i ≤ j):
  letI : Algebra (A i) (A j) := by exact AlgebraTower.toAlgebra h
  letI : Algebra (A i) (B j) := by exact e.toAlgebraOverLeft i j h
  AlgEquiv (A i) (A j) (B j) := by
  letI instAij: Algebra (A i) (A j) := by exact AlgebraTower.toAlgebra h
  letI instAiBij: Algebra (A i) (B j) := by exact e.toAlgebraOverLeft i j h
  letI instAlgEquiv: AlgEquiv (A i) (A j) (B j) := by exact {
    toEquiv := by
      have hRingEquiv := e.toRingEquiv j
      exact hRingEquiv.toEquiv
    commutes' := fun r => by
      simp only [RingEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe]
      unfold instAij instAiBij
      rw [algebraMap, algebraMap, Algebra.algebraMap, Algebra.algebraMap,AlgebraTower.toAlgebra,
        AlgebraTowerEquiv.toAlgebraOverLeft, AlgebraTowerEquiv.algebraMapRightUp]
      simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply]
      exact Eq.symm (e.commutesLeft' i j h r)
    map_mul' := fun x y => by
      simp only [RingEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe, map_mul]
    map_add' := fun x y => by
      simp only [RingEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe, map_add]
  }
  exact instAlgEquiv

def AlgebraTowerEquiv.toAlgEquivOverRight (e : AlgebraTowerEquiv A B) (i j : ι) (h : i ≤ j):
  letI : Algebra (B i) (B j) := by exact AlgebraTower.toAlgebra h
  letI : Algebra (B i) (A j) := by exact e.toAlgebraOverRight i j h
  AlgEquiv (B i) (B j) (A j) := (e.symm.toAlgEquivOverLeft i j h)

structure CoherentAlgebraTowerEquiv (A : ι → Type*) [∀ i, CommSemiring (A i)] [CoherentAlgebraTower A]
  (B : ι → Type*) [∀ i, CommSemiring (B i)] [CoherentAlgebraTower B] extends AlgebraTowerEquiv A B
