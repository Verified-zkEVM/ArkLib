/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import Mathlib

/-!
  # Tower of Algebras and Tower of Algebra Equivalences

  This file contains definitions, theorems, instances that are used in
  defining tower of algebras and their equivalences.

  ## Main definitions

  * `TowerOfAlgebra` : a tower of algebras
  * `AssocTowerOfAlgebra` : a tower of associative algebras
  * `TowerOfAlgebraEquiv` : an equivalence of towers of algebras
  * `AssocTowerOfAlgebraEquiv` : an equivalence of towers of associative algebras
-/

class TowerOfAlgebra {ι : Type*} [Preorder ι] (TA : ι → Type*)
  [∀ i, CommSemiring (TA i)] where
  protected towerAlgebraMap : ∀ i j, (h: i ≤ j) → (TA i →+* TA j)
  -- for case where smul is not derived from towerAlgebraMap
  protected smul: ∀ i j, (h: i ≤ j) → (SMul (TA i) (TA j))
  commutes' : ∀ (i j : ι) (h : i ≤ j) (r : TA i) (x : TA j),
    (towerAlgebraMap i j h r) * x = x * (towerAlgebraMap i j h r)
  smul_def' : ∀ (i j : ι) (h : i ≤ j) (r : TA i) (x : TA j),
    (smul i j h).smul r x = (towerAlgebraMap i j h r) * x

class AssocTowerOfAlgebra {ι : Type*} [Preorder ι] (TA : ι → Type*)
  [∀ i, CommSemiring (TA i)] extends TowerOfAlgebra TA where
  assoc': ∀ (i j k : ι) (h1 : i ≤ j) (h2 : j ≤ k),
    towerAlgebraMap (i:=i) (j:=k) (h:=h1.trans h2) =
      (towerAlgebraMap (i:=j) (j:=k) (h:=h2)).comp
      (towerAlgebraMap (i:=i) (j:=j) (h:=h1))

variable {ι : Type*} [Preorder ι]
  {A : ι → Type*} [∀ i, CommSemiring (A i)] [TowerOfAlgebra A]
  {B : ι → Type*} [∀ i, CommSemiring (B i)] [TowerOfAlgebra B]
  {C : ι → Type*} [∀ i, CommSemiring (C i)] [AssocTowerOfAlgebra C]

@[simp]
def TowerOfAlgebra.toAlgebra {i j : ι} (h : i ≤ j) : Algebra (A i) (A j) :=
  (TowerOfAlgebra.towerAlgebraMap (i:=i) (j:=j) (h:=h)).toAlgebra

@[simp]
instance AssocTowerOfAlgebra.toIsScalarTower (a : AssocTowerOfAlgebra C) {i j k : ι}
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
      unfold instIJ instJK instIK TowerOfAlgebra.toAlgebra
      simp_rw [algebraMap, Algebra.algebraMap]
      have h_assoc := a.assoc' (i:=i) (j:=j) (k:=k) (h1:=h1) (h2:=h2)
      rw [h_assoc]
      rw [mul_assoc]
  }

structure TowerOfAlgebraEquiv (A : ι → Type*) [∀ i, CommSemiring (A i)] [a : TowerOfAlgebra A]
  (B : ι → Type*) [∀ i, CommSemiring (B i)] [TowerOfAlgebra B]
  where
    toRingEquiv: ∀ i, (A i ≃+* B i)
    commutesLeft' : ∀ (i j : ι) (h : i ≤ j) (r : A i),
      TowerOfAlgebra.towerAlgebraMap (TA:=B) (i:=i) (j:=j) (h:=h) ((toRingEquiv i) r) =
      (toRingEquiv j) (TowerOfAlgebra.towerAlgebraMap (TA:=A) (i:=i) (j:=j) (h:=h) r)

lemma TowerOfAlgebraEquiv.commutesRight' (e : TowerOfAlgebraEquiv A B)
    {i j : ι} (h : i ≤ j) (r : B i) :
  TowerOfAlgebra.towerAlgebraMap (TA:=A) (i:=i) (j:=j) (h:=h) ((e.toRingEquiv i).symm r) =
  (e.toRingEquiv j).symm (TowerOfAlgebra.towerAlgebraMap (TA:=B) (i:=i) (j:=j) (h:=h) r):= by
  apply (e.toRingEquiv j).injective
  set r2: A i := (e.toRingEquiv i).symm r
  rw [←e.commutesLeft' (i:=i) (j:=j) (h:=h) (r:=r2)]
  simp only [RingEquiv.apply_symm_apply]
  have h_e_r2_rfl: e.toRingEquiv i r2 = r := by exact RingEquiv.apply_symm_apply (e.toRingEquiv i) r
  rw [h_e_r2_rfl]

def TowerOfAlgebraEquiv.symm (e : TowerOfAlgebraEquiv A B) : TowerOfAlgebraEquiv B A where
  toRingEquiv := fun i => (e.toRingEquiv i).symm
  commutesLeft' := fun i j h r => by exact commutesRight' e h r

def TowerOfAlgebraEquiv.algebraMapRightUp (e : TowerOfAlgebraEquiv A B) (i j : ι)
    (h : i ≤ j): (A i) →+* (B j) := by
  have hBij: B i →+* B j := TowerOfAlgebra.towerAlgebraMap (TA:=B) (i:=i) (j:=j) (h:=h)
  have hiRingEquiv: RingEquiv (A i) (B i) := e.toRingEquiv i
  exact hBij.comp hiRingEquiv.toRingHom

def TowerOfAlgebraEquiv.algebraMapLeftUp (e : TowerOfAlgebraEquiv A B) (i j : ι)
    (h : i ≤ j): (B i) →+* (A j) := by
  have hAij: A i →+* A j := TowerOfAlgebra.towerAlgebraMap (TA:=A) (i:=i) (j:=j) (h:=h)
  have hjRingEquiv: RingEquiv (B i) (A i) := (e.toRingEquiv i).symm
  exact hAij.comp hjRingEquiv.toRingHom

def TowerOfAlgebraEquiv.toAlgebraOverLeft (e : TowerOfAlgebraEquiv A B) (i j : ι)
    (h : i ≤ j): Algebra (A i) (B j) := by
  exact (e.algebraMapRightUp i j h).toAlgebra

def TowerOfAlgebraEquiv.toAlgebraOverRight (e : TowerOfAlgebraEquiv A B) (i j : ι)
    (h : i ≤ j): Algebra (B i) (A j) := by
  exact (e.algebraMapLeftUp i j h).toAlgebra

def TowerOfAlgebraEquiv.toAlgEquivOverLeft (e : TowerOfAlgebraEquiv A B) (i j : ι) (h : i ≤ j):
  letI : Algebra (A i) (A j) := by exact TowerOfAlgebra.toAlgebra h
  letI : Algebra (A i) (B j) := by exact e.toAlgebraOverLeft i j h
  AlgEquiv (A i) (A j) (B j) := by
  letI instAij: Algebra (A i) (A j) := by exact TowerOfAlgebra.toAlgebra h
  letI instAiBij: Algebra (A i) (B j) := by exact e.toAlgebraOverLeft i j h
  letI instAlgEquiv: AlgEquiv (A i) (A j) (B j) := by exact {
    toEquiv := by
      have hRingEquiv := e.toRingEquiv j
      exact hRingEquiv.toEquiv
    commutes' := fun r => by
      simp only [RingEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe]
      unfold instAij instAiBij
      rw [algebraMap, algebraMap, Algebra.algebraMap, Algebra.algebraMap,TowerOfAlgebra.toAlgebra,
        TowerOfAlgebraEquiv.toAlgebraOverLeft, TowerOfAlgebraEquiv.algebraMapRightUp]
      simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply]
      exact Eq.symm (e.commutesLeft' i j h r)
    map_mul' := fun x y => by
      simp only [RingEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe, map_mul]
    map_add' := fun x y => by
      simp only [RingEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe, map_add]
  }
  exact instAlgEquiv

def TowerOfAlgebraEquiv.toAlgEquivOverRight (e : TowerOfAlgebraEquiv A B) (i j : ι) (h : i ≤ j):
  letI : Algebra (B i) (B j) := by exact TowerOfAlgebra.toAlgebra h
  letI : Algebra (B i) (A j) := by exact e.toAlgebraOverRight i j h
  AlgEquiv (B i) (B j) (A j) := (e.symm.toAlgEquivOverLeft i j h)

structure AssocTowerOfAlgebraEquiv (A : ι → Type*) [∀ i, CommSemiring (A i)] [AssocTowerOfAlgebra A]
  (B : ι → Type*) [∀ i, CommSemiring (B i)] [AssocTowerOfAlgebra B] extends TowerOfAlgebraEquiv A B
