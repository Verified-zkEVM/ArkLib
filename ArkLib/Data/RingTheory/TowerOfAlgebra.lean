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

structure AssocTowerOfAlgebraEquiv (A : ι → Type*) [∀ i, CommSemiring (A i)] [AssocTowerOfAlgebra A]
  (B : ι → Type*) [∀ i, CommSemiring (B i)] [AssocTowerOfAlgebra B] extends TowerOfAlgebraEquiv A B
