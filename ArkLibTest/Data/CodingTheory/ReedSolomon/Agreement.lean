/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Agreement
import Mathlib.FieldTheory.Finite.Extension

noncomputable section

open Polynomial ReedSolomon

private abbrev E₄ := FiniteField.Extension (ZMod 2) 2 2
local instance : DecidableEq E₄ := Classical.decEq _

private def onePointDomain {F : Type*} (x : F) : Fin 1 ↪ F :=
  ⟨fun _ ↦ x, fun _ _ _ ↦ Subsingleton.elim _ _⟩

/-- Agreement sets are preserved by the algebra map from `ZMod 2` into its degree-two extension.
-/
example (P : (ZMod 2)[X]) (y : Fin 1 → ZMod 2) :
    polynomialAgreementSet
        ((onePointDomain (0 : ZMod 2)).trans
          ⟨algebraMap (ZMod 2) E₄, (algebraMap (ZMod 2) E₄).injective⟩)
        (fun i ↦ algebraMap (ZMod 2) E₄ (y i)) (P.map (algebraMap (ZMod 2) E₄)) =
      polynomialAgreementSet (onePointDomain (0 : ZMod 2)) y P :=
  polynomialAgreementSet_map _ _ (algebraMap (ZMod 2) E₄).injective y P

/-- Injectivity is needed: reducing `2 * X` modulo two creates agreement at the point `1` that
was absent over the integers. -/
example :
    (polynomialAgreementSet (onePointDomain (1 : ℤ)) (fun _ ↦ 0) (2 * X : ℤ[X])).card = 0 ∧
      (polynomialAgreementSet (onePointDomain (1 : ZMod 2)) (fun _ ↦ 0)
        ((2 * X : ℤ[X]).map (Int.castRingHom (ZMod 2)))).card = 1 := by
  constructor
  · have hset :
        polynomialAgreementSet (onePointDomain (1 : ℤ)) (fun _ ↦ 0) (2 * X : ℤ[X]) = ∅ := by
      ext i
      constructor
      · intro hi
        rw [mem_polynomialAgreementSet] at hi
        have hei : i = 0 := Subsingleton.elim _ _
        subst i
        change (2 * X : ℤ[X]).eval 1 = 0 at hi
        norm_num [Polynomial.eval_mul] at hi
      · intro hi
        simp at hi
    simp [hset]
  · have hmap : ((2 * X : ℤ[X]).map (Int.castRingHom (ZMod 2))) = 0 := by
      simp [CharTwo.two_eq_zero]
    rw [hmap]
    simp [polynomialAgreementSet, onePointDomain]
