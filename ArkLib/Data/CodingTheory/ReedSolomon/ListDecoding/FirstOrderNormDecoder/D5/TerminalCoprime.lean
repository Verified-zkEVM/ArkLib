/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderNormDecoder.D5.FactorTower

/-!
# Coprimality of terminal D5 factors

The D5 factor tower preserves both the exact product of its terminal base moduli and squarefreeness
of the initial modulus.  Consequently, distinct terminal factors are relatively prime.  This is
the algebraic input for coefficientwise Chinese remainder reconstruction.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.FirstOrderNormDecoder.D5

open CompPoly Polynomial

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

local instance terminalCoprimeDecidableEqF : DecidableEq F := instDecidableEqOfLawfulBEq
local instance terminalCoprimeDecidableEqCPolynomial : DecidableEq (CPolynomial F) :=
  instDecidableEqOfLawfulBEq

/-- A squarefree product has pairwise relatively prime factors.  The statement includes the empty
and singleton lists. -/
theorem pairwise_isRelPrime_of_squarefree_list_product
    {R : Type*} [CommMonoidWithZero R] [IsCancelMulZero R] [DecompositionMonoid R]
    (factors : List R) (hfree : Squarefree factors.prod) :
    factors.Pairwise IsRelPrime := by
  induction factors with
  | nil => simp
  | cons factor factors ih =>
      rw [List.prod_cons, squarefree_mul_iff] at hfree
      rw [List.pairwise_cons]
      refine ⟨?_, ih hfree.2.2⟩
      intro other hother
      exact hfree.1.of_dvd_right (List.dvd_prod hother)

/-- The proof-facing polynomial images of all terminal tower moduli are pairwise relatively prime.
-/
theorem factorTower_moduli_pairwise_isRelPrime (state : TowerState (F := F)) :
    ((factorTower state).map fun terminal => terminal.modulus.toPoly).Pairwise IsRelPrime := by
  apply pairwise_isRelPrime_of_squarefree_list_product
  have hproduct := congrArg (CPolynomial.toPoly (R := F))
    (factorTower_modulus_product state)
  have hmap :
      ((factorTower state).map fun terminal => terminal.modulus.toPoly).prod =
        ((factorTower state).map TerminalGCDBranch.modulus).prod.toPoly := by
    induction factorTower state with
    | nil => simp [CPolynomial.toPoly_one]
    | cons terminal terminals ih =>
        simp [CPolynomial.toPoly_mul, ih]
  rw [hmap, hproduct]
  exact state.modulus_squarefree

/-- Terminal moduli are pairwise coprime in the Bézout form consumed by executable modular
inversion. -/
theorem factorTower_moduli_pairwise_isCoprime (state : TowerState (F := F)) :
    ((factorTower state).map TerminalGCDBranch.modulus).Pairwise
      (fun left right => IsCoprime left.toPoly right.toPoly) := by
  rw [List.pairwise_map]
  exact List.pairwise_map.mp
    ((factorTower_moduli_pairwise_isRelPrime state).imp fun h =>
      isRelPrime_iff_isCoprime.mp h)

end ReedSolomon.ListDecoding.FirstOrderNormDecoder.D5
