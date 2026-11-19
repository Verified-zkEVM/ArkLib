/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

import ArkLib.Data.CodingTheory.ReedMuller.AffineCombiner.PellikaanWu
import Mathlib.FieldTheory.Finite.GaloisField

/-! # Acceptance cases for the Reed–Muller to Reed–Solomon candidate correspondence -/

open FiniteField ReedMuller Polynomial Finset

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private noncomputable instance : Fintype (GaloisField 2 2) := Fintype.ofFinite _

private noncomputable instance : DecidableEq (GaloisField 2 2) := Classical.decEq _

private theorem finrank_eq : Module.finrank (ZMod 2) (GaloisField 2 2) = 2 :=
  GaloisField.finrank 2 (by norm_num)

private noncomputable def b : Module.Basis (Fin 2) (ZMod 2) (GaloisField 2 2) :=
  Module.finBasisOfFinrankEq _ _ finrank_eq

-- Over `F₂ ⊆ F₄` (`k = 2`, `n = 4`), the substituted affine multiplier has degree at most
-- `n / q₀ = 2`.
example (α : Fin 3 → GaloisField 2 2) :
    (traceSubstitution b ((affineMultiplier α).map
      (algebraMap (GaloisField 2 2) (GaloisField 2 2)))).natDegree ≤ 2 := by
  exact (natDegree_traceSubstitution_map_affineMultiplier_le b α).trans_eq (by simp [ZMod.card])

-- The `4³ = 64` coefficient vectors over `F₄` give `64` distinct univariate multipliers.
example : Function.Injective fun α : Fin 3 → GaloisField 2 2 ↦
    traceSubstitution b ((affineMultiplier α).map
      (algebraMap (GaloisField 2 2) (GaloisField 2 2))) :=
  traceSubstitution_map_affineMultiplier_injective b

-- Coefficients over the subfield `F₂` are mapped into `F₄`: the `2³ = 8` vectors stay distinct.
example : Function.Injective fun α : Fin 3 → ZMod 2 ↦
    traceSubstitution b ((affineMultiplier α).map (algebraMap (ZMod 2) (GaloisField 2 2))) :=
  traceSubstitution_map_affineMultiplier_injective b

-- Over `F = F₂`, take `f(z) = z₀`, `g(z) = 1`, `M = X₁` and `P = X₀`.
-- The combined word is `z₀ + z₁`, and `P` agrees with it exactly where `z₁ = 0`.
-- That is `2` of the `4` grid points, so `P̃` has `2` agreements on `F₄`.
example :
    #(ReedSolomon.polynomialAgreementSet (ReedSolomon.algebraMapDomain _ _)
        (ReedSolomon.combinedWord (ReedSolomon.algebraMapDomain _ _)
          (fun x ↦ algebraMap (ZMod 2) (GaloisField 2 2) (traceCoordinateEquiv (ZMod 2) b x 0))
          (fun _ ↦ algebraMap (ZMod 2) (GaloisField 2 2) 1)
          (traceSubstitution b ((MvPolynomial.X 1 : MvPolynomial (Fin 2) (ZMod 2)).map
            (algebraMap (ZMod 2) (GaloisField 2 2)))))
        (traceSubstitution b ((MvPolynomial.X 0 : MvPolynomial (Fin 2) (ZMod 2)).map
          (algebraMap (ZMod 2) (GaloisField 2 2))))) = 2 := by
  rw [card_polynomialAgreementSet_traceSubstitution b (fun z ↦ z 0) (fun _ ↦ 1)]
  simp only [agreementSet, Fin.isValue, MvPolynomial.eval_X, gridPoint_apply,
    Algebra.algebraMap_self, RingHom.id_apply, combinedWord, mul_one, left_eq_add]
  decide

-- The same count with caller-supplied decidable equalities on `F` and `F'`.
example [DecidableEq (ZMod 2)] [DecidableEq (GaloisField 2 2)]
    (f g : (Fin 2 → ZMod 2) → ZMod 2) (M P : MvPolynomial (Fin 2) (ZMod 2)) :
    #(ReedSolomon.polynomialAgreementSet (ReedSolomon.algebraMapDomain _ _)
        (ReedSolomon.combinedWord (ReedSolomon.algebraMapDomain _ _)
          (fun x ↦ algebraMap (ZMod 2) (GaloisField 2 2) (f (traceCoordinateEquiv (ZMod 2) b x)))
          (fun x ↦ algebraMap (ZMod 2) (GaloisField 2 2) (g (traceCoordinateEquiv (ZMod 2) b x)))
          (traceSubstitution b (M.map (algebraMap (ZMod 2) (GaloisField 2 2)))))
        (traceSubstitution b (P.map (algebraMap (ZMod 2) (GaloisField 2 2))))) =
      #(agreementSet (combinedWord f g M) P) :=
  card_polynomialAgreementSet_traceSubstitution b f g M P

/-- info: 'ReedMuller.map_polynomialAgreementSet_traceSubstitution' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.map_polynomialAgreementSet_traceSubstitution

/-- info: 'ReedMuller.card_polynomialAgreementSet_traceSubstitution' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.card_polynomialAgreementSet_traceSubstitution

/-- info: 'ReedMuller.traceSubstitution_map_affineMultiplier' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.traceSubstitution_map_affineMultiplier

/-- info: 'ReedMuller.natDegree_traceSubstitution_map_affineMultiplier_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.natDegree_traceSubstitution_map_affineMultiplier_le

/-- info: 'ReedMuller.traceSubstitution_map_affineMultiplier_injective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.traceSubstitution_map_affineMultiplier_injective

/-- info: 'ReedSolomon.algebraMapDomain_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.algebraMapDomain_apply
