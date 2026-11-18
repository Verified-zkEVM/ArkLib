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
    (traceSubstitution b (affineMultiplier α)).natDegree ≤ 2 := by
  simpa [ZMod.card] using natDegree_traceSubstitution_affineMultiplier_le b α

-- The `4³ = 64` coefficient vectors give `64` distinct univariate multipliers.
example : Function.Injective fun α : Fin 3 → GaloisField 2 2 ↦
    traceSubstitution b (affineMultiplier α) :=
  traceSubstitution_affineMultiplier_injective b

-- A candidate keeps its number of agreements with the combined word.
example (f g : (Fin 2 → ZMod 2) → GaloisField 2 2) (α : Fin 3 → GaloisField 2 2)
    (P : MvPolynomial (Fin 2) (GaloisField 2 2)) :
    #(ReedSolomon.polynomialAgreementSet (traceDomain _ _)
        (ReedSolomon.combinedWord (traceDomain _ _) (fun x ↦ f (traceCoordinateEquiv (ZMod 2) b x))
          (fun x ↦ g (traceCoordinateEquiv (ZMod 2) b x))
          (traceSubstitution b (affineMultiplier α)))
        (traceSubstitution b P)) =
      #(agreementSet (combinedWord f g (affineMultiplier α)) P) :=
  card_polynomialAgreementSet_traceSubstitution b f g _ P

-- The same correspondence with a caller-supplied decidable equality on `F'`.
example [DecidableEq (GaloisField 2 2)] (f g : (Fin 2 → ZMod 2) → GaloisField 2 2)
    (M P F₀ G₀ : MvPolynomial (Fin 2) (GaloisField 2 2)) :
    #(ReedSolomon.agreementLoss (traceDomain _ _) (fun x ↦ f (traceCoordinateEquiv (ZMod 2) b x))
        (fun x ↦ g (traceCoordinateEquiv (ZMod 2) b x)) (traceSubstitution b M)
        (traceSubstitution b P) (traceSubstitution b F₀) (traceSubstitution b G₀)) =
      #(agreementLoss f g M P F₀ G₀) :=
  card_agreementLoss_traceSubstitution b f g M P F₀ G₀

-- Every grid point is an agreement of `P = 0` with the zero words, and so is every point of
-- `F₄`.
example :
    #(ReedSolomon.polynomialAgreementSet (traceDomain (GaloisField 2 2) (GaloisField 2 2))
        (ReedSolomon.combinedWord (traceDomain _ _) (fun _ ↦ 0) (fun _ ↦ 0)
          (traceSubstitution b (affineMultiplier 0)))
        (traceSubstitution b (0 : MvPolynomial (Fin 2) (GaloisField 2 2)))) = 4 := by
  rw [card_polynomialAgreementSet_traceSubstitution b (fun _ ↦ 0) (fun _ ↦ 0)]
  simp [agreementSet]

/-- info: 'ReedMuller.card_polynomialAgreementSet_traceSubstitution' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.card_polynomialAgreementSet_traceSubstitution

/-- info: 'ReedMuller.card_agreementLoss_traceSubstitution' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.card_agreementLoss_traceSubstitution

/-- info: 'ReedMuller.isLossWitness_traceSubstitution' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.isLossWitness_traceSubstitution

/-- info: 'ReedMuller.traceSubstitution_affineMultiplier_injective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.traceSubstitution_affineMultiplier_injective

/-- info: 'ReedMuller.traceDomain_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.traceDomain_apply

/-- info: 'ReedMuller.traceSubstitution_affineMultiplier' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.traceSubstitution_affineMultiplier

/-- info: 'ReedMuller.natDegree_traceSubstitution_affineMultiplier_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.natDegree_traceSubstitution_affineMultiplier_le

/-- info: 'ReedMuller.map_polynomialAgreementSet_traceSubstitution' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.map_polynomialAgreementSet_traceSubstitution

/-- info: 'ReedMuller.map_agreementLoss_traceSubstitution' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.map_agreementLoss_traceSubstitution
