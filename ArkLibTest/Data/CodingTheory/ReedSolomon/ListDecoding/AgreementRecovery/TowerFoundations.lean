/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.AgreementRecovery.TowerCorrectness
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.AgreementRecovery.TowerEmbedding
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.AgreementRecovery.TowerBatch
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.TowerAlgebra.SplitZeroUnit
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Separable

/-! Executed zero-divisor and empty-piece checks for the Milestone 1 tower adapters. -/

namespace ArkLibTest.TowerFoundations
open CompPoly Polynomial
open ReedSolomon.ListDecoding ReedSolomon.ListDecoding.TowerAlgebra

private abbrev F := ZMod 3

private def G : CPolynomial F := CPolynomial.X * (CPolynomial.X - CPolynomial.C 1)

private theorem G_monic : G.toPoly.Monic := by
  simp only [G, CPolynomial.toPoly_mul, CPolynomial.toPoly_sub, CPolynomial.X_toPoly,
    CPolynomial.C_toPoly]
  exact Polynomial.monic_X.mul (Polynomial.monic_X_sub_C 1)

private theorem G_squarefree : Squarefree G.toPoly := by
  simp only [G, CPolynomial.toPoly_mul, CPolynomial.toPoly_sub, CPolynomial.X_toPoly,
    CPolynomial.C_toPoly]
  apply (Polynomial.separable_X.mul Polynomial.separable_X_sub_C ?_).squarefree
  exact ⟨1, -1, by simp⟩

private theorem G_degree : G.toPoly.degree = 2 := by
  simp only [G, CPolynomial.toPoly_mul, CPolynomial.toPoly_sub, CPolynomial.X_toPoly,
    CPolynomial.C_toPoly, Polynomial.degree_mul, Polynomial.degree_X, Polynomial.degree_X_sub_C]
  norm_num

private def family : FiniteRepresentation F := ⟨G, [CPolynomial.C 1]⟩

private theorem family_wellFormed : family.WellFormed 1 := by
  refine ⟨G_monic, G_squarefree, rfl, ?_⟩
  intro c hc
  obtain rfl : c = CPolynomial.C 1 := by simpa [family] using hc
  change (CPolynomial.C (1 : F)).toPoly.degree < G.toPoly.degree
  rw [CPolynomial.C_toPoly, G_degree]
  exact Polynomial.degree_C_le.trans_lt (by norm_num)

private def tower : TowerRepresentation (F := F) := TowerRepresentation.ofUnivariate family

private theorem tower_wellFormed : tower.WellFormed 1 :=
  TowerRepresentation.ofUnivariate_wellFormed family family_wellFormed (by
    rw [CPolynomial.natDegree_toPoly, Polynomial.natDegree_pos_iff_degree_pos]
    change 0 < G.toPoly.degree
    rw [G_degree]
    norm_num)

/-- The element U is a zero divisor: the U=0 component is zero, and U=1 is a unit component. -/
private def splitU := splitZeroUnit tower (CPolynomial.C CPolynomial.X) tower_wellFormed


/-- An identically zero residual yields no spurious unit piece. -/
private def splitZero := splitZeroUnit tower 0 tower_wellFormed


/-- A unit residual yields no spurious zero piece. -/
private def splitOne := splitZeroUnit tower 1 tower_wellFormed


/- Repeated moduli are legal batch inputs and preserve result order. -/

private def extensionG : CPolynomial F := CPolynomial.X ^ 2 + CPolynomial.C 1

private theorem extensionG_monic : extensionG.toPoly.Monic := by
  rw [extensionG, CPolynomial.toPoly_add, CPolynomial.toPoly_pow, CPolynomial.X_toPoly,
    CPolynomial.C_toPoly]
  exact Polynomial.monic_X_pow_add_C (n := 2) (a := (1 : F)) (by decide)

private theorem extensionG_squarefree : Squarefree extensionG.toPoly := by
  have hs : (Polynomial.X ^ 2 - Polynomial.C (-1 : F)).Separable :=
    Polynomial.separable_X_pow_sub_C (-1) (by decide) (by decide)
  simpa [extensionG, CPolynomial.toPoly_add, CPolynomial.toPoly_pow, CPolynomial.X_toPoly,
    CPolynomial.C_toPoly] using hs.squarefree

private theorem extensionG_degree : extensionG.toPoly.degree = 2 := by
  simp only [extensionG, CPolynomial.toPoly_add, CPolynomial.toPoly_pow, CPolynomial.X_toPoly,
    CPolynomial.C_toPoly]
  exact Polynomial.degree_X_pow_add_C (by omega) 1

private def extensionFamily : FiniteRepresentation F := ⟨extensionG, [CPolynomial.C 1]⟩

private theorem extensionFamily_wellFormed : extensionFamily.WellFormed 1 := by
  refine ⟨extensionG_monic, extensionG_squarefree, rfl, ?_⟩
  intro c hc
  obtain rfl : c = CPolynomial.C 1 := by simpa [extensionFamily] using hc
  change (CPolynomial.C (1 : F)).toPoly.degree < extensionG.toPoly.degree
  rw [CPolynomial.C_toPoly, extensionG_degree]
  exact Polynomial.degree_C_le.trans_lt (by norm_num)

private def extensionTower : TowerRepresentation (F := F) :=
  TowerRepresentation.ofUnivariate extensionFamily

private theorem extensionTower_wellFormed : extensionTower.WellFormed 1 :=
  TowerRepresentation.ofUnivariate_wellFormed extensionFamily extensionFamily_wellFormed (by
    rw [CPolynomial.natDegree_toPoly, Polynomial.natDegree_pos_iff_degree_pos]
    change 0 < extensionG.toPoly.degree
    rw [extensionG_degree]
    norm_num)

/- The base modulus has no F₃ roots: this family genuinely needs an extension-defined parameter. -/
example (u : F) : extensionG.toPoly.eval u ≠ 0 := by
  simp only [extensionG, CPolynomial.toPoly_add, CPolynomial.toPoly_pow,
    CPolynomial.X_toPoly, CPolynomial.C_toPoly, Polynomial.eval_add,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
  fin_cases u <;> decide


/- Nevertheless every geometric parameter represents the base-field constant one. -/
example {L : Type*} [Field L] (ι : F →+* L) (u v : L) :
    extensionTower.specialize ι u v = Polynomial.C 1 := by
  rw [extensionTower, TowerRepresentation.ofUnivariate_specialize]
  simp [FiniteRepresentation.specialize, extensionFamily,
    Polynomial.JetHornerMachine.coefficientPolynomial, CPolynomial.C_toPoly]


private def domain : Fin 2 ↪ F :=
  ⟨fun i => i.val, by
    intro i j hij
    apply Fin.ext
    have h := congrArg ZMod.val hij
    simpa [ZMod.val_natCast_of_lt (by omega : i.val < 3),
      ZMod.val_natCast_of_lt (by omega : j.val < 3)] using h⟩

private def packet : AgreementRecovery.Tower.Component F 1 :=
  ⟨extensionTower, extensionTower_wellFormed⟩

/- Duplicate extension-defined parameter families return one base-field message. -/

/- Full agreement testing rejects the represented constant if the requested threshold fails. -/

#print axioms AgreementRecovery.Tower.recoverAgreement_represented_exact
#print axioms AgreementRecovery.Tower.recoverAgreement_exact_of_coverage

/-- Executed by the compiled agreement recovery runtime suite. -/
def run : IO Unit := do
  unless (splitU.length == 2) do
    throw (IO.userError "tower foundation check 1 failed")
  unless ((splitU.map fun child => child.tag.isZero).contains true) do
    throw (IO.userError "tower foundation check 2 failed")
  unless ((splitU.map fun child => child.tag.isZero).contains false) do
    throw (IO.userError "tower foundation check 3 failed")
  unless ((splitU.map fun child => child.tower.dimension).sum == 2) do
    throw (IO.userError "tower foundation check 4 failed")
  unless (splitZero.length == 1) do
    throw (IO.userError "tower foundation check 5 failed")
  unless (splitZero.all fun child => child.tag.isZero) do
    throw (IO.userError "tower foundation check 6 failed")
  unless (splitOne.length == 1) do
    throw (IO.userError "tower foundation check 7 failed")
  unless (splitOne.all fun child => !child.tag.isZero) do
    throw (IO.userError "tower foundation check 8 failed")
  unless ((AgreementRecovery.TowerBatch.restrictBases .naive .remainderOnly
  (CPolynomial.C (CPolynomial.X ^ 2)) [G, G]).length == 2) do
    throw (IO.userError "tower foundation check 9 failed")
  unless ((splitZeroUnit extensionTower 0 extensionTower_wellFormed).length == 1) do
    throw (IO.userError "tower foundation check 10 failed")
  unless (((splitZeroUnit extensionTower 0 extensionTower_wellFormed).map
  fun child => child.tower.dimension).sum == 2) do
    throw (IO.userError "tower foundation check 11 failed")
  unless (AgreementRecovery.Tower.recoverAgreement (RingHom.id F) domain (fun _ => 1)
  1 2 [packet, packet] == [[1]]) do
    throw (IO.userError "tower foundation check 12 failed")
  unless (AgreementRecovery.Tower.recoverAgreement (RingHom.id F) domain (fun i => i.val)
  1 2 [packet] == []) do
    throw (IO.userError "tower foundation check 13 failed")

end ArkLibTest.TowerFoundations
