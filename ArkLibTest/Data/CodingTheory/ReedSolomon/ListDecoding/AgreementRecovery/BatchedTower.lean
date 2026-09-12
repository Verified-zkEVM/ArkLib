/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.AgreementRecovery.BatchedTowerCorrectness
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.AgreementRecovery.TowerEmbedding
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.TowerAlgebra.Normalization
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Separable

/-! Executable checks for product-tree batching in the live tower recovery path. -/

namespace ArkLibTest.BatchedTower

open CompPoly CompPoly.CPolynomial Polynomial
open ReedSolomon.ListDecoding ReedSolomon.ListDecoding.AgreementRecovery

private abbrev F := ZMod 3

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

private def packet : AgreementRecovery.Tower.Component F 1 :=
  ⟨extensionTower, extensionTower_wellFormed⟩

private def domain : Fin 2 ↪ F :=
  ⟨fun i => i.val, by
    intro i j hij
    apply Fin.ext
    have h := congrArg ZMod.val hij
    simpa [ZMod.val_natCast_of_lt (by omega : i.val < 3),
      ZMod.val_natCast_of_lt (by omega : j.val < 3)] using h⟩

private def allOnes : Fin 2 → F := fun _ => 1

private def duplicateLive :
    List (ComponentScan.Block (AgreementRecovery.Tower.Component F 1) (Fin 2)) :=
  [⟨packet, []⟩, ⟨packet, []⟩]

/-- The first row really sends one common residual through a product tree containing duplicate
base moduli; both live components then record their first agreement. -/
private def afterFirst := AgreementRecovery.BatchedTower.advanceFamily
  (.naive : MulContext F) (.remainderOnly : ModContext F)
  (RingHom.id F) domain allOnes 1 packet (0 : Fin 2) duplicateLive

/-- With `k = 1`, the second row exercises early stopping: neither retained block consumes a new
batch remainder or sample position. -/
private def afterSecond := AgreementRecovery.BatchedTower.advanceFamily
  (.naive : MulContext F) (.remainderOnly : ModContext F)
  (RingHom.id F) domain allOnes 1 packet (1 : Fin 2) afterFirst

/-- A genuine two-point fiber whose stored constant coefficient is the fiber variable `V`.
Splitting the residual `V` produces the distinct fibers `V` and `V - 1` over the same base. -/
private def rawBranchingFiber : CPolynomial (CPolynomial F) :=
  CPolynomial.X * (CPolynomial.X - CPolynomial.C 1)

private def branchingFiber : CPolynomial (CPolynomial F) :=
  TowerRepresentation.reduceBase CPolynomial.X rawBranchingFiber

private def branchingTower : TowerRepresentation (F := F) where
  modulus := CPolynomial.X
  fiber := branchingFiber
  coefficients :=
    [TowerRepresentation.reduceElement CPolynomial.X branchingFiber CPolynomial.X,
      TowerRepresentation.reduceElement CPolynomial.X branchingFiber 0]

private theorem branchingTower_wellFormed : branchingTower.WellFormed 2 := by
  have hbaseMonic : (CPolynomial.X : CPolynomial F).monic := by
    rw [CPolynomial.monic_toPoly_iff, CPolynomial.X_toPoly]
    exact Polynomial.monic_X
  have hbasePos : 0 < (CPolynomial.X : CPolynomial F).natDegree := by
    rw [CPolynomial.natDegree_toPoly, CPolynomial.X_toPoly, Polynomial.natDegree_X]
    exact Nat.zero_lt_one
  have hrawMonic : rawBranchingFiber.monic := by
    rw [CPolynomial.monic_toPoly_iff]
    simpa [rawBranchingFiber, CPolynomial.toPoly_mul, CPolynomial.toPoly_sub,
      CPolynomial.X_toPoly, CPolynomial.C_toPoly] using
      (Polynomial.monic_X.mul (Polynomial.monic_X_sub_C (1 : CPolynomial F)))
  have hfiberMonic : branchingFiber.monic := by
    exact TowerRepresentation.monic_reduceBase hbaseMonic hbasePos hrawMonic
  have hfiberPos : 0 < branchingFiber.natDegree := by
    rw [branchingFiber, ReedSolomon.ListDecoding.TowerAlgebra.natDegree_reduceBase
      CPolynomial.X hbaseMonic hbasePos rawBranchingFiber hrawMonic]
    rw [CPolynomial.natDegree_toPoly]
    simp only [rawBranchingFiber, CPolynomial.toPoly_mul, CPolynomial.toPoly_sub,
      CPolynomial.X_toPoly, CPolynomial.C_toPoly]
    rw [Polynomial.Monic.natDegree_mul Polynomial.monic_X
      (Polynomial.monic_X_sub_C (1 : CPolynomial F))]
    simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_⟩
  · exact hbaseMonic
  · simpa [branchingTower, CPolynomial.X_toPoly] using
      (Polynomial.irreducible_X (R := F)).squarefree
  · exact hbasePos
  · exact hfiberMonic
  · exact hfiberPos
  · exact TowerRepresentation.baseReduced_reduceBase hbaseMonic rawBranchingFiber
  · intro K _ ι u hu
    have hsep : Squarefree ((Polynomial.X : K[X]) * (Polynomial.X - Polynomial.C 1)) := by
      apply (Polynomial.separable_X.mul Polynomial.separable_X_sub_C ?_).squarefree
      exact ⟨1, -1, by simp⟩
    rw [branchingTower, branchingFiber, TowerRepresentation.reduceBase,
      FirstOrderNormDecoder.D5.specialize_reduceFiberCoefficients ι u hbaseMonic hu]
    simpa [rawBranchingFiber, FirstOrderNormDecoder.D5.specializeFiberCPolynomial,
      CPolynomial.toPoly_mul, CPolynomial.toPoly_sub, CPolynomial.X_toPoly,
      CPolynomial.C_toPoly] using hsep
  · intro coefficient hc
    simp only [branchingTower, List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact TowerRepresentation.elementReduced_reduceElement hbaseMonic hfiberMonic
        hfiberPos CPolynomial.X
    · rcases hc with rfl | hc
      · exact TowerRepresentation.elementReduced_reduceElement hbaseMonic hfiberMonic hfiberPos 0
      · contradiction

private def branchingPacket : AgreementRecovery.Tower.Component F 2 :=
  ⟨branchingTower, branchingTower_wellFormed⟩

/-- The nonzero source residual `V` splits into two live descendants with a repeated base modulus
and genuinely different fibers. -/
private def fiberBranches :
    List (ComponentScan.Block (AgreementRecovery.Tower.Component F 2) (Fin 2)) :=
  (AgreementRecovery.BatchedTower.splitWithResidual 2 branchingPacket CPolynomial.X).map
    fun child => ⟨child.2, []⟩

/-- A real batched row over the two distinct fiber branches. Reduction modulo `V` records an
agreement, while reduction modulo `V - 1` records a rejection. -/
private def afterFiberBatch := AgreementRecovery.BatchedTower.advanceFamily
  (.naive : MulContext F) (.remainderOnly : ModContext F)
  (RingHom.id F) domain (fun _ => 0) 2 branchingPacket (1 : Fin 2) fiberBranches

/- The base modulus has no F₃ roots, so successful recovery genuinely covers extension-only
parameter roots. -/
example (u : F) : extensionG.toPoly.eval u ≠ 0 := by
  simp only [extensionG, CPolynomial.toPoly_add, CPolynomial.toPoly_pow,
    CPolynomial.X_toPoly, CPolynomial.C_toPoly, Polynomial.eval_add,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
  fin_cases u <;> decide

/- The batching layer keys only on base moduli. Thus two live branches with the same base modulus
but different fiber moduli occupy two repeated product-tree leaves and keep independent local
fiber reductions. -/
example (a b : AgreementRecovery.Tower.Component F 1)
    (hmod : a.val.modulus = b.val.modulus) (_hfiber : a.val.fiber ≠ b.val.fiber) :
    AgreementRecovery.BatchedTower.liveModuli 1
      ([⟨a, []⟩, ⟨b, []⟩] :
        List (ComponentScan.Block (AgreementRecovery.Tower.Component F 1) (Fin 2))) =
      [a.val.modulus, a.val.modulus] := by
  simp [AgreementRecovery.BatchedTower.liveModuli, hmod]

#print axioms AgreementRecovery.BatchedTower.recoverAgreement_represented_exact
#print axioms AgreementRecovery.BatchedTower.mem_recoverAgreement_iff_tower
#print axioms AgreementRecovery.BatchedTower.recoverAgreement_exact_of_coverage

/-- Runtime checks for duplicate live moduli, empty batches, early stopping, extension-only roots,
deduplication, and final agreement rejection. -/
def run : IO Unit := do
  unless (AgreementRecovery.BatchedTower.liveModuli 1 duplicateLive ==
      [extensionG, extensionG]) do
    throw (IO.userError "batched tower check 1 failed: duplicate live moduli")
  unless ((AgreementRecovery.BatchedTower.advanceFamily
      (.naive : MulContext F) (.remainderOnly : ModContext F)
      (RingHom.id F) domain allOnes 1 packet (0 : Fin 2) []).isEmpty) do
    throw (IO.userError "batched tower check 2 failed: empty batch")
  unless (afterFirst.length == 2) do
    throw (IO.userError "batched tower check 3 failed: live component count")
  unless (afterFirst.all fun block => block.positions.length == 1) do
    throw (IO.userError "batched tower check 4 failed: first agreement")
  unless (afterSecond.map (fun block => block.positions) ==
      afterFirst.map (fun block => block.positions)) do
    throw (IO.userError "batched tower check 5 failed: early stopping")
  unless (AgreementRecovery.BatchedTower.recoverAgreementDefault
      (RingHom.id F) domain allOnes 1 2 [packet] == [[1]]) do
    throw (IO.userError "batched tower check 6 failed: extension-only root recovery")
  unless (AgreementRecovery.BatchedTower.recoverAgreementDefault
      (RingHom.id F) domain allOnes 1 2 [packet, packet] == [[1]]) do
    throw (IO.userError "batched tower check 7 failed: output deduplication")
  unless (AgreementRecovery.BatchedTower.recoverAgreementDefault
      (RingHom.id F) domain (fun i => i.val) 1 2 [packet] == []) do
    throw (IO.userError "batched tower check 8 failed: final agreement rejection")
  unless (fiberBranches.length == 2 &&
      (fiberBranches.map fun block => block.component.val.fiber).dedup.length == 2) do
    throw (IO.userError "batched tower check 9 failed: distinct live fiber branches")
  unless (AgreementRecovery.BatchedTower.liveModuli 2 fiberBranches ==
      [CPolynomial.X, CPolynomial.X]) do
    throw (IO.userError "batched tower check 10 failed: repeated base for distinct fibers")
  unless (afterFiberBatch.map (fun block => block.positions.length) == [1, 0]) do
    throw (IO.userError "batched tower check 11 failed: branch-local fiber reductions")

end ArkLibTest.BatchedTower
