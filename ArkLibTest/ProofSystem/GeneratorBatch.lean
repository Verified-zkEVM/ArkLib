/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ProofSystem.Component.PowerBatch
import Mathlib.Algebra.Field.ZMod

/-!
# Executable generator batching over a prime field

The honest family passes the quotient verifier for all power and affine seeds and all
verification points. The constant family `[-1, 0, 1]` is rejected at the zero affine seed.
-/

open CompPoly FiniteDomainQuotient CoreDefinitions OracleComp OracleSpec
open scoped NNReal ENNReal ProbabilityTheory

namespace ArkLibTest.GeneratorBatch

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private abbrev F := ZMod 5

private def points : Finset F := {0, 1}

private def domain : QuotientZeroTest.Domain F := QuotientZeroTest.finiteDomain F points

private def honestFamily (_ : Fin 3) : _root_.GeneratorBatch.Poly F 3 :=
  ⟨nodal points, by rw [nodal_toPoly, Lagrange.natDegree_nodal]; decide⟩

private def falseFamily (i : Fin 3) : _root_.GeneratorBatch.Poly F 3 :=
  ⟨CPolynomial.C (![(-1 : F), 0, 1] i), by simp⟩

private def affineStatement (family : Fin 3 → _root_.GeneratorBatch.Poly F 3)
    (seed : Fin 2 → F) : Unit × ∀ i, QuotientZeroTest.OStmtIn F 3 i :=
  _root_.GeneratorBatch.output F (Fin 2 → F) 3 3 (AffineSpaceGenerator F 2)
    (by decide) ((), family) seed

private def quotientTranscript (stmt : Unit × ∀ i, QuotientZeroTest.OStmtIn F 3 i)
    (z : F) : (QuotientZeroTest.pSpec F domain 3).FullTranscript :=
  fun | ⟨0, _⟩ => quotient points (stmt.2 ())
      | ⟨1, _⟩ => z

run_cmd do
  for a in List.finRange 5 do
    let stmt := _root_.PowerBatch.output F 3 3 (by decide) ((), honestFamily) (a.val : F)
    for z in List.finRange 5 do
      unless decide (QuotientZeroTest.check F domain 3 stmt
          (quotientTranscript stmt (z.val : F))) do
        throwError "An honest power batch failed the quotient verifier."
  for a in List.finRange 5 do
    for b in List.finRange 5 do
      let seed : Fin 2 → F := ![(a.val : F), (b.val : F)]
      let stmt := affineStatement honestFamily seed
      for z in List.finRange 5 do
        unless decide (QuotientZeroTest.check F domain 3 stmt
            (quotientTranscript stmt (z.val : F))) do
          throwError "An honest affine batch failed the quotient verifier."
  let stmt := affineStatement falseFamily 0
  if decide (QuotientZeroTest.check F domain 3 stmt (quotientTranscript stmt 0)) then
    throwError "The false affine batch was accepted at a domain point."

example {ι : Type} (oSpec : OracleSpec ι) :
    (QuotientZeroTest.oracleVerifier F domain 3 oSpec).toVerifier.verify
      (affineStatement falseFamily 0)
      (quotientTranscript (affineStatement falseFamily 0) 0) =
      failure := by
  rw [QuotientZeroTest.oracleVerifier_toVerifier, ite_eq_right (by decide +kernel)]

/-- The affine component accepts the existing zero-evasion certificate through the generic API. -/
example {ι σ : Type} (oSpec : OracleSpec ι) (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) :
    (_root_.GeneratorBatch.oracleVerifier F (Fin 2 → F) 3 3 (AffineSpaceGenerator F 2)
      (by decide) oSpec).toVerifier.rbrKnowledgeSoundnessWorstCase init impl
      (_root_.GeneratorBatch.relIn F domain 3 3) (_root_.GeneratorBatch.relOut F domain 3)
      (fun _ => unitInterval.toNNReal (cappedError (1 / Fintype.card F))) :=
  _root_.GeneratorBatch.oracleVerifier_rbrKnowledgeSoundnessWorstCase F (Fin 2 → F)
    domain 3 3 (AffineSpaceGenerator F 2) (by decide) oSpec init impl _
    (isZeroEvadingGenerator_affineSpaceGenerator 2)

/-- The tensor instance's raw error remains usable without a dimension/cardinality restriction. -/
example {ι σ : Type} (oSpec : OracleSpec ι) (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) :
    (_root_.GeneratorBatch.oracleVerifier F (Fin 6 → F) 3 (2 ^ 6)
      (multilinearGenerator F 6) (by decide) oSpec).toVerifier.rbrKnowledgeSoundnessWorstCaseWith
      init impl
      (_root_.GeneratorBatch.relIn F domain 3 (2 ^ 6))
      (_root_.GeneratorBatch.relOut F domain 3) (fun _ => Unit)
      (_root_.GeneratorBatch.rbrExtractor F (Fin 6 → F) 3 (2 ^ 6) oSpec)
      (_root_.GeneratorBatch.knowledgeStateFunction F (Fin 6 → F) domain 3 (2 ^ 6)
        (multilinearGenerator F 6) (by decide) oSpec init impl)
      (fun _ => (6 : ℝ≥0) / 5) := by
  apply _root_.GeneratorBatch.oracleVerifier_rbrKnowledgeSoundnessWorstCaseWith_of_prob_le
  intro v hv
  simpa only [ENNReal.coe_div (by norm_num : (5 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat,
    ZMod.card, Nat.cast_ofNat] using prob_dotProduct_multilinearGenerator_eq_zero_le 6 v hv

end ArkLibTest.GeneratorBatch
