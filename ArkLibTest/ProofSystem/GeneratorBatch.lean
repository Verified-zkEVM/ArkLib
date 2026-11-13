/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ProofSystem.Component.GeneratorBatch
import ArkLib.Data.CodingTheory.ProximityGenerator.ZeroEvading
import ArkLib.OracleReduction.Composition.Sequential.GuardedRoundByRound
import ArkLib.OracleReduction.Composition.Sequential.GuardedNary
import Mathlib.Algebra.Field.ZMod

/-!
# Executable generator batching over a prime field

The honest family passes the quotient verifier for all power and affine seeds and all
verification points. The constant family `[-1, 0, 1]` is rejected at the zero affine seed.
Power weights hide this false family at exactly two seeds, realizing the `2/5` error. The power
instance also exercises empty batches, verifier materialization and guarded composition
with the quotient zero test.
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
    let stmt := _root_.GeneratorBatch.output F F 3 3 (powerBatchGenerator F 3)
      (by decide) ((), honestFamily) (a.val : F)
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
      (by decide) oSpec).toVerifier.rbrKnowledgeSoundness init impl
      (_root_.GeneratorBatch.relIn F domain 3 3) (_root_.GeneratorBatch.relOut F domain 3)
      (fun _ => unitInterval.toNNReal (cappedError (1 / Fintype.card F))) :=
  _root_.GeneratorBatch.oracleVerifier_rbrKnowledgeSoundness F (Fin 2 → F)
    domain 3 3 (AffineSpaceGenerator F 2) (by decide) oSpec init impl _
    (isZeroEvadingGenerator_affineSpaceGenerator 2)

/-- The tensor instance's raw error remains usable without a dimension/cardinality restriction. -/
example {ι σ : Type} (oSpec : OracleSpec ι) (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) :
    (_root_.GeneratorBatch.oracleVerifier F (Fin 6 → F) 3 (2 ^ 6)
      (multilinearGenerator F 6) (by decide) oSpec).toVerifier.rbrKnowledgeSoundnessWith
      init impl
      (_root_.GeneratorBatch.relIn F domain 3 (2 ^ 6))
      (_root_.GeneratorBatch.relOut F domain 3) (fun _ => Unit)
      (_root_.GeneratorBatch.rbrExtractor F (Fin 6 → F) 3 (2 ^ 6) oSpec)
      (_root_.GeneratorBatch.knowledgeStateFunction F (Fin 6 → F) domain 3 (2 ^ 6)
        (multilinearGenerator F 6) (by decide) oSpec init impl)
      (fun _ => (6 : ℝ≥0) / 5) := by
  apply _root_.GeneratorBatch.oracleVerifier_rbrKnowledgeSoundnessWith_of_prob_le
  intro v hv
  simpa only [ENNReal.coe_div (by norm_num : (5 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat,
    ZMod.card, Nat.cast_ofNat] using prob_dotProduct_multilinearGenerator_eq_zero_le 6 v hv

private def honestStatement : Unit × ∀ i, _root_.GeneratorBatch.OStmtIn F 3 3 i :=
  ((), honestFamily)

private def honestTranscript : (_root_.GeneratorBatch.pSpec F).FullTranscript :=
  fun | ⟨0, _⟩ => (2 : F)

private def hidingChallenges : Finset F :=
  Finset.univ.filter fun α =>
    ∀ z ∈ points, eval (_root_.GeneratorBatch.batch (by decide : 0 < 3)
      falseFamily (powerBatchGenerator F 3 α)) z = 0

example : ∀ α : F, ∀ z ∈ points,
    eval (_root_.GeneratorBatch.batch (by decide : 0 < 3)
      honestFamily (powerBatchGenerator F 3 α)) z = 0 := by
  decide +kernel

example : hidingChallenges = {1, -1} := by decide +kernel

example : hidingChallenges.card = 2 := by decide +kernel

example : eval (_root_.GeneratorBatch.batch (by decide : 0 < 3)
    falseFamily (powerBatchGenerator F 3 0)) 0 = -1 := by
  decide +kernel

run_cmd do
  for a in List.finRange 5 do
    let α : F := a.val
    for z in [(0 : F), 1] do
      unless eval (_root_.GeneratorBatch.batch (by decide : 0 < 3)
          honestFamily (powerBatchGenerator F 3 α)) z == 0 do
        throwError "An honest batch must vanish on the domain."
  unless hidingChallenges == {1, -1} do
    throwError "The false family must have exactly two hiding challenges."
  unless eval (_root_.GeneratorBatch.batch (by decide : 0 < 3)
      falseFamily (powerBatchGenerator F 3 0)) 0 == -1 do
    throwError "Challenge zero must expose the false constant family."
  unless eval (_root_.GeneratorBatch.batch (by decide : 0 < 3)
      falseFamily (powerBatchGenerator F 3 2)) 3 == 3 do
    throwError "Virtual evaluation must compute minus one plus the challenge squared."

example :
    Pr{let α ← $ᵗ F}[Polynomial.ZeroOn points
      (Polynomial.powerBatch (fun i => (falseFamily i).val.toPoly) α)] ≤
      (2 : ℝ≥0∞) / 5 := by
  have hfalse : ¬ ∀ i, Polynomial.ZeroOn points (falseFamily i).val.toPoly := by
    intro h
    have hzero := h 0 0 (by decide)
    simp [falseFamily] at hzero
  have h := Polynomial.prob_zeroOn_generatorBatch_le (powerBatchGenerator F 3)
    (isZeroEvadingGenerator_powerBatchGenerator 3) hfalse
  change Pr{let α ← $ᵗ F}[Polynomial.ZeroOn points
    (Polynomial.powerBatch (fun i => (falseFamily i).val.toPoly) α)] ≤ _ at h
  norm_num [F, cappedError, ENNReal.ofReal_div_of_pos] at h
  exact h

example {ι σ : Type} (oSpec : OracleSpec ι) (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) :
    (_root_.GeneratorBatch.oracleVerifier F F 3 3 (powerBatchGenerator F 3)
      (by decide) oSpec).toVerifier
      |>.rbrKnowledgeSoundness init impl (_root_.GeneratorBatch.relIn F domain 3 3)
        (_root_.GeneratorBatch.relOut F domain 3) (fun _ => (2 : ℝ≥0) / 5) := by
  have h := _root_.GeneratorBatch.oracleVerifier_rbrKnowledgeSoundness F F
    domain 3 3 (powerBatchGenerator F 3) (by decide) oSpec init impl _
    (isZeroEvadingGenerator_powerBatchGenerator 3)
  norm_num [F, cappedError, unitInterval.toNNReal] at h
  exact h

example {ι : Type} (oSpec : OracleSpec ι) :
    (_root_.GeneratorBatch.oracleVerifier F F 3 3 (powerBatchGenerator F 3)
      (by decide) oSpec).toVerifier.verify
      honestStatement honestTranscript =
      pure (_root_.GeneratorBatch.output F F 3 3 (powerBatchGenerator F 3)
        (by decide) honestStatement 2) :=
  _root_.GeneratorBatch.oracleVerifier_toVerifier F F 3 3 (powerBatchGenerator F 3)
    (by decide) oSpec _ _

example : _root_.GeneratorBatch.relOut F domain 3 = QuotientZeroTest.relIn F domain 3 :=
  _root_.GeneratorBatch.relOut_eq_quotient_relIn F domain 3

example (α : F) :
    eval (_root_.GeneratorBatch.batch (by decide : 0 < 1)
      (fun i : Fin 0 => Fin.elim0 i) (powerBatchGenerator F 0 α)) 0 = 0 := by
  simp [eval, CPolynomial.eval_horner_eq_eval,
    CPolynomial.eval_toPoly]

namespace Composition

variable (F : Type) [Field F] [DecidableEq F] (D : QuotientZeroTest.Domain F) (d k : ℕ)

private def oracleIndex : Fin 3 → Type
  | 0 => Fin k
  | 1 => Unit
  | 2 => Empty

private def oracleStatement : (i : Fin 3) → oracleIndex k i → Type
  | 0 => _root_.GeneratorBatch.OStmtIn F d k
  | 1 => QuotientZeroTest.OStmtIn F d
  | 2 => QuotientZeroTest.OStmtOut

private instance : ∀ i j, OracleInterface (oracleStatement F d k i j)
  | 0 => fun _ => inferInstanceAs (OracleInterface (_root_.GeneratorBatch.Poly F d))
  | 1 => fun _ => inferInstanceAs (OracleInterface (FiniteDomainQuotient.Poly F d))
  | 2 => QuotientZeroTest.instOracleInterfaceOStmtOut

private abbrev rounds : Fin 2 → ℕ
  | 0 => 1
  | 1 => 2

private def protocol : (i : Fin 2) → ProtocolSpec (rounds i)
  | 0 => _root_.GeneratorBatch.pSpec F
  | 1 => QuotientZeroTest.pSpec F D d

private instance : ∀ i j, OracleInterface ((protocol F D d i).Message j)
  | 0 => _root_.GeneratorBatch.instOracleInterfaceMessagePSpec F
  | 1 => QuotientZeroTest.instOracleInterfaceMessagePSpec F D d

private instance [SampleableType F] : ∀ i j, SampleableType ((protocol F D d i).Challenge j)
  | 0 => _root_.GeneratorBatch.instSampleableTypeChallengePSpec F
  | 1 => QuotientZeroTest.instSampleableTypeChallengePSpec F D d

private def relation : (i : Fin 3) → Set ((Unit × ∀ j, oracleStatement F d k i j) × Unit)
  | 0 => _root_.GeneratorBatch.relIn F D d k
  | 1 => QuotientZeroTest.relIn F D d
  | 2 => QuotientZeroTest.relOut

variable (hd : 0 < d) {ι : Type} (oSpec : OracleSpec ι)

private def verifier : (i : Fin 2) → OracleVerifier oSpec Unit
    (oracleStatement F d k i.castSucc) Unit (oracleStatement F d k i.succ)
    (protocol F D d i)
  | 0 => _root_.GeneratorBatch.oracleVerifier F F d k (powerBatchGenerator F k) hd oSpec
  | 1 => QuotientZeroTest.oracleVerifier F D d oSpec

private def guards : ∀ i, (verifier F D d k hd oSpec i).toVerifier.GuardedForm
  | 0 => _root_.GeneratorBatch.guardedForm F F d k (powerBatchGenerator F k) hd oSpec
  | 1 => QuotientZeroTest.guardedForm F D d oSpec

/-- Per-challenge bounds are mathematical views using noncomputable real division. -/
private noncomputable def challengeError [Fintype F] :
    (i : Fin 2) → (protocol F D d i).ChallengeIdx → ℝ≥0
  | 0 => fun _ => ((k - 1 : ℕ) : ℝ≥0) / Fintype.card F
  | 1 => fun _ => (d : ℝ≥0) / Fintype.card F

variable [Fintype F] [SampleableType F]
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- The actual batching and quotient oracle verifiers compose their named guarded certificates. -/
theorem composedCertificate (hcard : D.points.card ≤ d) :
    (OracleVerifier.seqCompose (fun _ : Fin 3 => Unit) (oracleStatement F d k)
      (verifier F D d k hd oSpec)).toVerifier.rbrKnowledgeSoundness init impl
      (_root_.GeneratorBatch.relIn F D d k) QuotientZeroTest.relOut
      (fun i =>
        let ij := ProtocolSpec.seqComposeChallengeIdxToSigma i
        challengeError F D d k ij.1 ij.2) := by
  apply OracleVerifier.seqCompose_rbrKnowledgeSoundness_of_guarded
    (fun _ : Fin 3 => Unit) (oracleStatement F d k) (fun _ => Unit)
    (relation F D d k) (verifier F D d k hd oSpec) (guards F D d k hd oSpec)
    (challengeError F D d k)
  intro i
  fin_cases i
  · refine ⟨_, _root_.GeneratorBatch.rbrExtractor F F d k oSpec,
      _root_.GeneratorBatch.knowledgeStateFunction F F D d k (powerBatchGenerator F k)
        hd oSpec init impl, ?_⟩
    apply _root_.GeneratorBatch.oracleVerifier_rbrKnowledgeSoundnessWith_of_prob_le
    intro v hv
    change _ ≤ ((((k - 1 : ℕ) : ℝ≥0) / Fintype.card F : ℝ≥0) : ℝ≥0∞)
    simpa only [ENNReal.coe_div (by simp : (Fintype.card F : ℝ≥0) ≠ 0),
      ENNReal.coe_natCast] using prob_dotProduct_powerBatchGenerator_eq_zero_le v hv
  · exact QuotientZeroTest.oracleVerifier_rbrKnowledgeSoundness
      F D d oSpec init impl hcard

omit [DecidableEq F] [SampleableType F] in
/-- The quotient uses the inclusive degree bound, contributing `d / |F|` to the total error. -/
theorem composedChallengeError :
    (∑ i : (ProtocolSpec.seqCompose (protocol F D d)).ChallengeIdx,
      let ij := ProtocolSpec.seqComposeChallengeIdxToSigma i
      challengeError F D d k ij.1 ij.2) =
      ((k - 1 : ℕ) : ℝ≥0) / Fintype.card F + (d : ℝ≥0) / Fintype.card F := by
  rw [ProtocolSpec.sum_seqComposeChallengeIdxToSigma]
  rw [Fin.sum_univ_two]
  have hbatch : (Finset.univ : Finset (protocol F D d 0).ChallengeIdx).card = 1 := by
    change (Finset.univ : Finset {i : Fin 1 //
      (!v[.V_to_P] : Fin 1 → Direction) i = .V_to_P}).card = 1
    decide
  have hquotient : (Finset.univ : Finset (protocol F D d 1).ChallengeIdx).card = 1 := by
    change (Finset.univ : Finset {i : Fin 2 //
      (!v[.P_to_V, .V_to_P] : Fin 2 → Direction) i = .V_to_P}).card = 1
    decide
  simp only [challengeError, Finset.sum_const, nsmul_eq_mul]
  rw [hbatch, hquotient]
  simp

/-- Guarded composition gives ordinary knowledge soundness with both challenge errors. -/
theorem composedKnowledgeSoundness (hcard : D.points.card ≤ d) :
    (OracleVerifier.seqCompose (fun _ : Fin 3 => Unit) (oracleStatement F d k)
      (verifier F D d k hd oSpec)).knowledgeSoundness init impl
      (_root_.GeneratorBatch.relIn F D d k) QuotientZeroTest.relOut
      (((k - 1 : ℕ) : ℝ≥0) / Fintype.card F + (d : ℝ≥0) / Fintype.card F) := by
  have h := OracleVerifier.knowledgeSoundness_of_rbrKnowledgeSoundness_of_guarded
    (OracleVerifier.seqComposeGuardedForm (fun _ : Fin 3 => Unit) (oracleStatement F d k)
      (guards F D d k hd oSpec))
    (composedCertificate F D d k hd oSpec init impl hcard)
  rw [composedChallengeError] at h
  exact h

end Composition

end ArkLibTest.GeneratorBatch

/--
info: 'ArkLibTest.GeneratorBatch.Composition.composedKnowledgeSoundness' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ArkLibTest.GeneratorBatch.Composition.composedKnowledgeSoundness
