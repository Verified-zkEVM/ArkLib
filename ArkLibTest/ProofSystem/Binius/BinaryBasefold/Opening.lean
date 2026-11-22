/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao, Alexander Hicks
-/
import ArkLib.ProofSystem.Binius.BinaryBasefold.Opening
import ArkLib.ProofSystem.RingSwitching.Packing.Compatibility
import Mathlib.FieldTheory.Finite.GaloisField

/-! Acceptance controls for the Binary Basefold multilinear opening. -/

open OracleSpec OracleComp ProtocolSpec AdditiveNTT MvPolynomial
open Binius.BinaryBasefold RingSwitching Sumcheck.Structured Binius.BinaryBasefold.Opening
open scoped NNReal
noncomputable section
namespace BbfOpeningControls

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L]
  [SampleableType L]
variable (K : Type) [Field K] [Fintype K] [DecidableEq K]
  [Fact (Fintype.card K = 2)] [Algebra K L]
local instance [Finite K] : Fact (Nat.Prime (ringChar K)) := ⟨CharP.prime_ringChar K⟩

variable (β : Fin r → L) [Fact (LinearIndependent K β)] [Fact (β 0 = 1)]
variable {ℓ R ϑ : ℕ} [NeZero ℓ] [NeZero R] [NeZero ϑ]
  {h_rate : ℓ + R < r} [Fact (ϑ ∣ ℓ)]

omit [SampleableType L] [DecidableEq K] [Fact (β 0 = 1)] [NeZero R] in
theorem honest_input (t : MultilinearPoly L ℓ) (point : Fin ℓ → L) :
    ((⟨point, t.val.eval point⟩,
        honestInitialOracleStatement K β ϑ (h_ℓ_add_R_rate := h_rate) t), ⟨t⟩) ∈
      (abstractInput K β (ϑ := ϑ) (h_rate := h_rate)).toStrictRelInput := by
  exact ⟨rfl, abstractInput_strictInitialCompatibility_honest K β t⟩

def nonconstantSource : MultilinearPoly L ℓ :=
  ⟨MvPolynomial.X 0, (mem_restrictDegree_iff_degreeOf_le _ _).mpr (fun i => degreeOf_X_le i 0)⟩

omit [SampleableType L] [Fintype L] [DecidableEq L] in
theorem nonconstantSource_ne_zero : nonconstantSource (L := L) (ℓ := ℓ) ≠ 0 := by
  intro h
  have hx := congrArg Subtype.val h
  change MvPolynomial.X (0 : Fin ℓ) = (0 : MvPolynomial (Fin ℓ) L) at hx
  exact MvPolynomial.X_ne_zero (R := L) (0 : Fin ℓ) hx

omit [SampleableType L] [Fintype L] [DecidableEq L] in
theorem nonconstantSource_evaluations :
    (nonconstantSource (L := L) (ℓ := ℓ)).val.eval (fun _ => 0) = 0 ∧
      (nonconstantSource (L := L) (ℓ := ℓ)).val.eval (fun _ => 1) = 1 := by
  simp [nonconstantSource]

omit [SampleableType L] [DecidableEq K] [Fact (β 0 = 1)] [NeZero R] in
theorem false_zero_claim_no_witness (point : Fin ℓ → L)
    (w : WitMLP L ℓ) :
    ((⟨point, 1⟩, honestInitialOracleStatement K β ϑ
      (h_ℓ_add_R_rate := h_rate) (0 : MultilinearPoly L ℓ)), w) ∉
      (abstractInput K β (ϑ := ϑ) (h_rate := h_rate)).toRelInput := by
  rintro ⟨heval, hcompat⟩
  have hzero := firstOracleWitnessConsistent_getFirstOracle_honestInitialOracleStatement K β ϑ
    (h_ℓ_add_R_rate := h_rate) (0 : MultilinearPoly L ℓ)
  have ht := firstOracleWitnessConsistent_functional K β _ _ _ hcompat hzero
  change w.t = 0 at ht
  change 1 = w.t.val.eval point at heval
  rw [ht] at heval
  simp at heval

theorem honest_probability (γ : ℕ) (t : MultilinearPoly L ℓ) (point : Fin ℓ → L)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    let R := OracleReduction.toReduction (Oₛₒ := fun i : Empty => nomatch i)
      (openingReduction K β id mlpWitnessEquiv γ (ϑ := ϑ) (h_rate := h_rate))
    let pSpec := (!p[] : ProtocolSpec 0) ++ₚ fullPSpec K β γ (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_rate)
    let pImpl : QueryImpl ([]ₒ + [pSpec.Challenge]ₒ'challengeOracleInterface)
      (StateT σ ProbComp) := QueryImpl.addLift impl challengeQueryImpl
    Pr{let out ← OptionT.mk do
      let st ← init
      (simulateQ pImpl (R.run ((⟨point, t.val.eval point⟩ : MLPEvalStatement L ℓ),
        honestInitialOracleStatement K β ϑ (h_ℓ_add_R_rate := h_rate) t)
        (⟨t⟩ : WitMLP L ℓ)).run).run' st}[
          (out.2, out.1.2.2) ∈ acceptRejectOracleRel ∧ out.1.2.1 = out.2] = 1 := by
  have h := openingReduction_perfectCompleteness K β id mlpWitnessEquiv γ init impl (ϑ := ϑ)
    (h_rate := h_rate)
  change Reduction.perfectCompleteness init impl
    (strictInputRelation K β id mlpWitnessEquiv (ϑ := ϑ) (h_rate := h_rate)) acceptRejectOracleRel
    (OracleReduction.toReduction (Oₛₒ := fun i : Empty => nomatch i)
      (openingReduction K β id mlpWitnessEquiv γ (ϑ := ϑ) (h_rate := h_rate))) at h
  rw [Reduction.perfectCompleteness_eq_prob_one] at h
  exact h (⟨point, t.val.eval point⟩,
    honestInitialOracleStatement K β ϑ (h_ℓ_add_R_rate := h_rate) t) ⟨t⟩
    (honest_input K β t point)

omit [SampleableType L] [DecidableEq K] [Fact (Fintype.card K = 2)]
  [Fact (β 0 = 1)] [NeZero R] in
theorem error_backend (γ : ℕ)
    (j : (fullPSpec K β γ (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate)).ChallengeIdx) :
    openingError K β γ (ϑ := ϑ) (h_rate := h_rate)
      (ChallengeIdx.sumEquiv (Sum.inr j)) =
        FullBinaryBasefold.fullRbrKnowledgeError K β γ (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_rate) j := by
  simp only [openingError, Equiv.symm_apply_apply, Sum.elim_inr]

-- The converted zero-wire verifier keeps the supplied first-oracle family.
example (Context : Type) (ctx : Context) (point : Fin ℓ → L) (claim : L)
    (ost : ∀ j, OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) 0 j)
    (tr : (!p[] : ProtocolSpec 0).FullTranscript) :
    (frontVerifier K β (contextualQuery (L := L) (ℓ := ℓ) Context)
      (ϑ := ϑ) (h_rate := h_rate)).toVerifier.verify ((ctx, (point, claim)), ost) tr =
        pure (statement (⟨point, claim⟩ : MLPEvalStatement L ℓ), ost) :=
  (frontGuard K β (contextualQuery Context)).verify_eq _ _

-- The contextual contract uses the displayed evaluation point and the same packed source.
example (Context : Type) (ctx : Context) (point : Fin ℓ → L) (claim : L)
    (ost : ∀ j, OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) 0 j)
    (t : MultilinearPoly L ℓ) :
    (((ctx, (point, claim)), ost), t) ∈
        contextualInputRelation K β Context (ϑ := ϑ) (h_rate := h_rate) ↔
      claim = t.val.eval point ∧
        FirstOracleWitnessConsistent K β t (getFirstOracle K β ost) := Iff.rfl

end BbfOpeningControls

noncomputable section
namespace BbfGf16Parameters

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
abbrev Gf16 := GaloisField 2 4
local instance : Fintype Gf16 := Fintype.ofFinite Gf16
local instance : DecidableEq Gf16 := Classical.decEq Gf16
local instance : SampleableType Gf16 := SampleableType.ofFintype Gf16
local instance : Fact (Fintype.card (ZMod 2) = 2) := ⟨by simp⟩
local instance : Fact ((1 : ℕ) ∣ 1) := ⟨by decide⟩

def rawBasis : Module.Basis (Fin 4) (ZMod 2) Gf16 :=
  Module.finBasisOfFinrankEq (ZMod 2) Gf16 (GaloisField.finrank 2 (by decide))

def betaBasis : Module.Basis (Fin 4) (ZMod 2) Gf16 :=
  rawBasis.map ((Units.mk0 (rawBasis 0) (rawBasis.ne_zero 0)).mulLeftLinearEquiv
    (ZMod 2) Gf16).symm

theorem betaBasis_zero : betaBasis 0 = 1 := by
  change ((Units.mk0 (rawBasis 0) (rawBasis.ne_zero 0)).mulLeftLinearEquiv
    (ZMod 2) Gf16).symm (rawBasis 0) = 1
  rw [Units.symm_mulLeftLinearEquiv_apply]
  simp [rawBasis.ne_zero]

local instance : Fact (LinearIndependent (ZMod 2) (betaBasis : Fin 4 → Gf16)) :=
  ⟨betaBasis.linearIndependent⟩
local instance : Fact (betaBasis 0 = 1) := ⟨betaBasis_zero⟩

local instance : Fact (Nat.Prime (ringChar (ZMod 2))) :=
  ⟨CharP.prime_ringChar (ZMod 2)⟩

def exampleOpening : RingSwitching.MLIOPCS Gf16 1 :=
  mliopcs (ZMod 2) betaBasis 8 (ϑ := 1) (R := 1) (h_rate := by decide)

example {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :=
  exampleOpening.rbrKnowledgeSoundness (init := init) (impl := impl)

theorem card_gf16 : Fintype.card Gf16 = 16 := by
  rw [← Nat.card_eq_fintype_card]
  exact GaloisField.card 2 4 (by decide)

example :
    FullBinaryBasefold.concreteBinaryBasefoldKnowledgeError Gf16 1 1 8 =
      (6 / 16 + (3 / 4 : ℝ≥0)^8) ∧
    FullBinaryBasefold.concreteBinaryBasefoldKnowledgeError Gf16 1 1 8 < 1 := by
  norm_num [FullBinaryBasefold.concreteBinaryBasefoldKnowledgeError, card_gf16]
example :
    (∑ j, openingError (ZMod 2) betaBasis 8 (ℓ := 1) (ϑ := 1) (R := 1)
      (h_rate := by decide) j) < 1 := by
  refine lt_of_le_of_lt (openingError_sum_le_concrete (ZMod 2) betaBasis 8
    (ℓ := 1) (ϑ := 1) (R := 1) (h_rate := by decide)) ?_
  norm_num [FullBinaryBasefold.concreteBinaryBasefoldKnowledgeError, card_gf16]

example {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :=
  BbfOpeningControls.honest_probability (ZMod 2) betaBasis 8
    (BbfOpeningControls.nonconstantSource (L := Gf16) (ℓ := 1)) ![1] init impl
    (ϑ := 1) (R := 1) (h_rate := by decide)

end BbfGf16Parameters

/--
info: 'Binius.BinaryBasefold.Opening.mliopcs' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Binius.BinaryBasefold.Opening.mliopcs

/--
info: 'Binius.BinaryBasefold.Opening.contextualVerifier_rbrKnowledgeSoundness' depends
on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Binius.BinaryBasefold.Opening.contextualVerifier_rbrKnowledgeSoundness

/--
info: 'Binius.BinaryBasefold.Opening.contextualReduction_perfectCompleteness' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Binius.BinaryBasefold.Opening.contextualReduction_perfectCompleteness

/--
info: 'Binius.BinaryBasefold.Opening.abstractInput_functional' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Binius.BinaryBasefold.Opening.abstractInput_functional

/--
info: 'BbfOpeningControls.honest_probability' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BbfOpeningControls.honest_probability

/--
info: 'BbfOpeningControls.nonconstantSource_evaluations' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BbfOpeningControls.nonconstantSource_evaluations

/--
info: 'BbfOpeningControls.false_zero_claim_no_witness' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BbfOpeningControls.false_zero_claim_no_witness
