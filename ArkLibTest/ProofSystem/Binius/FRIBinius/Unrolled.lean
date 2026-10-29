/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.ProofSystem.Binius.FRIBinius.Unrolled.General
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Fused FRI-Binius trust-boundary regression checks

The complete security and completeness proofs, and their scalar error bound, must remain
independent of admissions in other imported framework declarations.
-/

open Binius.FRIBinius.Unrolled

namespace Binius.FRIBinius.UnrolledTests

local instance : Fact (Nat.Prime 17) := ⟨by decide⟩

private def terminalStatement (target : ZMod 17) :
    Binius.BinaryBasefold.Statement (L := ZMod 17) Unit (Fin.last 1) :=
  ⟨target, fun _ => 3, ()⟩

local instance (f : Unit → (Fin 1 → ZMod 17) → ZMod 17)
    (s : Binius.BinaryBasefold.Statement (L := ZMod 17) Unit (Fin.last 1)) (c : ZMod 17) :
    Decidable (Terminal.check f s c) := by
  unfold Terminal.check
  infer_instance

-- Execute the guard, rather than prove it using a native-evaluation axiom.
/-- info: true -/
#guard_msgs in
#eval decide (Terminal.check (fun _ _ => (4 : ZMod 17)) (terminalStatement 12) 3)
/-- info: false -/
#guard_msgs in
#eval decide (Terminal.check (fun _ _ => (4 : ZMod 17)) (terminalStatement 12) 2)
/-- info: true -/
#guard_msgs in
#eval decide (Terminal.check (fun _ _ => (0 : ZMod 17)) (terminalStatement 0) 9)
/-- info: false -/
#guard_msgs in
#eval decide (Terminal.check (fun _ _ => (0 : ZMod 17)) (terminalStatement 1) 9)

end Binius.FRIBinius.UnrolledTests

namespace Binius.FRIBinius.UnrolledGf16

open Module OracleSpec OracleComp MvPolynomial Sumcheck.Structured
open scoped NNReal
noncomputable section

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
abbrev L := GaloisField 2 4
local instance : Fintype L := Fintype.ofFinite L
local instance : DecidableEq L := Classical.decEq L
local instance : SampleableType L := SampleableType.ofFintype L
local instance : Fact (Fintype.card (ZMod 2) = 2) := ⟨by simp⟩
local instance : Fact ((1 : ℕ) ∣ 1) := ⟨by decide⟩

private def rawBasis : Basis (Fin 4) (ZMod 2) L :=
  Module.finBasisOfFinrankEq (ZMod 2) L (GaloisField.finrank 2 (by decide))

private def beta : Basis (Fin (2 ^ 2)) (ZMod 2) L :=
  rawBasis.map ((Units.mk0 (rawBasis 0) (rawBasis.ne_zero 0)).mulLeftLinearEquiv
    (ZMod 2) L).symm

local instance : Fact (beta 0 = 1) := ⟨by
  change ((Units.mk0 (rawBasis 0) (rawBasis.ne_zero 0)).mulLeftLinearEquiv
    (ZMod 2) L).symm (rawBasis 0) = 1
  rw [Units.symm_mulLeftLinearEquiv_apply]
  simp [rawBasis.ne_zero]⟩

private def source : MultilinearPoly (ZMod 2) 3 :=
  ⟨MvPolynomial.X 2,
    (mem_restrictDegree_iff_degreeOf_le _ _).mpr (fun i => degreeOf_X_le i 2)⟩

-- Exercise a nonconstant source in the unpacked suffix, not merely a constant packed word.
example : source.val.eval (fun _ => 0) = 0 ∧ source.val.eval (fun _ => 1) = 1 := by
  simp [source]

-- All field, rate, block-size and basis hypotheses have concrete witnesses here.
example := honest_input 2 (ZMod 2) beta (ϑ := 1) (R := 1) (ℓ' := 1)
  (by decide) rfl (fun _ => 1) source

-- The query phase ignores this metadata; preserve the original query's unpacked suffix.
private def queryContext (ctx : (Fin 3 → L) × (Fin 2 → L)) : SumcheckBaseContext L 1 :=
  ⟨fun i => ctx.1 ⟨2 + i.val, by omega⟩, 0⟩

example {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :=
  fullReduction_perfectCompleteness 2 (ZMod 2) beta (ϑ := 1) (R := 1) (ℓ' := 1)
    (by decide) rfl queryContext 8 init impl

example {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :=
  fullVerifier_rbrKnowledgeSoundnessWorstCase 2 (ZMod 2) beta (ϑ := 1) (R := 1) (ℓ' := 1)
    (by decide) rfl queryContext 8 init impl

example {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :=
  fullVerifier_knowledgeSoundness 2 (ZMod 2) beta (ϑ := 1) (R := 1) (ℓ' := 1)
    (by decide) rfl queryContext 8 init impl

example {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :=
  fullVerifier_soundness 2 (ZMod 2) beta (ϑ := 1) (R := 1) (ℓ' := 1)
    (by decide) rfl queryContext 8 init impl

private theorem card_field : Fintype.card L = 16 := by
  rw [← Nat.card_eq_fintype_card]
  exact GaloisField.card 2 4 (by decide)

-- One fused loop charges 2ℓ', not the unfused 4ℓ'. The bound is nontrivial.
example : concreteError 2 (L := L) (ℓ' := 1) (R := 1) 8 =
    (8 / 16 + (3 / 4 : ℝ≥0) ^ 8) ∧
    concreteError 2 (L := L) (ℓ' := 1) (R := 1) 8 < 1 := by
  norm_num [concreteError, card_field]

end
end Binius.FRIBinius.UnrolledGf16

/--
info: 'Binius.FRIBinius.Unrolled.fullVerifier_rbrKnowledgeSoundnessWorstCase'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fullVerifier_rbrKnowledgeSoundnessWorstCase

/--
info: 'Binius.FRIBinius.Unrolled.fullReduction_perfectCompleteness'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fullReduction_perfectCompleteness

/--
info: 'Binius.FRIBinius.Unrolled.fullError_sum_le_concrete'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fullError_sum_le_concrete

/--
info: 'Binius.FRIBinius.Unrolled.fullVerifier_rbrKnowledgeSoundness'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fullVerifier_rbrKnowledgeSoundness

/--
info: 'Binius.FRIBinius.Unrolled.strictInputRelation_subset_inputRelation'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms strictInputRelation_subset_inputRelation

/--
info: 'Binius.FRIBinius.Unrolled.fullVerifier_knowledgeSoundness'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fullVerifier_knowledgeSoundness

/--
info: 'Binius.FRIBinius.Unrolled.fullVerifier_soundness'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fullVerifier_soundness
