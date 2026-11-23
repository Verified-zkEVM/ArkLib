/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLibTest.ProofSystem.RingSwitching.Conformance.BiniusComposition
import ArkLib.ProofSystem.Binius.FRIBinius.Executable.Completeness
import ArkLib.ProofSystem.Binius.FRIBinius.Executable.Soundness

/-!
# Security of both executable FRI-Binius openings

The executable reductions have perfect completeness on the exact encoding relation and
knowledge soundness at the original concrete errors on the proximity relation.
-/

open OracleComp OracleSpec Module
open Binius.FRIBinius Binius.BinaryBasefold
open ArkLibTest.RingSwitchingConformance.BiniusComposition BbfGf16Parameters

noncomputable section

namespace ArkLibTest.FRIBinius.Executable

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance : Fintype Gf16 := Fintype.ofFinite Gf16
local instance : DecidableEq Gf16 := Classical.decEq Gf16
local instance : SampleableType Gf16 := SampleableType.ofFintype Gf16
local instance : Fact (Fintype.card (ZMod 2) = 2) := ⟨by simp⟩
local instance : Fact ((1 : ℕ) ∣ 1) := ⟨by decide⟩
local instance : Fact (basis 0 = 1) := ⟨betaBasis_zero⟩

private def coords (x : Gf16) (u : Fin 2 → Fin 2) : ZMod 2 :=
  basis.repr x (finFunctionFinEquiv u)

private theorem rate : 1 + 1 < 2 ^ 2 := by decide
private theorem dimensions : 3 = 1 + 2 := rfl

private abbrev unrolled :=
  Binius.FRIBinius.Executable.unrolledReduction (K := ZMod 2) (ϑ := 1) (⇑basis)
    coords dimensions rate 8 ⟨basis, rfl, rfl⟩

private abbrev modular :=
  Binius.FRIBinius.Executable.modularReduction (K := ZMod 2) (ϑ := 1) (⇑basis)
    coords dimensions rate 8 ⟨basis, rfl, rfl⟩

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

example : OracleProof.perfectCompleteness init impl
    (Binius.FRIBinius.Executable.strictInputRelation (ϑ := 1) basis rate dimensions) unrolled :=
  Binius.FRIBinius.Executable.unrolledReduction_perfectCompleteness
    (ϑ := 1) basis rate dimensions 8 coords rfl init impl

example : OracleProof.perfectCompleteness init impl
    (Binius.FRIBinius.Executable.strictInputRelation (ϑ := 1) basis rate dimensions) modular :=
  Binius.FRIBinius.Executable.modularReduction_perfectCompleteness
    (ϑ := 1) basis rate dimensions 8 coords rfl init impl

example : OracleProof.knowledgeSoundness init impl
    (Binius.FRIBinius.Executable.inputRelation (ϑ := 1) basis rate dimensions)
    (unrolled.verifier (Oₛₒ := fun i : Empty => nomatch i))
    (Unrolled.concreteError 2 (L := Gf16) (ℓ' := 1) (R := 1) 8) :=
  Binius.FRIBinius.Executable.unrolledVerifier_knowledgeSoundness
    (ϑ := 1) basis rate 8 dimensions coords rfl init impl

example : OracleProof.knowledgeSoundness init impl
    (Binius.FRIBinius.Executable.inputRelation (ϑ := 1) basis rate dimensions)
    (modular.verifier (Oₛₒ := fun i : Empty => nomatch i))
    (Binius.FRIBinius.RingSwitch.concreteError 2 (L := Gf16) (ℓ' := 1) (R := 1) 8) :=
  Binius.FRIBinius.Executable.modularVerifier_knowledgeSoundness
    (ϑ := 1) basis rate 8 dimensions coords rfl init impl

end ArkLibTest.FRIBinius.Executable

/--
info: 'Binius.FRIBinius.Executable.unrolledVerifier_rbrKnowledgeSoundness' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Binius.FRIBinius.Executable.unrolledVerifier_rbrKnowledgeSoundness

/--
info: 'Binius.FRIBinius.Executable.modularVerifier_rbrKnowledgeSoundness' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Binius.FRIBinius.Executable.modularVerifier_rbrKnowledgeSoundness
