/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Security.Basic
import ArkLib.ProofSystem.ConstraintSystem.Plonk

/-!

# Plonk Gate-Check Protocol

The Plonk gate-check is the first component of the Plonk PIOP: the prover sends the
wire assignment, the verifier checks all gate equations in the constraint system.

Modeled as a 1-round `Reduction` using ArkLib's OracleReduction framework. This
protocol forms the foundation for the full Plonk PIOP — composition with the
permutation argument (copy constraints) is handled separately in
`ArkLib.ProofSystem.Plonk.PermutationCheck`.

## Protocol structure

- **ProtocolSpec**: 1 round, P → V, message type `Fin numWires → 𝓡`
- **Statement**: `Plonk.ConstraintSystem 𝓡 numWires numGates`
- **Witness**: `Fin numWires → 𝓡` (wire assignment)
- **Input relation**: `cs.accepts w` (all gate equations satisfied)
- **Output**: `(cs, w)` pair (for composition with downstream reductions)

## References

* [Gabizon, A., Williamson, Z.J., and Ciobotaru, O., *Plonk: Permutations over lagrange-bases
    for oecumenical noninteractive arguments of knowledge*][GWZC19]

-/

noncomputable section

namespace Plonk

open OracleComp OracleSpec ProtocolSpec

section GateCheck

variable (𝓡 : Type) [CommRing 𝓡] (numWires numGates : ℕ)

@[reducible]
def gateCheckPSpec : ProtocolSpec 1 :=
  ⟨!v[.P_to_V], !v[Fin numWires → 𝓡]⟩

instance : ∀ i, VCVCompatible ((gateCheckPSpec 𝓡 numWires).Challenge i)
  | ⟨0, h⟩ => nomatch h

instance : ∀ i, SampleableType ((gateCheckPSpec 𝓡 numWires).Challenge i)
  | ⟨0, h⟩ => nomatch h

instance : ProverOnly (gateCheckPSpec 𝓡 numWires) where
  prover_first' := rfl

variable {𝓡} {numWires} {numGates}

@[inline, specialize]
def gateCheckProver :
    Prover []ₒ
      (ConstraintSystem 𝓡 numWires numGates) (Fin numWires → 𝓡)
      (ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡)) Unit
      (gateCheckPSpec 𝓡 numWires) where
  PrvState
  | 0 => ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡)
  | 1 => ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡)
  input := id
  sendMessage | ⟨0, _⟩ => fun ⟨cs, w⟩ => pure (w, ⟨cs, w⟩)
  receiveChallenge | ⟨0, h⟩ => nomatch h
  output := fun ⟨cs, w⟩ => pure (⟨cs, w⟩, ())

variable [DecidableEq 𝓡]

instance acceptsDecidable (cs : ConstraintSystem 𝓡 numWires numGates) (w : Fin numWires → 𝓡) :
    Decidable (cs.accepts w) :=
  inferInstanceAs (Decidable (∀ i : Fin numGates, (cs i).eval w = 0))

@[inline, specialize]
def gateCheckVerifier :
    Verifier []ₒ
      (ConstraintSystem 𝓡 numWires numGates)
      (ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡))
      (gateCheckPSpec 𝓡 numWires) where
  verify := fun cs transcript => do
    let w : Fin numWires → 𝓡 := transcript 0
    guard (cs.accepts w)
    return ⟨cs, w⟩

@[inline, specialize]
def gateCheckReduction :
    Reduction []ₒ
      (ConstraintSystem 𝓡 numWires numGates) (Fin numWires → 𝓡)
      (ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡)) Unit
      (gateCheckPSpec 𝓡 numWires) where
  prover := gateCheckProver
  verifier := gateCheckVerifier

@[reducible, simp]
def gateCheckRelIn :
    Set (ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡)) :=
  { p | p.1.accepts p.2 }

@[reducible, simp]
def gateCheckRelOut :
    Set ((ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡)) × Unit) :=
  Prod.fst ⁻¹' gateCheckRelIn

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

set_option maxHeartbeats 1600000 in
open Classical in
theorem gateCheck_perfectCompleteness :
    (gateCheckReduction (𝓡 := 𝓡) (numWires := numWires) (numGates := numGates)).perfectCompleteness
      init impl gateCheckRelIn gateCheckRelOut := by
  simp only [Reduction.perfectCompleteness, Reduction.completeness, ENNReal.coe_zero, tsub_zero]
  intro cs w hIn
  simp only [gateCheckRelIn, Set.mem_setOf_eq] at hIn
  have hrun : (gateCheckReduction (𝓡 := 𝓡) (numWires := numWires)
      (numGates := numGates)).run cs w =
      OptionT.mk (pure (some (⟨fun | ⟨0, _⟩ => w, (cs, w), ()⟩, (cs, w)))) := by
    simp only [Reduction.run, Verifier.run, Prover.run_of_prover_first,
      gateCheckReduction, gateCheckProver, gateCheckVerifier, guard, if_pos hIn, id,
      OracleComp.liftComp_pure, pure_bind, map_pure, bind_pure_comp, monadLift_pure,
      OptionT.run_pure, Option.getM]; rfl
  simp only [hrun]
  rw [ge_iff_le, one_le_probEvent_iff, probEvent_eq_one_iff]
  refine ⟨?_, ?_⟩
  · rw [OptionT.probFailure_eq, OptionT.run_mk]
    simp only [probFailure_eq_zero, zero_add]
    apply probOutput_eq_zero_of_not_mem_support
    simp only [support_bind, Set.mem_iUnion, not_exists]
    intro s _
    erw [simulateQ_pure]
    rw [StateT.run'_eq, StateT.run_pure]
    simp [map_pure, support_pure]
  · intro x hx
    rw [OptionT.mem_support_iff] at hx
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
    obtain ⟨s, _, hx⟩ := hx
    erw [simulateQ_pure] at hx
    rw [StateT.run'_eq, StateT.run_pure] at hx
    simp only [map_pure, support_pure, Set.mem_singleton_iff] at hx
    cases hx
    exact ⟨hIn, rfl⟩

end GateCheck

end Plonk

end
