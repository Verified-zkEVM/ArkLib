/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Security.Basic
import ArkLib.ProofSystem.ConstraintSystem.Plonk

/-!

# Plonk Permutation Check Protocol

The permutation check verifies that copy constraints are satisfied: the extended
wire assignment is constant on orbits of the permutation induced by the constraint system.

Modeled as a 1-round `Reduction` using ArkLib's OracleReduction framework, parallel
to the gate-check protocol in `ArkLib.ProofSystem.Plonk.Basic`.

## Protocol structure

- **ProtocolSpec**: 1 round, P → V, message type `Fin (3 * numGates) → 𝓡`
- **Statement**: `Plonk.ConstraintSystem 𝓡 numWires numGates`
- **Witness**: `Fin (3 * numGates) → 𝓡` (extended wire assignment)
- **Input relation**: `CopyConstraintsSatisfied f (cs.perm)`
- **Output**: `(cs, f)` pair

## References

* [Gabizon, A., Williamson, Z.J., and Ciobotaru, O., *Plonk: Permutations over lagrange-bases
    for oecumenical noninteractive arguments of knowledge*][GWZC19]

-/

noncomputable section

namespace Plonk

open OracleComp OracleSpec ProtocolSpec

section Extend

variable (𝓡 : Type) [CommRing 𝓡] (numWires numGates : ℕ)

/-- Maps a position in `Fin (3 * numGates)` to the wire index it references.
Position `(k, g)` via `finProdFinEquiv` references wire `a`/`b`/`c` of gate `g`. -/
def wireOfPosition (cs : ConstraintSystem 𝓡 numWires numGates)
    (j : Fin (3 * numGates)) : Fin numWires :=
  let p := finProdFinEquiv.symm j
  if p.1 = 0 then (cs p.2).a
  else if p.1 = 1 then (cs p.2).b
  else (cs p.2).c

/-- Extends a wire assignment to the full position domain using the constraint system's
wire routing: position `j` gets value `w (wireOfPosition cs j)`. -/
def extendWireAssignment (cs : ConstraintSystem 𝓡 numWires numGates)
    (w : Fin numWires → 𝓡) : Fin (3 * numGates) → 𝓡 :=
  w ∘ wireOfPosition 𝓡 numWires numGates cs

end Extend

section PermutationCheck

variable (𝓡 : Type) [CommRing 𝓡] (numWires numGates : ℕ)

@[reducible]
def permCheckPSpec : ProtocolSpec 1 :=
  ⟨!v[.P_to_V], !v[Fin (3 * numGates) → 𝓡]⟩

instance : ∀ i, VCVCompatible ((permCheckPSpec 𝓡 numGates).Challenge i)
  | ⟨0, h⟩ => nomatch h

instance : ∀ i, SampleableType ((permCheckPSpec 𝓡 numGates).Challenge i)
  | ⟨0, h⟩ => nomatch h

instance : ProverOnly (permCheckPSpec 𝓡 numGates) where
  prover_first' := rfl

variable {𝓡} {numWires} {numGates}

@[inline, specialize]
def permCheckProver :
    Prover []ₒ
      (ConstraintSystem 𝓡 numWires numGates) (Fin (3 * numGates) → 𝓡)
      (ConstraintSystem 𝓡 numWires numGates × (Fin (3 * numGates) → 𝓡)) Unit
      (permCheckPSpec 𝓡 numGates) where
  PrvState
  | 0 => ConstraintSystem 𝓡 numWires numGates × (Fin (3 * numGates) → 𝓡)
  | 1 => ConstraintSystem 𝓡 numWires numGates × (Fin (3 * numGates) → 𝓡)
  input := id
  sendMessage | ⟨0, _⟩ => fun ⟨cs, f⟩ => pure (f, ⟨cs, f⟩)
  receiveChallenge | ⟨0, h⟩ => nomatch h
  output := fun ⟨cs, f⟩ => pure (⟨cs, f⟩, ())

variable [DecidableEq 𝓡]

instance copyConstraintsDecidable (f : Fin (3 * numGates) → 𝓡)
    (σ : Equiv.Perm (Fin (3 * numGates))) :
    Decidable (CopyConstraintsSatisfied f σ) :=
  inferInstanceAs (Decidable (∀ i, f (σ i) = f i))

@[inline, specialize]
def permCheckVerifier :
    Verifier []ₒ
      (ConstraintSystem 𝓡 numWires numGates)
      (ConstraintSystem 𝓡 numWires numGates × (Fin (3 * numGates) → 𝓡))
      (permCheckPSpec 𝓡 numGates) where
  verify := fun cs transcript => do
    let f : Fin (3 * numGates) → 𝓡 := transcript 0
    guard (CopyConstraintsSatisfied f cs.perm)
    return ⟨cs, f⟩

@[inline, specialize]
def permCheckReduction :
    Reduction []ₒ
      (ConstraintSystem 𝓡 numWires numGates) (Fin (3 * numGates) → 𝓡)
      (ConstraintSystem 𝓡 numWires numGates × (Fin (3 * numGates) → 𝓡)) Unit
      (permCheckPSpec 𝓡 numGates) where
  prover := permCheckProver
  verifier := permCheckVerifier

@[reducible, simp]
def permCheckRelIn :
    Set (ConstraintSystem 𝓡 numWires numGates × (Fin (3 * numGates) → 𝓡)) :=
  { p | CopyConstraintsSatisfied p.2 p.1.perm }

@[reducible, simp]
def permCheckRelOut :
    Set ((ConstraintSystem 𝓡 numWires numGates × (Fin (3 * numGates) → 𝓡)) × Unit) :=
  Prod.fst ⁻¹' permCheckRelIn

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

set_option maxHeartbeats 1600000 in
omit [CommRing 𝓡] in
open Classical in
theorem permCheck_perfectCompleteness :
    (permCheckReduction (𝓡 := 𝓡) (numWires := numWires) (numGates := numGates)).perfectCompleteness
      init impl permCheckRelIn permCheckRelOut := by
  simp only [Reduction.perfectCompleteness, Reduction.completeness, ENNReal.coe_zero, tsub_zero]
  intro cs f hIn
  simp only [permCheckRelIn, Set.mem_setOf_eq] at hIn
  have hrun : (permCheckReduction (𝓡 := 𝓡) (numWires := numWires)
      (numGates := numGates)).run cs f =
      OptionT.mk (pure (some (⟨fun | ⟨0, _⟩ => f, (cs, f), ()⟩, (cs, f)))) := by
    simp only [Reduction.run, Verifier.run, Prover.run_of_prover_first,
      permCheckReduction, permCheckProver, permCheckVerifier, guard, if_pos hIn, id,
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

end PermutationCheck

end Plonk

end
