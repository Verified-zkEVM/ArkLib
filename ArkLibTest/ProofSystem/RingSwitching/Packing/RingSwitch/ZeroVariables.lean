/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.RingSwitching.Packing.RingSwitch
import Mathlib.Algebra.Field.ZMod

/-!
# No retained variables over a ring with zero divisors

The complete program still sends its head carrier and final opening value, with only the head
challenge. Its completeness theorem needs no domain assumption, and its exact error sum has no
sumcheck contribution. The oracle exposes the constant packed polynomial as specification data.
-/
noncomputable section
namespace RingSwitching.Packing.Tests.ZeroVariables
open Module MvPolynomial OracleSpec OracleComp ProtocolSpec

abbrev data : PackingData (ZMod 4) := PackingData.ofBasis (Basis.singleton Unit (ZMod 4))

def layout : ClaimLayout data 0 where
  Source := Unit → (ZMod 4)⦃≤ 1⦄[X Fin 0]
  Query := Nat
  components := Equiv.refl _
  point _ := Fin.elim0
  weight _ _ := 1
  eval _ p := aeval Fin.elim0 (p ()).val
  reconstruct _ _ := by simp

def pc : PackedCommitment data.P 0 where
  ιC := Unit
  OStmt _ := data.P⦃≤ 1⦄[X Fin 0]
  Oᵢ _ := OracleInterface.instDefault
  commitsTo ost p := ost () = p

instance : SampleableType (ZMod 4) := SampleableType.ofFintype _
abbrev bat : BatchingStrategy (ZMod 4) data.ιE :=
  BatchingStrategy.singleton (ZMod 4) data.ιE
abbrev codec : (data.ιP → data.E) ≃ (data.ιP → data.E) := Equiv.refl _

example {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (RingSwitch.reduction data 0 layout codec bat.toBatchingRule pc).perfectCompleteness
      init impl (Head.relIn data 0 layout pc)
      (pc.evalRelWithContext (layout.Query × bat.Challenge)) :=
  RingSwitch.perfectCompleteness data 0 layout codec bat.toBatchingRule pc init impl

example : (∑ i, RingSwitch.rbrError (M := data.ιP → data.E) data 0 bat i) = 0 := by
  rw [RingSwitch.rbrError_sum]
  simp [bat, BatchingStrategy.singleton]

example : Fintype.card
    (RingSwitch.pSpec (M := data.ιP → data.E) data 0 bat.toBatchingRule).MessageIdx = 2 := by
  decide

example : Fintype.card
    (RingSwitch.pSpec (M := data.ιP → data.E) data 0 bat.toBatchingRule).ChallengeIdx = 1 := by
  decide

end RingSwitching.Packing.Tests.ZeroVariables
