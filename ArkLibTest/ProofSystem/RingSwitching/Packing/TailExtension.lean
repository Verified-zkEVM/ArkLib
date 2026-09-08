/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.RingSwitching.Packing.Tail.Knowledge
import ArkLibTest.ProofSystem.RingSwitching.Packing.PackedCommitment
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# An opening outside the packed coefficient field

P=ZMod3 and C=GF9 are concrete, distinct finite fields. The committed polynomial is X. Its
final opening at a chosen point outside the image of P is that very C-valued point.
The round and entire tail use the production extractors and two-ninths challenge bound.
-/

noncomputable section

namespace RingSwitching.Packing.Tests.TailExtension

open MvPolynomial OracleSpec OracleComp ProtocolSpec
open NonfunctionalCommitment
open scoped NNReal

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
abbrev P := ZMod 3
abbrev C := GaloisField 3 2
local instance : Fintype C := Fintype.ofFinite _

abbrev exactPC := ExactPackedCommitment.polynomialOracle P 1
abbrev pc : PackedCommitment P 1 := exactPC.toPackedCommitment

def p : P⦃≤ 1⦄[X Fin 1] := ⟨X 0, by simp [mem_restrictDegree_iff_degreeOf_le]⟩
def ost := pc.commit p
def multiplier : Unit → C⦃≤ 1⦄[X Fin 1] := fun _ => constant 1 1

/-- The concrete challenge field has nine elements, strictly more than the packed field. -/
theorem challenge_card : Fintype.card C = 9 := by
  rw [Fintype.card_eq_nat_card]
  exact GaloisField.card (p := 3) (n := 2) (by decide)

/-- Cardinalities rule out surjective coefficient transport. -/
theorem transport_not_surjective : ¬ Function.Surjective (algebraMap P C) := by
  intro h
  have hcard := Fintype.card_le_of_surjective (algebraMap P C) h
  rw [challenge_card, ZMod.card] at hcard
  omega

/-- There really is a challenge coordinate outside the packed coefficient field. -/
theorem outside_exists : ∃ c : C, ∀ a : P, algebraMap P C a ≠ c := by
  simpa only [Function.Surjective, not_forall, not_exists] using transport_not_surjective

def point : C := Classical.choose outside_exists

theorem point_outside (a : P) : algebraMap P C a ≠ point := Classical.choose_spec outside_exists a

def stmt : Tail.Statement Unit C (0 : Fin 1).castSucc :=
  ⟨(), Fin.elim0, hypercubeSum 1 (Tail.productPoly (multiplier ()) p).val 0 Fin.elim0⟩
def g := Tail.Round.honestMessage multiplier 0 stmt p
def next := Tail.Round.nextStatement 0 stmt g point

/-- Honest input is the Boolean sum of the transported nonconstant packed polynomial. -/
theorem source_related : ((stmt, ost), p) ∈ Tail.rel multiplier pc (0 : Fin 1).castSucc :=
  ⟨rfl, pc.commitsTo_commit p⟩

/-- The round accepts this genuine challenge-extension point with the same oracle. -/
theorem round_accepts :
    (Tail.Round.verifier pc 0).toVerifier.verify (stmt, ost) (FullTranscript.mk2 g point) =
      pure (next, ost) := by
  rw [Tail.Round.verifier_verify]
  exact if_pos (Tail.Round.honest_check multiplier pc 0 source_related)

/-- The original P-polynomial satisfies the residual relation at this C-valued point. -/
theorem next_related : ((next, ost), p) ∈ Tail.rel multiplier pc (Fin.last 1) :=
  Tail.Round.honest_relOut multiplier pc 0 source_related point

/-- The opening of X is outside the coefficient field. -/
theorem packed_evaluation : aeval next.challenges p.val = point := by
  simp [next, Tail.Round.nextStatement, stmt, p, Fin.snoc]

/-- The terminal sends and forwards the C-valued point itself, retaining the original P witness. -/
theorem terminal_forwards_extension :
    (Tail.Terminal.verifier multiplier pc).toVerifier.verify (next, ost)
      (Tail.Terminal.transcript point) = pure ((next.challenges, point), ost) := by
  rw [Tail.Terminal.verifier_verify]
  exact if_pos (packed_evaluation ▸ Tail.Terminal.honest_check multiplier pc next_related)

/-- The whole tail's WC contract anchors the same P-polynomial by commitment functionality. -/
theorem worst_case {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    Verifier.rbrKnowledgeSoundnessWorstCaseWith init impl
      (Tail.rel multiplier pc 0) pc.evalRel (Tail.verifier multiplier pc).toVerifier
      (Tail.Witness (P := P) (m := 1)) (Tail.extractor (C := C) (Context := Unit) pc)
      (Tail.knowledgeStateFunction multiplier pc init impl) (Tail.rbrError (C := C) (m := 1)) :=
  Tail.rbrKnowledgeSoundnessWorstCaseWith multiplier pc exactPC.commitsTo_functional init impl

/-- Every scalar-round challenge is bounded by two ninths. -/
theorem error (i : (Tail.pSpec C 1).ChallengeIdx) :
    Tail.rbrError i = (2 / 9 : ℝ≥0) := by
  rw [Tail.rbrError_eq, challenge_card]
  norm_num

end RingSwitching.Packing.Tests.TailExtension

end
