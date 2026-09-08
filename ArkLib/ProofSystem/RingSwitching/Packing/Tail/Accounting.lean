/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.RingSwitching.Packing.Tail.FullFamilyOpening
import ArkLib.ProofSystem.RingSwitching.Packing.Tail.ScalarOpening
/-!
# Accounting for packing protocol challenge errors

The canonical sequence and append equivalences count one batching challenge and one scalar
challenge per retained variable. These are exact sums of the declared per-challenge RBR
knowledge errors. This module does not infer ordinary soundness from RBR knowledge security.
-/

noncomputable section
namespace RingSwitching.Packing
open ProtocolSpec
open scoped NNReal
variable {C : Type} [CommRing C]

/-- A scalar product-sumcheck round contains exactly one challenge. -/
private theorem card_round : Fintype.card (Tail.Round.pSpec C).ChallengeIdx = 1 := by
  change Fintype.card {j : Fin 2 //
    (!v[Direction.P_to_V, Direction.V_to_P] j) = Direction.V_to_P} = 1
  decide

omit [CommRing C] in
/-- The terminal value message contributes no challenge. -/
private theorem card_terminal : Fintype.card (Tail.Terminal.pSpec C).ChallengeIdx = 0 := by
  change Fintype.card {j : Fin 1 // (!v[Direction.P_to_V] j) = Direction.V_to_P} = 0
  decide

/-- The scalar-round sequence has one challenge per retained variable. -/
private theorem card_loop (m : ℕ) : Fintype.card (Tail.loopSpec C m).ChallengeIdx = m := by
  change Fintype.card (seqCompose (fun _ : Fin m => Tail.Round.pSpec C)).ChallengeIdx = m
  rw [← Fintype.card_congr (seqComposeChallengeEquiv (fun _ : Fin m => Tail.Round.pSpec C))]
  simp [Fintype.card_sigma, card_round]

/-- Appending the terminal message leaves the loop challenge count unchanged. -/
private theorem card_tail (m : ℕ) : Fintype.card (Tail.pSpec C m).ChallengeIdx = m := by
  change Fintype.card (Tail.loopSpec C m ++ₚ Tail.Terminal.pSpec C).ChallengeIdx = m
  rw [← Fintype.card_congr (ChallengeIdx.sumEquiv
    (pSpec₁ := Tail.loopSpec C m) (pSpec₂ := Tail.Terminal.pSpec C))]
  simp [Fintype.card_sum, card_loop, card_terminal]

/-- The empty input adapter preserves the tail challenge count. -/
private theorem card_familyTail (m : ℕ) :
    Fintype.card (FullFamilyTail.pSpec (C := C) m).ChallengeIdx = m := by
  change Fintype.card (!p[] ++ₚ Tail.pSpec C m).ChallengeIdx = m
  rw [← Fintype.card_congr (ChallengeIdx.sumEquiv
    (pSpec₁ := !p[]) (pSpec₂ := Tail.pSpec C m))]
  simp [Fintype.card_sum, card_tail]

variable {B : Type} [CommRing B] (data : PackingData B)
  (m : ℕ) (bat : BatchingStrategy C data.ιE) [Fintype C]

omit [Fintype C] in
/-- The full-family checked head has one batching challenge. -/
private theorem card_head : Fintype.card (FullFamily.pSpec data bat).ChallengeIdx = 1 := by
  change Fintype.card {j : Fin 2 //
    (!v[Direction.P_to_V, Direction.V_to_P] j) = Direction.V_to_P} = 1
  decide

set_option backward.isDefEq.respectTransparency false in
/--
The sum of the full-family reduction's per-challenge errors is the batching error plus `2 * m
/ |C|`.
-/
theorem FullFamilyOpening.rbrError_sum : (∑ i, FullFamilyOpening.rbrError data m bat i) =
    bat.error + (m : ℝ≥0) * (2 / Fintype.card C) := by
  calc
    _ = ∑ j : (FullFamily.pSpec data bat).ChallengeIdx ⊕
        (FullFamilyTail.pSpec (C := C) m).ChallengeIdx,
        FullFamilyOpening.rbrError data m bat (ChallengeIdx.sumEquiv j) :=
      (Equiv.sum_comp (ChallengeIdx.sumEquiv (pSpec₁ := FullFamily.pSpec data bat)
        (pSpec₂ := FullFamilyTail.pSpec (C := C) m))
          (FullFamilyOpening.rbrError data m bat)).symm
    _ = _ := by
      simp only [Fintype.sum_sum_type, FullFamilyOpening.rbrError_head,
        FullFamilyOpening.rbrError_tail, Finset.sum_const, Finset.card_univ, card_head,
        card_familyTail, nsmul_eq_mul, Nat.cast_one, one_mul]


omit [Fintype C] in
/-- The scalar head is deterministic, leaving one full-family batching challenge. -/
private theorem card_scalarHead : Fintype.card (ScalarFamily.pSpec data bat).ChallengeIdx = 1 := by
  change Fintype.card {j : Fin 3 //
    (!v[Direction.P_to_V, Direction.P_to_V, Direction.V_to_P] j) = Direction.V_to_P} = 1
  decide

set_option backward.isDefEq.respectTransparency false in
/--
The sum of the scalar reduction's per-challenge errors is the batching error plus `2 * m /
|C|`.
-/
theorem ScalarOpening.rbrError_sum : (∑ i, ScalarOpening.rbrError data m bat i) =
    bat.error + (m : ℝ≥0) * (2 / Fintype.card C) := by
  calc
    _ = ∑ j : (ScalarFamily.pSpec data bat).ChallengeIdx ⊕
        (FullFamilyTail.pSpec (C := C) m).ChallengeIdx,
        ScalarOpening.rbrError data m bat (ChallengeIdx.sumEquiv j) :=
      (Equiv.sum_comp (ChallengeIdx.sumEquiv (pSpec₁ := ScalarFamily.pSpec data bat)
        (pSpec₂ := FullFamilyTail.pSpec (C := C) m))
          (ScalarOpening.rbrError data m bat)).symm
    _ = _ := by
      simp only [Fintype.sum_sum_type, ScalarOpening.rbrError_head,
        ScalarOpening.rbrError_tail, Finset.sum_const, Finset.card_univ, card_scalarHead,
        card_familyTail, nsmul_eq_mul, Nat.cast_one, one_mul]

end RingSwitching.Packing
