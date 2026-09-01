/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Prelude

/-!
# Binary Basefold soundness events

Definitions for compliance and the folding bad event, built on the distance lemmas in the prelude.
-/

namespace Binius.BinaryBasefold

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
open scoped NNReal
open Code BerlekampWelch
open Finset AdditiveNTT Polynomial MvPolynomial Nat Matrix

noncomputable section

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 : ℕ} [NeZero ℓ] [NeZero 𝓡]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}

/-- Compliance condition (Definition 4.17). The current oracle is fiber-wise close, the next
oracle is close to its code, and their unique closest codewords are consistent with folding. -/
def isCompliant (i : Fin ℓ) (steps : ℕ) [NeZero steps]
    (h_i_add_steps : i + steps ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (f_i_plus_steps : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ⟨i + steps, by omega⟩)
    (challenges : Fin steps → L) : Prop :=
  ∃ (h_fw_dist_lt : 2 * fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i) (steps := steps) h_i_add_steps f_i <
        (BBF_CodeDistance ℓ 𝓡 ⟨i + steps, by omega⟩ : ℕ∞))
    (h_dist_next_lt : 2 * distFromCode f_i_plus_steps
      (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i + steps, by omega⟩) <
        (BBF_CodeDistance ℓ 𝓡 ⟨i + steps, by omega⟩ : ℕ∞)),
    let h_dist_curr_lt := fiberwise_dist_lt_imp_dist_lt_unique_decoding_radius 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) steps h_i_add_steps f_i
      (h_fw_dist_lt := h_fw_dist_lt)
    let f_bar_i := uniqueClosestCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i, by omega⟩) (h_i := fin_ℓ_lt_ℓ_add_R i) f_i h_dist_curr_lt
    let f_bar_i_plus_steps := uniqueClosestCodeword 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i + steps, by omega⟩)
      (h_i := fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps) f_i_plus_steps h_dist_next_lt
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (steps := ⟨steps, by apply Nat.lt_succ_of_le; exact Nat.le_of_add_left_le h_i_add_steps⟩)
      (i := ⟨i, by omega⟩)
      (h_i_add_steps := by simp only; exact fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps)
      f_bar_i challenges = f_bar_i_plus_steps

omit [CharP L 2] [NeZero ℓ] in
/-- A fiber-wise far oracle cannot be compliant. -/
lemma farness_implies_non_compliance (i : Fin ℓ) (steps : ℕ) [NeZero steps]
    (h_i_add_steps : i + steps ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (f_i_plus_steps : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ⟨i + steps, by omega⟩)
    (challenges : Fin steps → L)
    (h_far : 2 * Code.distFromCode f_i
      (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩) ≥
        (BBF_CodeDistance ℓ 𝓡 ⟨i, by omega⟩ : ℕ∞)) :
    ¬ isCompliant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
      h_i_add_steps f_i f_i_plus_steps challenges := by
  intro h_compliant
  rcases h_compliant with ⟨h_fw_dist_lt, _, _⟩
  have h_close := fiberwise_dist_lt_imp_dist_lt_unique_decoding_radius 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps) h_i_add_steps f_i
    h_fw_dist_lt
  exact LT.lt.not_ge h_close h_far

/-- The folding bad event (Definition 4.19): folding either loses existing disagreements from a
close oracle or makes a fiber-wise far oracle appear close to the next code. -/
def foldingBadEvent (i : Fin ℓ) (steps : ℕ) [NeZero steps] (h_i_add_steps : i + steps ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (challenges : Fin steps → L) : Prop :=
  let d_i_plus_steps := BBF_CodeDistance ℓ 𝓡 ⟨i + steps, by omega⟩
  if h_is_close : 2 * fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i) steps h_i_add_steps f_i < (d_i_plus_steps : ℕ∞) then
    let h_dist_curr_lt := fiberwise_dist_lt_imp_dist_lt_unique_decoding_radius 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps) h_i_add_steps f_i h_is_close
    let f_bar_i := uniqueClosestCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i, by omega⟩) (h_i := by apply Nat.lt_add_of_pos_right_of_le; omega) f_i
      h_dist_curr_lt
    let folded_f_i := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (steps := ⟨steps, by omega⟩) (i := ⟨i, by omega⟩)
      (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) f_i challenges
    let folded_f_bar_i := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (steps := ⟨steps, by omega⟩) (i := ⟨i, by omega⟩)
      (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) f_bar_i challenges
    let fiberwise_disagreements := fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f_i f_bar_i
    let folded_disagreements := disagreementSet 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      i steps h_i_add_steps folded_f_i folded_f_bar_i
    ¬ (fiberwise_disagreements ⊆ folded_disagreements)
  else
    let folded_f_i := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (steps := ⟨steps, by omega⟩) (i := ⟨i, by omega⟩)
      (h_i_add_steps := by simp only; apply Nat.lt_add_of_pos_right_of_le; omega) f_i challenges
    let dist_to_code := distFromCode folded_f_i
      (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i + steps, by omega⟩)
    2 * dist_to_code < (d_i_plus_steps : ℕ∞)

end

end Binius.BinaryBasefold
