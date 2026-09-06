/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLibExamples.ReedSolomon.ConcreteCurveMCA
import ArkLibExamples.ReedSolomon.LambdaVMFields

/-!
# Derived ZisK curve counts and their local error budgets

Each of the six curves supplies its actual exceptional set over cubic Goldilocks. The initial
row uses one bit of batching grinding; the five folding rows use no grinding.

## Reading the statements

The domain and all received constituent words are arbitrary. Each row chooses one finite
exceptional set before the challenge and close candidate. Outside it, the candidate is
exactly a power combination of base-field messages with the same full agreement set.
The accompanying inequality checks the corresponding local algebraic error slot.

## Paper correspondence and entry point

Read `exists_exceptional_at_target` for the six curve rows in Section 6.4 (ZisK) of the main paper.
`i = 0` is the initial powers batching; the other five indices are folding rows.
`Fin r` means an index with `r` possible values, and `↪` requires distinct evaluation points.
The arbitrary `values` are the received constituent words, not assumed polynomial messages.
The theorem constructs the exceptional set from this data before considering any challenge or
candidate. Its last clause recovers polynomial messages with equality of the full agreement sets.

`algebraicSlot` is the paper's batching/folding contribution `E / (g q)`: only the initial row
has `g = 2`. The definition records the one-bit grinding allowance in the analytical model;
it does not assert that the deployed transcript implements that allowance.
`ZisK.query_at_target` separately proves the 111-query inequality with the existing 16 grinding
bits. `replacement_payload_strict` compares the removed responses with the added nonce.

These are per-phase mathematical bounds and the pinned response-size model. The existing
16 query-grinding bits are unchanged. Adding the batching nonce requires the transcript
hook described in the application discussion; no deployed verifier is modeled here.
-/

open Polynomial ReedSolomon

namespace ArkLibExamples.ReedSolomon.ZisKCertifiedBudget

open ConcreteFields ConcreteCurves ConcreteCurveBounds

noncomputable section

/-- The semantic algebraic slot, including one initial batching-grinding bit. -/
def algebraicSlot (i : Fin 6) (count : ℕ) : ℚ :=
  (count : ℚ) / ((if i = 0 then 2 else 1) * ZisK.challengeCardinality)

/-- The denominator is the cardinality of the actual challenge field, with its grinding factor. -/
theorem algebraicSlot_eq_field_card (i : Fin 6) (count : ℕ) :
    algebraicSlot i count = (count : ℚ) /
      ((if i = 0 then 2 else 1) * (Fintype.card GoldilocksCubic : ℚ)) := by
  rw [LambdaVMFields.goldilocksCubic_card_eq_zisK]
  rfl

/-- Every recorded ceiling fits its local 128-bit slot. -/
theorem recorded_slot_le (i : Fin 6) :
    algebraicSlot i (zisKBudget i) ≤ (1 / 2 ^ 128 : ℚ) := by
  fin_cases i <;> norm_num [algebraicSlot, zisKBudget, ZisK.challengeCardinality]

/-- The characteristic of the canonical challenge field discharges all six geometric conditions. -/
theorem characteristic_admissible (i : Fin 6) :
    max ((zisK i).k - 1) (zisK i).totalJetCap < ringChar GoldilocksCubic := by
  rw [goldilocksCubic_ringChar]
  fin_cases i <;> norm_num [zisK, Goldilocks.fieldSize]

open Classical in
/-- Constructed exceptional sets meet the per-phase budgets. -/
theorem exists_exceptional_at_target (i : Fin 6)
    -- Any evaluation domain and received tuple of the recorded width; no bound is an input.
    (domain : Fin (zisK i).n ↪ GoldilocksCubic)
    (values : Fin ((zisK i).batchingDegree + 1) → Fin (zisK i).n → GoldilocksCubic) :
    -- One finite exceptional set is chosen before z and P, simultaneously for all candidates.
    ∃ exceptional : Finset GoldilocksCubic,
      -- Its actual cardinality is bounded by the checked integer ceiling for this row.
      (exceptional.card : ℚ) ≤ zisKBudget i ∧
        -- Use that same set's cardinality in the local error expression E / (g q).
        algebraicSlot i exceptional.card ≤ (1 / 2 ^ 128 : ℚ) ∧
        -- Every sufficiently close low-degree candidate outside the set has exact recovery.
        ∀ z ∉ exceptional, ∀ P : GoldilocksCubic[X], P.degree < (zisK i).k →
          (zisK i).agreement ≤
            (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
          -- P is a powers combination of messages; its entire agreement set is their common set.
          HasExactPowerAgreement domain values (RingHom.id GoldilocksCubic) (zisK i).k z P := by
  -- First construct the set and exact-recovery proof from the finite interpolation theorem.
  obtain ⟨exceptional, hcard, hgood⟩ :=
    ConcreteCurveMCA.zisK_exists_exceptional_exact_powerAgreement i domain values
      (algebraMap GoldilocksCubic (AlgebraicClosure GoldilocksCubic))
      (Or.inr (characteristic_admissible i))
  -- Only the numerical error comparison remains; no recovery premise is added here.
  refine ⟨exceptional, hcard, ?_, hgood⟩
  apply le_trans ?_ (recorded_slot_le i)
  unfold algebraicSlot
  exact div_le_div_of_nonneg_right hcard (by positivity)

/-- Keeping the outer payload fixed, the three removed query responses outweigh the new nonce. -/
theorem replacement_payload_strict (unchanged : ℕ) :
    unchanged + ZisK.replacementQueries * 8784 + 8 <
      unchanged + ZisK.originalQueries * 8784 := by
  have h := ZisK.payload_reduction unchanged
  omega

end

end ArkLibExamples.ReedSolomon.ZisKCertifiedBudget
