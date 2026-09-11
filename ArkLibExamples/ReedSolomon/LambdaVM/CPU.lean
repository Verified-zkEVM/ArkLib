/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLibExamples.ReedSolomon.LambdaVM.Certificates
import ArkLibExamples.ReedSolomon.LambdaVM.AirBounds
import ArkLibExamples.ReedSolomon.LambdaVM.Budget
import ArkLibExamples.ReedSolomon.LambdaVM.Payload
import ArkLibExamples.ReedSolomon.LambdaVM.Reconstruction
import ArkLibExamples.ReedSolomon.LambdaVM.Folding
import ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.AnchoredAgreement

/-!
# LambdaVM's CPU table at 208 queries

Fix the 38 received main columns before sampling two distinct early evaluation points.
The complete candidate family uses degree bound `T + 3`: undoing the cubic DEEP divisor
can produce degree `T + 2`. Its cardinality is proved from the interpolation certificate.
The subsequent degree-50 powers combination has 51 terms and degree bound `T`.
Keeping these two degree bounds separate is essential to the local error calculation.

The endpoint constructs actual curve exceptions and the actual anchor collision set.
It bounds their contribution together with the CPU AIR/OOD and query terms by `2^-128`.
`AirBounds` derives the residual and cancellation degrees from stated AIR hypotheses;
`Reconstruction` and `Folding` expose the local extraction steps. This endpoint sums their
allocations; it does not identify the sum with an acceptance probability for a full transcript.
This is a mathematical specialization with an explicit transcript-order condition, not
verification of LambdaVM's prover, verifier, or serialization implementation.
-/
open Polynomial ReedSolomon ReedSolomon.ListDecoding
namespace ArkLibExamples.ReedSolomon.LambdaVM.CPU
open ConcreteFields
open scoped BigOperators
noncomputable section
local instance cPUDecidableEq : DecidableEq GoldilocksCubic := Classical.decEq _

/-- The list theorem's threshold is exactly the selected integer agreement. -/
theorem cpu_threshold : agreementThreshold gap 65536 (32768 + 3) ≤ 45690 := by
  simpa [listProfile] using le_of_eq threshold_eq

/-- Every jointly agreeing main tuple belongs to this complete finite candidate family.
It depends on the committed words, before either early point or any lookup challenge. -/
def mainCandidates (domain : Fin 65536 ↪ GoldilocksCubic)
    (received : Matrix (Fin 65536) (Fin 38) GoldilocksCubic) :
    Finset (Fin 38 → GoldilocksCubic[X]) :=
  AnchoredAgreement.candidateFamily (T := 32768) (A := 45690)
    domain received gap gap_admissible.1 (by decide) (by decide) cpu_threshold
    (widthThirtyEight_lambda_le domain)

/-- The CPU list ceiling is derived for the complete family, not assumed for a chosen subset. -/
theorem mainCandidates_card_le (domain : Fin 65536 ↪ GoldilocksCubic)
    (received : Matrix (Fin 65536) (Fin 38) GoldilocksCubic) :
    (mainCandidates domain received).card ≤ listBound :=
  AnchoredAgreement.candidateFamily_card_le domain received gap gap_admissible.1
    (by decide) (by decide) cpu_threshold (widthThirtyEight_lambda_le domain)

/-- The probability of an early pair failing to distinguish CPU candidates has the exact
outside-domain sampling denominator, over the actual cubic Goldilocks field. -/
theorem mainCandidates_collision_le (domain : Fin 65536 ↪ GoldilocksCubic)
    (received : Matrix (Fin 65536) (Fin 38) GoldilocksCubic) :
    AnchoredAgreement.badAnchorRate domain (mainCandidates domain received) ≤
      anchorError listBound := by
  have hspace : 65536 + 1 < Fintype.card GoldilocksCubic := by
    rw [fieldSize_eq]
    decide
  have h := AnchoredAgreement.candidateFamily_badAnchorRate_le domain received gap
    gap_admissible.1 (by decide) (by decide) cpu_threshold
    (widthThirtyEight_lambda_le domain) hspace
  simpa only [mainCandidates, fieldSize_eq, anchorError, traceRows, length] using h

/-- Every good early pair fixes the trace before lookup. The claims may depend on the
sampled pair. The selected option precedes every later OOD value, quotient, and interpolant;
`none` means that successful later extraction is impossible. -/
theorem trace_fixed_before_lookup
    (domain : Fin 65536 ↪ GoldilocksCubic)
    (received : Matrix (Fin 65536) (Fin 38) GoldilocksCubic)
    (s₁ s₂ : GoldilocksCubic)
    (hSampled : (s₁, s₂) ∈ ArkLib.TwoPointPolynomialCollision.orderedDistinctPairs
      (ArkLib.TwoPointPolynomialCollision.outsideDomain domain))
    (hGood : (s₁, s₂) ∉ AnchoredAgreement.badAnchorPairs domain
      (mainCandidates domain received))
    (claimed₁ claimed₂ : Fin 38 → GoldilocksCubic) :
    ∃ selected : Option (Fin 38 → GoldilocksCubic[X]),
      (∀ tuple, selected = some tuple → tuple ∈ mainCandidates domain received ∧
        AnchoredAgreement.twoAnchorValues s₁ s₂ tuple = ⟨claimed₁, claimed₂⟩) ∧
      ∀ later : AnchoredAgreement.LaterCubicReconstruction (F := GoldilocksCubic) 38,
        AnchoredAgreement.SuccessfulCubicReconstruction domain received s₁ s₂
            claimed₁ claimed₂ (T := 32768) (A := 45690) later →
          selected.map (AnchoredAgreement.traceRemainderTuple 32768) =
            some (AnchoredAgreement.traceRemainderTuple 32768
              (AnchoredAgreement.cubicReconstructedTuple s₁ s₂ later.z
                later.quotient later.interpolant)) := by
  exact AnchoredAgreement.exists_selectedTrace_before_later domain received gap
    gap_admissible.1 (by decide) (by decide) cpu_threshold
    (widthThirtyEight_lambda_le domain) (by decide) s₁ s₂ hSampled hGood claimed₁ claimed₂

/-- The actual nine curve sets and actual early collision fraction fit one CPU-local allocation.
All received words are arbitrary. Curve sets precede their challenges and candidates; the main
candidate family precedes the early points and subsequent lookup randomness. -/
theorem exists_certified_cpu_budget
    (domains : ∀ i : Fin 9, Fin (profiles i).n ↪ GoldilocksCubic)
    (values : ∀ i : Fin 9, Fin ((profiles i).batchingDegree + 1) →
      Fin (profiles i).n → GoldilocksCubic)
    (received : Matrix (Fin 65536) (Fin 38) GoldilocksCubic) :
    ∃ family : ExceptionalFamily domains values,
      (mainCandidates (domains 0) received).card ≤ listBound ∧
      localError (∑ i, (family.exceptional i).card) listBound 208
        (AnchoredAgreement.badAnchorRate (domains 0)
          (mainCandidates (domains 0) received)) < (1 / 2 ^ 128 : ℚ) := by
  obtain ⟨family⟩ := exists_exceptionalFamily domains values
  refine ⟨family, mainCandidates_card_le _ _, ?_⟩
  exact local_error_of_bounds family.total_card_le le_rfl (mainCandidates_collision_le _ _)


end
end ArkLibExamples.ReedSolomon.LambdaVM.CPU
