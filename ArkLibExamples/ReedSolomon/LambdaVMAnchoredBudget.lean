/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLibExamples.ReedSolomon.LambdaVMAnchoredCandidates
import ArkLibExamples.ReedSolomon.LambdaVMCertifiedBudget

/-!
# Certified anchored LambdaVM budgets

The current LambdaVM application samples two distinct field points outside the main evaluation
domain and opens the twelve main-column polynomials at both points before LogUp.  Distinct
degree-`T + 2` candidate tuples can share both claimed openings only when the anchor pair lies in
a set of density at most
`choose(L, 2) * ((T + 2) / (q - n - 1)) ^ 2`.

This module combines that derived collision bound with the five anchored list certificates and
the already certified polynomial-curve exceptional sets.  It checks the complete changed local
expression from the paper: curve exceptions, query acceptance after 20 grinding bits, the
`7 L / q` cancellation term, the restored cubic-quotient OOD term, and anchor collision.  Every
row is strictly below `2^-128` over the canonical cubic Goldilocks field.

## Reading the statements

`collision_rate_le_of_agreement` applies to any finite family of polynomial tuples, including the
twelve main columns.  It derives the family-size bound from joint agreement and the interleaved
`Lambda` theorem before applying the collision count.  `exists_certified_anchored_main_budgets`
then consumes the resulting actual collision fraction in the local sum.  `payload_reduction`
checks the paper's net byte reductions after charging 576 bytes for two openings of twelve
cubic-field elements.

## Reading the paper's final EQ-table statement

Start at `exists_certified_anchored_main_budgets`, corresponding to Section 6.5, equation (56),
and Table 3 of the main paper. The five indices select trace lengths
2048, 4096, 8192, 16384, and 32768.
Here `profiles` supplies the original main-tuple dimension `T + 3`, while `lambdaVM` supplies
the initial and folding curve profiles. Distinguishing these prevents a degree-`T + 2` recovered
main polynomial from being mistaken for a degree-`< T` DEEP quotient.

The inputs after `∀ ... candidates` describe any finite collection of twelve-column tuples
whose joint agreement meets the threshold. No list-size, collision-rate, or exceptional-set
bound is assumed. The conclusion bounds each of these quantities, then puts the actual
collision fraction and exceptional cardinalities into one rational error expression.
`ExceptionalFamily` also carries exact polynomial recovery outside its sets.

The term-by-term comments on `localErrorWithCollision` follow the order of the paper's equation.
The final inequality is strict. `payload_reduction` is the separate byte calculation, including
the 576 bytes for two openings of twelve cubic-field elements.

This is the local analytical model used by the application table.  It does not model transcript
serialization, the full VM protocol, or unrelated LogUp error terms.
-/

open Polynomial Code
open ReedSolomon ReedSolomon.ListDecoding

namespace ArkLibExamples.ReedSolomon.LambdaVMAnchoredBudget

open ConcreteFields ConcreteCurves ConcreteCurveBounds
open LambdaVMAnchoredLists LambdaVMFields LambdaVMTables
open LambdaVMAnchoredCandidates
open LambdaVMCertifiedBudget
open ArkLib.TwoPointPolynomialCollision
open ArkLib.FiniteFieldBudget

noncomputable section

local instance : DecidableEq GoldilocksCubic := Classical.decEq _

/-- Degree cap of a polynomial restored from the anchored cubic main DEEP quotient. -/
def anchorDegree (i : Fin 5) : ℕ := traceRows i + 2

/-- Conservative probability contribution of collisions among at most `list` candidates. -/
def anchorCollisionError (i : Fin 5) (list : ℕ) : ℚ :=
  (list.choose 2 : ℚ) *
    ((anchorDegree i : ℚ) /
      (LambdaVM.challengeCardinality - (profiles i).n - 1 : ℕ)) ^ 2

/-- The complete changed local expression for one anchored LambdaVM row. -/
def localError (i : Fin 5) (exceptional list : ℕ) : ℚ :=
  (exceptional : ℚ) / LambdaVM.challengeCardinality +
    (1 / 2 ^ 20 : ℚ) *
      (((profiles i).agreement : ℚ) / (profiles i).n) ^ (tables i).queries +
    (7 * list : ℕ) / LambdaVM.challengeCardinality +
    (((4 * traceRows i + 6) * list + 2 * (profiles i).n + 2 : ℕ) : ℚ) /
      (LambdaVM.challengeCardinality - (profiles i).n - traceRows i : ℕ) +
    anchorCollisionError i list

/-- The same local expression with an actual exceptional-pair fraction in place of its
closed-form upper bound. -/
def localErrorWithCollision (i : Fin 5) (exceptional list : ℕ) (collision : ℚ) : ℚ :=
  -- Initial powers batching and all binary folds: (E_17 + sum_j E_j) / q.
  (exceptional : ℚ) / LambdaVM.challengeCardinality +
    -- Query term a^t; this is the only term receiving the 20 grinding bits.
    (1 / 2 ^ 20 : ℚ) *
      (((profiles i).agreement : ℚ) / (profiles i).n) ^ (tables i).queries +
    -- Candidate-dependent cancellation contribution, 7 Lambda / q.
    (7 * list : ℕ) / LambdaVM.challengeCardinality +
    -- AIR/OOD residual contribution after restoring the cubic main-column quotient.
    (((4 * traceRows i + 6) * list + 2 * (profiles i).n + 2 : ℕ) : ℚ) /
      (LambdaVM.challengeCardinality - (profiles i).n - traceRows i : ℕ) +
    -- Actual fraction of anchor pairs that fail to distinguish the candidate tuples.
    collision

/-- The five exact paper inputs make the changed local expression strictly smaller than
`2^-128`. -/
theorem budget_at_target (i : Fin 5) :
    localError i (tables i).exceptionalBudget (listBounds i) <
      (1 / 2 ^ 128 : ℚ) := by
  rw [localError, anchorCollisionError, Nat.choose_two_right]
  fin_cases i <;> norm_num [tables, profiles, listBounds, traceRows, anchorDegree,
    LambdaVM.challengeCardinality]

/-- Smaller certified exceptional sets and candidate lists preserve the strict local target. -/
theorem local_error_of_count_bounds (i : Fin 5) {exceptional list : ℕ}
    (hE : exceptional ≤ (tables i).exceptionalBudget)
    (hL : list ≤ listBounds i) :
    localError i exceptional list < (1 / 2 ^ 128 : ℚ) := by
  apply lt_of_le_of_lt _ (budget_at_target i)
  unfold localError anchorCollisionError
  gcongr

/-- A collision fraction below the derived anchor term can be substituted into the complete
local expression without weakening the target. -/
theorem local_error_with_collision_of_bounds (i : Fin 5) {exceptional list : ℕ}
    {collision : ℚ} (hE : exceptional ≤ (tables i).exceptionalBudget)
    (hL : list ≤ listBounds i) (hcollision : collision ≤ anchorCollisionError i list) :
    localErrorWithCollision i exceptional list collision < (1 / 2 ^ 128 : ℚ) := by
  apply lt_of_le_of_lt _ (local_error_of_count_bounds i hE hL)
  unfold localErrorWithCollision localError
  gcongr

/-- The finite-set collision theorem specializes to the exact LambdaVM anchor expression over
the canonical cubic Goldilocks field.  The width remains arbitrary; use width 12 for the main
columns. -/
theorem collision_rate_le (i : Fin 5) (width : ℕ)
    (domain : Fin (profiles i).n ↪ GoldilocksCubic)
    (candidates : Finset (Fin width → GoldilocksCubic[X]))
    (hdegree : ∀ tuple ∈ candidates, ∀ j, (tuple j).natDegree ≤ anchorDegree i)
    (hlist : candidates.card ≤ listBounds i) :
    collisionRate domain candidates ≤ anchorCollisionError i (listBounds i) := by
  have hspace : (profiles i).n + 1 < Fintype.card GoldilocksCubic := by
    rw [goldilocksCubic_card_eq_lambdaVM]
    fin_cases i <;> norm_num [profiles, LambdaVM.challengeCardinality]
  simpa [anchorCollisionError, goldilocksCubic_card_eq_lambdaVM] using
    ArkLib.TwoPointPolynomialCollision.collisionRate_le
      domain candidates hdegree hlist hspace

/-- Joint agreement with a single received word discharges the list-size premise internally.
This is the public collision statement used for the twelve main columns. -/
theorem collision_rate_le_of_agreement (i : Fin 5) (width : ℕ)
    (domain : Fin (profiles i).n ↪ GoldilocksCubic)
    (received : Matrix (Fin (profiles i).n) (Fin width) GoldilocksCubic)
    (candidates : Finset (Fin width → GoldilocksCubic[X]))
    (hdegree : ∀ tuple ∈ candidates, ∀ j, (tuple j).degree < (profiles i).k)
    (hagreement : ∀ tuple ∈ candidates,
      (profiles i).agreement ≤ Code.agree (tupleEvaluation domain tuple) received) :
    collisionRate domain candidates ≤ anchorCollisionError i (listBounds i) := by
  rw [anchorCollisionError, anchorDegree, ← goldilocksCubic_card_eq_lambdaVM]
  simpa using
    goldilocksCubic_collisionRate_le_of_agreement
      i width domain received candidates hdegree hagreement

/-- For any actual close candidate family, its derived collision fraction can replace the anchor
union-bound term in the complete local error expression.  Neither a list cap nor a final error
bound is assumed. -/
theorem local_error_with_candidate_collision (i : Fin 5) (width : ℕ)
    (domain : Fin (profiles i).n ↪ GoldilocksCubic)
    (received : Matrix (Fin (profiles i).n) (Fin width) GoldilocksCubic)
    (candidates : Finset (Fin width → GoldilocksCubic[X]))
    (hdegree : ∀ tuple ∈ candidates, ∀ j, (tuple j).degree < (profiles i).k)
    (hagreement : ∀ tuple ∈ candidates,
      (profiles i).agreement ≤ Code.agree (tupleEvaluation domain tuple) received)
    {exceptional : ℕ} (hE : exceptional ≤ (tables i).exceptionalBudget) :
    localErrorWithCollision i exceptional (listBounds i) (collisionRate domain candidates) <
      (1 / 2 ^ 128 : ℚ) := by
  apply local_error_with_collision_of_bounds i hE le_rfl
  exact collision_rate_le_of_agreement i width domain received candidates hdegree hagreement

/-- The initial curve row and anchored list profile have the same evaluation-domain length. -/
theorem initialRow_length_eq (i : Fin 5) :
    (lambdaVM (initialRow i)).n = (profiles i).n := by
  fin_cases i <;> decide

/-- Reuse each table's initial curve domain for its anchored list statements. -/
def initialListDomain
    (domains : ∀ i : Fin 35, Fin (lambdaVM i).n ↪ GoldilocksCubic) (i : Fin 5) :
    Fin (profiles i).n ↪ GoldilocksCubic where
  toFun j := domains (initialRow i) (Fin.cast (initialRow_length_eq i).symm j)
  inj' := (domains (initialRow i)).injective.comp
    (Fin.cast_injective (initialRow_length_eq i).symm)

/-- Actual curve exceptional sets, width-12 and width-18 anchored list ceilings, and the exact
five-row local budget all hold simultaneously for arbitrary domains and received power tuples. -/
theorem exists_certified_anchored_budgets
    (curveDomains : ∀ i : Fin 35, Fin (lambdaVM i).n ↪ GoldilocksCubic)
    (curveValues : ∀ i : Fin 35,
      Fin ((lambdaVM i).batchingDegree + 1) → Fin (lambdaVM i).n → GoldilocksCubic) :
    ∃ family : ExceptionalFamily curveDomains curveValues,
      ∀ i : Fin 5,
        windowSum (fun j ↦ (family.exceptional j).card) i ≤
            (tables i).exceptionalBudget ∧
        Lambda
            (Code.interleavedCodeSet (κ := Fin 12)
              (ReedSolomon.code (initialListDomain curveDomains i) (profiles i).k :
                Set (Fin (profiles i).n → GoldilocksCubic)))
            (capacityRadius (gap i) (profiles i).n (profiles i).k) ≤
              (listBounds i : ℕ∞) ∧
        Lambda
            (Code.interleavedCodeSet (κ := Fin 18)
              (ReedSolomon.code (initialListDomain curveDomains i) (profiles i).k :
                Set (Fin (profiles i).n → GoldilocksCubic)))
            (capacityRadius (gap i) (profiles i).n (profiles i).k) ≤
              (listBounds i : ℕ∞) ∧
        localError i (windowSum (fun j ↦ (family.exceptional j).card) i)
            (listBounds i) < (1 / 2 ^ 128 : ℚ) := by
  let family := (exists_exceptionalFamily curveDomains curveValues).some
  refine ⟨family, fun i ↦ ⟨family.window_card_le i,
    lambda_le i 12 (initialListDomain curveDomains i) (characteristic_admissible i),
    widthEighteen_lambda_le i (initialListDomain curveDomains i), ?_⟩⟩
  exact local_error_of_count_bounds i (family.window_card_le i) le_rfl

/-- The five-row semantic endpoint for the twelve main columns.  For every received main-column
word and every finite family of jointly agreeing degree-bounded candidates, the family cardinality
and anchor-collision fraction are derived, and the local expression using that actual fraction is
strictly below `2^-128`. -/
theorem exists_certified_anchored_main_budgets
    -- Arbitrary received data for all 35 curves; these are not assumed valid codewords.
    (curveDomains : ∀ i : Fin 35, Fin (lambdaVM i).n ↪ GoldilocksCubic)
    (curveValues : ∀ i : Fin 35,
      Fin ((lambdaVM i).batchingDegree + 1) → Fin (lambdaVM i).n → GoldilocksCubic) :
    -- Construct one family of exceptional sets, with exact recovery, before choosing candidates.
    ∃ family : ExceptionalFamily curveDomains curveValues,
      -- Fix a table size and any received main word, with any finite set of close candidates.
      ∀ (i : Fin 5)
        (received : Matrix (Fin (profiles i).n) (Fin 12) GoldilocksCubic)
        (candidates : Finset (Fin 12 → GoldilocksCubic[X])),
        -- Membership conditions only: each column has the specified degree and the tuple is close.
        (∀ tuple ∈ candidates, ∀ j, (tuple j).degree < (profiles i).k) →
        (∀ tuple ∈ candidates,
          (profiles i).agreement ≤
            Code.agree (tupleEvaluation (initialListDomain curveDomains i) tuple) received) →
        -- Conclusion 1: the same actual curve exceptions fit this table's summed budget.
        windowSum (fun j ↦ (family.exceptional j).card) i ≤
            (tables i).exceptionalBudget ∧
        -- Conclusion 2: joint agreement itself bounds the number of candidate tuples.
        candidates.card ≤ listBounds i ∧
        -- Conclusion 3: two early openings distinguish them except on this fraction of pairs.
        collisionRate (initialListDomain curveDomains i) candidates ≤
            anchorCollisionError i (listBounds i) ∧
        -- Conclusion 4: combine the actual exceptions/collisions with the proved list ceiling.
        localErrorWithCollision i
            (windowSum (fun j ↦ (family.exceptional j).card) i) (listBounds i)
            (collisionRate (initialListDomain curveDomains i) candidates) <
              (1 / 2 ^ 128 : ℚ) := by
  -- Obtain geometric witnesses, then apply the list, collision, and arithmetic theorems in order.
  let family := (exists_exceptionalFamily curveDomains curveValues).some
  refine ⟨family, fun i received candidates hdegree hagreement ↦
    ⟨family.window_card_le i, ?_, ?_, ?_⟩⟩
  · exact candidate_card_le i 12 (initialListDomain curveDomains i) received
      (characteristic_admissible i) candidates hdegree hagreement
  · exact collision_rate_le_of_agreement i 12 (initialListDomain curveDomains i)
      received candidates hdegree hagreement
  · exact local_error_with_candidate_collision i 12 (initialListDomain curveDomains i)
      received candidates hdegree hagreement (family.window_card_le i)

/-- Two openings of twelve cubic-field elements cost 576 bytes. -/
def anchorProofBytes : ℕ := 2 * 12 * 24

/-- Net removed field-element and authentication-path bytes after charging the anchors. -/
def savedBytes : Fin 5 → ℕ := ![30936, 34176, 36824, 34848, 30952]

/-- The separately serialized response model gives the five net reductions recorded in the
anchored application table, for any unchanged outer payload. -/
theorem payload_reduction (i : Fin 5) (unchanged : ℕ) :
    unchanged + 219 * (tables i).responseBytes =
      unchanged + (tables i).queries * (tables i).responseBytes +
        anchorProofBytes + savedBytes i := by
  have h : 219 * (tables i).responseBytes =
      (tables i).queries * (tables i).responseBytes + anchorProofBytes + savedBytes i := by
    fin_cases i <;> decide
  omega

/-- Net anchored savings through the shared fixed-payload calculation. -/
theorem fixed_payload_saving (i : Fin 5) :
    fixedPayloadSaving 219 (tables i).queries (tables i).responseBytes anchorProofBytes =
      savedBytes i := by
  fin_cases i <;> norm_num [fixedPayloadSaving, tables, anchorProofBytes, savedBytes]

end

end ArkLibExamples.ReedSolomon.LambdaVMAnchoredBudget
